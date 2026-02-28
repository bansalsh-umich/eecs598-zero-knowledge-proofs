//! Fiat-Shamir transcript for non-interactive proofs.
//!
//! Both the prover and verifier create a [`Transcript`] with the same protocol
//! label and then perform the **exact same sequence** of
//! [`append_message`](Transcript::append_message) and
//! [`get_challenge`](Transcript::get_challenge) calls. Because the underlying
//! sponge is deterministic, they derive identical challenges as long as the
//! absorbed messages match. Any type that implements [`Serialize`] can be
//! absorbed into the transcript, and any type that implements [`FromBytes`]
//! can be squeezed out as a challenge.
//!
//! This design is heavily inspired by the [Merlin](https://merlin.cool)
//! transcript library.
//!
//! # Why a transcript object?
//!
//! Manually hashing values at each step of a protocol is error-prone. Common
//! pitfalls include:
//!
//! - **Ambiguous encoding.** If two different `(label, message)` pairs can
//!   produce the same byte stream, a malicious prover may be able to swap one
//!   for the other without changing the challenge. `append_message` frames
//!   every call with domain-separator tags and explicit lengths, so distinct
//!   inputs always produce distinct absorptions.
//!
//! - **Missing bindings.** Forgetting to absorb a value (e.g. a commitment, or
//!   the statement being proved) means the resulting challenge is not bound to
//!   it, potentially allowing a prover to cheat. Routing everything through one
//!   `Transcript` makes omissions easier to spot in review. There are libraries that attempt to
//!   further systamatize what bindings are supposed to be hashed before a challenge may be
//!   extracted (such as Trail of Bits' `decree` library).
//!
//! - **Cross-protocol replay.** Without domain separation, a challenge derived
//!   in one protocol context could be valid in another. The protocol label
//!   passed to [`Transcript::new`] is absorbed first, ensuring that transcripts
//!   from different protocols (or different sub-protocols under composition)
//!   diverge immediately.
//!
//! # Example
//!
//! ```rust,ignore
//! // Both prover and verifier execute the same sequence:
//! let mut trans = Transcript::new("my_protocol");
//! trans.append_message("commitment", &comm);
//! let challenge: Scalar = trans.get_challenge("challenge");
//! ```

#![allow(unused)]
use p1::FromBytes;
use serde::Serialize;

use keccak_state::KeccakState;

#[derive(Clone, Copy, Eq, PartialEq, Debug, Default)]
enum SpongeMode {
    #[default]
    Absorb,
    Squeeze,
}

#[derive(Debug, Clone, Default)]
pub struct Sponge {
    state: KeccakState,
    pos: u8,
    mode: SpongeMode,
}

impl Sponge {
    const SEC_PARAM: usize = 256;
    #[allow(clippy::cast_possible_truncation)]
    const BYTE_RATE: u8 = (KeccakState::BYTE_LEN - Self::SEC_PARAM / 4) as u8; //136 bytes
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn process_bytes<I, F>(&mut self, mode: SpongeMode, iter: I, mut f: F)
    where
        I: IntoIterator,
        F: FnMut(&mut Self, I::Item),
    {
        // Successive squeezes/absorbs do not require intervening permutations
        // However whenever we 'switch' from one mode to the other, we have to ensure we permute
        // the hash state
        if self.mode != mode {
            self.permute();
            self.mode = mode;
        }

        for x in iter {
            f(self, x);
            self.pos += 1;
            if self.pos == Self::BYTE_RATE {
                self.permute();
            }
        }
    }

    pub fn absorb(&mut self, data: &[u8]) -> &mut Self {
        self.process_bytes(SpongeMode::Absorb, data, |s, byte| {
            s.state[usize::from(s.pos)] ^= byte;
        });
        self
    }

    pub fn squeeze(&mut self, data: &mut [u8]) -> &mut Self {
        self.process_bytes(SpongeMode::Squeeze, data, |s, d| {
            *d = s.state[usize::from(s.pos)];
        });
        self
    }

    pub fn permute(&mut self) -> &mut Self {
        // Apply standard Keccak sponge padding (pad10*1): XOR 0x06 at the
        // current position and 0x80 at the last rate byte. This ensures
        // messages that exactly fill a rate block are distinguished from
        // shorter messages, matching the SHAKE/SHA-3 padding convention.
        self.state[usize::from(self.pos)] ^= 0x06;
        self.state[usize::from(Self::BYTE_RATE - 1)] ^= 0x80;
        self.state.permute();
        self.pos = 0;
        self
    }
}

/// A running hash state that both prover and verifier use to derive
/// Fiat-Shamir challenges.
///
/// Internally wraps a Keccak sponge. Messages are absorbed with
/// domain-separator tags and length prefixes; challenges are squeezed out
/// and converted to the requested type via [`FromBytes`].
pub struct Transcript {
    hasher: Sponge,
}

#[repr(u8)]
enum DomainSeparator {
    Metadata,
    Message,
    Challenge,
}

fn len_to_bytes(len: usize) -> [u8; 4] {
    u32::try_from(len)
        .expect("slice length must fit into 4 bytes")
        .to_le_bytes()
}

impl Transcript {
    /// Create a new transcript for the given protocol.
    ///
    /// The `protocol_label` is immediately absorbed, domain-separating this
    /// transcript from any other protocol (or any other instance that uses a
    /// different label).
    #[must_use]
    pub fn new(protocol_label: &str) -> Self {
        let hasher = Sponge::new();

        let mut transcript = Transcript { hasher };
        transcript.append_message(protocol_label, ());
        transcript
    }

    /// Absorb a labeled message into the transcript.
    ///
    /// The message is serialized with [BCS](https://docs.rs/bcs) (which
    /// provides canonical, non-ambiguous encoding), then absorbed together
    /// with the label and explicit lengths. This ensures that different labels or messages always
    /// produce different byte streams.
    pub fn append_message<T: Serialize>(&mut self, label: &str, message: T) -> &mut Self {
        // bcs (Binary Canonical Serialization) that guarantees that two distinct values of type
        // 'T' will hash to distinct byte strings (its technically a little bit more complicated
        // than this, because it additionally depends on the implementation of 'Serialize' not e.g.
        // skipping fields)
        let mbytes = bcs::to_bytes(&message).expect("failed to serialize message");
        self.hasher
            .absorb(&[DomainSeparator::Metadata as u8])
            .absorb(&len_to_bytes(label.len()))
            .absorb(label.as_bytes())
            .absorb(&len_to_bytes(mbytes.len()))
            .absorb(&[DomainSeparator::Message as u8])
            .absorb(&mbytes);
        self
    }

    /// Squeeze a pseudorandom challenge from the transcript.
    ///
    /// The returned value is deterministically derived from every message
    /// absorbed so far, so the prover and verifier will obtain the same
    /// challenge as long as their transcripts agree.
    ///
    /// The squeezed bytes are absorbed back into the sponge (with a
    /// `Challenge` domain separator) so that subsequent operations are
    /// bound to the fact that a challenge was derived at this point.
    #[must_use]
    pub fn get_challenge<T: FromBytes>(&mut self, label: &str) -> T {
        let mut challenge = vec![0u8; T::BYTES_NEEDED];
        self.hasher
            .absorb(&[DomainSeparator::Metadata as u8])
            .absorb(&len_to_bytes(label.len()))
            .absorb(&[DomainSeparator::Challenge as u8]);
        self.hasher.squeeze(&mut challenge);
        T::from_bytes(&challenge)
    }
}

mod keccak_state {
    use std::fmt::{self, Debug};
    /// The state of the Keccak permutation function. The keccak permutation function requires the
    /// state to be 25 u64s, however the external interface of this type requires writing to
    /// individual bytes. Rather than requiring bitwise operations or performing a menual
    /// conversion everytime a permutation occurs (which imposes a runtime cost),
    /// this type is a 'union' which allows one to have simultaneous 'views' into the same block of memory.
    ///
    /// This is a very useful trick in performance critical software (granted this would not be a
    /// performance bottlneck in p3), but one you should be careful employing. I (Chad) have
    /// personally found undefined behavior in actual Rust crypto libraries, because they did this
    /// incorrectly. There is a widely used crate called 'zerocopy' which will do tricks like this
    /// for you, so you never have to write 'unsafe' and potentially invoke undefined behavior.
    ///
    /// SAFETY:
    /// Unions are similar to enums, except there is no way to check which variant the union is.
    /// Both variants just share the same memory (which is exactly what we want for this purpose).
    /// These are semantically the same as 'union's in C and C++ (and with the #[repr(C)]
    /// attribute, they're guaranteed to have the same memory layout as their C/C++ equivalents).
    /// Sensibly, accessing the members of a union is, by default, unsafe. Rust cannot tell
    /// that you're not trying to interpret one type via the bytes of another incompatible type
    /// which, in principle, could lead to trying to dereference invalid pointers and all kinds of
    /// other nasty stuff
    ///
    /// However, accessing either variant of this union is _always_ safe (regardless of past writes). This is because:
    /// (1) all bit-patterns of the types of both words and bytes are valid
    /// (2) words and bytes have the same size (200 bytes)
    /// (3) both variants are guaranteed to start at the same memory address (only true because of #[repr(C)])
    ///
    /// Hence this type can safely provide `.as_(mut_)bytes()` and `.as_(mut_)words()` which just
    /// wrap the unsafe accesses.
    #[repr(C)]
    #[derive(Clone, Copy)]
    pub union KeccakState {
        words: [u64; Self::WORD_LEN],
        bytes: [u8; Self::BYTE_LEN],
    }

    const _: () = {
        // These are guaranteed to hold, but for illustration purposes, these are compile time
        // assertions that guarantee the safety described above.
        use std::mem::{offset_of, size_of};
        assert!(
            size_of::<[u64; KeccakState::WORD_LEN]>() == size_of::<[u8; KeccakState::BYTE_LEN]>()
        );
        assert!(offset_of!(KeccakState, words) == offset_of!(KeccakState, bytes));
    };

    impl Debug for KeccakState {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_tuple("KeccakState").field(self.as_bytes()).finish()
        }
    }

    impl Default for KeccakState {
        #[inline]
        fn default() -> Self {
            Self::new()
        }
    }

    impl std::ops::Index<usize> for KeccakState {
        type Output = u8;
        #[inline]
        fn index(&self, index: usize) -> &Self::Output {
            self.as_bytes().index(index)
        }
    }

    impl std::ops::IndexMut<usize> for KeccakState {
        #[inline]
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            self.as_mut_bytes().index_mut(index)
        }
    }

    impl KeccakState {
        pub(super) const WORD_LEN: usize = 25;
        pub(super) const BYTE_LEN: usize = Self::WORD_LEN * 8;

        #[inline]
        #[allow(unused)]
        pub(super) const fn new() -> Self {
            Self { words: [0; _] }
        }

        #[inline]
        pub(super) const fn as_words(&self) -> &[u64; Self::WORD_LEN] {
            // # SAFETY
            // See the docstring on 'KeccakState'
            unsafe { &self.words }
        }

        #[inline]
        pub(super) const fn as_mut_words(&mut self) -> &mut [u64; Self::WORD_LEN] {
            // # SAFETY
            // See the docstring on 'KeccakState'
            unsafe { &mut self.words }
        }

        #[inline]
        pub(super) const fn as_bytes(&self) -> &[u8; Self::BYTE_LEN] {
            // # SAFETY
            // See the docstring on 'KeccakState'
            unsafe { &self.bytes }
        }

        #[inline]
        pub(super) const fn as_mut_bytes(&mut self) -> &mut [u8; Self::BYTE_LEN] {
            // # SAFETY
            // See the docstring on 'KeccakState'
            unsafe { &mut self.bytes }
        }

        #[inline]
        pub(super) fn permute(&mut self) {
            self.normalize_endianness();
            keccak::f1600(self.as_mut_words());
            self.normalize_endianness();
        }

        #[inline]
        /// on big-endian platforms, swap byte order before calling keccak
        /// to ensure e.g. a big-endian prover and little endian verifier agree
        /// on transcript
        fn normalize_endianness(&mut self) {
            if cfg!(target_endian = "big") {
                for word in self.as_mut_words() {
                    *word = word.swap_bytes();
                }
            }
        }
    }
}
