use crate::{Circuit, ConstraintInterpreter, Lc, Result, Variable, Visibility};
use p1::Field;

#[derive(Clone)]
/// A gadget that represents a bit in the constraint system
pub struct AllocatedBit {
    /// Known value, if one is available.
    pub value: Option<bool>,
    /// Underlying variable in the constraint system.
    pub var: Variable,
}

impl AllocatedBit {
    pub fn alloc<F: Field, I: ConstraintInterpreter<F>>(
        interp: &mut I,
        value: Option<bool>,
    ) -> Result<Self> {
        // Format: Allocate -> enforce constraint -> return value and allocated
        let allocated = interp.alloc(|| "Alloc bit", Visibility::Private, || value.map(F::from))?;

        interp.enforce(|| "boolean constraint", Lc::from(allocated),Lc::from(F::one()) - allocated, Lc::zero());

        Ok(AllocatedBit {
            value,
            var: allocated,
        })
    }
    /// Constrain and return the XOR of two allocated bits.
    pub fn xor<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
        other: &Self,
    ) -> Result<Self> {
        let value = if let (Some(a), Some(b)) = (self.value, other.value) {
            Some(a ^ b)
        } else {
            None
        };

        let var = interp.alloc(
            || "XOR",
            Visibility::Private,
            || value.map(F::from),
        )?;

        interp.enforce(
            || "xor constraint",
            Lc::from(self.var) * F::from(2),
            Lc::from(other.var),
            Lc::from(self.var) + other.var - var,
        );

        Ok(AllocatedBit {
            value,
            var,
        })
     }
}

/// A boolean value represented either as a constrained bit, its negation, or a
/// constant.
#[derive(Clone)]
pub enum Boolean {
    /// A bit variable.
    Is(AllocatedBit),
    /// The logical negation of a bit variable.
    Not(AllocatedBit),
    /// A literal boolean constant.
    Const(bool),
}

impl Boolean {
    /// Return the known boolean value, if one is available.
    pub fn val(&self) -> Option<bool> {
        match self {
            Boolean::Is(b) => b.value,
            Boolean::Not(b) => b.value.map(|v| !v),
            Boolean::Const(v) => Some(*v),
        }
    }

    /// Convert this boolean into the corresponding linear combination.
    pub fn lc<F: Field>(&self) -> Lc<F> {
        match self {
            Boolean::Is(b) => Lc::from(b.var),
            Boolean::Not(b) => Lc::from(F::one()) - b.var,
            Boolean::Const(true) => Lc::from(F::one()),
            Boolean::Const(false) => Lc::zero(),
        }
    }

    /// Constrain and return the XOR of two booleans.
    ///
    /// Constant cases are simplified without allocating new variables.
    pub fn xor<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
        other: &Self,
    ) -> Result<Self> {
        match (self, other) {
            (Boolean::Const(a), Boolean::Const(b)) => Ok(Boolean::Const(*a ^ *b)),
            (Boolean::Const(false), x) | (x, Boolean::Const(false)) => Ok(x.clone()),
            (Boolean::Const(true), Boolean::Is(b)) | (Boolean::Is(b), Boolean::Const(true)) => {
                Ok(Boolean::Not(b.clone()))
            }
            (Boolean::Const(true), Boolean::Not(b)) | (Boolean::Not(b), Boolean::Const(true)) => {
                Ok(Boolean::Is(b.clone()))
            }
            (Boolean::Is(a), Boolean::Is(b)) => Ok(Boolean::Is(a.xor(interp, b)?)),
            (Boolean::Not(a), Boolean::Is(b)) | (Boolean::Is(b), Boolean::Not(a)) => {
                Ok(Boolean::Not(a.xor(interp, b)?))
            }
            (Boolean::Not(a), Boolean::Not(b)) => Ok(Boolean::Is(a.xor(interp, b)?)),
        }
    }

    /// Constrain and return `(a & b) XOR ((!a) & c)`.
    pub fn chr<F: Field, I: ConstraintInterpreter<F>>(
        a: &Self,
        b: &Self,
        c: &Self,
        interp: &mut I,
    ) -> Result<Self> {
        match a {
            Boolean::Const(false) => return Ok(c.clone()),
            Boolean::Const(true) => return Ok(b.clone()),
            _ => {}
        }
        let val = a
            .val()
            .zip(b.val())
            .zip(c.val())
            .map(|((a, b), c)| (a & b) ^ (!a & c));
        let mut result_value = None;
        let result_var = interp.alloc(
            || "chr",
            Visibility::Private,
            || {
                result_value = val;
                val.map(F::from)
            },
        )?;
        interp.enforce(
            || "a*(b-c) = result-c",
            a.lc::<F>(),
            b.lc::<F>() - c.lc::<F>(),
            Lc::from(result_var) - c.lc::<F>(),
        );
        Ok(Boolean::Is(AllocatedBit {
            value: result_value,
            var: result_var,
        }))
    }

    /// Constrain and return the majority of `a`, `b`, and `c`.
    pub fn maj<F: Field, I: ConstraintInterpreter<F>>(
        a: &Self,
        b: &Self,
        c: &Self,
        interp: &mut I,
    ) -> Result<Self> {
        if let (Boolean::Const(av), Boolean::Const(bv), Boolean::Const(cv)) = (a, b, c) {
            return Ok(Boolean::Const((*av & *bv) | (*av & *cv) | (*bv & *cv)));
        }
        let t_val = a.val().zip(b.val()).map(|(a, b)| a & b);
        let t_var = interp.alloc(|| "maj t", Visibility::Private, || t_val.map(F::from))?;
        interp.enforce(|| "t = a*b", a.lc::<F>(), b.lc::<F>(), Lc::from(t_var));

        let val = a
            .val()
            .zip(b.val())
            .zip(c.val())
            .map(|((a, b), c)| (a & b) | (a & c) | (b & c));
        let mut result_value = None;
        let result_var = interp.alloc(
            || "maj",
            Visibility::Private,
            || {
                result_value = val;
                val.map(F::from)
            },
        )?;
        interp.enforce(
            || "(a+b-2t)*c = result-t",
            a.lc::<F>() + b.lc::<F>() - (F::from(2), t_var),
            c.lc::<F>(),
            Lc::from(result_var) - t_var,
        );
        Ok(Boolean::Is(AllocatedBit {
            value: result_value,
            var: result_var,
        }))
    }
}

/// A 32-bit word represented in little-endian bit order.
pub struct UInt32 {
    /// Bits from least significant to most significant.
    pub bits: Vec<Boolean>,
    /// Known word value, if one is available.
    pub value: Option<u32>,
}

impl UInt32 {
    /// Allocate a 32-bit word as 32 little-endian bits, with bit `i`
    /// representing `(value >> i) & 1`.
    pub fn alloc<F: Field, I: ConstraintInterpreter<F>>(
        interp: &mut I,
        value: Option<u32>,
    ) -> Result<Self> {
        let mut bits = Vec::with_capacity(32);

        for i in 0..32 {
            let bit_val = value.map(|v| ((v >> i) & 1) == 1);
            let bit = AllocatedBit::alloc(interp, bit_val)?;
            bits.push(Boolean::Is(bit));
        }

        Ok(UInt32 {
            bits,
            value,
        })
    }

    /// Return `self.rotate_right(shift)`.
    pub fn rotr(&self, shift: usize) -> Self {
        let mut new_bits = vec![Boolean::Const(false); 32];
        for i in 0..32 {
            new_bits[i] = self.bits[(i + shift) % 32].clone();
        }

        let new_value = if let Some(v) = self.value {
            Some(v.rotate_right(shift as u32))
        } else {
            None
        };

        UInt32 {
            bits: new_bits,
            value: new_value,
        }
    }
    /// Return a constant 32-bit word encoded in little-endian bit order.
    pub fn constant(val: u32) -> Self {
        UInt32 {
            bits: (0..32)
                .map(|i| Boolean::Const((val >> i) & 1 == 1))
                .collect(),
            value: Some(val),
        }
    }

    /// Constrain and return the word whose bits are `self[i] XOR other[i]`.
    pub fn xor<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
        other: &Self,
    ) -> Result<Self> {
        let value = self.value.zip(other.value).map(|(a, b)| a ^ b);
        let bits = self
            .bits
            .iter()
            .zip(&other.bits)
            .map(|(a, b)| a.xor(interp, b))
            .collect::<Result<Vec<_>>>()?;
        Ok(UInt32 { bits, value })
    }

    /// Return the SHA-256 upper-sigma function
    /// `ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)`.
    pub fn big_sigma0<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
    ) -> Result<Self> {
        let r2 = self.rotr(2);
        let r13 = self.rotr(13);
        let r22 = self.rotr(22);

        let xor_1 = r2.xor(interp, &r13)?;
        let xor_2 = xor_1.xor(interp, &r22)?;

        Ok(xor_2)
    }

    /// Return the SHA-256 upper-sigma function
    /// `ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)`.
    pub fn big_sigma1<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
    ) -> Result<Self> {
        let r6 = self.rotr(6);
        let r11 = self.rotr(11);
        let r25 = self.rotr(25);

        let xor_1 = r6.xor(interp, &r11)?;
        let xor_2 = xor_1.xor(interp, &r25)?;

        Ok(xor_2)
    }

    /// Apply SHA-256's choose function bitwise:
    /// the `i`th output bit is `(a_i & b_i) XOR ((!a_i) & c_i)`.
    pub fn chr_word<F: Field, I: ConstraintInterpreter<F>>(
        a: &Self,
        b: &Self,
        c: &Self,
        interp: &mut I,
    ) -> Result<Self> {
        let mut bits = vec![Boolean::Const(false); 32];
        for i in 0..32 {
            let a_i = &a.bits[i];
            let b_i = &b.bits[i];
            let c_i = &c.bits[i];
            bits[i] = Boolean::chr(a_i, b_i, c_i, interp)?;
        }

        let value = a.value.zip(b.value).zip(c.value).map(|((a, b), c)| {
            (a & b) ^ (!a & c)
        });

        Ok(UInt32 {bits, value})
    }

    /// Apply SHA-256's majority function bitwise:
    /// the `i`th output bit is the majority of `a_i`, `b_i`, and `c_i`.
    pub fn maj_word<F: Field, I: ConstraintInterpreter<F>>(
        a: &Self,
        b: &Self,
        c: &Self,
        interp: &mut I,
    ) -> Result<Self> {
        let mut bits = vec![Boolean::Const(false); 32];
        for i in 0..32 {
            let a_i = &a.bits[i];
            let b_i = &b.bits[i];
            let c_i = &c.bits[i];
            bits[i] = Boolean::maj(a_i, b_i, c_i, interp)?;
        }

        let value = a.value.zip(b.value).zip(c.value).map(|((a, b), c)| {
            (a & b) | (a & c) | (b & c)
        });

        Ok(UInt32 {bits, value})
    }

    /// Build an LC equal to `sum(bits[i] * 2^i)`
    fn pack_lc<F: Field>(bits: &[Boolean]) -> Lc<F> {
        let mut lc = Lc::zero();
        let mut coeff = F::one();
        let two = F::from(2);
        for bit in bits {
            match bit {
                Boolean::Is(b) => lc = lc + (coeff, b.var),
                Boolean::Not(b) => lc = lc + coeff - (coeff, b.var),
                Boolean::Const(true) => lc = lc + coeff,
                Boolean::Const(false) => {}
            }
            coeff *= two;
        }
        lc
    }

    /// Constrain and return `self + other (mod 2^32)`.
    ///
    /// The result bits are freshly allocated, and one extra carry bit accounts
    /// for the possible overflow past bit 31.
    pub fn add<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
        other: &Self,
    ) -> Result<Self> {
        let value = self.value.zip(other.value).map(|(a, b)| a.wrapping_add(b));

        let mut result_bits = Vec::with_capacity(32);
        let mut carry = Boolean::Const(false);

        for i in 0..32 {
            let curr_self = &self.bits[i];
            let curr_other = &other.bits[i];

            // Need to do zips since these values are options so there's a chance there's nothing there, only do computation
            // if all of the values are not None
            let sum_val = curr_self
                .val()
                .zip(curr_other.val())
                .zip(carry.val())
                .map(|((av, bv), cv)| ((av as u8 + bv as u8 + cv as u8) % 2) == 1);

            let sum_bit = AllocatedBit::alloc(interp, sum_val)?;
            let sum_bool = Boolean::Is(sum_bit.clone());

            let next_carry_val = curr_self
                .val()
                .zip(curr_other.val())
                .zip(carry.val())
                .map(|((av, bv), cv)| (av & bv) | (av & cv) | (bv & cv));

            let next_carry_bit = AllocatedBit::alloc(interp, next_carry_val)?;
            let next_carry_bool = Boolean::Is(next_carry_bit.clone());

            interp.enforce(
                || "full adder",
                curr_self.lc::<F>() + curr_other.lc::<F>() + carry.lc::<F>()
                    - sum_bool.lc::<F>()
                    - (F::from(2), next_carry_bit.var),
                Lc::from(F::one()),
                Lc::zero(),
            );

            result_bits.push(sum_bool);
            carry = next_carry_bool;
        }

        Ok(UInt32 {
            bits: result_bits,
            value,
        })
    }
}

/// A reduced-round SHA-256 circuit over a single 32-byte input block.
pub struct SHA256 {
    /// Private 32-byte input as 8 big-endian u32 words.
    /// `None` entries are used when the verifier doesn't know the input.
    pub input: Vec<Option<u32>>,
    /// Public 8-word output digest.
    pub output: Vec<u32>,
}

/// Real SHA-256 has 64 rounds but our circuit will have just 4
const NUM_ROUNDS: usize = 4;

/// Synthesizes the reduced-round SHA-256 circuit and exposes the digest as
/// public output.
///
/// At a high level, this should:
/// 1. Allocate the 256-bit private input as eight 32-bit words.
/// 2. Build the single-block message schedule used by this reduced instance.
/// 3. Initialize the eight working variables from the SHA-256 IV.
/// 4. Run `NUM_ROUNDS` compression rounds, computing `T1` and `T2` from the
///    usual SHA-256 ingredients (`Sigma0`, `Sigma1`, `Ch`, `Maj`, constants,
///    and schedule words).
/// 5. Add the final working state back into the IV.
/// 6. Allocate the expected digest as public output and constrain it to match
///    the computed state.
///
/// The important implementation point is that the arithmetic should be
/// expressed in terms of the word gadgets above, rather than by manually
/// manipulating raw linear combinations for each SHA-256 formula.
impl<F: Field> Circuit<F> for SHA256 {
    fn synthesize<I: ConstraintInterpreter<F>>(self, interp: &mut I) -> Result<()> {
        const IV: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        const K: [u32; 4] = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5];
        let mut words = Vec::with_capacity(self.input.len());

        // Step 1:  Allocate the 256-bit private input as eight 32-bit words.
        for w in self.input {
            let word = UInt32::alloc(interp, w)?;  // w: Option<u32>
            words.push(word);
        }

        // Step 2: Build the single-block message schedule used by this reduced instance.
        // TODO: This is just stuff from online, not sure if its correct
        let mut w = Vec::with_capacity(16);

        for word in words {
            w.push(word); // w[0..8]
        }

        w.push(UInt32::constant(0x80000000)); // w[8]
        for _ in 9..15 {
            w.push(UInt32::constant(0));
        }
        w.push(UInt32::constant(0x00000100)); // w[15]

        // Step 3: Initialize the eight working variables from the SHA-256 IV.
        // TODO: Is there a less clunky way to do this?
        // Need to be mutable since they get re-assigned apparently
        let mut a = UInt32::constant(IV[0]);
        let mut b = UInt32::constant(IV[1]);
        let mut c = UInt32::constant(IV[2]);
        let mut d = UInt32::constant(IV[3]);
        let mut e = UInt32::constant(IV[4]);
        let mut f = UInt32::constant(IV[5]);
        let mut g = UInt32::constant(IV[6]);
        let mut h = UInt32::constant(IV[7]);
        // Step 4:  Run `NUM_ROUNDS` compression rounds, computing `T1` and `T2` from the
        //    usual SHA-256 ingredients (`Sigma0`, `Sigma1`, `Ch`, `Maj`, constants,
        //    and schedule words).
        for i in 0..NUM_ROUNDS {
            let k_i = UInt32::constant(K[i]);

            // TODO: Check if this is correct, I couldn't find the formula online so I just used the formula that AI gave me
            let s1 = e.big_sigma1(interp)?;
            let ch = UInt32::chr_word(&e, &f, &g, interp)?;

            let t1 = h
                .add(interp, &s1)?
                .add(interp, &ch)?
                .add(interp, &k_i)?
                .add(interp, &w[i])?;

            let s0 = a.big_sigma0(interp)?;
            let maj = UInt32::maj_word(&a, &b, &c, interp)?;

            let t2 = s0.add(interp, &maj)?;

            let new_h = g;
            let new_g = f;
            let new_f = e;
            let new_e = d.add(interp, &t1)?;
            let new_d = c;
            let new_c = b;
            let new_b = a;
            let new_a = t1.add(interp, &t2)?;

            a = new_a;
            b = new_b;
            c = new_c;
            d = new_d;
            e = new_e;
            f = new_f;
            g = new_g;
            h = new_h;
        }
        // Step 5: Add the final working state back into the IV
        let out0 = a.add(interp, &UInt32::constant(IV[0]))?;
        let out1 = b.add(interp, &UInt32::constant(IV[1]))?;
        let out2 = c.add(interp, &UInt32::constant(IV[2]))?;
        let out3 = d.add(interp, &UInt32::constant(IV[3]))?;
        let out4 = e.add(interp, &UInt32::constant(IV[4]))?;
        let out5 = f.add(interp, &UInt32::constant(IV[5]))?;
        let out6 = g.add(interp, &UInt32::constant(IV[6]))?;
        let out7 = h.add(interp, &UInt32::constant(IV[7]))?;

        // Step 6: Allocate the expected digest as public output and constrain it to match
        //    the computed state.
        let final_words = vec![out0, out1, out2, out3, out4, out5, out6, out7];

        for (expected, computed) in self.output.into_iter().zip(final_words.into_iter()) {
            let public_var = interp.alloc(
                || "public digest word",
                Visibility::Public,
                || Some(F::from(expected as u64)),
            )?;

            interp.enforce(
                || "digest word equality",
                UInt32::pack_lc::<F>(&computed.bits),
                Lc::from(F::one()),
                Lc::from(public_var),
            );
        }
        // Returns nothing
        Ok(())
    }
}
