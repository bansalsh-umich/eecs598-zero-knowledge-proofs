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
        todo!()
    }
    /// Constrain and return the XOR of two allocated bits.
    pub fn xor<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
        other: &Self,
    ) -> Result<Self> {
        todo!()
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
        todo!()
    }

    /// Return `self.rotate_right(shift)`.
    pub fn rotr(&self, shift: usize) -> Self {
        todo!()
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
        todo!()
    }

    /// Return the SHA-256 upper-sigma function
    /// `ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)`.
    pub fn big_sigma1<F: Field, I: ConstraintInterpreter<F>>(
        &self,
        interp: &mut I,
    ) -> Result<Self> {
        todo!()
    }

    /// Apply SHA-256's choose function bitwise:
    /// the `i`th output bit is `(a_i & b_i) XOR ((!a_i) & c_i)`.
    pub fn chr_word<F: Field, I: ConstraintInterpreter<F>>(
        a: &Self,
        b: &Self,
        c: &Self,
        interp: &mut I,
    ) -> Result<Self> {
        todo!()
    }

    /// Apply SHA-256's majority function bitwise:
    /// the `i`th output bit is the majority of `a_i`, `b_i`, and `c_i`.
    pub fn maj_word<F: Field, I: ConstraintInterpreter<F>>(
        a: &Self,
        b: &Self,
        c: &Self,
        interp: &mut I,
    ) -> Result<Self> {
        todo!()
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
        todo!()
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
        todo!()
    }
}
