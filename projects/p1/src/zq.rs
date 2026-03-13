use std::{
    fmt,
    iter::{Product, Sum},
    marker::PhantomData,
    ops::{Add, AddAssign, BitAnd, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, Sub, SubAssign},
    str::FromStr,
};

use num_traits::{Inv, One, Pow, Zero};
use serde::{Deserialize, Serialize};
use sfs_bigint::{U256, U512};

use crate::{Field, Random, moduli::PrimeModulus};

/// An integer modulo `Q`, where `Q` is encoded at the type level.
///
/// This struct represents elements of the ring ℤ/Qℤ (integers mod Q). The actual
/// value is stored as a `U256`, but the modulus `Q` is tracked through the type
/// system rather than stored as runtime data. For this course you may assume that moduli are less
/// than 256 bits.
///
/// A note on `PhantomData`:
///
/// We want the type system to distinguish between integers under different moduli.
/// For example, `Zq<Modulus17>` and `Zq<Modulus23>` should be incompatible types.
///
/// However, we don't actually need to *store* the modulus in each element—it's
/// a constant determined by the type.
///
/// It's a zero-sized type that disappears at runtime. It just serves as a marker for the type
/// system.
///
/// Q should implement PrimeModulus which allows its value to be queried via `Q::VALUE`
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Zq<Q> {
    value: U256,

    #[serde(skip)]
    _modulus: PhantomData<Q>,
}

impl<Q> Zq<Q> {
    /// Constructs a Zq<Q> without reducing `value` first. Can be a performance optimization when
    /// you _know_ a value is less than the modulus.
    const fn new_unchecked(value: U256) -> Self {
        Zq {
            value,
            _modulus: PhantomData,
        }
    }

    /// you _must_ ensure when calling this that the integer represented by s is < `Q::VALUE`.
    /// Should only be used when constructing a Zq<Q> in `const` contexts.
    /// (Not relevant for student implementations)
    pub(crate) const fn from_str_unchecked(s: &str, radix: u32) -> Self {
        Self::new_unchecked(U256::from_str_radix_const(s, radix))
    }

    #[must_use]
    pub const fn as_int(&self) -> &U256 {
        &self.value
    }
}

impl<Q: PrimeModulus> Zq<Q> {
    pub fn new(value: U256) -> Self {
        Zq::new_unchecked(value % Q::VALUE)
    }
    // returns *self^2
    pub fn square(&self) -> Self {
        *self * *self
    }

    // Returns *self^3
    pub fn cube(&self) -> Self {
        *self * *self * *self
    }

    //Note that this will just reduce the bytes mod Q; this does _not_ guarantee a uniform distribution!
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Zq::new(U256::from_le_slice(bytes))
    }

    pub fn legendre_symbol(&self) -> i32 {
        let exponent = (Q::VALUE - 1.into()) / 2.into();
        //This will be 1, -1 (= Q-1), or 0. Figure out which in a dumb way that branches.
        let result = self.pow(exponent);
        if result == Zq::one() {
            1
        } else if result == Zq::new(Q::VALUE - 1.into()) {
            -1
        } else if result == Zq::zero() {
            0
        } else {
            panic!("Result of legendre symbol is not 1, -1, or 0");
        }
    }

    pub fn square_roots(&self) -> Option<(Self, Self)> {
        //First panic if we can't use the easy method. We don't have a tonelli-shanks.
        assert!((Q::VALUE % 4.into()) == 3.into());
        let legendre_symbol = self.legendre_symbol();
        //If we don't have square roots, return None
        if legendre_symbol != 1 {
            return None;
        }
        //Now we know we have square roots and we can use the easy method,
        //so compute them.
        let y0 = self.pow((Q::VALUE + 1.into()) / 4.into());
        let y1 = Zq::new(Q::VALUE - y0.value);
        Some((y0, y1))
    }

    /// Computes the modular inverse of many elements simultaneously.
    ///
    /// Given `[a, b, c, ...]`, returns `[a⁻¹, b⁻¹, c⁻¹, ...]`.
    ///
    /// Montgomery batch inversion allows one to do this with just a single modular inverse
    /// and O(n) multiplications
    ///
    /// # Panics
    ///
    /// Panics if any element is zero.
    pub fn batch_invert(values: &[Zq<Q>]) -> Vec<Zq<Q>> {
        // // OPTIONAL: replace me with montgomery batch inversion
        // values.iter().map(|val| val.inv()).collect()
        if values.is_empty() {
            return vec![];
        }
        let n = values.len();
        let mut products: Vec<Zq<Q>> = Vec::with_capacity(n);
        let mut acc = Zq::one();
        for &v in values {
            acc *= v;
            products.push(acc);
        }
        let acc_inv = acc.inv();
        let mut inverses: Vec<Zq<Q>> = vec![Zq::zero(); n];
        let mut suffix_product = acc_inv;
        for i in (1..n).rev() {
            inverses[i] = suffix_product * products[i - 1];
            suffix_product *= values[i];
        }
        inverses[0] = suffix_product;
        inverses
    }

    /// Returns the number of bits needed to represent this value.
    pub fn bit_length(&self) -> usize {
        self.value.bit_length()
    }

    /// Returns true if the i-th bit (0-indexed from the LSB) is set.
    pub fn bit(&self, i: usize) -> bool {
        self.value.bit(i)
    }
}

impl<Q: PrimeModulus> FromStr for Zq<Q> {
    type Err = <U256 as FromStr>::Err;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        U256::from_str(s).map(Zq::new)
    }
}
impl<Q: PrimeModulus> Pow<u64> for Zq<Q> {
    type Output = Zq<Q>;
    /// Computes modular exponentiation: `self^exp mod Q`.
    ///
    /// # Hint
    ///
    /// Use the **square-and-multiply** algorithm (analogous to double-and-add
    /// for elliptic curves) to reduce the number of operations from `exp` to
    /// at most `2 · log₂(exp)`.
    fn pow(self, exp: u64) -> Self::Output {
        let mut result = Zq::one();
        let bit_length = 64 - exp.leading_zeros();
        for i in (0..bit_length).rev() {
            result = result.square();
            if exp >> i & 1 == 1 {
                result = result * self;
            }
        }
        result
    }
}

impl<Q: PrimeModulus> Pow<U256> for Zq<Q> {
    type Output = Zq<Q>;
    /// Computes modular exponentiation: `self^exp mod Q`.
    ///
    /// This is the same operation as [`Pow<u64>::pow`], but accepts a 256-bit
    /// exponent. Your implementation should look substantially similar.
    fn pow(self, exp: U256) -> Self::Output {
        let mut result = Zq::one();
        for i in (0..exp.bit_length()).rev() {
            result = result.square();
            if exp.bit(i) {
                result *= self;
            }
        }
        result
    }
}

impl<Q> From<u64> for Zq<Q>
where
    Q: PrimeModulus,
{
    fn from(value: u64) -> Self {
        Zq::new(From::from(value))
    }
}

impl<Q> From<bool> for Zq<Q>
where
    Q: PrimeModulus,
{
    fn from(value: bool) -> Self {
        Zq::new(U256::from(u64::from(value)))
    }
}
impl<Q: PrimeModulus> Add for Zq<Q> {
    type Output = Zq<Q>;
    /// Computes modular addition: `(self + rhs) mod Q`.
    ///
    /// Returns the unique representative in `[0, Q)` that is congruent to the
    /// sum of `self` and `rhs` modulo `Q`.
    ///
    /// # The Challenge
    ///
    /// Both `self.value` and `rhs.value` are in `[0, Q)`, so their sum lies in
    /// `[0, 2Q - 2]`. The result must be reduced back into `[0, Q)`:
    ///
    /// ```text
    /// result = if sum >= Q::VALUE { sum - Q::VALUE } else { sum }
    /// ```
    ///
    /// However there's a wrinkle!
    ///
    /// `U256` arithmetic can overflow! If `Q` is close to 2²⁵⁶,
    /// then `self + rhs` might exceed 2²⁵⁶ - 1 and wrap around.
    ///
    /// # Useful Primitives
    ///
    /// `U256` provides two methods that help handle overflow and underflow:
    ///
    /// ### `carrying_add`
    /// ```text
    /// fn carrying_add(&self, rhs: &U256) -> (U256, bool)
    /// ```
    /// Computes `self + rhs`, returning:
    /// - The low 256 bits of the sum (wrapping on overflow)
    /// - A boolean indicating whether overflow occurred (i.e., the "carry out")
    ///
    /// Example: if `a + b = 2²⁵⁶ + 42`, then `carrying_add` returns `(42, true)`.
    ///
    /// ### `borrowing_sub`
    /// ```text
    /// fn borrowing_sub(&self, rhs: &U256) -> (U256, bool)
    /// ```
    /// Computes `self - rhs`, returning:
    /// - The result as if computed with unlimited precision, then truncated to 256 bits
    /// - A boolean indicating whether underflow occurred (i.e., a "borrow" was needed)
    ///
    /// Example: if `self = 10` and `rhs = 15`, then `borrowing_sub` returns
    /// `(2²⁵⁶ - 5, true)` since the subtraction underflowed.
    fn add(self, rhs: Self) -> Self::Output {
        let (sum, carry) = self.value.carrying_add(&rhs.value);
        let (reduced, borrow) = sum.borrowing_sub(&Q::VALUE);
        let needs_reduction = carry || !borrow;
        Self::new_unchecked(if needs_reduction { reduced } else { sum })
    }
}
impl<Q: PrimeModulus> Neg for Zq<Q> {
    type Output = Zq<Q>;
    /// Computes the additive inverse: `-self mod Q`.
    fn neg(self) -> Self::Output {
        let value = if self.value.is_zero() {
            U256::zero()
        } else {
            Q::VALUE - self.value
        };

        Self::new_unchecked(value)
    }
}

impl<Q: PrimeModulus> Neg for &Zq<Q> {
    type Output = Zq<Q>;
    fn neg(self) -> Self::Output {
        -*self
    }
}

impl<Q: PrimeModulus> Zero for Zq<Q> {
    fn zero() -> Self {
        Zq::<Q>::new_unchecked(U256::zero())
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
}

impl<Q: PrimeModulus> One for Zq<Q> {
    fn one() -> Self {
        Zq::<Q>::new_unchecked(U256::one())
    }
}
impl<Q: PrimeModulus> Sub for Zq<Q> {
    type Output = Zq<Q>;
    /// Computes modular subtraction: `(self - rhs) mod Q`.
    ///
    /// Returns the unique representative in `[0, Q)` that is congruent to the
    /// difference of `self` and `rhs` modulo `Q`.
    ///
    /// # The Challenge
    ///
    /// Both `self.value` and `rhs.value` are in `[0, Q)`, so their difference lies in
    /// `(-(Q - 1), Q - 1)`, or equivalently `[-(Q - 1), Q - 1]`. When `self < rhs`,
    /// the result is negative and must be corrected:
    ///
    /// ```text
    /// result = if self >= rhs { self - rhs } else { self - rhs + Q::VALUE }
    /// ```
    ///
    /// The tricky part: `U256` is unsigned and cannot represent negative numbers!
    /// Subtracting a larger value from a smaller one causes underflow and wraps around.
    ///
    /// # Useful Primitives
    ///
    /// See the documentation for [`Add::add`](Self::add) for detailed explanations of
    /// `U256::carrying_add` and `U256::borrowing_sub`. The short version:
    ///
    /// - `borrowing_sub` returns `(wrapped_result, underflow_occurred)`
    /// - `carrying_add` returns `(wrapped_result, overflow_occurred)`
    fn sub(self, rhs: Self) -> Self::Output {
        let (tentative_diff, underflow) = self.value.borrowing_sub(&rhs.value);
        Zq::new_unchecked(if underflow {
            tentative_diff.carrying_add(&Q::VALUE).0
        } else {
            tentative_diff
        })
    }
}
impl<Q: PrimeModulus> Mul for Zq<Q> {
    type Output = Zq<Q>;
    /// Computes modular multiplication: `(self * rhs) mod Q`.
    ///
    /// Returns the unique representative in `[0, Q)` that is congruent to the
    /// product of `self` and `rhs` modulo `Q`.
    ///
    /// # The Challenge
    ///
    /// Both `self.value` and `rhs.value` are in `[0, Q)`, so their product lies in
    /// `[0, (Q - 1)²]`. Unlike addition (where the result fits in at most 257 bits),
    /// multiplication of two 256-bit numbers can produce a result up to 512 bits.
    ///
    /// For this, you may use a wider integer type U512 to store the intermediary product.
    ///
    /// # Useful Primitives
    ///
    /// ### `widening_mul`
    /// ```text
    /// fn widening_mul(&self, rhs: &U256) -> U512
    /// ```
    /// Computes the full 512-bit product of two 256-bit integers. No overflow is possible
    /// since the result type is wide enough to hold any product.
    ///
    /// ### `U512::split`
    /// ```text
    /// fn split(&self) -> (U256, U256)
    /// ```
    /// Splits a 512-bit integer into its low and high 256-bit halves: `(low, high)`.
    fn mul(self, rhs: Self) -> Self::Output {
        let modulus = U512::from(Q::VALUE);
        let product = self.value.widening_mul(&rhs.value);
        let reduced = product % modulus;
        let (low, high) = reduced.split();
        debug_assert!(high.is_zero(), "Multiplication result exceeds 256 bits");
        Zq::new_unchecked(low)
    }
}

impl<Q: PrimeModulus> MulAssign<Zq<Q>> for Zq<Q> {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<Q: PrimeModulus> SubAssign<Zq<Q>> for Zq<Q> {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<Q: PrimeModulus> AddAssign<Zq<Q>> for Zq<Q> {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<Q: PrimeModulus> DivAssign<Zq<Q>> for Zq<Q> {
    fn div_assign(&mut self, other: Self) {
        *self = *self / other;
    }
}

impl<Q: PrimeModulus> Div for Zq<Q> {
    type Output = Self;
    #[expect(clippy::suspicious_arithmetic_impl)]
    fn div(self, other: Self) -> Self::Output {
        self * other.inv()
    }
}

impl<Q> Shr<usize> for Zq<Q> {
    type Output = Zq<Q>;
    fn shr(self, rhs: usize) -> Self::Output {
        Zq::new_unchecked(self.value >> rhs)
    }
}

impl<Q> BitAnd<u64> for Zq<Q> {
    type Output = Zq<Q>;
    fn bitand(self, rhs: u64) -> Self::Output {
        Zq::new_unchecked(self.value & rhs.into())
    }
}

impl<Q> BitAnd for Zq<Q> {
    type Output = Zq<Q>;
    fn bitand(self, rhs: Self) -> Self::Output {
        Zq::new_unchecked(self.value & rhs.value)
    }
}

impl<Q: PrimeModulus> fmt::Debug for Zq<Q> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} (mod {})", self.value, Q::VALUE)
    }
}

impl<Q: PrimeModulus> fmt::Display for Zq<Q> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
/// Generates a uniformly random element of ℤ/Qℤ.
///
/// Returns a random value sampled uniformly from `[0, Q)`.
///
/// # Why Not Just Use `random_bytes % Q`?
///
/// A tempting approach is to generate a random 256-bit integer and reduce it mod `Q`:
///
/// ```text
/// let r = U256::random(); // U256 doesn't actually have this method, but suppose it did
/// return r % Q;  // DON'T DO THIS!
/// ```
///
/// This produces a **biased** distribution. To see why, consider a simple example
/// with small numbers: suppose we're sampling mod 3 from a random value in `[0, 7]`:
///
/// ```text
/// value:     0  1  2  3  4  5  6  7
/// value % 3: 0  1  2  0  1  2  0  1
/// ```
///
/// Values 0 and 1 each appear 3 times, but 2 appears only twice. The distribution
/// is not uniform.
///
/// Instead you should utilize `rejection sampling`.
///
/// # Useful Primitives
///
/// ### `rand::Rng::fill_bytes`
/// ```text
/// fn fill_bytes(&mut self, dest: &mut [u8])
/// ```
/// Fills a byte slice with random data. This is the recommended way to generate
/// random bytes from the provided `source`.
///
/// Example usage:
/// ```text
/// let mut bytes = [0u8; 32];
/// source.fill_bytes(&mut bytes);
///
/// ```
/// ### `U256::from_le_slice`
/// ```text
/// fn from_le_slice(bytes: &[u8]) -> U256
/// ```
/// Constructs a `U256` from a byte slice interpreted as a little-endian integer.
/// The slice is zero-padded on the right (high-order bytes) if shorter than 32 bytes.
///
/// ### `U256::bit_length`
/// ```text
/// fn bit_length(&self) -> usize
/// ```
/// Returns the minimum number of bits needed to represent this integer.
/// Equivalently, `⌈log₂(self + 1)⌉` for nonzero values.
impl<Q: PrimeModulus> Random for Zq<Q> {
    fn random(source: &mut impl rand::Rng) -> Self {
        let bit_len = Q::VALUE.bit_length();
        let num_bytes = bit_len.div_ceil(8);
        // Using a mask makes sure that, even if we have a very small Q
        // like 2, we don't reject a huge amount of things (because we can only)
        // generate values at the granularity of a byte.
        let mask = U256::MAX >> (256 - bit_len);

        let mut bytes: [u8; 32] = [0u8; U256::BYTES];
        loop {
            source.fill_bytes(&mut bytes[..num_bytes]);
            let generated_value = U256::from_le_slice(&bytes) & mask;
            if generated_value < Q::VALUE {
                return Self::new_unchecked(generated_value);
            }
        }
    }
}

impl<Q: PrimeModulus> Inv for Zq<Q> {
    type Output = Zq<Q>;

    /// Computes the modular multiplicative inverse: `self⁻¹ mod Q`.
    ///
    /// Returns the unique element `b ∈ [1, Q)` such that `self · b ≡ 1 (mod Q)` via the **extended
    /// Euclidean algorithm**.
    ///
    /// Panics if `self` is zero, or more generally if `gcd(self, Q::VALUE) != 1`
    fn inv(self) -> Self::Output {
        // Initially, we thought that the extended Euclidean algorithm relied on
        // the coefficients becoming negative (otherwise reaching 1 would not be
        // possible). But if we remain in (mod Q) world, the math still works
        // out. EEA calculates ax + Qy = gcd(a, Q) = 1, where x is the modular
        // inverse (clearly), and so (in mod world) we would get ax = 1 (mod Q).
        assert!(!self.is_zero(), "0 has no modular inverse");

        // r values stay as U256 (control GCD computation)
        // t values are Zq (we only need the coefficient mod Q)
        let mut r0 = Q::VALUE;
        let mut r1 = self.value;
        let mut t0 = Self::zero();
        let mut t1 = Self::one();

        while !r1.is_zero() {
            let q = r0 / r1;
            let q_mod = Self::new(q);
            // We know none of these values will overflow or underflow because
            // q * r1 is guaranteed to be in the range 0 < q * r1 < r0
            (r0, r1) = (r1, r0 - q * r1);
            // We know that this won't overflow for similar reasons
            (t0, t1) = (t1, t0 - q_mod * t1);
        }

        // This is guaranteed to be true because Q is Prime
        debug_assert!(r0 == U256::one(), "GCD must be 1 for Modular Inverse");
        t0
    }
}

impl<Q: PrimeModulus> Sum for Zq<Q> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), Add::add)
    }
}

impl<Q: PrimeModulus> Product for Zq<Q> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl<Q: PrimeModulus> Field for Zq<Q> {
    type Order = Q;
}

// STUDENTS NEED NOT PROCEED BELOW THIS LINE
// Note that _in most cases_ you would be able to simply #[derive()]
// all of the below implementations
//
// However, the implementations that #[derive(Trait)] would generate would look like
//
// impl<Q: Trait> Trait for Zq<Q> { .. }
//
// Normally, this is what you want, however because 'Q' is a phantom type (Zq actually contains no
// value of type Q), this implementation is too restrictive. Zq implements e.g. Eq regardless of whether Q does,
// so you want an implementation like
//
// impl<Q> Trait for Zq<Q> { .. }
//
// instead.
//
//
// Derive isn't smart enough to detect this, however, there are crates that automate this kind of boilerplate
// (such as derive_where and derive_more) which provide more powerful versions of Rust's builtin
// `derive`
impl<Q> Copy for Zq<Q> {}
impl<Q> Clone for Zq<Q> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Q> PartialEq for Zq<Q> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<Q> Eq for Zq<Q> {}

impl<Q> PartialOrd for Zq<Q> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<Q> Ord for Zq<Q> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl<Q> std::hash::Hash for Zq<Q> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}
impl<Q> Default for Zq<Q> {
    fn default() -> Self {
        Zq::new_unchecked(U256::default())
    }
}

/// An element of Z/QZ stored in Montgomery form.
///
/// Instead of storing x directly, we store x_bar = x * r mod n where r = 2^256
/// and n = Q::VALUE. This makes multiplication much cheaper: instead of dividing
/// by n (expensive), we divide by r (free -- just discard low 256 bits).
pub struct MontgomeryZq<Q> {
    value: U256,
    _modulus: PhantomData<Q>,
}

impl<Q: PrimeModulus> MontgomeryZq<Q> {
    /// Wraps a raw U256 that is *already* in Montgomery form (i.e. already
    /// represents x*r mod n). No reduction is performed.
    const fn from_montgomery_unchecked(value: U256) -> Self {
        MontgomeryZq {
            value,
            _modulus: PhantomData,
        }
    }
}

impl<Q: PrimeModulus> MontgomeryZq<Q> {
    /// Montgomery reduction (REDC): given a U512 value x, compute x * r^(-1) mod n.
    ///
    /// This is the core operation. It replaces division-by-n with division-by-r
    /// (a free bit-shift) by finding a multiple of n that zeroes out the low 256
    /// bits of x.
    ///
    /// Algorithm:
    ///   1. q = x_low * n' mod 2^256   (find the right multiple of n)
    ///   2. (x - q*n) has its low 256 bits all zero by construction
    ///   3. result = (x - q*n) / 2^256  (just take the high half)
    ///   4. if result < 0, add n         (at most one correction needed)
    fn redc(x: U512) -> Self {
        let x_high = x.split().1;
        let q = ((x.split().0).widening_mul(Q::montgomery_n_prime()))
            .split()
            .0;
        let m = q.widening_mul(&Q::VALUE).split().1;
        let (result, borrow) = x_high.borrowing_sub(&m);
        if borrow {
            MontgomeryZq::from_montgomery_unchecked(result.carrying_add(&Q::VALUE).0)
        } else {
            MontgomeryZq::from_montgomery_unchecked(result)
        }
    }

    /// Returns self^2 in Montgomery space.
    pub fn square(&self) -> Self {
        *self * *self
    }
}

impl<Q: PrimeModulus> From<Zq<Q>> for MontgomeryZq<Q> {
    /// Convert from normal form to Montgomery form: x -> x * r mod n.
    ///
    /// Uses the precomputed r^2 mod n constant:
    ///   x_bar = REDC(x * r^2) = x * r^2 * r^(-1) mod n = x * r mod n
    fn from(zq: Zq<Q>) -> Self {
        let r2 = *Q::montgomery_r2_mod_n();
        // x * r^2 as a full 512-bit product, then REDC to get x * r mod n
        let product = zq.value.widening_mul(&r2);
        Self::redc(product)
    }
}

impl<Q: PrimeModulus> From<MontgomeryZq<Q>> for Zq<Q> {
    /// Convert from Montgomery form back to normal form: x_bar -> x_bar * r^(-1) mod n = x.
    ///
    /// This is just REDC applied to x_bar (treated as a 512-bit number with high half = 0).
    fn from(mont: MontgomeryZq<Q>) -> Self {
        let reduced: MontgomeryZq<Q> = MontgomeryZq::redc(U512::from(mont.value));
        Zq::new_unchecked(reduced.value)
    }
}

impl<Q: PrimeModulus> Add for MontgomeryZq<Q> {
    type Output = Self;
    /// Modular addition -- identical to Zq::add since Montgomery form is linear:
    ///   x_bar + y_bar = (x + y) * r mod n
    fn add(self, rhs: Self) -> Self::Output {
        let (sum, carry) = self.value.carrying_add(&rhs.value);
        let (reduced, borrow) = sum.borrowing_sub(&Q::VALUE);
        let needs_reduction = carry || !borrow;
        MontgomeryZq::from_montgomery_unchecked(if needs_reduction { reduced } else { sum })
    }
}

impl<Q: PrimeModulus> Sub for MontgomeryZq<Q> {
    type Output = Self;
    /// Modular subtraction -- identical to Zq::sub since Montgomery form is linear:
    ///   x_bar - y_bar = (x - y) * r mod n
    fn sub(self, rhs: Self) -> Self::Output {
        let (tentative_diff, underflow) = self.value.borrowing_sub(&rhs.value);
        MontgomeryZq::from_montgomery_unchecked(if underflow {
            tentative_diff.carrying_add(&Q::VALUE).0
        } else {
            tentative_diff
        })
    }
}

impl<Q: PrimeModulus> Neg for MontgomeryZq<Q> {
    type Output = Self;
    /// Additive inverse -- identical to Zq::neg: if zero return zero, else n - value.
    fn neg(self) -> Self::Output {
        let value = if self.value.is_zero() {
            U256::zero()
        } else {
            Q::VALUE - self.value
        };

        MontgomeryZq::from_montgomery_unchecked(value)
    }
}

impl<Q: PrimeModulus> Mul for MontgomeryZq<Q> {
    type Output = Self;
    /// Montgomery multiplication: x_bar * y_bar * r^(-1) mod n = (x * y) * r mod n.
    ///
    /// This is where Montgomery pays off -- one widening multiply + REDC,
    /// no division by n anywhere.
    fn mul(self, rhs: Self) -> Self::Output {
        let product = self.value.widening_mul(&rhs.value);
        Self::redc(product)
    }
}

impl<Q: PrimeModulus> Div for MontgomeryZq<Q> {
    type Output = Self;
    /// Division via multiplication by the inverse.
    #[expect(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl<Q: PrimeModulus> AddAssign for MontgomeryZq<Q> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<Q: PrimeModulus> SubAssign for MontgomeryZq<Q> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<Q: PrimeModulus> MulAssign for MontgomeryZq<Q> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<Q: PrimeModulus> DivAssign for MontgomeryZq<Q> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

// -- Identity elements --------------------------------------------------------

impl<Q: PrimeModulus> Zero for MontgomeryZq<Q> {
    /// Zero in Montgomery form: 0 * r = 0.
    fn zero() -> Self {
        Self::from_montgomery_unchecked(U256::zero())
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
}

impl<Q: PrimeModulus> One for MontgomeryZq<Q> {
    /// One in Montgomery form: 1 * r mod n = r mod n (precomputed).
    fn one() -> Self {
        Self::from_montgomery_unchecked(*Q::montgomery_r_mod_n())
    }
}

impl<Q: PrimeModulus> Pow<u64> for MontgomeryZq<Q> {
    type Output = Self;
    /// Square-and-multiply exponentiation, entirely in Montgomery space.
    fn pow(self, exp: u64) -> Self::Output {
        let mut result = Self::one();
        let bit_length = u64::BITS - exp.leading_zeros();
        for i in (0..bit_length).rev() {
            result = result.square();
            if exp >> i & 1 == 1 {
                result = result * self;
            }
        }
        result
    }
}

impl<Q: PrimeModulus> Pow<U256> for MontgomeryZq<Q> {
    type Output = Self;
    /// Square-and-multiply exponentiation with a 256-bit exponent.
    fn pow(self, exp: U256) -> Self::Output {
        let mut result = Self::one();
        for i in (0..exp.bit_length()).rev() {
            result = result.square();
            if exp.bit(i) {
                result = result * self;
            }
        }
        result
    }
}

impl<Q: PrimeModulus> Inv for MontgomeryZq<Q> {
    type Output = Self;
    /// Computes the modular inverse using Fermat's Little Theorem.
    ///
    /// This is strictly faster than EEA for 256-bit integers because it avoids
    /// expensive U256 divisions, replacing them with Montgomery multiplications.
    ///
    /// Formula: x^(P-2) mod P = x^-1 mod P
    fn inv(self) -> Self::Output {
        // We assert self is not zero, as 0 has no inverse.
        assert!(!self.is_zero(), "0 has no modular inverse");

        // P - 2
        let exp = Q::VALUE - U256::from(2u64);

        // This implicitly computes (xR)^(P-2) in Montgomery space,
        // which results in (x^(P-2))R = x^-1 * R mod P.
        self.pow(exp)
    }
}

impl<Q: PrimeModulus> Shl<usize> for MontgomeryZq<Q> {
    type Output = Self;

    /// Computes modular left shift: `self * 2^shift mod Q`.
    ///
    /// This is implemented as repeated doubling (addition), which is significantly
    /// faster than Montgomery multiplication for small shifts.
    fn shl(self, shift: usize) -> Self::Output {
        let mut result = self;
        for _ in 0..shift {
            result = result + result;
        }
        result
    }
}

impl<Q: PrimeModulus> ShlAssign<usize> for MontgomeryZq<Q> {
    fn shl_assign(&mut self, shift: usize) {
        for _ in 0..shift {
            *self = *self + *self;
        }
    }
}

impl<Q: PrimeModulus> From<u64> for MontgomeryZq<Q> {
    fn from(value: u64) -> Self {
        MontgomeryZq::from(Zq::<Q>::from(value))
    }
}

impl<Q: PrimeModulus> From<bool> for MontgomeryZq<Q> {
    fn from(value: bool) -> Self {
        MontgomeryZq::from(Zq::<Q>::from(value))
    }
}

impl<Q: PrimeModulus> Sum for MontgomeryZq<Q> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), Add::add)
    }
}

impl<Q: PrimeModulus> Product for MontgomeryZq<Q> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl<Q: PrimeModulus> Copy for MontgomeryZq<Q> {}
impl<Q: PrimeModulus> Clone for MontgomeryZq<Q> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Q: PrimeModulus> PartialEq for MontgomeryZq<Q> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<Q: PrimeModulus> Eq for MontgomeryZq<Q> {}

impl<Q: PrimeModulus> PartialOrd for MontgomeryZq<Q> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<Q: PrimeModulus> Ord for MontgomeryZq<Q> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl<Q: PrimeModulus> std::hash::Hash for MontgomeryZq<Q> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<Q: PrimeModulus> Default for MontgomeryZq<Q> {
    fn default() -> Self {
        MontgomeryZq::from_montgomery_unchecked(U256::default())
    }
}

impl<Q: PrimeModulus> fmt::Debug for MontgomeryZq<Q> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let normal: Zq<Q> = Zq::from(*self);
        write!(f, "{} (mod {})", normal.as_int(), Q::VALUE)
    }
}

impl<Q: PrimeModulus> fmt::Display for MontgomeryZq<Q> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}


impl<Q: PrimeModulus> crate::FromBytes for Zq<Q> {
    const BYTES_NEEDED: usize = 64;
    fn from_bytes(bytes: &[u8]) -> Self {
        assert!(
            bytes.len() >= Self::BYTES_NEEDED,
            "insufficient bytes length"
        );
        let (int, _) = (sfs_bigint::U512::from_le_slice(bytes) % From::from(Q::VALUE)).split();
        Zq::new(int)
    }
}
