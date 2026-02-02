use std::{
    iter::Sum,
    ops::{Add, AddAssign, Mul, Neg, Sub},
    str::FromStr,
};

use crate::{
    moduli::{P256, P256CurveOrder},
    zq::{MontgomeryZq, Zq},
};

use num_traits::{Inv, One, Zero};
use rand::rand_core::le;

///The prime defining the underlying field of the curve.
/// Note that this prime is equal to three mod four,
/// so square roots are easy in the field.
pub const SECP256R1_P256: &str =
    "0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF";

/// Curve parameters for the curve equation: y^2 = x^3 + a256*x +b256
pub const SECP256R1_A256: Zq<P256> = Zq::from_str_unchecked(
    "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc",
    16,
);

pub fn secp256r1_a256_montgomery() -> &'static MontgomeryZq<P256> {
    static SECP256R1_A256_MONTGOMERY: std::sync::LazyLock<MontgomeryZq<P256>> =
        std::sync::LazyLock::new(|| MontgomeryZq::from(SECP256R1_A256));
    &SECP256R1_A256_MONTGOMERY
}

pub const SECP256R1_B256: Zq<P256> = Zq::from_str_unchecked(
    "5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B",
    16,
);

pub const SECP256R1_CURVE_ORDER: Zq<P256> = Zq::from_str_unchecked(
    "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
    16,
);

pub const SECP256R1_G_X: Zq<P256> = Zq::from_str_unchecked(
    "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
    16,
);

pub const SECP256R1_G_Y: Zq<P256> = Zq::from_str_unchecked(
    "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5",
    16,
);

pub const SECP256R1_G: P256Point = P256Point::point_unchecked(SECP256R1_G_X, SECP256R1_G_Y);

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct PrivateZST;

/// A point on the NIST P-256 elliptic curve.
///
/// The P-256 curve is defined by the equation:
///
/// ```text
/// y² = x³ + ax + b  (mod p)
/// ```
///
/// where `a`, `b`, and `p` are specific constants defined by NIST. Points on the
/// curve, together with a special "point at infinity," form a **group** under
/// elliptic curve addition.
///
/// # The Point at Infinity
///
/// Every elliptic curve group includes a point at infinity, denoted `∞` or `𝒪`,
/// which serves as the **identity element**:
///
/// # Preventing Invalid Points (a note on PrivateZST)
///
/// Not every `(x, y)` pair lies on the curve!
///
/// We want to:
/// 1. **Prevent** external code from constructing `Point` with arbitrary coordinates
/// 2. **Allow** external code to pattern match on `Point` to extract `x` and `y` in an ergonomic
///    way.
///
///
/// One solution to this is to use `PrivateZST`: a **zero-sized private type** as a field:
///
/// ```text
/// Point {
///     x: Zq<P256>,    // Readable via pattern matching
///     y: Zq<P256>,    // Readable via pattern matching
///     _priv: PrivateZST,  // Can't be constructed externally
/// }
/// ```
///
/// External code *can* pattern match (ignoring `_priv` with `..`):
///
/// ```text
/// match point {
///     P256Point::Inf => { /* handle infinity */ }
///     P256Point::Point { x, y, .. } => { /* use x and y */ }
/// }
/// ```
///
/// But external code *cannot* construct the variant:
///
/// ```text
/// // Won't compile outside this module, can't name or create PrivateZST
/// let p = P256Point::Point { x, y, _priv: ??? };
/// ```
///
/// Since `PrivateZST` is zero-sized, it adds no runtime overhead. `P256Point::Point`
/// is exactly the size of two field elements.
///
/// An alternative representation would have been to represent `P256Point` as an enum wrapped in a
/// struct with an appropriate set of getter/setter-type methods.
///
/// Use the [`P256Point::point`] constructor to create valid points; it checks that
/// the coordinates satisfy the curve equation.
#[derive(Copy, Clone, Eq, PartialEq, Default)]
pub enum P256Point {
    ///The point at infinity
    #[default]
    Inf,
    ///The coordinates of a non-infinite curve point.
    /// Outside this module, this variant can be constructed via
    /// [`P256Point::point`]
    Point {
        x: Zq<P256>,
        y: Zq<P256>,
        // See above!
        #[allow(private_interfaces)]
        _priv: PrivateZST,
    },
}

impl P256Point {
    pub const GENERATOR: P256Point = SECP256R1_G;

    /// Attempts to construct a `P256Point::Point` from `x` and `y`
    ///
    /// # Errors
    /// Returns `Err(InvalidPointError::NotOnCurve(x, y))` if `(x,y)` is not a curve point.
    #[inline]
    pub fn point(x: Zq<P256>, y: Zq<P256>) -> Result<Self, InvalidPointError> {
        if Self::is_on_curve(&x, &y) {
            Ok(Self::point_unchecked(x, y))
        } else {
            Err(InvalidPointError::NotOnCurve(x, y))
        }
    }

    // convenience shorthand constructor
    // should only be called when x and y are known to be on the curve
    const fn point_unchecked(x: Zq<P256>, y: Zq<P256>) -> Self {
        P256Point::Point {
            x,
            y,
            _priv: PrivateZST,
        }
    }

    /// Returns a generator for the curve from a seed.
    /// The seed is given to an RNG that is used with P256Point::random()
    /// to construct the generator. Note the small size of the
    /// seed---this function should only be used to generate public parameters.
    /// If a protocol needs to generate an unpredictable group element, a
    /// much larger and truly random seed (and a different method) should be used.
    pub fn get_generator_from_seed(seed: usize) -> Self {
        use sha3::{
            Shake128,
            digest::{ExtendableOutput, Update, XofReader},
        };

        const MAX_ATTEMPTS: usize = 50;
        let mut hasher = Shake128::default();
        hasher.update(&seed.to_le_bytes());
        let mut reader = hasher.finalize_xof();
        let mut bytes = [0u8; 33];

        for _ in 0..MAX_ATTEMPTS {
            reader.read(&mut bytes);
            //This function's return value is not exactly uniform over
            //P256, but the statistical distance from uniform is quite small.
            let x = Zq::<P256>::from_bytes(&bytes[..32]);

            let rhs = x.cube() + SECP256R1_A256 * x + SECP256R1_B256;
            //Check if there's ys so that this x is on the curev.
            //We do this in the "slow" way for pedagogical purposes: first, compute the RHS of the curve equation,
            //and check its Legendre symbol to see whether there are square roots.
            //If there are, compute the square roots and choose one of them at random.
            //If there aren't, we go back above and get more bytes for another try at x and do it again.
            //This loop will terminate in only a couple attempts w.h.p.
            //https://papers.mathyvanhoef.com/dragonblood.pdf
            if let Some((y0, y1)) = rhs.square_roots() {
                let bit_choice = (bytes[32] & 1) == 1;
                let y = if bit_choice { y0 } else { y1 };
                return P256Point::point_unchecked(x, y);
            }
        }
        panic!("Could not find a point on the curve after {MAX_ATTEMPTS} attempts");
    }

    /// Returns true iff (x,y) is on the curve. Which is to say, y^2 = x^3 + a256 * x + b256
    #[inline]
    pub fn is_on_curve(x: &Zq<P256>, y: &Zq<P256>) -> bool {
        return y.square() == (x.cube() + SECP256R1_A256 * (*x) + SECP256R1_B256);
    }

    /// Computes a multi-scalar multiplication (MSM), also known as a linear combination of points.
    ///
    /// Given scalars `(s_0, s_1, ..., s_{n-1})` and elliptic curve points `(P_0, P_1, ..., P_{n-1})`,
    /// computes:
    ///
    /// ```text
    /// s_0·P_0 + s_1·P_1 + ... + s_{n-1}·P_{n-1}
    /// ```
    ///
    /// where `·` denotes scalar multiplication (repeated point addition) and `+` denotes
    /// elliptic curve point addition.
    ///
    /// # Efficiency Considerations
    ///
    /// A naive implementation computes each `s_i·P_i` independently and sums the results.
    /// If each scalar is `k` bits, this requires roughly `n·k` point additions.
    ///
    /// More sophisticated algorithms (such as Pippenger's algorithm or signed-digit
    /// methods) can significantly reduce the number of group operations by sharing
    /// work across the scalar multiplications. For this assignment, a correct naive
    /// implementation is acceptable.
    ///
    /// # Arguments
    ///
    /// * `scalars` - A slice of scalar field elements
    /// * `bases` - A slice of elliptic curve points (the "bases" being scaled)
    ///
    /// # Returns
    ///
    /// The elliptic curve point equal to the linear combination `Σᵢ scalars[i] · bases[i]`.
    ///
    /// # Panics
    ///
    /// Panics if `scalars.len() != bases.len()`.
    #[inline]
    pub fn msm(scalars: &[Zq<P256CurveOrder>], bases: &[P256Point]) -> P256Point {
        // TODO: Use Pippenger's algorithm with signed-digit representation for better efficiency.
        assert_eq!(scalars.len(), bases.len());
        let mut acc = P256Jacobian::identity();
        for i in 0..scalars.len() {
            let base = P256Jacobian::from(bases[i]);
            acc += base.scalar_mul(scalars[i]);
        }
        P256Point::from(acc)
    }

    /// Doubles the point: `2P`.
    /// Delegates to Jacobian doubling to avoid a modular inversion.
    fn double(&self) -> Self {
        match self {
            Self::Inf => Self::Inf,
            _ => {
                let j = P256Jacobian::from(*self);
                P256Point::from(j.double())
            }
        }
    }
}

impl Add for P256Point {
    type Output = P256Point;

    /// Computes elliptic curve point addition: `P + Q`.
    ///
    /// This is the group operation on the curve. The geometric interpretation:
    /// draw a line through `P` and `Q`, find the third intersection with the
    /// curve, then reflect across the x-axis.
    ///
    /// # Cases to Handle
    ///
    /// - `P + ∞ = ∞ + P = P` (identity)
    /// - `P + (-P) = ∞` (inverse)
    /// - `P + P` requires the **point doubling** formula (tangent line)
    /// - `P + Q` where `P ≠ ±Q` uses the **chord** formula
    ///
    /// The formulas for the chord and tangent cases differ—make sure to
    /// distinguish when `P = Q` vs `P ≠ Q`.
    /// Delegates to Jacobian addition to avoid a modular inversion.
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (Self::Inf, _) => rhs,
            (_, Self::Inf) => self,
            _ => {
                let j1 = P256Jacobian::from(self);
                let j2 = P256Jacobian::from(rhs);
                P256Point::from(j1 + j2)
            }
        }
    }
}

impl AddAssign for P256Point {
    /// Computes elliptic curve point addition assignment: `P += Q`.
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for P256Point {
    type Output = P256Point;

    /// Computes elliptic curve point subtraction: `P - Q`.
    ///
    /// # Hint
    ///
    /// This can be implemented trivially using `Add` and `Neg`.
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}
impl Neg for P256Point {
    type Output = P256Point;

    /// Computes the additive inverse: `-P`.
    #[inline]
    fn neg(self) -> Self::Output {
        match &self {
            &P256Point::Inf => P256Point::Inf,
            &P256Point::Point { x, y, .. } => P256Point::point_unchecked(x, -y),
        }
    }
}

impl Neg for &P256Point {
    type Output = P256Point;

    #[inline]
    fn neg(self) -> Self::Output {
        -*self
    }
}

impl Mul<Zq<P256CurveOrder>> for P256Point {
    type Output = P256Point;
    /// Computes scalar multiplication: `s · P`.
    ///
    /// Returns the point `P` added to itself `s` times:
    ///
    /// ```text
    /// s · P = P + P + ... + P   (s times)
    /// ```
    ///
    /// # Hints
    ///
    /// A naive loop is far too slow—scalars can be up to ~2²⁵⁶. Use the
    /// **double-and-add** algorithm, which is analogous to square-and-multiply
    /// for exponentiation:
    ///
    /// - "squaring" → point doubling (`P + P`)
    /// - "multiplying" → point addition (`acc + P`)
    ///
    /// This reduces the number of operations to at most `2k` where `k` is the
    /// bit-length of `s`.
    /// Uses Jacobian coordinates with mixed addition throughout, converting
    /// back to affine only at the end. This avoids ~256 modular inversions
    /// compared to the affine double-and-add approach.
    #[inline]
    fn mul(self, rhs: Zq<P256CurveOrder>) -> Self::Output {
        let base = P256Jacobian::from(self);
        P256Point::from(base.scalar_mul(rhs))
    }
}

impl Sum for P256Point {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(P256Point::zero(), Add::add)
    }
}

impl Zero for P256Point {
    #[inline]
    fn zero() -> Self {
        P256Point::Inf
    }
    #[inline]
    fn is_zero(&self) -> bool {
        matches!(self, P256Point::Inf)
    }
}

// we write our own Debug impl so PrivateZST doesn't show up
impl std::fmt::Debug for P256Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inf => write!(f, "P256Point::Inf"),
            Self::Point { x, y, .. } => f
                .debug_struct("P256Point::Point")
                .field("x", x)
                .field("y", y)
                .finish(),
        }
    }
}

impl std::fmt::Display for P256Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inf => write!(f, "(∞, ∞)"),
            Self::Point { x, y, .. } => write!(f, "({x}, {y})"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum InvalidPointError {
    NotOnCurve(Zq<P256>, Zq<P256>),
    Other(String),
}

impl From<String> for InvalidPointError {
    fn from(value: String) -> Self {
        InvalidPointError::Other(value)
    }
}
impl From<&str> for InvalidPointError {
    fn from(value: &str) -> Self {
        InvalidPointError::Other(value.to_owned())
    }
}

impl std::fmt::Display for InvalidPointError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotOnCurve(x, y) => write!(f, "Invalid point: ({x}, {y}) is not on-curve"),
            Self::Other(msg) => write!(f, "Invalid point: {msg}"),
        }
    }
}

impl std::error::Error for InvalidPointError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl FromStr for P256Point {
    type Err = InvalidPointError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        if s.is_empty() {
            return Err("Empty string".into());
        }

        //Parse the string as a tuple of two strings
        let (x, y) = s.split_once(',').ok_or("Invalid format")?;

        if x.trim() == "inf" && y.trim() == "inf" {
            return Ok(P256Point::zero());
        }

        //Parse the x and y coordinates
        let x = Zq::<P256>::from_str(x).map_err(|e| format!("{e}"))?;
        let y = Zq::<P256>::from_str(y).map_err(|e| format!("{e}"))?;
        //Check if point is on curve
        Self::point(x, y)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct P256Jacobian {
    x: MontgomeryZq<P256>,
    y: MontgomeryZq<P256>,
    z: MontgomeryZq<P256>,
}

impl P256Jacobian {
    fn identity() -> Self {
        P256Jacobian {
            x: MontgomeryZq::one(),
            y: MontgomeryZq::one(),
            z: MontgomeryZq::zero(),
        }
    }

    /// Scalar multiplication via double-and-add in Jacobian coordinates.
    /// Works for any Z (not just Z=1).
    fn scalar_mul(&self, scalar: Zq<P256CurveOrder>) -> Self {
        let mut result = P256Jacobian::identity();
        for i in (0..scalar.bit_length()).rev() {
            result = result.double();
            if scalar.bit(i) {
                result = result.add_impl(self);
            }
        }
        result
    }
}

impl From<P256Point> for P256Jacobian {
    fn from(point: P256Point) -> Self {
        match point {
            P256Point::Inf => P256Jacobian::identity(),
            P256Point::Point { x, y, .. } => P256Jacobian {
                x: MontgomeryZq::from(x),
                y: MontgomeryZq::from(y),
                z: MontgomeryZq::one(),
            },
        }
    }
}

impl From<P256Jacobian> for P256Point {
    fn from(jacobian: P256Jacobian) -> Self {
        if jacobian.z.is_zero() {
            return P256Point::Inf;
        }

        let z_inv = jacobian.z.inv();
        let z_inv_sq = z_inv.square();
        let z_inv_cb = z_inv_sq * z_inv;

        let x_affine = jacobian.x * z_inv_sq;
        let y_affine = jacobian.y * z_inv_cb;

        P256Point::point_unchecked(x_affine.into(), y_affine.into())
    }
}

impl P256Jacobian {
    // For point doubling, we can assume that A = -3 (which it does in this
    // case), so that lets us turn a multiplication into some additions and
    // a subtraction.
    fn double(&self) -> Self {
        if self.z.is_zero() {
            return *self;
        }

        let x = self.x;
        let y = self.y;
        let z = self.z;

        // Because we store the denominator in the z coordinate, we can avoid
        // any divisions here.

        // Slope Numerator: M = 3 X^2 + a Z^4
        // Numerator of Slope: M = 3 X^2 + a Z^4, but we can make this even
        // faster by substituting a = -3. Then: M = 3 (X^2 - Z^4) =
        // 3 (X - Z^2)(X + Z^2). However, we can do even better by replacing
        // multiplications by 3 with two additions.
        let zz = z.square();
        let x_minus_zz = x - zz;
        let x_plus_zz = x + zz;
        let partial_m = x_minus_zz * x_plus_zz;
        let m = partial_m + partial_m + partial_m; // multiply by 3

        // S = 4 X Y^2
        let yy = y.square();
        let s = (x * yy) << 2;

        // Final Calculations:
        // X' = M^2 - 2 S
        // Y' = M (S - X') - 8 Y^4
        // Z' = 2 Y Z
        let x_prime = m.square() - (s << 1);
        let y_prime = m * (s - x_prime) - (yy.square() << 3);
        let z_prime = (y * z) << 1;

        P256Jacobian {
            x: x_prime,
            y: y_prime,
            z: z_prime,
        }
    }
}

impl P256Jacobian {
    /// Core addition logic operating on references to avoid copying
    /// two full 96-byte Jacobian points up front. Individual 32-byte
    /// MontgomeryZq fields are copied on access (unavoidable since
    /// MontgomeryZq arithmetic is by-value), but we never memcpy
    /// the entire struct.
    ///
    /// Computes P3 = P1 + P2, where P1 = (X1, Y1, Z1) and P2 = (X2, Y2, Z2).
    ///
    /// Derivation:
    /// The goal is to compute the affine coordiantes (x3, y3):
    ///   x3 = lambda^2 - x1 - x2
    ///   y3 = lambda * (x1 - x3) - y1
    ///
    /// In Jacobian coordinates, we have:
    ///   lambda = (y2 - y1) / (x2 - x1)
    ///          = (Y2/Z2^3 - Y1/Z1^3) / (X2/Z2^2 - X1/Z1^2)
    ///
    /// To subtract these fractions (with unrelated Z denominators), we find a
    /// common denominator:
    ///   U1 = X1 * Z2^2, U2 = X2 * Z1^2     (Effective X numerators)
    ///   S1 = Y1 * Z2^3, S2 = Y2 * Z1^3     (Effective Y numerators)
    ///
    /// Now, the slope is:
    ///   lambda = (S2 - S1) / ((U2 - U1) * (Z1 * Z2))
    ///
    /// We define the delta values:
    ///   H = U2 - U1
    ///   r = 2 * (S2 - S1) (the scaling is for an optimization)
    fn add_impl(&self, rhs: &Self) -> Self {
        if self.z.is_zero() {
            return *rhs;
        }
        if rhs.z.is_zero() {
            return *self;
        }

        // If either operand has Z=1, use the cheaper mixed addition
        // (~8 muls + 3 sqrs vs ~12 muls + 4 sqrs). This is the common
        // case in scalar_mul where the base point stays affine.
        let one = MontgomeryZq::<P256>::one();
        if rhs.z == one {
            return self.add_mixed(rhs.x, rhs.y);
        }
        if self.z == one {
            return rhs.add_mixed(self.x, self.y);
        }

        // Normalize

        let z1_2 = self.z.square();
        let z2_2 = rhs.z.square();

        let u1 = self.x * z2_2;
        let u2 = rhs.x * z1_2;

        let s1 = self.y * rhs.z * z2_2;
        let s2 = rhs.y * self.z * z1_2;

        // Calculate Deltas

        let h = u2 - u1;
        let r = (s2 - s1) << 1;

        if h.is_zero() {
            if r.is_zero() {
                return self.double();
            } else {
                return P256Jacobian::identity();
            }
        }

        // Intermediate Values:
        // Z3 = 2 * Z1 * Z2 * H, so that we can simplify the X3 expression
        //
        // I = (2H)^2 = 4H^2
        // J = H * I = 4H^3
        // V = U1 * I = 4H^2 * U1
        let i = (h << 1).square();
        let j = h * i;
        let v = u1 * i;

        // Compute X3
        // Affine: x3 = lambda^2 - x1 - x2
        //
        // Substituting lambda = r / (2 * H * Z1 * Z2):
        // Numerator(X3) = r^2 - 4H^2 (U1 + U2)
        //               = r^2 - 4H^2(U1 + U1 + H)   [since U2 = U1 + H]
        //               = r^2 - 8H^2*U1 - 4H^3
        //               = r^2 - 2V - J
        let x3 = r.square() - (v << 1) - j;

        // Compute Y3
        // Affine: y3 = lambda * (x1 - x3) - y
        //
        // Scaling by coordinate weights:
        // Numerator(Y3) = r (V - X3) - 2 * S1 * J
        let y3 = r * (v - x3) - (s1 << 1) * j;

        // Compute Z3
        // Z3 = 2 * H * Z1 * Z2
        //
        // Optimization: 2ab = (a + b)^2 - a^2 - b^2
        // So: Z3 = ((Z1 + Z2)^2 - Z1^2 - Z2^2) * H
        let z_sum_sq = (self.z + rhs.z).square();
        let z3 = (z_sum_sq - z1_2 - z2_2) * h;

        P256Jacobian {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Mixed Point Addition: adds a Jacobian point to an Affine point
    ///
    /// Computes P3 = P1 + P2, where P1 = (X1, Y1, Z1) in Jacobian coordinates
    /// and P2 = (x2, y2) in Affine coordinates.
    ///
    /// Because P2 is in affine coordinates, its Z coordinate is implicitly 1,
    /// letting us simplify general addition a lot (to the point where special
    /// casing is worthwhile).
    ///
    /// 1. U1 = X1 * Z2^2  => U1 = X1 * 1^2 = X1
    /// 2. S1 = Y1 * Z2^3  => S1 = Y1 * 1^3 = Y1
    /// 3. Z3 = 2*Z1*Z2*H  => Z3 = 2*Z1*H
    fn add_mixed(&self, other_x: MontgomeryZq<P256>, other_y: MontgomeryZq<P256>) -> Self {
        if self.z.is_zero() {
            return P256Jacobian {
                x: other_x,
                y: other_y,
                z: MontgomeryZq::one(),
            };
        }

        // Normalization is simple
        let zz = self.z.square();
        let u1 = self.x;
        let u2 = other_x * zz;

        let s1 = self.y;
        let s2 = other_y * zz * self.z;

        // Calculate Deltas
        let h = u2 - u1;
        let r = (s2 - s1) << 1;

        if h.is_zero() {
            if r.is_zero() {
                return self.double();
            } else {
                return P256Jacobian::identity();
            }
        }

        // Compute (simple) helper terms
        // I = (2H)^2
        // J = H * I
        // V = U1 * I
        let i = (h << 1).square();
        let j = h * i;
        let v = u1 * i;

        // Compute X3, Y3
        let x3 = r.square() - (v << 1) - j;
        let y3 = r * (v - x3) - (s1 << 1) * j;

        // Z3 = 2 * H * Z1
        let z3 = (h * self.z) << 1;

        P256Jacobian {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

impl Add for P256Jacobian {
    type Output = P256Jacobian;
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        self.add_impl(&rhs)
    }
}

impl Add for &P256Jacobian {
    type Output = P256Jacobian;
    #[inline]
    fn add(self, rhs: &P256Jacobian) -> P256Jacobian {
        self.add_impl(rhs)
    }
}

impl AddAssign<&P256Jacobian> for P256Jacobian {
    #[inline]
    fn add_assign(&mut self, rhs: &P256Jacobian) {
        *self = self.add_impl(rhs);
    }
}

impl AddAssign for P256Jacobian {
    #[inline]
    fn add_assign(&mut self, rhs: P256Jacobian) {
        *self = self.add_impl(&rhs);
    }
}