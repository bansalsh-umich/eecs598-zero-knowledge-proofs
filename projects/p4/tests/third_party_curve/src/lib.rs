use derive_more::{Add, AddAssign, Debug, From, Mul, MulAssign, Neg, Product, Sub, SubAssign, Sum};
use num_traits::Pow;
use p256::elliptic_curve::Group;
use p256::elliptic_curve::group::GroupEncoding;
use serde::{Deserialize, Serialize};
use std::fmt::{self, Display};
use std::ops::{Div, DivAssign};

#[derive(
    Copy,
    Clone,
    Debug,
    Eq,
    PartialEq,
    Default,
    Add,
    AddAssign,
    Mul,
    MulAssign,
    Sub,
    SubAssign,
    Sum,
    Neg,
    Serialize,
    Deserialize,
)]
pub struct P256Point(#[serde(with = "as_encoded")] p256::ProjectivePoint);

impl std::hash::Hash for P256Point {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bytes().hash(state)
    }
}

mod as_encoded {
    use p256::elliptic_curve::sec1::FromEncodedPoint;
    use p256::elliptic_curve::sec1::ToEncodedPoint;
    use serde::de::Error as DeError;
    use serde::{Deserialize, Serialize};

    pub fn serialize<S: serde::Serializer>(
        point: &p256::ProjectivePoint,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        point.to_encoded_point(true).serialize(serializer)
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<p256::ProjectivePoint, D::Error> {
        let opt: Option<p256::ProjectivePoint> = p256::ProjectivePoint::from_encoded_point(
            &p256::EncodedPoint::deserialize(deserializer)?,
        )
        .into();
        opt.ok_or_else(|| D::Error::custom("point not on curve"))
    }
}

impl num_traits::Zero for P256Point {
    fn zero() -> Self {
        Self(p256::ProjectivePoint::identity())
    }

    fn is_zero(&self) -> bool {
        self.0.is_identity().unwrap_u8() != 0
    }
}

impl std::borrow::Borrow<p256::Scalar> for P256Scalar {
    fn borrow(&self) -> &p256::Scalar {
        &self.0
    }
}

impl p2::ec::EllipticCurve for P256Point {
    // no need to replace this with a performant version, because it isn't used.
    type BaseField = p1::zq::Zq<p1::moduli::P256CurveOrder>;
    type Scalar = P256Scalar;

    fn msm(scalars: &[Self::Scalar], points: &[Self]) -> Self {
        scalars
            .iter()
            .zip(points)
            .map(|(&scalar, &point)| Self(point.0 * scalar.0))
            .sum()
    }

    fn get_generator_from_seed(seed: u64) -> Self {
        use p256::elliptic_curve::sec1::FromEncodedPoint;
        use sha3::{Digest, Sha3_256};

        let mut counter: u64 = 0;
        loop {
            let mut hasher = Sha3_256::new();
            hasher.update(b"P256_GENERATOR_FROM_SEED");
            hasher.update(seed.to_le_bytes());
            hasher.update(counter.to_le_bytes());
            let hash = hasher.finalize();

            // Try to interpret hash as x-coordinate with even y parity
            let mut point_bytes = [0u8; 33];
            point_bytes[0] = 0x02;
            point_bytes[1..33].copy_from_slice(&hash);

            if let Ok(encoded) = p256::EncodedPoint::from_bytes(point_bytes) {
                let opt: Option<p256::ProjectivePoint> =
                    p256::ProjectivePoint::from_encoded_point(&encoded).into();
                if let Some(point) = opt
                    && point.is_identity().unwrap_u8() == 0
                {
                    return Self(point);
                }
            }
            counter += 1;
        }
    }
}

#[derive(
    Copy,
    Clone,
    Debug,
    Eq,
    PartialEq,
    Default,
    Ord,
    PartialOrd,
    Add,
    AddAssign,
    Mul,
    MulAssign,
    Sub,
    SubAssign,
    From,
    Sum,
    Product,
    Serialize,
    Deserialize,
    Neg,
)]
#[mul(forward)]
#[mul_assign(forward)]
pub struct P256Scalar(p256::Scalar);

impl std::hash::Hash for P256Scalar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bytes().hash(state)
    }
}

impl num_traits::Zero for P256Scalar {
    fn zero() -> Self {
        Self(p256::Scalar::ZERO)
    }
    fn is_zero(&self) -> bool {
        self.0 == p256::Scalar::ZERO
    }
}

impl From<u64> for P256Scalar {
    fn from(value: u64) -> Self {
        Self(p256::Scalar::from(value))
    }
}

impl num_traits::One for P256Scalar {
    fn one() -> Self {
        Self(p256::Scalar::ONE)
    }
}

impl Pow<u64> for P256Scalar {
    type Output = Self;
    #[inline]
    fn pow(self, rhs: u64) -> Self::Output {
        Self(self.0.pow_vartime(&[rhs]))
    }
}

impl Display for P256Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl From<bool> for P256Scalar {
    #[inline]
    fn from(value: bool) -> Self {
        Self(From::from(value as u64))
    }
}

impl p1::FromBytes for P256Scalar {
    const BYTES_NEEDED: usize = 64;
    #[inline]
    fn from_bytes(bytes: &[u8]) -> Self {
        use p256::elliptic_curve::ops::Reduce;
        use p256::elliptic_curve::scalar::FromUintUnchecked;
        // Split 64 bytes into two 32-byte chunks, reduce each, combine as: low + high * 2^256 mod n
        // This gives uniform distribution when input bytes are uniform random
        let low = p256::U256::from_le_slice(&bytes[..32]);
        let high = p256::U256::from_le_slice(&bytes[32..64]);
        let low_scalar = <p256::Scalar as Reduce<p256::U256>>::reduce(low);
        let high_scalar = <p256::Scalar as Reduce<p256::U256>>::reduce(high);
        // 2^256 mod n for P256 curve order n
        // n = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
        // 2^256 mod n = 0x00000000FFFFFFFF00000000000000004319055258E8617B0C46353D039CDAAF
        let two_256_mod_n_bytes: [u8; 32] = [
            0xAF, 0xDA, 0x9C, 0x03, 0x3D, 0x35, 0x46, 0x0C, 0x7B, 0x61, 0xE8, 0x58, 0x52, 0x05,
            0x19, 0x43, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF,
            0x00, 0x00, 0x00, 0x00,
        ];
        let two_256_mod_n = <p256::Scalar as FromUintUnchecked>::from_uint_unchecked(
            p256::U256::from_le_slice(&two_256_mod_n_bytes),
        );
        Self(low_scalar + high_scalar * two_256_mod_n)
    }
}

impl p1::Random for P256Scalar {
    #[inline]
    fn random(rng: &mut impl rand::Rng) -> Self {
        // Generate 64 random bytes and reduce to get uniform distribution
        let mut buf = [0u8; 64];
        rng.fill_bytes(&mut buf);
        p1::FromBytes::from_bytes(&buf)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl Div for P256Scalar {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0.invert().expect("divisor is non-zero"))
    }
}

impl DivAssign for P256Scalar {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs
    }
}

impl p1::Field for P256Scalar {
    type Order = p1::moduli::P256;
}
