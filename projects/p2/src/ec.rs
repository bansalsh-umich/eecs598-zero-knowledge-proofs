use std::{
    fmt::Debug,
    ops::{Add, Mul, Neg, Sub},
    sync::RwLock,
};

use p1::{Field, Zero, curve::P256Point, zq::Zq};

/// A trait representing an elliptic curve suitable for cryptographic operations.
///
/// We will only use P256Point concretely for this project, but we wanted the implementations of quokka and
/// delphian to be, in principle, agnostic over any elliptic cutve.
pub trait EllipticCurve:
    Sized
    + Add<Output = Self>
    + Sub<Output = Self>
    + Neg<Output = Self>
    + Mul<Self::Scalar, Output = Self>
    + Copy
    + Debug
    + Zero
    + PartialEq
    + Eq
    + Send
    + Sync
    + 'static
{
    /// The field over which the curve equation is defined.
    type BaseField: Field;

    /// The field of scalars for scalar multiplication.
    type Scalar: Field;

    fn msm(scalars: &[Self::Scalar], points: &[Self]) -> Self;

    /// Returns a deterministic generator point derived from the given seed.
    fn get_generator_from_seed(seed: u64) -> Self;

    /// Returns n independent generators [G_0, G_1, ..., G_{n-1}].
    ///
    /// This is equivalent to calling get_generator_from_seed for seeds 0 through n-1.
    /// Implementations may override this to provide caching for better performance.
    fn get_generators(n: usize) -> Vec<Self> {
        (0..n)
            .map(|i| Self::get_generator_from_seed(i as u64))
            .collect()
    }
}

// Convenience aliases, students should not really have to use these
pub type BaseFieldOf<E> = <E as EllipticCurve>::BaseField;
pub type ScalarOf<E> = <E as EllipticCurve>::Scalar;

impl EllipticCurve for P256Point {
    type BaseField = Zq<p1::moduli::P256>;
    type Scalar = Zq<p1::moduli::P256CurveOrder>;
    fn msm(scalars: &[Self::Scalar], points: &[Self]) -> Self {
        P256Point::msm(scalars, points)
    }

    fn get_generator_from_seed(seed: u64) -> Self {
        P256Point::get_generator_from_seed(seed as usize)
    }

    fn get_generators(n: usize) -> Vec<Self> {
        P256_GENERATOR_CACHE.get(n)
    }
}

struct GeneratorCache<E> {
    generators: RwLock<Vec<E>>,
}

impl<E: EllipticCurve> GeneratorCache<E> {
    const fn new() -> Self {
        GeneratorCache {
            generators: RwLock::new(Vec::new()),
        }
    }

    fn get(&self, n: usize) -> Vec<E> {
        let read = self.generators.read().unwrap();
        if read.len() >= n {
            return read[..n].to_vec();
        }
        drop(read);

        let mut write = self.generators.write().unwrap();
        let len = write.len();
        write.extend((len..n).map(|i| E::get_generator_from_seed(i as u64)));
        write[..n].to_vec()
    }
}

static P256_GENERATOR_CACHE: GeneratorCache<P256Point> = GeneratorCache::new();
