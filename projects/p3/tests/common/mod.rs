#![allow(dead_code)]

use proptest::prelude::*;
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::sync::LazyLock;
pub use third_party_curve::{P256Point, P256Scalar};

pub type E = P256Point;
pub type F = P256Scalar;

static TEST_SEED: LazyLock<u64> = LazyLock::new(|| {
    std::env::var("TEST_RNG_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(42)
});

pub fn test_rng() -> StdRng {
    StdRng::seed_from_u64(*TEST_SEED)
}

pub fn arb_zq() -> BoxedStrategy<F> {
    any::<u64>().prop_map(F::from).boxed()
}

/// Strategy for generating small non-zero field elements.
pub fn arb_small_zq() -> BoxedStrategy<F> {
    (1u64..1000).prop_map(F::from).boxed()
}
