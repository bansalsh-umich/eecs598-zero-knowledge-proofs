#![allow(dead_code)]

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
