#![allow(dead_code)]

use p1::moduli::P256CurveOrder;
use p1::zq::Zq;
use anyhow::Result;
use p2::ip::InteractiveProof;
use proptest::prelude::*;
use rand::rngs::StdRng;
use rand::SeedableRng;
use sfs_bigint::U256;
use std::sync::LazyLock;

pub type F = Zq<P256CurveOrder>;

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
    any::<U256>().prop_map(F::new).boxed()
}

/// Execute an interactive proof protocol synchronously by spinning up a
/// single-threaded tokio runtime. Returns (prover_result, verifier_result).
/// Uses a deterministic test RNG seeded from TEST_RNG_SEED env var (default: 42).
pub fn run_protocol<P: InteractiveProof>(
    name: impl Into<String>,
    stmt: P::Statement,
    wit: P::Witness,
) -> (Result<P::ProverOutput>, Result<P::VerifierOutput>) {
    let mut rng = test_rng();
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(p2::ip::execute_with_rng::<P, _>(name, stmt, wit, &mut rng))
}
