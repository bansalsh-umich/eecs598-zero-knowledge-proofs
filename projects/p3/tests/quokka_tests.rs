mod common;

use common::{E, F};
use num_traits::{One, Zero};
use p1::poly::Multilinear;
use p1::Random;
use p2::ec::EllipticCurve;
use p3::pedersen;
use p3::quokka::{self, PublicParams, Statement, Witness};
use p3::transcript::Transcript;
use proptest::prelude::*;

// ==============================================================================
// Helper functions
// ==============================================================================

fn setup_params(sqrt_n: usize) -> PublicParams<E> {
    let vec_gens = E::get_generators(sqrt_n);
    let h = E::get_generator_from_seed(10000u64);
    let g = E::get_generator_from_seed(10001u64);
    PublicParams {
        vec_gens,
        scalar_gens: [g, h],
    }
}

/// Convert an index to a hypercube point (vector of 0s and 1s).
fn index_to_hypercube_point(index: usize, num_vars: usize) -> Vec<F> {
    (0..num_vars)
        .map(|i| {
            if (index >> i) & 1 == 1 {
                F::one()
            } else {
                F::zero()
            }
        })
        .collect()
}

/// Helper to create a statement and witness for testing the opening protocol.
/// Requires a polynomial with an even number of variables.
fn make_opening_instance(
    poly: Multilinear<F>,
    point: Vec<F>,
    params: &PublicParams<E>,
) -> (Statement<E>, Witness<E>) {
    let num_rows = 1 << (poly.num_vars() / 2);
    let mut rng = common::test_rng();

    // Generate random openings for each row
    let openings: Vec<F> = (0..num_rows).map(|_| F::random(&mut rng)).collect();

    let comm_rows = quokka::commit(&poly, &openings, params);
    let eval = poly.evaluate(&point);

    let r_eval = F::random(&mut rng);
    let comm_eval = pedersen::commit(eval, r_eval, &params.scalar_gens);

    let stmt = Statement::new(comm_rows, point, comm_eval);
    let wit = Witness::new(poly, openings, eval, r_eval);
    (stmt, wit)
}

// ==============================================================================
// Commitment tests
// ==============================================================================

#[test]
fn commit_deterministic() {
    // Same polynomial with same openings produces same commitment
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let params = setup_params(2);
    let openings = vec![F::from(1), F::from(2)];

    let comm1 = quokka::commit(&poly, &openings, &params);
    let comm2 = quokka::commit(&poly, &openings, &params);

    assert_eq!(comm1, comm2);
}

#[test]
fn commit_different_polynomials_differ() {
    // Different polynomials produce different commitments (binding property)
    let params = setup_params(2);
    let openings = vec![F::from(1), F::from(2)];

    let poly1 = Multilinear::new(2, vec![F::from(1), F::from(2), F::from(3), F::from(4)]);
    let poly2 = Multilinear::new(2, vec![F::from(5), F::from(6), F::from(7), F::from(8)]);

    let comm1 = quokka::commit(&poly1, &openings, &params);
    let comm2 = quokka::commit(&poly2, &openings, &params);

    assert_ne!(comm1, comm2);
}

#[test]
fn commit_different_openings_differ() {
    // Same polynomial with different openings produces different commitments
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let params = setup_params(2);

    let openings1 = vec![F::from(1), F::from(2)];
    let openings2 = vec![F::from(3), F::from(4)];

    let comm1 = quokka::commit(&poly, &openings1, &params);
    let comm2 = quokka::commit(&poly, &openings2, &params);

    assert_ne!(comm1, comm2);
}

#[test]
fn commit_zero_vs_nonzero_differ() {
    // Zero polynomial should produce different commitment than non-zero polynomial
    let params = setup_params(2);
    let openings = vec![F::from(1), F::from(2)];

    let zero_poly = Multilinear::new(2, vec![F::zero(); 4]);
    let nonzero_poly = Multilinear::new(2, vec![F::from(1), F::from(2), F::from(3), F::from(4)]);

    let comm_zero = quokka::commit(&zero_poly, &openings, &params);
    let comm_nonzero = quokka::commit(&nonzero_poly, &openings, &params);

    assert_ne!(comm_zero, comm_nonzero);
}

// ==============================================================================
// Opening protocol completeness tests
// ==============================================================================

#[test]
fn quokka_open_two_variable_accepts() {
    let evals: Vec<F> = vec![F::from(5), F::from(7), F::from(11), F::from(13)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];
    let params = setup_params(2);
    let (stmt, wit) = make_opening_instance(poly, point, &params);

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
}

#[test]
fn quokka_open_four_variable_accepts() {
    let evals: Vec<F> = (1..=16).map(F::from).collect();
    let poly = Multilinear::new(4, evals);
    let point = vec![F::from(2), F::from(3), F::from(5), F::from(7)];
    let params = setup_params(4);
    let (stmt, wit) = make_opening_instance(poly, point, &params);

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
}

#[test]
fn quokka_open_at_origin_accepts() {
    let evals: Vec<F> = vec![F::from(42), F::from(0), F::from(0), F::from(0)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::zero(), F::zero()];
    let params = setup_params(2);
    let (stmt, wit) = make_opening_instance(poly, point, &params);

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
}

#[test]
fn quokka_open_at_ones_accepts() {
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(1), F::from(1)];
    let params = setup_params(2);
    let (stmt, wit) = make_opening_instance(poly, point, &params);

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
}

#[test]
fn quokka_open_zero_polynomial_accepts() {
    let evals: Vec<F> = vec![F::zero(); 4];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(123), F::from(456)];
    let params = setup_params(2);
    let (stmt, wit) = make_opening_instance(poly, point, &params);

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
}

// ==============================================================================
// Opening protocol soundness tests
// ==============================================================================

#[test]
fn quokka_wrong_value_rejected() {
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];
    let params = setup_params(2);
    let num_rows = 2;
    let mut rng = common::test_rng();

    let openings: Vec<F> = (0..num_rows).map(|_| F::random(&mut rng)).collect();
    let comm_rows = quokka::commit(&poly, &openings, &params);

    // Claim a wrong value
    let wrong_eval = poly.evaluate(&point) + F::from(1);
    let r_eval = F::random(&mut rng);
    let comm_eval = pedersen::commit(wrong_eval, r_eval, &params.scalar_gens);

    let stmt = Statement::new(comm_rows, point, comm_eval);
    let wit = Witness::new(poly, openings, wrong_eval, r_eval);

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    assert!(quokka::verify(&params, &stmt, &proof, &mut trans_v).is_err());
}

#[test]
fn quokka_wrong_commitment_rejected() {
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];
    let params = setup_params(2);
    let mut rng = common::test_rng();

    // Create a different polynomial to get a wrong commitment
    let wrong_evals: Vec<F> = vec![F::from(10), F::from(20), F::from(30), F::from(40)];
    let wrong_poly = Multilinear::new(2, wrong_evals);
    let wrong_openings = vec![F::from(1), F::from(2)];
    let wrong_comm = quokka::commit(&wrong_poly, &wrong_openings, &params);

    let eval = poly.evaluate(&point);
    let r_eval = F::random(&mut rng);
    let comm_eval = pedersen::commit(eval, r_eval, &params.scalar_gens);

    let stmt = Statement::new(wrong_comm, point, comm_eval);
    let wit = Witness::new(poly, vec![F::zero(), F::zero()], eval, r_eval); // wrong openings

    let mut trans_p = Transcript::new("quokka");
    let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

    let mut trans_v = Transcript::new("quokka");
    assert!(quokka::verify(&params, &stmt, &proof, &mut trans_v).is_err());
}

#[test]
fn quokka_all_hypercube_points_2var() {
    // Test opening at all 4 corners of the hypercube for a 2-variable polynomial.
    let evals: Vec<F> = vec![F::from(10), F::from(20), F::from(30), F::from(40)];
    let poly = Multilinear::new(2, evals.clone());
    let params = setup_params(2);

    for idx in 0..4 {
        let point = index_to_hypercube_point(idx, 2);
        let (stmt, wit) = make_opening_instance(poly.clone(), point, &params);
        // Verify the expected value matches the direct lookup
        assert_eq!(wit.eval, evals[idx], "value mismatch at index {}", idx);

        let mut trans_p = Transcript::new("quokka");
        let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

        let mut trans_v = Transcript::new("quokka");
        quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
    }
}

#[test]
fn quokka_all_hypercube_points_4var() {
    // Test opening at all 16 corners of the hypercube for a 4-variable polynomial.
    let evals: Vec<F> = (1..=16).map(F::from).collect();
    let poly = Multilinear::new(4, evals.clone());
    let params = setup_params(4);

    for (idx, &eval) in evals.iter().enumerate() {
        let point = index_to_hypercube_point(idx, 4);
        let (stmt, wit) = make_opening_instance(poly.clone(), point, &params);
        assert_eq!(wit.eval, eval, "value mismatch at index {}", idx);

        let mut trans_p = Transcript::new("quokka");
        let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

        let mut trans_v = Transcript::new("quokka");
        quokka::verify(&params, &stmt, &proof, &mut trans_v).unwrap();
    }
}

// ==============================================================================
// Property-based tests
// ==============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5))]

    #[test]
    fn quokka_accepts_correct_opening_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq(),
        r0 in common::arb_zq(), r1 in common::arb_zq()
    ) {
        let evals = vec![e0, e1, e2, e3];
        let poly = Multilinear::new(2, evals);
        let point = vec![r0, r1];
        let params = setup_params(2);
        let (stmt, wit) = make_opening_instance(poly, point, &params);

        let mut trans_p = Transcript::new("quokka");
        let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

        let mut trans_v = Transcript::new("quokka");
        prop_assert!(quokka::verify(&params, &stmt, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn quokka_accepts_correct_opening_4var(
        evals in proptest::collection::vec(common::arb_zq(), 16),
        r0 in common::arb_zq(), r1 in common::arb_zq(),
        r2 in common::arb_zq(), r3 in common::arb_zq()
    ) {
        let poly = Multilinear::new(4, evals);
        let point = vec![r0, r1, r2, r3];
        let params = setup_params(4);
        let (stmt, wit) = make_opening_instance(poly, point, &params);

        let mut trans_p = Transcript::new("quokka");
        let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

        let mut trans_v = Transcript::new("quokka");
        prop_assert!(quokka::verify(&params, &stmt, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn quokka_rejects_wrong_value_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq(),
        r0 in common::arb_zq(), r1 in common::arb_zq()
    ) {
        let evals = vec![e0, e1, e2, e3];
        let poly = Multilinear::new(2, evals);
        let point = vec![r0, r1];
        let params = setup_params(2);
        let num_rows = 2;
        let mut rng = common::test_rng();

        let openings: Vec<F> = (0..num_rows).map(|_| F::random(&mut rng)).collect();
        let comm_rows = quokka::commit(&poly, &openings, &params);

        let wrong_eval = poly.evaluate(&point) + F::from(1);
        let r_eval = F::random(&mut rng);
        let comm_eval = pedersen::commit(wrong_eval, r_eval, &params.scalar_gens);

        let stmt = Statement::new(comm_rows, point, comm_eval);
        let wit = Witness::new(poly, openings, wrong_eval, r_eval);

        let mut trans_p = Transcript::new("quokka");
        let proof = quokka::prove(&params, &stmt, &wit, &mut trans_p, rand::rng());

        let mut trans_v = Transcript::new("quokka");
        prop_assert!(quokka::verify(&params, &stmt, &proof, &mut trans_v).is_err());
    }
}
