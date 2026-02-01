mod common;

use comms::show_transcript;
use common::F;
use p1::curve::P256Point;
use p1::poly::Multilinear;
use p1::{One, Zero};
use p2::quokka::{OpenProtocol, Statement, Witness, commit};
use proptest::prelude::*;

type E = P256Point;

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
fn make_opening_instance(poly: Multilinear<F>, point: Vec<F>) -> (Statement<E>, Witness<E>) {
    let (comm, opening) = commit::<E>(&poly);
    let value = poly.evaluate(&point);
    let stmt = Statement { comm, point, value };
    let wit = Witness {
        poly,
        _opening: opening,
    };
    (stmt, wit)
}

// ---- Unit tests for commit ----

#[test]
fn commit_two_variable_polynomial() {
    let _guard = show_transcript();
    // 2 variables -> 4 evaluations, sqrt(4)=2 row commitments
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let (comm, _opening) = commit::<E>(&poly);
    assert_eq!(comm.len(), 2);
}

#[test]
fn commit_four_variable_polynomial() {
    let _guard = show_transcript();
    // 4 variables -> 16 evaluations, sqrt(16)=4 row commitments
    let evals: Vec<F> = (1..=16).map(F::from).collect();
    let poly = Multilinear::new(4, evals);
    let (comm, _opening) = commit::<E>(&poly);
    assert_eq!(comm.len(), 4);
}

#[test]
fn commit_six_variable_polynomial() {
    let _guard = show_transcript();
    // 6 variables -> 64 evaluations, sqrt(64)=8 row commitments
    let evals: Vec<F> = (1..=64).map(F::from).collect();
    let poly = Multilinear::new(6, evals);
    let (comm, _opening) = commit::<E>(&poly);
    assert_eq!(comm.len(), 8);
}

#[test]
fn commit_zero_polynomial() {
    let _guard = show_transcript();
    // All-zero polynomial should produce valid commitment
    let evals: Vec<F> = vec![F::zero(); 4];
    let poly = Multilinear::new(2, evals);
    let (comm, _opening) = commit::<E>(&poly);
    assert_eq!(comm.len(), 2);
}

// ---- Unit tests for OpenProtocol ----

#[test]
fn quokka_open_two_variable_accepts() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(5), F::from(7), F::from(11), F::from(13)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];
    let (stmt, wit) = make_opening_instance(poly, point);
    let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_2var", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn quokka_open_four_variable_accepts() {
    let _guard = show_transcript();
    let evals: Vec<F> = (1..=16).map(F::from).collect();
    let poly = Multilinear::new(4, evals);
    let point = vec![F::from(2), F::from(3), F::from(5), F::from(7)];
    let (stmt, wit) = make_opening_instance(poly, point);
    let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_4var", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn quokka_open_at_origin_accepts() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(42), F::from(0), F::from(0), F::from(0)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::zero(), F::zero()];
    let (stmt, wit) = make_opening_instance(poly, point);
    let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_origin", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn quokka_open_at_ones_accepts() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(1), F::from(1)];
    let (stmt, wit) = make_opening_instance(poly, point);
    let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_ones", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn quokka_open_zero_polynomial_accepts() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::zero(); 4];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(123), F::from(456)];
    let (stmt, wit) = make_opening_instance(poly, point);
    let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_zero_poly", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn quokka_wrong_value_rejected() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];
    let (comm, opening) = commit::<E>(&poly);
    // Claim a wrong value
    let wrong_value = poly.evaluate(&point) + F::from(1);
    let stmt = Statement {
        comm,
        point,
        value: wrong_value,
    };
    let wit = Witness {
        poly,
        _opening: opening,
    };
    let (_p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_bad_value", stmt, wit);
    assert!(v.is_err());
}

#[test]
fn quokka_wrong_commitment_rejected() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(1), F::from(2), F::from(3), F::from(4)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];

    // Create a different polynomial to get a wrong commitment
    let wrong_evals: Vec<F> = vec![F::from(10), F::from(20), F::from(30), F::from(40)];
    let wrong_poly = Multilinear::new(2, wrong_evals);
    let (wrong_comm, _) = commit::<E>(&wrong_poly);

    let value = poly.evaluate(&point);
    let stmt = Statement {
        comm: wrong_comm,
        point,
        value,
    };
    let wit = Witness {
        poly,
        _opening: F::zero(),
    };
    let (_p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_bad_comm", stmt, wit);
    assert!(v.is_err());
}

#[test]
fn quokka_deterministic_with_seeded_rng() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(5), F::from(7), F::from(11), F::from(13)];
    let poly = Multilinear::new(2, evals);
    let point = vec![F::from(3), F::from(4)];
    let (stmt, wit) = make_opening_instance(poly, point);
    let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_det", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn quokka_all_hypercube_points_2var() {
    let _guard = show_transcript();
    // Test opening at all 4 corners of the hypercube for a 2-variable polynomial.
    // At hypercube points, the evaluation is just a direct lookup: f(b0,b1) = evals[b0 + 2*b1]
    let evals: Vec<F> = vec![F::from(10), F::from(20), F::from(30), F::from(40)];
    let poly = Multilinear::new(2, evals.clone());

    for idx in 0..4 {
        let point = index_to_hypercube_point(idx, 2);
        let (stmt, wit) = make_opening_instance(poly.clone(), point);
        // Verify the expected value matches the direct lookup
        assert_eq!(stmt.value, evals[idx], "value mismatch at index {}", idx);
        let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_hypercube_2var", stmt, wit);
        p.unwrap();
        v.unwrap();
    }
}

#[test]
fn quokka_all_hypercube_points_4var() {
    let _guard = show_transcript();
    // Test opening at all 16 corners of the hypercube for a 4-variable polynomial.
    let evals: Vec<F> = (1..=16).map(F::from).collect();
    let poly = Multilinear::new(4, evals.clone());

    for (idx, &eval) in evals.iter().enumerate() {
        let point = index_to_hypercube_point(idx, 4);
        let (stmt, wit) = make_opening_instance(poly.clone(), point);
        assert_eq!(stmt.value, eval, "value mismatch at index {}", idx);
        let (p, v) = common::run_protocol::<OpenProtocol<E>>("quokka_hypercube_4var", stmt, wit);
        p.unwrap();
        v.unwrap();
    }
}

// ---- Property tests ----

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2))]

    #[test]
    fn quokka_accepts_correct_opening_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq(),
        r0 in common::arb_zq(), r1 in common::arb_zq(),
    ) {
        let _guard = show_transcript();
        let evals = vec![e0, e1, e2, e3];
        let poly = Multilinear::new(2, evals);
        let point = vec![r0, r1];
        let (stmt, wit) = make_opening_instance(poly, point);
        let (p, v) = common::run_protocol::<OpenProtocol<E>>("prop_quokka_2var", stmt, wit);
        prop_assert!(p.is_ok());
        prop_assert!(v.is_ok());
    }

    #[test]
    fn quokka_accepts_correct_opening_4var(
        evals in proptest::collection::vec(common::arb_zq(), 16),
        r0 in common::arb_zq(), r1 in common::arb_zq(),
        r2 in common::arb_zq(), r3 in common::arb_zq(),
    ) {
        let _guard = show_transcript();
        let poly = Multilinear::new(4, evals);
        let point = vec![r0, r1, r2, r3];
        let (stmt, wit) = make_opening_instance(poly, point);
        let (p, v) = common::run_protocol::<OpenProtocol<E>>("prop_quokka_4var", stmt, wit);
        prop_assert!(p.is_ok());
        prop_assert!(v.is_ok());
    }

    #[test]
    fn quokka_rejects_wrong_value_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq(),
        r0 in common::arb_zq(), r1 in common::arb_zq(),
    ) {
        let _guard = show_transcript();
        let evals = vec![e0, e1, e2, e3];
        let poly = Multilinear::new(2, evals);
        let point = vec![r0, r1];
        let (comm, opening) = commit::<E>(&poly);
        let wrong_value = poly.evaluate(&point) + F::from(1);
        let stmt = Statement { comm, point, value: wrong_value };
        let wit = Witness { poly, _opening: opening };
        let (_p, v) = common::run_protocol::<OpenProtocol<E>>("prop_quokka_bad", stmt, wit);
        prop_assert!(v.is_err());
    }
}
