mod common;

use comms::show_transcript;
use common::F;
use p1::poly::Multilinear;
use p2::combined::CombinedMLE;
use p2::sumcheck::{Protocol, Statement};
use proptest::prelude::*;

// ---- Unit tests ----

#[test]
fn sumcheck_single_variable_linear() {
    let _guard = show_transcript();
    // g(x0) = 3*x0 + 1, evals: g(0)=1, g(1)=4, sum = 5
    let poly = Multilinear::new(1, vec![F::from(1), F::from(4)]);
    let g = CombinedMLE::from(poly);
    let stmt = Statement {
        claimed_sum: F::from(5),
        num_vars: 1,
        max_degree: 1,
    };
    let (p, v) = common::run_protocol::<Protocol<F>>("sumcheck_1var", stmt, g);
    p.unwrap();
    let (val, challenges) = v.unwrap();
    assert_eq!(challenges.len(), 1);
    let expected = F::from(1) + F::from(3) * challenges[0];
    assert_eq!(val, expected);
}

#[test]
fn sumcheck_two_variable_linear() {
    let _guard = show_transcript();
    // g(x0, x1) = 2*x0 + 3*x1 + 5
    // evals: g(0,0)=5, g(1,0)=7, g(0,1)=8, g(1,1)=10, sum=30
    let poly = Multilinear::new(2, vec![F::from(5), F::from(7), F::from(8), F::from(10)]);
    let g = CombinedMLE::from(poly);
    let stmt = Statement {
        claimed_sum: F::from(30),
        num_vars: 2,
        max_degree: 1,
    };
    let (p, v) = common::run_protocol::<Protocol<F>>("sumcheck_2var", stmt, g);
    p.unwrap();
    v.unwrap();
}

#[test]
fn sumcheck_wrong_sum_rejected() {
    let _guard = show_transcript();
    let poly = Multilinear::new(1, vec![F::from(1), F::from(4)]);
    let g = CombinedMLE::from(poly);
    let stmt = Statement {
        claimed_sum: F::from(999),
        num_vars: 1,
        max_degree: 1,
    };
    let (_p, v) = common::run_protocol::<Protocol<F>>("sumcheck_bad", stmt, g);
    assert!(v.is_err());
}

#[test]
fn sumcheck_degree_2_combined() {
    let _guard = show_transcript();
    // g = f1*f2 where f1(x0,x1) = x0+1, f2(x0,x1) = x1+2
    let f1 = Multilinear::new(2, vec![F::from(1), F::from(2), F::from(1), F::from(2)]);
    let f2 = Multilinear::new(2, vec![F::from(2), F::from(2), F::from(3), F::from(3)]);
    let g = CombinedMLE::new(2, |e| e[0] * e[1], vec![f1, f2]);
    let stmt = Statement {
        claimed_sum: F::from(15),
        num_vars: 2,
        max_degree: 2,
    };
    let (p, v) = common::run_protocol::<Protocol<F>>("sumcheck_deg2", stmt, g);
    p.unwrap();
    v.unwrap();
}

#[test]
fn sumcheck_three_variables() {
    let _guard = show_transcript();
    let evals: Vec<F> = (1..=8).map(F::from).collect();
    let actual_sum: F = evals.iter().copied().sum();
    let poly = Multilinear::new(3, evals);
    let g = CombinedMLE::from(poly);
    let stmt = Statement {
        claimed_sum: actual_sum,
        num_vars: 3,
        max_degree: 1,
    };
    let (p, v) = common::run_protocol::<Protocol<F>>("sumcheck_3var", stmt, g);
    p.unwrap();
    v.unwrap();
}

#[test]
fn sumcheck_verifier_output_equals_polynomial_at_challenges() {
    let _guard = show_transcript();
    let evals: Vec<F> = vec![F::from(3), F::from(7), F::from(11), F::from(5)];
    let actual_sum: F = evals.iter().copied().sum();
    let poly = Multilinear::new(2, evals);
    let g = CombinedMLE::from(poly.clone());
    let stmt = Statement {
        claimed_sum: actual_sum,
        num_vars: 2,
        max_degree: 1,
    };
    let (p, v) = common::run_protocol::<Protocol<F>>("sumcheck_output", stmt, g);
    p.unwrap();
    let (val, challenges) = v.unwrap();
    assert_eq!(val, poly.evaluate(&challenges));
}

// ---- Property tests ----

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    #[test]
    fn sumcheck_accepts_correct_sum_1var(e0 in common::arb_zq(), e1 in common::arb_zq()) {
        let _guard = show_transcript();
        let evals = vec![e0, e1];
        let sum: F = evals.iter().copied().sum();
        let poly = Multilinear::new(1, evals);
        let g = CombinedMLE::from(poly);
        let stmt = Statement { claimed_sum: sum, num_vars: 1, max_degree: 1 };
        let (p, v) = common::run_protocol::<Protocol<F>>("prop_1var", stmt, g);
        prop_assert!(p.is_ok());
        prop_assert!(v.is_ok());
    }

    #[test]
    fn sumcheck_accepts_correct_sum_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq(),
    ) {
        let _guard = show_transcript();
        let evals = vec![e0, e1, e2, e3];
        let sum: F = evals.iter().copied().sum();
        let poly = Multilinear::new(2, evals);
        let g = CombinedMLE::from(poly);
        let stmt = Statement { claimed_sum: sum, num_vars: 2, max_degree: 1 };
        let (p, v) = common::run_protocol::<Protocol<F>>("prop_2var", stmt, g);
        prop_assert!(p.is_ok());
        prop_assert!(v.is_ok());
    }

    #[test]
    fn sumcheck_rejects_wrong_sum_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq(),
    ) {
        let _guard = show_transcript();
        let evals = vec![e0, e1, e2, e3];
        let sum: F = evals.iter().copied().sum();
        let wrong_sum = sum + F::from(1);
        let poly = Multilinear::new(2, evals);
        let g = CombinedMLE::from(poly);
        let stmt = Statement { claimed_sum: wrong_sum, num_vars: 2, max_degree: 1 };
        let (_p, v) = common::run_protocol::<Protocol<F>>("prop_bad", stmt, g);
        prop_assert!(v.is_err());
    }

    #[test]
    fn sumcheck_degree2_property(
        a0 in common::arb_zq(), a1 in common::arb_zq(),
        a2 in common::arb_zq(), a3 in common::arb_zq(),
        b0 in common::arb_zq(), b1 in common::arb_zq(),
        b2 in common::arb_zq(), b3 in common::arb_zq(),
    ) {
        let _guard = show_transcript();
        let f1 = Multilinear::new(2, vec![a0, a1, a2, a3]);
        let f2 = Multilinear::new(2, vec![b0, b1, b2, b3]);
        let g = CombinedMLE::new(2, |e| e[0] * e[1], vec![f1, f2]);
        let sum = g.sum_over_hypercube();
        let stmt = Statement { claimed_sum: sum, num_vars: 2, max_degree: 2 };
        let (p, v) = common::run_protocol::<Protocol<F>>("prop_deg2", stmt, g);
        prop_assert!(p.is_ok());
        prop_assert!(v.is_ok());
    }
}
