mod common;

use common::{E, F};
use p1::Random;
use p1::poly::Multilinear;
use p2::combined::CombinedMLE;
use p2::ec::EllipticCurve;
use p3::pedersen;
use p3::sumcheck::{self, PublicParams, Statement, Witness};
use p3::transcript::Transcript;
use proptest::prelude::*;

type S = F;

fn setup_params(num_vars: usize, max_degree: usize) -> PublicParams<E> {
    let total_gens = num_vars * (max_degree + 1);
    let vec_gens = E::get_generators(total_gens);
    let h = E::get_generator_from_seed(10000u64);
    let g = E::get_generator_from_seed(10001u64);
    PublicParams {
        vec_gens,
        scalar_gens: [g, h],
    }
}

fn commit_sum(params: &PublicParams<E>, sum: S) -> (E, S) {
    let mut rng = common::test_rng();
    let r = S::random(&mut rng);
    let comm = pedersen::commit(sum, r, &params.scalar_gens);
    (comm, r)
}

// ==============================================================================
// Unit tests
// ==============================================================================

#[test]
fn sumcheck_single_variable_linear() {
    let mut rng = common::test_rng();
    // g(x0) = 3*x0 + 1, evals: g(0)=1, g(1)=4, sum = 5
    let evals = vec![S::from(1u64), S::from(4u64)];
    let mle = Multilinear::new(1, evals);
    let combined = CombinedMLE::from(mle);
    let claimed_sum = combined.sum_over_hypercube();

    let num_vars = 1;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, claimed_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined.clone(),
        sum: claimed_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, challenges, r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    let (comm_final, v_challenges) =
        sumcheck::verify(&params, &statement, &proof, &mut trans_v).unwrap();

    assert_eq!(challenges, v_challenges);
    let expected_eval = combined.evaluate(&challenges);
    assert_eq!(
        comm_final,
        pedersen::commit(expected_eval, r_final, &params.scalar_gens)
    );
}

#[test]
fn sumcheck_two_variable_linear() {
    let mut rng = common::test_rng();
    // g(x0, x1) = 2*x0 + 3*x1 + 5
    // evals: g(0,0)=5, g(1,0)=7, g(0,1)=8, g(1,1)=10, sum=30
    let evals = vec![S::from(5u64), S::from(7u64), S::from(8u64), S::from(10u64)];
    let mle = Multilinear::new(2, evals);
    let combined = CombinedMLE::from(mle);
    let claimed_sum = combined.sum_over_hypercube();

    let num_vars = 2;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, claimed_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined,
        sum: claimed_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, _challenges, _r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    sumcheck::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn sumcheck_wrong_sum_rejected() {
    let mut rng = common::test_rng();
    let evals = vec![S::from(1u64), S::from(4u64)];
    let mle = Multilinear::new(1, evals);
    let combined = CombinedMLE::from(mle);
    let wrong_sum = combined.sum_over_hypercube() + S::from(1u64);

    let num_vars = 1;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, wrong_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined,
        sum: wrong_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, _challenges, _r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    assert!(sumcheck::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

#[test]
fn sumcheck_degree_2_combined() {
    let mut rng = common::test_rng();
    // g = f1*f2 where f1(x0,x1) = x0+1, f2(x0,x1) = x1+2
    let f1 = Multilinear::new(
        2,
        vec![S::from(1u64), S::from(2u64), S::from(1u64), S::from(2u64)],
    );
    let f2 = Multilinear::new(
        2,
        vec![S::from(2u64), S::from(2u64), S::from(3u64), S::from(3u64)],
    );
    let combined = CombinedMLE::new(2, |e| e[0] * e[1], vec![f1, f2]);
    let claimed_sum = combined.sum_over_hypercube();

    let num_vars = 2;
    let max_degree = 2;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, claimed_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined,
        sum: claimed_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, _challenges, _r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    sumcheck::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn sumcheck_three_variables() {
    let mut rng = common::test_rng();
    let evals: Vec<S> = (1..=8).map(S::from).collect();
    let actual_sum: S = evals.iter().copied().sum();
    let mle = Multilinear::new(3, evals);
    let combined = CombinedMLE::from(mle);

    let num_vars = 3;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, actual_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined,
        sum: actual_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, _challenges, _r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    sumcheck::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn sumcheck_verifier_output_equals_polynomial_at_challenges() {
    let mut rng = common::test_rng();
    let evals: Vec<S> = vec![S::from(3u64), S::from(7u64), S::from(11u64), S::from(5u64)];
    let actual_sum: S = evals.iter().copied().sum();
    let mle = Multilinear::new(2, evals);
    let combined = CombinedMLE::from(mle.clone());

    let num_vars = 2;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, actual_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined.clone(),
        sum: actual_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, challenges, r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    let (comm_final, v_challenges) =
        sumcheck::verify(&params, &statement, &proof, &mut trans_v).unwrap();

    // Verify Fiat-Shamir consistency: prover and verifier derive same challenges
    assert_eq!(challenges, v_challenges);

    // Verify that the commitment is to the correct evaluation
    let expected_eval = mle.evaluate(&v_challenges);
    assert_eq!(
        comm_final,
        pedersen::commit(expected_eval, r_final, &params.scalar_gens)
    );
}

#[test]
fn sumcheck_zero_polynomial() {
    let mut rng = common::test_rng();
    let evals: Vec<S> = vec![S::from(0u64); 4];
    let mle = Multilinear::new(2, evals);
    let combined = CombinedMLE::from(mle);
    let claimed_sum = S::from(0u64);

    let num_vars = 2;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, claimed_sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined,
        sum: claimed_sum,
        r_sum,
    };

    let mut trans_p = Transcript::new("zk_sumcheck");
    let (proof, _challenges, _r_final) =
        sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("zk_sumcheck");
    sumcheck::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

// ==============================================================================
// Transcript divergence tests
// ==============================================================================

#[test]
fn sumcheck_challenges_diverge_on_different_polynomials() {
    // Two different polynomials should produce different challenges
    let evals1 = vec![S::from(1u64), S::from(2u64), S::from(3u64), S::from(4u64)];
    let evals2 = vec![S::from(5u64), S::from(6u64), S::from(7u64), S::from(8u64)];

    let mle1 = Multilinear::new(2, evals1);
    let mle2 = Multilinear::new(2, evals2);
    let combined1 = CombinedMLE::from(mle1);
    let combined2 = CombinedMLE::from(mle2);

    let sum1 = combined1.sum_over_hypercube();
    let sum2 = combined2.sum_over_hypercube();

    let num_vars = 2;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);

    let (comm_sum1, r_sum1) = commit_sum(&params, sum1);
    let (comm_sum2, r_sum2) = commit_sum(&params, sum2);

    let stmt1 = Statement {
        comm_sum: comm_sum1,
        num_vars,
        max_degree,
    };
    let wit1 = Witness {
        polynomial: combined1,
        sum: sum1,
        r_sum: r_sum1,
    };
    let mut trans1 = Transcript::new("zk_sumcheck");
    let (_, challenges1, _) =
        sumcheck::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let stmt2 = Statement {
        comm_sum: comm_sum2,
        num_vars,
        max_degree,
    };
    let wit2 = Witness {
        polynomial: combined2,
        sum: sum2,
        r_sum: r_sum2,
    };
    let mut trans2 = Transcript::new("zk_sumcheck");
    let (_, challenges2, _) =
        sumcheck::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    // Different polynomials should produce different challenges
    assert_ne!(challenges1, challenges2);
}

#[test]
fn sumcheck_challenges_diverge_on_different_prover_randomness() {
    let mut rng = common::test_rng();
    // Same polynomial with different prover randomness should produce different challenges
    // because the round polynomials are blinded differently
    let evals = vec![S::from(1u64), S::from(2u64), S::from(3u64), S::from(4u64)];
    let mle = Multilinear::new(2, evals);
    let combined = CombinedMLE::from(mle);
    let sum = combined.sum_over_hypercube();

    let num_vars = 2;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);
    let (comm_sum, r_sum) = commit_sum(&params, sum);

    let statement = Statement {
        comm_sum,
        num_vars,
        max_degree,
    };
    let witness = Witness {
        polynomial: combined,
        sum,
        r_sum,
    };

    let mut trans1 = Transcript::new("zk_sumcheck");
    let (_, challenges1, _) = sumcheck::prove(
        &params,
        &statement.clone(),
        &witness.clone(),
        &mut trans1,
        &mut rng,
    );

    let mut trans2 = Transcript::new("zk_sumcheck");
    let (_, challenges2, _) = sumcheck::prove(&params, &statement, &witness, &mut trans2, &mut rng);

    // Different prover randomness should produce different challenges (due to blinding)
    assert_ne!(challenges1, challenges2);
}

#[test]
fn sumcheck_challenges_diverge_on_different_claimed_sums() {
    // Same polynomial but different claimed sums (one correct, one wrong)
    // should produce different transcript states
    let evals = vec![S::from(1u64), S::from(2u64), S::from(3u64), S::from(4u64)];
    let mle = Multilinear::new(2, evals);
    let combined = CombinedMLE::from(mle);
    let correct_sum = combined.sum_over_hypercube();
    let wrong_sum = correct_sum + S::from(1u64);

    let num_vars = 2;
    let max_degree = 1;
    let params = setup_params(num_vars, max_degree);

    let (comm_sum1, r_sum1) = commit_sum(&params, correct_sum);
    let (comm_sum2, r_sum2) = commit_sum(&params, wrong_sum);

    let stmt1 = Statement {
        comm_sum: comm_sum1,
        num_vars,
        max_degree,
    };
    let wit1 = Witness {
        polynomial: combined.clone(),
        sum: correct_sum,
        r_sum: r_sum1,
    };
    let mut trans1 = Transcript::new("zk_sumcheck");
    let (proof1, _, _) = sumcheck::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let stmt2 = Statement {
        comm_sum: comm_sum2,
        num_vars,
        max_degree,
    };
    let wit2 = Witness {
        polynomial: combined,
        sum: wrong_sum,
        r_sum: r_sum2,
    };
    let mut trans2 = Transcript::new("zk_sumcheck");
    let (proof2, _, _) = sumcheck::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    // Different claimed sums (different statements) should lead to different proofs
    // We check the dot_product proof challenge as it captures the full transcript state
    assert_ne!(proof1.dp_proof.c, proof2.dp_proof.c);
}

#[test]
fn sumcheck_challenges_diverge_on_different_params() {
    // Same polynomial and sum, but different generator parameters
    let evals = vec![S::from(1u64), S::from(2u64), S::from(3u64), S::from(4u64)];
    let mle = Multilinear::new(2, evals);
    let combined = CombinedMLE::from(mle);
    let sum = combined.sum_over_hypercube();

    let num_vars = 2;
    let max_degree = 1;

    // Two different parameter sets with different generators
    let total_gens = num_vars * (max_degree + 1);
    let vec_gens1 = E::get_generators(total_gens);
    let vec_gens2: Vec<E> = (100..100 + total_gens)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();

    let params1 = PublicParams {
        vec_gens: vec_gens1,
        scalar_gens: [
            E::get_generator_from_seed(10001u64),
            E::get_generator_from_seed(10000u64),
        ],
    };
    let params2 = PublicParams {
        vec_gens: vec_gens2,
        scalar_gens: [
            E::get_generator_from_seed(20001u64),
            E::get_generator_from_seed(20000u64),
        ],
    };

    let (comm_sum1, r_sum1) = commit_sum(&params1, sum);
    let (comm_sum2, r_sum2) = commit_sum(&params2, sum);

    let stmt1 = Statement {
        comm_sum: comm_sum1,
        num_vars,
        max_degree,
    };
    let wit1 = Witness {
        polynomial: combined.clone(),
        sum,
        r_sum: r_sum1,
    };
    let mut trans1 = Transcript::new("zk_sumcheck");
    let (_, challenges1, _) =
        sumcheck::prove(&params1, &stmt1, &wit1, &mut trans1, common::test_rng());

    let stmt2 = Statement {
        comm_sum: comm_sum2,
        num_vars,
        max_degree,
    };
    let wit2 = Witness {
        polynomial: combined,
        sum,
        r_sum: r_sum2,
    };
    let mut trans2 = Transcript::new("zk_sumcheck");
    let (_, challenges2, _) =
        sumcheck::prove(&params2, &stmt2, &wit2, &mut trans2, common::test_rng());

    // Different params should produce different challenges
    assert_ne!(challenges1, challenges2);
}

// ==============================================================================
// Property-based tests
// ==============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5))]

    #[test]
    fn sumcheck_accepts_correct_sum_1var(e0 in common::arb_zq(), e1 in common::arb_zq()) {
        let mut rng = common::test_rng();
        let evals = vec![e0, e1];
        let sum: S = evals.iter().copied().sum();
        let mle = Multilinear::new(1, evals);
        let combined = CombinedMLE::from(mle);

        let num_vars = 1;
        let max_degree = 1;
        let params = setup_params(num_vars, max_degree);
        let (comm_sum, r_sum) = commit_sum(&params, sum);

        let statement = Statement { comm_sum, num_vars, max_degree };
        let witness = Witness { polynomial: combined, sum, r_sum };

        let mut trans_p = Transcript::new("zk_sumcheck");
        let (proof, _challenges, _r_final) = sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

        let mut trans_v = Transcript::new("zk_sumcheck");
        prop_assert!(sumcheck::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn sumcheck_accepts_correct_sum_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq()
    ) {
        let mut rng = common::test_rng();
        let evals = vec![e0, e1, e2, e3];
        let sum: S = evals.iter().copied().sum();
        let mle = Multilinear::new(2, evals);
        let combined = CombinedMLE::from(mle);

        let num_vars = 2;
        let max_degree = 1;
        let params = setup_params(num_vars, max_degree);
        let (comm_sum, r_sum) = commit_sum(&params, sum);

        let statement = Statement { comm_sum, num_vars, max_degree };
        let witness = Witness { polynomial: combined, sum, r_sum };

        let mut trans_p = Transcript::new("zk_sumcheck");
        let (proof, _challenges, _r_final) = sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

        let mut trans_v = Transcript::new("zk_sumcheck");
        prop_assert!(sumcheck::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn sumcheck_rejects_wrong_sum_2var(
        e0 in common::arb_zq(), e1 in common::arb_zq(),
        e2 in common::arb_zq(), e3 in common::arb_zq()
    ) {
        let mut rng = common::test_rng();
        let evals = vec![e0, e1, e2, e3];
        let sum: S = evals.iter().copied().sum();
        let wrong_sum = sum + S::from(1u64);
        let mle = Multilinear::new(2, evals);
        let combined = CombinedMLE::from(mle);

        let num_vars = 2;
        let max_degree = 1;
        let params = setup_params(num_vars, max_degree);
        let (comm_sum, r_sum) = commit_sum(&params, wrong_sum);

        let statement = Statement { comm_sum, num_vars, max_degree };
        let witness = Witness { polynomial: combined, sum: wrong_sum, r_sum };

        let mut trans_p = Transcript::new("zk_sumcheck");
        let (proof, _challenges, _r_final) = sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

        let mut trans_v = Transcript::new("zk_sumcheck");
        prop_assert!(sumcheck::verify(&params, &statement, &proof, &mut trans_v).is_err());
    }

    #[test]
    fn sumcheck_degree2_property(
        a0 in common::arb_zq(), a1 in common::arb_zq(),
        a2 in common::arb_zq(), a3 in common::arb_zq(),
        b0 in common::arb_zq(), b1 in common::arb_zq(),
        b2 in common::arb_zq(), b3 in common::arb_zq()
    ) {
        let mut rng = common::test_rng();
        let f1 = Multilinear::new(2, vec![a0, a1, a2, a3]);
        let f2 = Multilinear::new(2, vec![b0, b1, b2, b3]);
        let combined = CombinedMLE::new(2, |e| e[0] * e[1], vec![f1, f2]);
        let sum = combined.sum_over_hypercube();

        let num_vars = 2;
        let max_degree = 2;
        let params = setup_params(num_vars, max_degree);
        let (comm_sum, r_sum) = commit_sum(&params, sum);

        let statement = Statement { comm_sum, num_vars, max_degree };
        let witness = Witness { polynomial: combined, sum, r_sum };

        let mut trans_p = Transcript::new("zk_sumcheck");
        let (proof, _challenges, _r_final) = sumcheck::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

        let mut trans_v = Transcript::new("zk_sumcheck");
        prop_assert!(sumcheck::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }
}
