#![allow(non_snake_case)]

mod common;

use common::{E, F};
use num_traits::{One, Zero};
use p2::ec::EllipticCurve;
use p2::sparsemat::{SparseMatrix, SparseVector};
use p3::delphian::{self, PublicParams, Statement, Witness};
use p3::transcript::Transcript;

// ==============================================================================
// Helper functions
// ==============================================================================

fn setup_params(w_size: usize, log_rows: usize, log_cols: usize) -> PublicParams<E> {
    let sqrt_w = 1usize << (w_size.ilog2() as usize / 2);
    let main_sc_num = log_rows * 4;
    let mv_sc_num = log_cols * 3;

    let quokka_gens: Vec<E> = (0..sqrt_w)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let main_sc_gens: Vec<E> = (sqrt_w..sqrt_w + main_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let mv_sc_gens: Vec<E> = (sqrt_w + main_sc_num..sqrt_w + main_sc_num + mv_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let h = E::get_generator_from_seed(10000u64);
    let g = E::get_generator_from_seed(10001u64);

    PublicParams::new(quokka_gens, main_sc_gens, mv_sc_gens, [g, h])
}

/// Simple R1CS: one constraint w0 * x0 = w1
/// z = [x0, 0, 0, 0 | w0, w1, 0, 0], rows=4, cols=8
fn multiplication_instance(a: F, b: F) -> (Statement<E>, Witness<E>) {
    let c = a * b;
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, a)]);
    let w = SparseVector::from_entries(4, vec![(0, b), (1, c)]);
    (Statement::new(A, B, C, x), Witness::new(w))
}

/// R1CS for: w0 + x0 = w1 (encoded as (w0 + x0) * 1 = w1)
/// A selects z[4]+z[0], B selects constant 1 via z[1]=1, C selects z[5]
/// z = [x0, 1, 0, 0 | w0, w1, 0, 0], rows=4, cols=8
fn addition_instance(x0: F, w0: F) -> (Statement<E>, Witness<E>) {
    let w1 = w0 + x0;
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one()), (0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 1, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, x0), (1, F::one())]);
    let w = SparseVector::from_entries(4, vec![(0, w0), (1, w1)]);
    (Statement::new(A, B, C, x), Witness::new(w))
}

/// R1CS for two constraints:
///   constraint 0: w0 * w0 = w1   (squaring)
///   constraint 1: w1 * x0 = w2   (scaling)
/// So w2 = w0^2 * x0.
/// z = [x0, 0, 0, 0 | w0, w1, w2, 0], rows=4, cols=8
fn square_then_scale(x0: F, w0: F) -> (Statement<E>, Witness<E>) {
    let w1 = w0 * w0;
    let w2 = w1 * x0;
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one()), (1, 5, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one()), (1, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one()), (1, 6, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, x0)]);
    let w = SparseVector::from_entries(4, vec![(0, w0), (1, w1), (2, w2)]);
    (Statement::new(A, B, C, x), Witness::new(w))
}

// ==============================================================================
// Completeness tests
// ==============================================================================

#[test]
fn delphian_simple_multiplication_accepts() {
    let mut rng = common::test_rng();
    let (stmt, wit) = multiplication_instance(F::from(3), F::from(7));
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

#[test]
fn delphian_multiplication_by_zero_accepts() {
    let mut rng = common::test_rng();
    let (stmt, wit) = multiplication_instance(F::from(5), F::zero());
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

#[test]
fn delphian_multiplication_by_one_accepts() {
    let mut rng = common::test_rng();
    let (stmt, wit) = multiplication_instance(F::from(42), F::one());
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

#[test]
fn delphian_addition_accepts() {
    let mut rng = common::test_rng();
    let (stmt, wit) = addition_instance(F::from(10), F::from(20));
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

#[test]
fn delphian_square_then_scale_accepts() {
    let mut rng = common::test_rng();
    // w0=3, w1=9, x0=5, w2=45
    let (stmt, wit) = square_then_scale(F::from(5), F::from(3));
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

// ==============================================================================
// Soundness tests
// ==============================================================================

#[test]
fn delphian_wrong_witness_rejected() {
    let mut rng = common::test_rng();
    // A picks w0 (col 4), B picks x0 (col 0), C picks w1 (col 5)
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, F::from(3))]);
    // 3 * 7 = 21, but we claim 20
    let w = SparseVector::from_entries(4, vec![(0, F::from(7)), (1, F::from(20))]);
    let stmt = Statement::new(A, B, C, x);
    let wit = Witness::new(w);
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    assert!(delphian::verify(&params, &stmt, proof, &mut trans_v).is_err());
}

#[test]
fn delphian_wrong_addition_rejected() {
    let mut rng = common::test_rng();
    // Addition circuit: (w0 + x0) * 1 = w1, but we give wrong w1
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one()), (0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 1, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, F::from(10)), (1, F::one())]);
    // correct w1 = 10 + 20 = 30, but we claim 31
    let w = SparseVector::from_entries(4, vec![(0, F::from(20)), (1, F::from(31))]);
    let stmt = Statement::new(A, B, C, x);
    let wit = Witness::new(w);
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    assert!(delphian::verify(&params, &stmt, proof, &mut trans_v).is_err());
}

#[test]
fn delphian_deterministic_with_seeded_rng() {
    let (stmt, wit) = multiplication_instance(F::from(11), F::from(13));
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, common::test_rng());

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

#[test]
fn delphian_wrong_constraint_output_rejected() {
    let mut rng = common::test_rng();
    // w0 * w0 = w1, w1 * x0 = w2
    // Correct: w0=3, w1=9, x0=5, w2=45
    // Wrong: w0=3, w1=9, x0=5, w2=46
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one()), (1, 5, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one()), (1, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one()), (1, 6, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, F::from(5))]);
    let w = SparseVector::from_entries(4, vec![(0, F::from(3)), (1, F::from(9)), (2, F::from(46))]);
    let stmt = Statement::new(A, B, C, x);
    let wit = Witness::new(w);
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    assert!(delphian::verify(&params, &stmt, proof, &mut trans_v).is_err());
}

#[test]
fn delphian_all_zero_witness_accepts() {
    let mut rng = common::test_rng();
    // Trivial circuit: 0 * 0 = 0
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 6, F::one())]);
    let x = SparseVector::from_entries(4, vec![]); // all zeros
    let w = SparseVector::from_entries(4, vec![]); // all zeros
    let stmt = Statement::new(A, B, C, x);
    let wit = Witness::new(w);
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans_p = Transcript::new("delphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("delphian");
    delphian::verify(&params, &stmt, proof, &mut trans_v).unwrap();
}

// ==============================================================================
// Transcript divergence tests
// ==============================================================================

#[test]
fn delphian_challenges_diverge_on_different_witnesses() {
    // Same circuit structure, but different witness values
    let (stmt1, wit1) = multiplication_instance(F::from(3), F::from(7));
    let (stmt2, wit2) = multiplication_instance(F::from(5), F::from(11));
    let params = setup_params(wit1.w.size, 2, 3);

    let mut trans1 = Transcript::new("delphian");
    let proof1 = delphian::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let mut trans2 = Transcript::new("delphian");
    let proof2 = delphian::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    // Different witnesses/statements should produce different proofs
    // Check the main sumcheck proof's final commitment differs
    assert_ne!(
        proof1.sc_phase1_proof.comm_final,
        proof2.sc_phase1_proof.comm_final
    );
}

#[test]
fn delphian_challenges_diverge_on_different_public_inputs() {
    // Same witness structure, different public input x
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);

    // x0=3, w0=7, w1=21
    let x1 = SparseVector::from_entries(4, vec![(0, F::from(3))]);
    let w1 = SparseVector::from_entries(4, vec![(0, F::from(7)), (1, F::from(21))]);

    // x0=5, w0=7, w1=35 (same w0, different x0)
    let x2 = SparseVector::from_entries(4, vec![(0, F::from(5))]);
    let w2 = SparseVector::from_entries(4, vec![(0, F::from(7)), (1, F::from(35))]);

    let stmt1 = Statement::new(A.clone(), B.clone(), C.clone(), x1);
    let stmt2 = Statement::new(A, B, C, x2);
    let wit1 = Witness::new(w1);
    let wit2 = Witness::new(w2);
    let params = setup_params(wit1.w.size, 2, 3);

    let mut trans1 = Transcript::new("delphian");
    let proof1 = delphian::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let mut trans2 = Transcript::new("delphian");
    let proof2 = delphian::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    // Different public inputs should produce different proofs
    assert_ne!(
        proof1.sc_phase1_proof.dp_proof.c,
        proof2.sc_phase1_proof.dp_proof.c
    );
}

#[test]
fn delphian_challenges_diverge_on_different_prover_randomness() {
    let mut rng = common::test_rng();
    // Same statement and witness, but different prover randomness
    let (stmt, wit) = multiplication_instance(F::from(3), F::from(7));
    let params = setup_params(wit.w.size, 2, 3);

    let mut trans1 = Transcript::new("delphian");
    let proof1 = delphian::prove(&params, &stmt.clone(), &wit.clone(), &mut trans1, &mut rng);

    let mut trans2 = Transcript::new("delphian");
    let proof2 = delphian::prove(&params, &stmt, &wit, &mut trans2, &mut rng);

    // Different prover randomness should produce different proofs (due to blinding)
    // The quokka commitment will differ
    assert_ne!(proof1.comm_w, proof2.comm_w);
    // And consequently the entire proof transcript diverges
    assert_ne!(
        proof1.sc_phase1_proof.dp_proof.c,
        proof2.sc_phase1_proof.dp_proof.c
    );
}

#[test]
fn delphian_challenges_diverge_on_different_params() {
    // Same statement and witness, but different generator parameters
    let (stmt, wit) = multiplication_instance(F::from(3), F::from(7));

    // Create two different parameter sets
    let sqrt_w = 1usize << (wit.w.size.ilog2() as usize / 2);
    // rows=4 -> log_rows=2, cols=8 -> log_cols=3
    let main_sc_num = 2 * 4; // log_rows * (max_degree+1)
    let mv_sc_num = 3 * 3; // log_cols * (max_degree+1)

    // Params1: use seeds starting at 0
    let quokka_gens1: Vec<E> = (0..sqrt_w)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let main_sc_gens1: Vec<E> = (sqrt_w..sqrt_w + main_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let mv_sc_gens1: Vec<E> = (sqrt_w + main_sc_num..sqrt_w + main_sc_num + mv_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let params1 = PublicParams::new(
        quokka_gens1,
        main_sc_gens1,
        mv_sc_gens1,
        [
            E::get_generator_from_seed(10001u64),
            E::get_generator_from_seed(10000u64),
        ],
    );

    // Params2: use seeds starting at 1000
    let base = 1000;
    let quokka_gens2: Vec<E> = (base..base + sqrt_w)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let main_sc_gens2: Vec<E> = (base + sqrt_w..base + sqrt_w + main_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let mv_sc_gens2: Vec<E> = (base + sqrt_w + main_sc_num
        ..base + sqrt_w + main_sc_num + mv_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let params2 = PublicParams::new(
        quokka_gens2,
        main_sc_gens2,
        mv_sc_gens2,
        [
            E::get_generator_from_seed(20001u64),
            E::get_generator_from_seed(20000u64),
        ],
    );

    let mut trans1 = Transcript::new("delphian");
    let proof1 = delphian::prove(
        &params1,
        &stmt.clone(),
        &wit.clone(),
        &mut trans1,
        common::test_rng(),
    );

    let mut trans2 = Transcript::new("delphian");
    let proof2 = delphian::prove(&params2, &stmt, &wit, &mut trans2, common::test_rng());

    // Different params should produce different proofs
    assert_ne!(
        proof1.sc_phase1_proof.dp_proof.c,
        proof2.sc_phase1_proof.dp_proof.c
    );
}
