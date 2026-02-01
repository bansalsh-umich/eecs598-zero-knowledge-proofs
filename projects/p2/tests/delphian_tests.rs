#![allow(non_snake_case)]

mod common;

use comms::show_transcript;
use common::F;
use p1::curve::P256Point;
use p1::{One, Zero};
use p2::delphian::{Protocol, Statement, Witness};
use p2::sparsemat::{SparseMatrix, SparseVector};

type E = P256Point;

/// Simple R1CS: one constraint w0 * x0 = w1
/// z = [x0, 0, 0, 0 | w0, w1, 0, 0], rows=4, cols=8
/// (Using 4-element vectors so quokka has even number of variables)
fn multiplication_instance(a: F, b: F) -> (Statement<E>, Witness<E>) {
    let c = a * b;
    // A picks w0 (col 4), B picks x0 (col 0), C picks w1 (col 5)
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, a)]);
    let w = SparseVector::from_entries(4, vec![(0, b), (1, c)]);
    (Statement::<E>::new(A, B, C, x), Witness::<E>::new(w))
}

/// R1CS for: w0 + x0 = w1 (encoded as (w0 + x0) * 1 = w1)
/// A selects z[4]+z[0], B selects constant 1 via z[1]=1, C selects z[5]
/// z = [x0, 1, 0, 0 | w0, w1, 0, 0], rows=4, cols=8
/// (Using 4-element vectors so quokka has even number of variables)
fn addition_instance(x0: F, w0: F) -> (Statement<E>, Witness<E>) {
    let w1 = w0 + x0;
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one()), (0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 1, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, x0), (1, F::one())]);
    let w = SparseVector::from_entries(4, vec![(0, w0), (1, w1)]);
    (Statement::<E>::new(A, B, C, x), Witness::<E>::new(w))
}

/// R1CS for two constraints:
///   constraint 0: w0 * w0 = w1   (squaring)
///   constraint 1: w1 * x0 = w2   (scaling)
/// So w2 = w0^2 * x0.
/// z = [x0, 0, 0, 0 | w0, w1, w2, 0], rows=4, cols=8
fn square_then_scale(x0: F, w0: F) -> (Statement<E>, Witness<E>) {
    let w1 = w0 * w0;
    let w2 = w1 * x0;
    // A: row0 picks w0 (col 4), row1 picks w1 (col 5)
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one()), (1, 5, F::one())]);
    // B: row0 picks w0 (col 4), row1 picks x0 (col 0)
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one()), (1, 0, F::one())]);
    // C: row0 picks w1 (col 5), row1 picks w2 (col 6)
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one()), (1, 6, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, x0)]);
    let w = SparseVector::from_entries(4, vec![(0, w0), (1, w1), (2, w2)]);
    (Statement::<E>::new(A, B, C, x), Witness::<E>::new(w))
}

// ---- Unit tests ----

#[test]
fn delphian_simple_multiplication_accepts() {
    let _guard = show_transcript();
    let (stmt, wit) = multiplication_instance(F::from(3), F::from(7));
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_mul", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn delphian_multiplication_by_zero_accepts() {
    let _guard = show_transcript();
    let (stmt, wit) = multiplication_instance(F::from(5), F::zero());
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_zero", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn delphian_multiplication_by_one_accepts() {
    let _guard = show_transcript();
    let (stmt, wit) = multiplication_instance(F::from(42), F::one());
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_one", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn delphian_addition_accepts() {
    let _guard = show_transcript();
    let (stmt, wit) = addition_instance(F::from(10), F::from(20));
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_add", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn delphian_square_then_scale_accepts() {
    let _guard = show_transcript();
    // w0=3, w1=9, x0=5, w2=45
    let (stmt, wit) = square_then_scale(F::from(5), F::from(3));
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_sq_scale", stmt, wit);
    p.unwrap();
    v.unwrap();
}

#[test]
fn delphian_wrong_witness_rejected() {
    let _guard = show_transcript();
    // A picks w0 (col 4), B picks x0 (col 0), C picks w1 (col 5)
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, F::from(3))]);
    // 3 * 7 = 21, but we claim 20
    let w = SparseVector::from_entries(4, vec![(0, F::from(7)), (1, F::from(20))]);
    let stmt = Statement::<E>::new(A, B, C, x);
    let wit = Witness::<E>::new(w);
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_bad", stmt, wit);
    assert!(p.is_err() || v.is_err());
}

#[test]
fn delphian_wrong_addition_rejected() {
    let _guard = show_transcript();
    // Addition circuit: (w0 + x0) * 1 = w1, but we give wrong w1
    // A selects z[4]+z[0], B selects z[1]=1, C selects z[5]
    let A = SparseMatrix::from_entries(4, 8, vec![(0, 0, F::one()), (0, 4, F::one())]);
    let B = SparseMatrix::from_entries(4, 8, vec![(0, 1, F::one())]);
    let C = SparseMatrix::from_entries(4, 8, vec![(0, 5, F::one())]);
    let x = SparseVector::from_entries(4, vec![(0, F::from(10)), (1, F::one())]);
    // correct w1 = 10 + 20 = 30, but we claim 31
    let w = SparseVector::from_entries(4, vec![(0, F::from(20)), (1, F::from(31))]);
    let stmt = Statement::<E>::new(A, B, C, x);
    let wit = Witness::<E>::new(w);
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_bad_add", stmt, wit);
    assert!(p.is_err() || v.is_err());
}

#[test]
fn delphian_deterministic_with_seeded_rng() {
    let _guard = show_transcript();
    let (stmt, wit) = multiplication_instance(F::from(11), F::from(13));
    let (p, v) = common::run_protocol::<Protocol<E>>("delphian_det", stmt, wit);
    p.unwrap();
    v.unwrap();
}
