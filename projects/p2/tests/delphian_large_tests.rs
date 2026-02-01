#![allow(non_snake_case, dead_code, unused_imports)]

mod common;

use comms::show_transcript;
use common::F;
use p1::curve::P256Point;
use p1::{One, Zero};
use p2::delphian::{Protocol, Statement, Witness};
use p2::sparsemat::{SparseMatrix, SparseVector};
use proptest::prelude::*;

type E = P256Point;

const NUM_CONSTRAINTS: usize = 1024;
const WIT_SIZE: usize = 64; // must be 2^(even) for quokka commit
const NUM_COLS: usize = WIT_SIZE * 2;
/// Number of nonzero terms per row in A and B matrices.
const FAN_IN: usize = 32;

/// A single constraint: (sum of a_terms) * (sum of b_terms) = z[out_col]
/// Each row of A has FAN_IN nonzeros, each row of B has FAN_IN nonzeros,
/// each row of C has 1 nonzero.
#[derive(Debug, Clone)]
struct Constraint {
    a_terms: Vec<(usize, F)>,
    b_terms: Vec<(usize, F)>,
    out_col: usize,
}

/// Strategy for generating independent constraints with FAN_IN terms per row.
///
/// The circuit has NUM_CONSTRAINTS rows but only WIT_SIZE witness variables.
/// Constraints are grouped by (i % WIT_SIZE) - all constraints in a group
/// use the same coefficients and output to the same witness slot.
/// Each constraint only uses public inputs (x), not witness values.
fn arb_gadget_circuit() -> BoxedStrategy<(
    Vec<Constraint>,
    Vec<F>, // x_vals (public input, length WIT_SIZE)
    Vec<F>, // w_vals (witness, length WIT_SIZE)
)> {
    // Coefficients: each unique constraint template needs FAN_IN*2 coefficients
    let num_coeffs = WIT_SIZE * FAN_IN * 2;
    (
        proptest::collection::vec(common::arb_zq(), num_coeffs),
        proptest::collection::vec(common::arb_zq(), WIT_SIZE),
    )
        .prop_map(|(coeffs, x_vals)| {
            let mut constraints = Vec::with_capacity(NUM_CONSTRAINTS);
            let mut w_vals = vec![F::zero(); WIT_SIZE];

            // z = [x | w], x occupies columns 0..WIT_SIZE, w occupies WIT_SIZE..NUM_COLS
            // w_vals[j] corresponds to column WIT_SIZE + j in z.

            // Helper: evaluate a linear combination over x values only
            let eval_lc_x = |terms: &[(usize, F)], x: &[F]| -> F {
                terms.iter().map(|&(col, coeff)| coeff * x[col]).sum()
            };

            // First, compute w_vals from template constraints (one per witness slot)
            for (j, w_val) in w_vals.iter_mut().enumerate() {
                let base = j * FAN_IN * 2;
                // A side: FAN_IN terms from x, spread across columns
                let a_terms: Vec<_> = (0..FAN_IN)
                    .map(|k| ((j + k) % WIT_SIZE, coeffs[base + k]))
                    .collect();
                // B side: FAN_IN terms from x, different spread
                let b_terms: Vec<_> = (0..FAN_IN)
                    .map(|k| ((j + FAN_IN + k) % WIT_SIZE, coeffs[base + FAN_IN + k]))
                    .collect();

                let a_val = eval_lc_x(&a_terms, &x_vals);
                let b_val = eval_lc_x(&b_terms, &x_vals);
                *w_val = a_val * b_val;
            }

            // Now generate all NUM_CONSTRAINTS constraints
            // Constraint i uses the same template as constraint (i % WIT_SIZE)
            for i in 0..NUM_CONSTRAINTS {
                let j = i % WIT_SIZE;
                let base = j * FAN_IN * 2;

                let a_terms: Vec<_> = (0..FAN_IN)
                    .map(|k| ((j + k) % WIT_SIZE, coeffs[base + k]))
                    .collect();
                let b_terms: Vec<_> = (0..FAN_IN)
                    .map(|k| ((j + FAN_IN + k) % WIT_SIZE, coeffs[base + FAN_IN + k]))
                    .collect();

                constraints.push(Constraint {
                    a_terms,
                    b_terms,
                    out_col: WIT_SIZE + j,
                });
            }

            (constraints, x_vals, w_vals)
        })
        .boxed()
}

/// Build the A, B, C matrices and x, w vectors from constraints.
fn build_r1cs(
    constraints: &[Constraint],
    x_vals: &[F],
    w_vals: &[F],
) -> (Statement<E>, Witness<E>) {
    let rows = NUM_CONSTRAINTS;
    let cols = NUM_COLS;

    let mut a_entries = Vec::new();
    let mut b_entries = Vec::new();
    let mut c_entries = Vec::new();

    for (row, c) in constraints.iter().enumerate() {
        for &(col, coeff) in &c.a_terms {
            a_entries.push((row, col, coeff));
        }
        for &(col, coeff) in &c.b_terms {
            b_entries.push((row, col, coeff));
        }
        c_entries.push((row, c.out_col, F::one()));
    }

    let A = SparseMatrix::from_entries(rows, cols, a_entries);
    let B = SparseMatrix::from_entries(rows, cols, b_entries);
    let C = SparseMatrix::from_entries(rows, cols, c_entries);

    let x = SparseVector::from_dense(x_vals);
    let w = SparseVector::from_dense(w_vals);

    (Statement::<E>::new(A, B, C, x), Witness::<E>::new(w))
}

#[cfg(debug_assertions)]
mod release_guard {
    #[test]
    fn delphian_random_large_instance() {
        panic!(
            "this test may be very slow unless run in release mode; add --release to your cargo command"
        );
    }

    #[test]
    fn delphian_perturbed_instance_rejected() {
        panic!(
            "this test may be very slow unless run in release mode; add --release to your cargo command"
        );
    }
}

#[cfg(not(debug_assertions))]
proptest! {
    #![proptest_config(ProptestConfig::with_cases(2))]

    #[test]
    fn delphian_random_large_instance(
        (constraints, x_vals, w_vals) in arb_gadget_circuit(),
    ) {
        let _guard = show_transcript();
        let (stmt, wit) = build_r1cs(&constraints, &x_vals, &w_vals);
        let total = NUM_CONSTRAINTS * NUM_COLS;
        println!(
            "A nnz: {}/{} ({:.1}%), B nnz: {}/{} ({:.1}%), C nnz: {}/{} ({:.1}%)",
            stmt.A.nnz(), total, 100.0 * stmt.A.nnz() as f64 / total as f64,
            stmt.B.nnz(), total, 100.0 * stmt.B.nnz() as f64 / total as f64,
            stmt.C.nnz(), total, 100.0 * stmt.C.nnz() as f64 / total as f64,
        );
        let start = std::time::Instant::now();
        let (p, v) = common::run_protocol::<Protocol<E>>("delphian_large", stmt, wit);
        println!("protocol execution: {:?}", start.elapsed());
        prop_assert!(p.is_ok(), "prover failed: {:?}", p.unwrap_err());
        prop_assert!(v.is_ok(), "verifier failed: {:?}", v.unwrap_err());
    }

    #[test]
    fn delphian_perturbed_instance_rejected(
        (constraints, x_vals, w_vals) in arb_gadget_circuit(),
        perturb_idx in 0..WIT_SIZE,
    ) {
        let _guard = show_transcript();
        // Perturb one witness value to break the R1CS constraint at that row.
        let mut w_vals_bad = w_vals.clone();
        w_vals_bad[perturb_idx] += F::one();

        let (stmt, wit) = build_r1cs(&constraints, &x_vals, &w_vals_bad);
        let (p, v) = common::run_protocol::<Protocol<E>>("delphian_perturbed", stmt, wit);
        prop_assert!(p.is_err() || v.is_err(), "expected rejection for perturbed witness");
    }
}
