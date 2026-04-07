#![allow(non_snake_case)]

mod common;

use common::F;
use num_traits::{One, Zero};
use p4::{
    Circuit, ConstraintInterpreter, Lc, ProverMatrixifier, Result, VerifierMatrixifier, Visibility,
};
struct R1csInstance {
    a: p2::sparsemat::SparseMatrix<F>,
    b: p2::sparsemat::SparseMatrix<F>,
    c: p2::sparsemat::SparseMatrix<F>,
    z: Vec<F>,
    n_pub: usize,
}

impl R1csInstance {
    fn from_prover(m: ProverMatrixifier<F>) -> Self {
        let (([a, b, c], stmt_vec), witness) = m.into_statement_and_witness();
        let n_pub = stmt_vec.size;
        let mut z = vec![F::zero(); a.cols];
        for (i, &v) in stmt_vec.iter() {
            z[i] = v;
        }
        for (i, &v) in witness.iter() {
            z[n_pub + i] = v;
        }
        Self { a, b, c, z, n_pub }
    }

    fn n_constraints(&self) -> usize {
        self.a.rows
    }

    fn is_satisfied(&self) -> bool {
        self.is_satisfied_with(&self.z)
    }

    fn is_satisfied_with(&self, z: &[F]) -> bool {
        for row in 0..self.a.rows {
            let az: F = self.a.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
            let bz: F = self.b.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
            let cz: F = self.c.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
            if az * bz != cz {
                return false;
            }
        }
        true
    }

    fn satisfied_with_private_set_to(&self, priv_idx: usize, val: F) -> bool {
        let mut z = self.z.clone();
        z[self.n_pub + priv_idx] = val;
        self.is_satisfied_with(&z)
    }
}
#[test]
fn alloc_public_returns_public_variable() {
    let mut m = ProverMatrixifier::<F>::new();
    let v = m.alloc(|| "x", Visibility::Public, || Some(F::from(42))).unwrap();
    assert_eq!(v.visibility(), Visibility::Public);
    // Index 0 is reserved for Variable::one(), so first user public var is index 1
    assert_eq!(v.get_index(), 1);
}

#[test]
fn alloc_private_returns_private_variable() {
    let mut m = ProverMatrixifier::<F>::new();
    let v = m.alloc(|| "w", Visibility::Private, || Some(F::from(7))).unwrap();
    assert_eq!(v.visibility(), Visibility::Private);
    assert_eq!(v.get_index(), 0);
}

#[test]
fn alloc_increments_indices_separately() {
    let mut m = ProverMatrixifier::<F>::new();
    let pub0 = m.alloc(|| "x0", Visibility::Public, || Some(F::from(1))).unwrap();
    let priv0 = m.alloc(|| "w0", Visibility::Private, || Some(F::from(2))).unwrap();
    let pub1 = m.alloc(|| "x1", Visibility::Public, || Some(F::from(3))).unwrap();
    let priv1 = m.alloc(|| "w1", Visibility::Private, || Some(F::from(4))).unwrap();

    assert_eq!(pub0.get_index(), 1);
    assert_eq!(pub1.get_index(), 2);
    assert_eq!(priv0.get_index(), 0);
    assert_eq!(priv1.get_index(), 1);
}

#[test]
fn alloc_prover_stores_assignments_at_correct_indices() {
    let mut m = ProverMatrixifier::<F>::new();
    let w0 = m.alloc(|| "w0", Visibility::Private, || Some(F::from(42))).unwrap();
    let w1 = m.alloc(|| "w1", Visibility::Private, || Some(F::from(99))).unwrap();
    let x0 = m.alloc(|| "x0", Visibility::Public, || Some(F::from(7))).unwrap();
    // Enforce a dummy constraint so we get a row
    m.enforce(|| "dummy", Lc::from(w0), Lc::from(F::one()), Lc::from(w0));

    let inst = R1csInstance::from_prover(m);
    // Public: index 0 = one (1), index 1 = x0 (7)
    assert_eq!(inst.z[0], F::one());
    assert_eq!(inst.z[x0.get_index()], F::from(7));
    // Private: offset by n_pub=2, so w0 at z[2], w1 at z[3]
    assert_eq!(inst.z[inst.n_pub + w0.get_index()], F::from(42));
    assert_eq!(inst.z[inst.n_pub + w1.get_index()], F::from(99));
}

#[test]
fn alloc_verifier_skips_private_assignments() {
    let mut m = VerifierMatrixifier::<F>::new();
    let v = m.alloc(|| "w", Visibility::Private, || None::<F>).unwrap();
    assert_eq!(v.visibility(), Visibility::Private);
}

#[test]
fn alloc_verifier_requires_public_assignments() {
    let mut m = VerifierMatrixifier::<F>::new();
    let result = m.alloc(|| "x", Visibility::Public, || None::<F>);
    assert!(result.is_err());
}

#[test]
fn alloc_prover_requires_all_assignments() {
    let mut m = ProverMatrixifier::<F>::new();
    let result = m.alloc(|| "w", Visibility::Private, || None::<F>);
    assert!(result.is_err());
}
#[test]
fn enforce_records_constraint_in_correct_matrices() {
    // Constraint: w * x = p. Verify each matrix selects the right variable.
    let mut m = ProverMatrixifier::<F>::new();
    let x_val = F::from(3);
    let w_val = F::from(7);
    let p_val = x_val * w_val;
    let x = m.alloc(|| "x", Visibility::Public, || Some(x_val)).unwrap();
    let w = m.alloc(|| "w", Visibility::Private, || Some(w_val)).unwrap();
    let p = m.alloc(|| "p", Visibility::Private, || Some(p_val)).unwrap();
    m.enforce(|| "mul", Lc::from(w), Lc::from(x), Lc::from(p));

    let inst = R1csInstance::from_prover(m);
    assert_eq!(inst.n_constraints(), 1);
    assert!(inst.is_satisfied());
    // Changing w should break the constraint
    assert!(!inst.satisfied_with_private_set_to(w.get_index(), F::from(999)));
    // Changing p (the product) should break it
    assert!(!inst.satisfied_with_private_set_to(p.get_index(), F::from(999)));
}

#[test]
fn enforce_multiple_constraints_independently_verified() {
    // Two constraints: w0 * w0 = w1, w1 * x = w2
    let mut m = ProverMatrixifier::<F>::new();
    let x_val = F::from(5);
    let w0_val = F::from(3);
    let w1_val = w0_val * w0_val; // 9
    let w2_val = w1_val * x_val; // 45

    let x = m.alloc(|| "x", Visibility::Public, || Some(x_val)).unwrap();
    let w0 = m.alloc(|| "w0", Visibility::Private, || Some(w0_val)).unwrap();
    let w1 = m.alloc(|| "w1", Visibility::Private, || Some(w1_val)).unwrap();
    let w2 = m.alloc(|| "w2", Visibility::Private, || Some(w2_val)).unwrap();
    m.enforce(|| "square", Lc::from(w0), Lc::from(w0), Lc::from(w1));
    m.enforce(|| "scale", Lc::from(w1), Lc::from(x), Lc::from(w2));

    let inst = R1csInstance::from_prover(m);
    assert_eq!(inst.n_constraints(), 2);
    assert!(inst.is_satisfied());
    // Breaking w1 should violate at least one constraint
    assert!(!inst.satisfied_with_private_set_to(w1.get_index(), F::from(0)));
    // Breaking w2 should violate the second constraint
    assert!(!inst.satisfied_with_private_set_to(w2.get_index(), F::from(0)));
}

#[test]
fn into_statement_correct_dimensions() {
    let mut m = ProverMatrixifier::<F>::new();
    let x = m.alloc(|| "x", Visibility::Public, || Some(F::from(3))).unwrap();
    let w = m.alloc(|| "w", Visibility::Private, || Some(F::from(7))).unwrap();
    let prod = m.alloc(|| "p", Visibility::Private, || Some(F::from(21))).unwrap();
    m.enforce(|| "mul", Lc::from(w), Lc::from(x), Lc::from(prod));

    let inst = R1csInstance::from_prover(m);
    // 2 public vars (one + x), 2 private vars (w, prod), total cols = 4
    assert_eq!(inst.a.cols, 4);
    assert_eq!(inst.n_constraints(), 1);
    assert_eq!(inst.n_pub, 2);
}

#[test]
fn into_statement_column_layout_public_then_private() {
    // Verify the exact column mapping: public cols [0..n_pub), private cols [n_pub..)
    let mut m = ProverMatrixifier::<F>::new();
    let x = m.alloc(|| "x", Visibility::Public, || Some(F::from(5))).unwrap();
    let w = m.alloc(|| "w", Visibility::Private, || Some(F::from(3))).unwrap();
    // Constraint: w * 1 = x  (A=w, B=1, C=x)
    m.enforce(|| "test", Lc::from(w), Lc::from(F::one()), Lc::from(x));

    let inst = R1csInstance::from_prover(m);
    // n_pub = 2 (one, x). w is private index 0, so column = 2.
    // A matrix row 0 should have entry at column 2 (w) with coefficient 1.
    let a_entries: Vec<_> = inst.a.iter().map(|((r, c), &v)| (r, c, v)).collect();
    assert!(
        a_entries.iter().any(|&(r, c, v)| r == 0 && c == 2 && v == F::one()),
        "A[0] should select private var w at column 2 with coefficient 1, got {:?}",
        a_entries
    );
    // C matrix row 0 should have entry at column 1 (x) with coefficient 1.
    let c_entries: Vec<_> = inst.c.iter().map(|((r, c), &v)| (r, c, v)).collect();
    assert!(
        c_entries.iter().any(|&(r, c, v)| r == 0 && c == 1 && v == F::one()),
        "C[0] should select public var x at column 1 with coefficient 1, got {:?}",
        c_entries
    );
}

#[test]
fn into_statement_public_vector_contains_one() {
    let m = ProverMatrixifier::<F>::new();
    let ((_, stmt_vec), _) = m.into_statement_and_witness();
    assert_eq!(stmt_vec.size, 1); // only Variable::one()
    let one_val: Vec<_> = stmt_vec.iter().filter(|(i, _)| *i == 0).collect();
    assert_eq!(one_val.len(), 1);
    assert_eq!(*one_val[0].1, F::one());
}

#[test]
fn into_statement_and_witness_satisfies_r1cs() {
    let mut m = ProverMatrixifier::<F>::new();
    let x_val = F::from(3);
    let w_val = F::from(7);
    let p_val = x_val * w_val;
    let x = m.alloc(|| "x", Visibility::Public, || Some(x_val)).unwrap();
    let w = m.alloc(|| "w", Visibility::Private, || Some(w_val)).unwrap();
    let p = m.alloc(|| "p", Visibility::Private, || Some(p_val)).unwrap();
    m.enforce(|| "mul", Lc::from(w), Lc::from(x), Lc::from(p));

    let inst = R1csInstance::from_prover(m);
    assert!(inst.n_constraints() > 0);
    assert!(inst.is_satisfied());
    // Wrong product must fail
    assert!(!inst.satisfied_with_private_set_to(p.get_index(), F::from(20)));
}

#[test]
fn into_statement_and_witness_linear_combination_constraint() {
    // Constraint with a non-trivial LC: (2*w + x) * 1 = p
    let mut m = ProverMatrixifier::<F>::new();
    let x_val = F::from(3);
    let w_val = F::from(7);
    let p_val = F::from(2) * w_val + x_val; // 17

    let x = m.alloc(|| "x", Visibility::Public, || Some(x_val)).unwrap();
    let w = m.alloc(|| "w", Visibility::Private, || Some(w_val)).unwrap();
    let p = m.alloc(|| "p", Visibility::Private, || Some(p_val)).unwrap();
    let a_lc = Lc::from((F::from(2), w)) + x;
    m.enforce(|| "lc", a_lc, Lc::from(F::one()), Lc::from(p));

    let inst = R1csInstance::from_prover(m);
    assert!(inst.n_constraints() > 0);
    assert!(inst.is_satisfied());
    assert!(!inst.satisfied_with_private_set_to(p.get_index(), F::from(0)));
}

struct SquareCircuit {
    w: Option<F>,
    x: Option<F>,
}

impl Circuit<F> for SquareCircuit {
    fn synthesize<I: ConstraintInterpreter<F>>(self, cs: &mut I) -> Result<()> {
        let w = cs.alloc(|| "w", Visibility::Private, || self.w)?;
        let x = cs.alloc(|| "x", Visibility::Public, || self.x)?;
        cs.enforce(|| "w*w=x", Lc::from(w), Lc::from(w), Lc::from(x));
        Ok(())
    }
}

#[test]
fn circuit_synthesize_satisfying_and_sound() {
    let mut m = ProverMatrixifier::<F>::new();
    SquareCircuit { w: Some(F::from(4)), x: Some(F::from(16)) }
        .synthesize(&mut m)
        .unwrap();

    let inst = R1csInstance::from_prover(m);
    assert!(inst.n_constraints() > 0);
    assert!(inst.is_satisfied());
    // w=5 with x=16 should not satisfy (5^2=25≠16)
    assert!(!inst.satisfied_with_private_set_to(0, F::from(5)));
}

#[test]
fn circuit_synthesize_unsatisfying_detected() {
    // w=4, x=15 (wrong: 4^2 != 15)
    let mut m = ProverMatrixifier::<F>::new();
    SquareCircuit { w: Some(F::from(4)), x: Some(F::from(15)) }
        .synthesize(&mut m)
        .unwrap();

    let inst = R1csInstance::from_prover(m);
    assert!(inst.n_constraints() > 0);
    assert!(!inst.is_satisfied(), "Bad witness should not satisfy R1CS");
}
