mod common;

use common::{E, F};
use p1::Random;
use p2::ec::EllipticCurve;
use p3::pedersen::{self, commit, vector_commit};
use p3::transcript::Transcript;
use proptest::prelude::*;

fn generators() -> [E; 2] {
    [
        E::get_generator_from_seed(0u64),
        E::get_generator_from_seed(1u64),
    ]
}

// ==============================================================================
// open protocol tests
// ==============================================================================

#[test]
fn open_completeness_basic() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let r = F::random(&mut rng);
    let commitment = commit(x, r, &[g, h]);

    let params = pedersen::open::PublicParams { generators: [g, h] };
    let statement = pedersen::open::Statement { commitment };
    let witness = pedersen::open::Witness { x, r };

    let mut trans_p = Transcript::new("open");
    let proof = pedersen::open::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("open");
    pedersen::open::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn open_soundness_wrong_value() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let r = F::random(&mut rng);
    let commitment = commit(x, r, &[g, h]);

    let params = pedersen::open::PublicParams { generators: [g, h] };
    let statement = pedersen::open::Statement { commitment };
    // Wrong witness: use x+1 instead of x
    let witness = pedersen::open::Witness {
        x: x + F::from(1),
        r,
    };

    let mut trans_p = Transcript::new("open");
    let proof = pedersen::open::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("open");
    assert!(pedersen::open::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

#[test]
fn open_soundness_wrong_randomness() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let r = F::random(&mut rng);
    let commitment = commit(x, r, &[g, h]);

    let params = pedersen::open::PublicParams { generators: [g, h] };
    let statement = pedersen::open::Statement { commitment };
    // Wrong witness: use r+1 instead of r
    let witness = pedersen::open::Witness {
        x,
        r: r + F::from(1),
    };

    let mut trans_p = Transcript::new("open");
    let proof = pedersen::open::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("open");
    assert!(pedersen::open::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

// ==============================================================================
// equals protocol tests
// ==============================================================================

#[test]
fn equals_completeness_basic() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let r1 = F::random(&mut rng);
    let r2 = F::random(&mut rng);
    let comm1 = commit(x, r1, &[g, h]);
    let comm2 = commit(x, r2, &[g, h]);

    let params = pedersen::equals::PublicParams { generators: [g, h] };
    let statement = pedersen::equals::Statement { comm1, comm2 };
    let witness = pedersen::equals::Witness { x, r1, r2 };

    let mut trans_p = Transcript::new("equals");
    let proof = pedersen::equals::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("equals");
    pedersen::equals::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn equals_completeness_same_randomness() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let r = F::random(&mut rng);
    let comm1 = commit(x, r, &[g, h]);
    let comm2 = commit(x, r, &[g, h]);

    let params = pedersen::equals::PublicParams { generators: [g, h] };
    let statement = pedersen::equals::Statement { comm1, comm2 };
    let witness = pedersen::equals::Witness { x, r1: r, r2: r };

    let mut trans_p = Transcript::new("equals");
    let proof = pedersen::equals::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("equals");
    pedersen::equals::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn equals_soundness_different_values() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x1 = F::random(&mut rng);
    let x2 = F::random(&mut rng);
    let r1 = F::random(&mut rng);
    let r2 = F::random(&mut rng);
    let comm1 = commit(x1, r1, &[g, h]);
    let comm2 = commit(x2, r2, &[g, h]);

    let params = pedersen::equals::PublicParams { generators: [g, h] };
    let statement = pedersen::equals::Statement { comm1, comm2 };
    // Use x1 for both, but the commitments are to different values
    let witness = pedersen::equals::Witness { x: x1, r1, r2 };

    let mut trans_p = Transcript::new("equals");
    let proof = pedersen::equals::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("equals");
    assert!(pedersen::equals::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

#[test]
fn equals_soundness_wrong_witness_value() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let r1 = F::random(&mut rng);
    let r2 = F::random(&mut rng);
    let comm1 = commit(x, r1, &[g, h]);
    let comm2 = commit(x, r2, &[g, h]);

    let params = pedersen::equals::PublicParams { generators: [g, h] };
    let statement = pedersen::equals::Statement { comm1, comm2 };
    // Wrong witness: use x+1 instead of x
    let witness = pedersen::equals::Witness {
        x: x + F::from(1),
        r1,
        r2,
    };

    let mut trans_p = Transcript::new("equals");
    let proof = pedersen::equals::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("equals");
    assert!(pedersen::equals::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

// ==============================================================================
// product protocol tests
// ==============================================================================

#[test]
fn product_completeness_basic() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let y = F::random(&mut rng);
    let z = x * y;
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);
    let comm_x = commit(x, rx, &[g, h]);
    let comm_y = commit(y, ry, &[g, h]);
    let comm_z = commit(z, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };
    let statement = pedersen::product::Statement {
        comm_x,
        comm_y,
        comm_z,
    };
    let witness = pedersen::product::Witness {
        x,
        y,
        z,
        rx,
        ry,
        rz,
    };

    let mut trans_p = Transcript::new("product");
    let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("product");
    pedersen::product::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn product_completeness_zero_factor() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::from(0);
    let y = F::random(&mut rng);
    let z = x * y; // z = 0
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);
    let comm_x = commit(x, rx, &[g, h]);
    let comm_y = commit(y, ry, &[g, h]);
    let comm_z = commit(z, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };
    let statement = pedersen::product::Statement {
        comm_x,
        comm_y,
        comm_z,
    };
    let witness = pedersen::product::Witness {
        x,
        y,
        z,
        rx,
        ry,
        rz,
    };

    let mut trans_p = Transcript::new("product");
    let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("product");
    pedersen::product::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn product_completeness_one_factor() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::from(1);
    let y = F::random(&mut rng);
    let z = x * y; // z = y
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);
    let comm_x = commit(x, rx, &[g, h]);
    let comm_y = commit(y, ry, &[g, h]);
    let comm_z = commit(z, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };
    let statement = pedersen::product::Statement {
        comm_x,
        comm_y,
        comm_z,
    };
    let witness = pedersen::product::Witness {
        x,
        y,
        z,
        rx,
        ry,
        rz,
    };

    let mut trans_p = Transcript::new("product");
    let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("product");
    pedersen::product::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn product_soundness_wrong_product() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let y = F::random(&mut rng);
    let z_wrong = x * y + F::from(1); // z != x*y
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);
    let comm_x = commit(x, rx, &[g, h]);
    let comm_y = commit(y, ry, &[g, h]);
    let comm_z = commit(z_wrong, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };
    let statement = pedersen::product::Statement {
        comm_x,
        comm_y,
        comm_z,
    };
    let witness = pedersen::product::Witness {
        x,
        y,
        z: z_wrong,
        rx,
        ry,
        rz,
    };

    let mut trans_p = Transcript::new("product");
    let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("product");
    assert!(pedersen::product::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

#[test]
fn product_soundness_mismatched_witness() {
    let [g, h] = generators();
    let mut rng = common::test_rng();
    let x = F::random(&mut rng);
    let y = F::random(&mut rng);
    let z = x * y;
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);
    let comm_x = commit(x, rx, &[g, h]);
    let comm_y = commit(y, ry, &[g, h]);
    let comm_z = commit(z, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };
    let statement = pedersen::product::Statement {
        comm_x,
        comm_y,
        comm_z,
    };
    // Wrong witness: use wrong x value
    let witness = pedersen::product::Witness {
        x: x + F::from(1),
        y,
        z,
        rx,
        ry,
        rz,
    };

    let mut trans_p = Transcript::new("product");
    let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("product");
    assert!(pedersen::product::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

// ==============================================================================
// dot_product protocol tests
// ==============================================================================

fn setup_dot_product_params(n: usize) -> pedersen::dot_product::PublicParams<E> {
    let vec_gens = E::get_generators(n);
    let h = E::get_generator_from_seed(100u64);
    let g = E::get_generator_from_seed(101u64);
    pedersen::dot_product::PublicParams {
        vec_gens,
        scalar_gens: [g, h],
    }
}

fn inner_product(a: &[F], b: &[F]) -> F {
    a.iter().zip(b.iter()).map(|(&ai, &bi)| ai * bi).sum()
}

#[test]
fn dot_product_completeness_basic() {
    let n = 4;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let result = inner_product(&a, &x);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
    let comm_result = commit(result, r_result, &params.scalar_gens);

    let statement = pedersen::dot_product::Statement {
        a: a.clone(),
        comm_x,
        comm_result,
    };
    let witness = pedersen::dot_product::Witness {
        x,
        r_x,
        result,
        r_result,
    };

    let mut trans_p = Transcript::new("dot_product");
    let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("dot_product");
    pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn dot_product_completeness_zero_vector() {
    let n = 4;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = vec![F::from(0); n];
    let result = F::from(0);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
    let comm_result = commit(result, r_result, &params.scalar_gens);

    let statement = pedersen::dot_product::Statement {
        a,
        comm_x,
        comm_result,
    };
    let witness = pedersen::dot_product::Witness {
        x,
        r_x,
        result,
        r_result,
    };

    let mut trans_p = Transcript::new("dot_product");
    let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("dot_product");
    pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn dot_product_completeness_large_vector() {
    let n = 16;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let result = inner_product(&a, &x);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
    let comm_result = commit(result, r_result, &params.scalar_gens);

    let statement = pedersen::dot_product::Statement {
        a: a.clone(),
        comm_x,
        comm_result,
    };
    let witness = pedersen::dot_product::Witness {
        x,
        r_x,
        result,
        r_result,
    };

    let mut trans_p = Transcript::new("dot_product");
    let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("dot_product");
    pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).unwrap();
}

#[test]
fn dot_product_soundness_wrong_result() {
    let n = 4;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let wrong_result = inner_product(&a, &x) + F::from(1);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
    let comm_result = commit(wrong_result, r_result, &params.scalar_gens);

    let statement = pedersen::dot_product::Statement {
        a,
        comm_x,
        comm_result,
    };
    let witness = pedersen::dot_product::Witness {
        x,
        r_x,
        result: wrong_result,
        r_result,
    };

    let mut trans_p = Transcript::new("dot_product");
    let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("dot_product");
    assert!(pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

#[test]
fn dot_product_soundness_wrong_vector() {
    let n = 4;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let result = inner_product(&a, &x);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
    let comm_result = commit(result, r_result, &params.scalar_gens);

    let statement = pedersen::dot_product::Statement {
        a,
        comm_x,
        comm_result,
    };
    // Wrong witness: modify x[0]
    let mut x_wrong = x.clone();
    x_wrong[0] += F::from(1);
    let witness = pedersen::dot_product::Witness {
        x: x_wrong,
        r_x,
        result,
        r_result,
    };

    let mut trans_p = Transcript::new("dot_product");
    let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut rng);

    let mut trans_v = Transcript::new("dot_product");
    assert!(pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).is_err());
}

// ==============================================================================
// Transcript divergence tests
// ==============================================================================

#[test]
fn open_challenges_diverge_on_different_statements() {
    let [g, h] = generators();
    let mut rng = common::test_rng();

    let x1 = F::random(&mut rng);
    let x2 = F::random(&mut rng);
    let r = F::random(&mut rng);

    let comm1 = commit(x1, r, &[g, h]);
    let comm2 = commit(x2, r, &[g, h]);

    let params = pedersen::open::PublicParams { generators: [g, h] };

    let stmt1 = pedersen::open::Statement { commitment: comm1 };
    let wit1 = pedersen::open::Witness { x: x1, r };
    let mut trans1 = Transcript::new("open");
    let proof1 = pedersen::open::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let stmt2 = pedersen::open::Statement { commitment: comm2 };
    let wit2 = pedersen::open::Witness { x: x2, r };
    let mut trans2 = Transcript::new("open");
    let proof2 = pedersen::open::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    // Different statements should produce different challenges
    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn open_challenges_diverge_on_different_prover_randomness() {
    let [g, h] = generators();
    let mut rng = common::test_rng();

    let x = F::random(&mut rng);
    let r = F::random(&mut rng);
    let commitment = commit(x, r, &[g, h]);

    let params = pedersen::open::PublicParams { generators: [g, h] };
    let statement = pedersen::open::Statement { commitment };
    let witness = pedersen::open::Witness { x, r };

    let mut trans1 = Transcript::new("open");
    let proof1 = pedersen::open::prove(&params, &statement, &witness, &mut trans1, &mut rng);

    let mut trans2 = Transcript::new("open");
    let proof2 = pedersen::open::prove(&params, &statement, &witness, &mut trans2, &mut rng);

    // Different prover randomness should produce different challenges (due to blinding)
    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn equals_challenges_diverge_on_different_statements() {
    let [g, h] = generators();
    let mut rng = common::test_rng();

    let x = F::random(&mut rng);
    let r1 = F::random(&mut rng);
    let r2 = F::random(&mut rng);
    let r3 = F::random(&mut rng);

    let comm1 = commit(x, r1, &[g, h]);
    let comm2_a = commit(x, r2, &[g, h]);
    let comm2_b = commit(x, r3, &[g, h]);

    let params = pedersen::equals::PublicParams { generators: [g, h] };

    let stmt_a = pedersen::equals::Statement {
        comm1,
        comm2: comm2_a,
    };
    let wit_a = pedersen::equals::Witness { x, r1, r2 };
    let mut trans_a = Transcript::new("equals");
    let proof_a =
        pedersen::equals::prove(&params, &stmt_a, &wit_a, &mut trans_a, common::test_rng());

    let stmt_b = pedersen::equals::Statement {
        comm1,
        comm2: comm2_b,
    };
    let wit_b = pedersen::equals::Witness { x, r1, r2: r3 };
    let mut trans_b = Transcript::new("equals");
    let proof_b =
        pedersen::equals::prove(&params, &stmt_b, &wit_b, &mut trans_b, common::test_rng());

    assert_ne!(proof_a.c, proof_b.c);
}

#[test]
fn equals_challenges_diverge_on_different_prover_randomness() {
    let [g, h] = generators();
    let mut rng = common::test_rng();

    let x = F::random(&mut rng);
    let r1 = F::random(&mut rng);
    let r2 = F::random(&mut rng);
    let comm1 = commit(x, r1, &[g, h]);
    let comm2 = commit(x, r2, &[g, h]);

    let params = pedersen::equals::PublicParams { generators: [g, h] };
    let statement = pedersen::equals::Statement { comm1, comm2 };
    let witness = pedersen::equals::Witness { x, r1, r2 };

    let mut trans1 = Transcript::new("equals");
    let proof1 = pedersen::equals::prove(&params, &statement, &witness, &mut trans1, &mut rng);

    let mut trans2 = Transcript::new("equals");
    let proof2 = pedersen::equals::prove(&params, &statement, &witness, &mut trans2, &mut rng);

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn product_challenges_diverge_on_different_statements() {
    let [g, h] = generators();
    let mut rng = common::test_rng();

    let x = F::random(&mut rng);
    let y1 = F::random(&mut rng);
    let y2 = F::random(&mut rng);
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);

    let comm_x = commit(x, rx, &[g, h]);
    let comm_y1 = commit(y1, ry, &[g, h]);
    let comm_y2 = commit(y2, ry, &[g, h]);
    let comm_z1 = commit(x * y1, rz, &[g, h]);
    let comm_z2 = commit(x * y2, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };

    let stmt1 = pedersen::product::Statement {
        comm_x,
        comm_y: comm_y1,
        comm_z: comm_z1,
    };
    let wit1 = pedersen::product::Witness {
        x,
        y: y1,
        z: x * y1,
        rx,
        ry,
        rz,
    };
    let mut trans1 = Transcript::new("product");
    let proof1 = pedersen::product::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let stmt2 = pedersen::product::Statement {
        comm_x,
        comm_y: comm_y2,
        comm_z: comm_z2,
    };
    let wit2 = pedersen::product::Witness {
        x,
        y: y2,
        z: x * y2,
        rx,
        ry,
        rz,
    };
    let mut trans2 = Transcript::new("product");
    let proof2 = pedersen::product::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn product_challenges_diverge_on_different_prover_randomness() {
    let [g, h] = generators();
    let mut rng = common::test_rng();

    let x = F::random(&mut rng);
    let y = F::random(&mut rng);
    let z = x * y;
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);
    let comm_x = commit(x, rx, &[g, h]);
    let comm_y = commit(y, ry, &[g, h]);
    let comm_z = commit(z, rz, &[g, h]);

    let params = pedersen::product::PublicParams { generators: [g, h] };
    let statement = pedersen::product::Statement {
        comm_x,
        comm_y,
        comm_z,
    };
    let witness = pedersen::product::Witness {
        x,
        y,
        z,
        rx,
        ry,
        rz,
    };

    let mut trans1 = Transcript::new("product");
    let proof1 = pedersen::product::prove(&params, &statement, &witness, &mut trans1, &mut rng);

    let mut trans2 = Transcript::new("product");
    let proof2 = pedersen::product::prove(&params, &statement, &witness, &mut trans2, &mut rng);

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn dot_product_challenges_diverge_on_different_statements() {
    let n = 4;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a1: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let a2: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);

    let result1 = inner_product(&a1, &x);
    let result2 = inner_product(&a2, &x);
    let comm_result1 = commit(result1, r_result, &params.scalar_gens);
    let comm_result2 = commit(result2, r_result, &params.scalar_gens);

    let stmt1 = pedersen::dot_product::Statement {
        a: a1,
        comm_x,
        comm_result: comm_result1,
    };
    let wit1 = pedersen::dot_product::Witness {
        x: x.clone(),
        r_x,
        result: result1,
        r_result,
    };
    let mut trans1 = Transcript::new("dot_product");
    let proof1 =
        pedersen::dot_product::prove(&params, &stmt1, &wit1, &mut trans1, common::test_rng());

    let stmt2 = pedersen::dot_product::Statement {
        a: a2,
        comm_x,
        comm_result: comm_result2,
    };
    let wit2 = pedersen::dot_product::Witness {
        x,
        r_x,
        result: result2,
        r_result,
    };
    let mut trans2 = Transcript::new("dot_product");
    let proof2 =
        pedersen::dot_product::prove(&params, &stmt2, &wit2, &mut trans2, common::test_rng());

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn dot_product_challenges_diverge_on_different_prover_randomness() {
    let n = 4;
    let params = setup_dot_product_params(n);
    let mut rng = common::test_rng();

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let result = inner_product(&a, &x);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
    let comm_result = commit(result, r_result, &params.scalar_gens);

    let statement = pedersen::dot_product::Statement {
        a,
        comm_x,
        comm_result,
    };
    let witness = pedersen::dot_product::Witness {
        x,
        r_x,
        result,
        r_result,
    };

    let mut trans1 = Transcript::new("dot_product");
    let proof1 = pedersen::dot_product::prove(
        &params,
        &statement.clone(),
        &witness.clone(),
        &mut trans1,
        &mut rng,
    );

    let mut trans2 = Transcript::new("dot_product");
    let proof2 = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans2, &mut rng);

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn open_challenges_diverge_on_different_params() {
    let mut rng = common::test_rng();

    // Two different generator sets
    let g1 = E::get_generator_from_seed(0u64);
    let h1 = E::get_generator_from_seed(1u64);
    let g2 = E::get_generator_from_seed(2u64);
    let h2 = E::get_generator_from_seed(3u64);

    let x = F::random(&mut rng);
    let r = F::random(&mut rng);

    // Same witness values, but commitments under different generators
    let comm1 = commit(x, r, &[g1, h1]);
    let comm2 = commit(x, r, &[g2, h2]);

    let params1 = pedersen::open::PublicParams {
        generators: [g1, h1],
    };
    let params2 = pedersen::open::PublicParams {
        generators: [g2, h2],
    };

    let stmt1 = pedersen::open::Statement { commitment: comm1 };
    let stmt2 = pedersen::open::Statement { commitment: comm2 };
    let witness = pedersen::open::Witness { x, r };

    let mut trans1 = Transcript::new("open");
    let proof1 = pedersen::open::prove(&params1, &stmt1, &witness, &mut trans1, common::test_rng());

    let mut trans2 = Transcript::new("open");
    let proof2 = pedersen::open::prove(&params2, &stmt2, &witness, &mut trans2, common::test_rng());

    // Different params should produce different challenges
    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn equals_challenges_diverge_on_different_params() {
    let mut rng = common::test_rng();

    let g1 = E::get_generator_from_seed(0u64);
    let h1 = E::get_generator_from_seed(1u64);
    let g2 = E::get_generator_from_seed(2u64);
    let h2 = E::get_generator_from_seed(3u64);

    let x = F::random(&mut rng);
    let r1 = F::random(&mut rng);
    let r2 = F::random(&mut rng);

    let comm1_a = commit(x, r1, &[g1, h1]);
    let comm2_a = commit(x, r2, &[g1, h1]);
    let comm1_b = commit(x, r1, &[g2, h2]);
    let comm2_b = commit(x, r2, &[g2, h2]);

    let params1 = pedersen::equals::PublicParams {
        generators: [g1, h1],
    };
    let params2 = pedersen::equals::PublicParams {
        generators: [g2, h2],
    };

    let stmt1 = pedersen::equals::Statement {
        comm1: comm1_a,
        comm2: comm2_a,
    };
    let stmt2 = pedersen::equals::Statement {
        comm1: comm1_b,
        comm2: comm2_b,
    };
    let witness = pedersen::equals::Witness { x, r1, r2 };

    let mut trans1 = Transcript::new("equals");
    let proof1 =
        pedersen::equals::prove(&params1, &stmt1, &witness, &mut trans1, common::test_rng());

    let mut trans2 = Transcript::new("equals");
    let proof2 =
        pedersen::equals::prove(&params2, &stmt2, &witness, &mut trans2, common::test_rng());

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn product_challenges_diverge_on_different_params() {
    let mut rng = common::test_rng();

    let g1 = E::get_generator_from_seed(0u64);
    let h1 = E::get_generator_from_seed(1u64);
    let g2 = E::get_generator_from_seed(2u64);
    let h2 = E::get_generator_from_seed(3u64);

    let x = F::random(&mut rng);
    let y = F::random(&mut rng);
    let z = x * y;
    let rx = F::random(&mut rng);
    let ry = F::random(&mut rng);
    let rz = F::random(&mut rng);

    let comm_x1 = commit(x, rx, &[g1, h1]);
    let comm_y1 = commit(y, ry, &[g1, h1]);
    let comm_z1 = commit(z, rz, &[g1, h1]);
    let comm_x2 = commit(x, rx, &[g2, h2]);
    let comm_y2 = commit(y, ry, &[g2, h2]);
    let comm_z2 = commit(z, rz, &[g2, h2]);

    let params1 = pedersen::product::PublicParams {
        generators: [g1, h1],
    };
    let params2 = pedersen::product::PublicParams {
        generators: [g2, h2],
    };

    let stmt1 = pedersen::product::Statement {
        comm_x: comm_x1,
        comm_y: comm_y1,
        comm_z: comm_z1,
    };
    let stmt2 = pedersen::product::Statement {
        comm_x: comm_x2,
        comm_y: comm_y2,
        comm_z: comm_z2,
    };
    let witness = pedersen::product::Witness {
        x,
        y,
        z,
        rx,
        ry,
        rz,
    };

    let mut trans1 = Transcript::new("product");
    let proof1 =
        pedersen::product::prove(&params1, &stmt1, &witness, &mut trans1, common::test_rng());

    let mut trans2 = Transcript::new("product");
    let proof2 =
        pedersen::product::prove(&params2, &stmt2, &witness, &mut trans2, common::test_rng());

    assert_ne!(proof1.c, proof2.c);
}

#[test]
fn dot_product_challenges_diverge_on_different_params() {
    let n = 4;
    let mut rng = common::test_rng();

    // Two different parameter sets
    let vec_gens1 = E::get_generators(n);
    let vec_gens2: Vec<E> = (100..100 + n)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let h1 = E::get_generator_from_seed(50u64);
    let g1 = E::get_generator_from_seed(51u64);
    let h2 = E::get_generator_from_seed(52u64);
    let g2 = E::get_generator_from_seed(53u64);

    let params1 = pedersen::dot_product::PublicParams {
        vec_gens: vec_gens1.clone(),
        scalar_gens: [g1, h1],
    };
    let params2 = pedersen::dot_product::PublicParams {
        vec_gens: vec_gens2.clone(),
        scalar_gens: [g2, h2],
    };

    let a: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let x: Vec<F> = (0..n).map(|_| F::random(&mut rng)).collect();
    let result = inner_product(&a, &x);
    let r_x = F::random(&mut rng);
    let r_result = F::random(&mut rng);

    let comm_x1 = vector_commit(&x, r_x, &vec_gens1, h1);
    let comm_result1 = commit(result, r_result, &[g1, h1]);
    let comm_x2 = vector_commit(&x, r_x, &vec_gens2, h2);
    let comm_result2 = commit(result, r_result, &[g2, h2]);

    let stmt1 = pedersen::dot_product::Statement {
        a: a.clone(),
        comm_x: comm_x1,
        comm_result: comm_result1,
    };
    let stmt2 = pedersen::dot_product::Statement {
        a,
        comm_x: comm_x2,
        comm_result: comm_result2,
    };
    let witness = pedersen::dot_product::Witness {
        x,
        r_x,
        result,
        r_result,
    };

    let mut trans1 = Transcript::new("dot_product");
    let proof1 = pedersen::dot_product::prove(
        &params1,
        &stmt1,
        &witness.clone(),
        &mut trans1,
        common::test_rng(),
    );

    let mut trans2 = Transcript::new("dot_product");
    let proof2 =
        pedersen::dot_product::prove(&params2, &stmt2, &witness, &mut trans2, common::test_rng());

    assert_ne!(proof1.c, proof2.c);
}

// ==============================================================================
// Property-based tests
// ==============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5))]

    #[test]
    fn open_completeness_property(x in common::arb_zq(), r in common::arb_zq()) {
        let [g, h] = generators();
        let commitment = commit(x, r, &[g, h]);

        let params = pedersen::open::PublicParams { generators: [g, h] };
        let statement = pedersen::open::Statement { commitment };
        let witness = pedersen::open::Witness { x, r };

        let mut trans_p = Transcript::new("open");
        let proof = pedersen::open::prove(&params, &statement, &witness, &mut trans_p, &mut common::test_rng());

        let mut trans_v = Transcript::new("open");
        prop_assert!(pedersen::open::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn equals_completeness_property(
        x in common::arb_zq(),
        r1 in common::arb_zq(),
        r2 in common::arb_zq()
    ) {
        let [g, h] = generators();
        let comm1 = commit(x, r1, &[g, h]);
        let comm2 = commit(x, r2, &[g, h]);

        let params = pedersen::equals::PublicParams { generators: [g, h] };
        let statement = pedersen::equals::Statement { comm1, comm2 };
        let witness = pedersen::equals::Witness { x, r1, r2 };

        let mut trans_p = Transcript::new("equals");
        let proof = pedersen::equals::prove(&params, &statement, &witness, &mut trans_p, &mut common::test_rng());

        let mut trans_v = Transcript::new("equals");
        prop_assert!(pedersen::equals::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn product_completeness_property(
        x in common::arb_zq(),
        y in common::arb_zq(),
        rx in common::arb_zq(),
        ry in common::arb_zq(),
        rz in common::arb_zq()
    ) {
        let [g, h] = generators();
        let z = x * y;
        let comm_x = commit(x, rx, &[g, h]);
        let comm_y = commit(y, ry, &[g, h]);
        let comm_z = commit(z, rz, &[g, h]);

        let params = pedersen::product::PublicParams { generators: [g, h] };
        let statement = pedersen::product::Statement { comm_x, comm_y, comm_z };
        let witness = pedersen::product::Witness { x, y, z, rx, ry, rz };

        let mut trans_p = Transcript::new("product");
        let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut common::test_rng());

        let mut trans_v = Transcript::new("product");
        prop_assert!(pedersen::product::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn product_soundness_property(
        x in common::arb_zq(),
        y in common::arb_zq(),
        delta in common::arb_small_zq(), // small non-zero delta
        rx in common::arb_zq(),
        ry in common::arb_zq(),
        rz in common::arb_zq()
    ) {
        let [g, h] = generators();
        let z_wrong = x * y + delta; // z != x*y
        let comm_x = commit(x, rx, &[g, h]);
        let comm_y = commit(y, ry, &[g, h]);
        let comm_z = commit(z_wrong, rz, &[g, h]);

        let params = pedersen::product::PublicParams { generators: [g, h] };
        let statement = pedersen::product::Statement { comm_x, comm_y, comm_z };
        let witness = pedersen::product::Witness { x, y, z: z_wrong, rx, ry, rz };

        let mut trans_p = Transcript::new("product");
        let proof = pedersen::product::prove(&params, &statement, &witness, &mut trans_p, &mut common::test_rng());

        let mut trans_v = Transcript::new("product");
        prop_assert!(pedersen::product::verify(&params, &statement, &proof, &mut trans_v).is_err());
    }

    #[test]
    fn dot_product_completeness_property(
        a0 in common::arb_zq(), a1 in common::arb_zq(),
        a2 in common::arb_zq(), a3 in common::arb_zq(),
        x0 in common::arb_zq(), x1 in common::arb_zq(),
        x2 in common::arb_zq(), x3 in common::arb_zq(),
        r_x in common::arb_zq(),
        r_result in common::arb_zq()
    ) {
        let params = setup_dot_product_params(4);

        let a = vec![a0, a1, a2, a3];
        let x = vec![x0, x1, x2, x3];
        let result = inner_product(&a, &x);

        let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
        let comm_result = commit(result, r_result, &params.scalar_gens);

        let statement = pedersen::dot_product::Statement {
            a,
            comm_x,
            comm_result,
        };
        let witness = pedersen::dot_product::Witness {
            x,
            r_x,
            result,
            r_result,
        };

        let mut trans_p = Transcript::new("dot_product");
        let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut common::test_rng());

        let mut trans_v = Transcript::new("dot_product");
        prop_assert!(pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).is_ok());
    }

    #[test]
    fn dot_product_soundness_property(
        a0 in common::arb_zq(), a1 in common::arb_zq(),
        a2 in common::arb_zq(), a3 in common::arb_zq(),
        x0 in common::arb_zq(), x1 in common::arb_zq(),
        x2 in common::arb_zq(), x3 in common::arb_zq(),
        r_x in common::arb_zq(),
        r_result in common::arb_zq()
    ) {
        let params = setup_dot_product_params(4);

        let a = vec![a0, a1, a2, a3];
        let x = vec![x0, x1, x2, x3];
        let wrong_result = inner_product(&a, &x) + F::from(1);

        let comm_x = vector_commit(&x, r_x, &params.vec_gens, params.scalar_gens[1]);
        let comm_result = commit(wrong_result, r_result, &params.scalar_gens);

        let statement = pedersen::dot_product::Statement {
            a,
            comm_x,
            comm_result,
        };
        let witness = pedersen::dot_product::Witness {
            x,
            r_x,
            result: wrong_result,
            r_result,
        };

        let mut trans_p = Transcript::new("dot_product");
        let proof = pedersen::dot_product::prove(&params, &statement, &witness, &mut trans_p, &mut common::test_rng());

        let mut trans_v = Transcript::new("dot_product");
        prop_assert!(pedersen::dot_product::verify(&params, &statement, &proof, &mut trans_v).is_err());
    }
}
