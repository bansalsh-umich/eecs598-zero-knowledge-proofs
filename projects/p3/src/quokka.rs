#![allow(unused)]
use crate::{
    pedersen::{self},
    transcript::Transcript,
};
use anyhow::Result;
use p1::Zero;
use p1::poly::Multilinear;
use p2::ec::{EllipticCurve, ScalarOf};
use serde::{Deserialize, Serialize};

pub type PublicParams<E> = pedersen::dot_product::PublicParams<E>;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = ""))]
pub struct Statement<E: EllipticCurve> {
    /// Commitments to the rows of the evaluation matrix (sqrt(N) elements).
    pub comm_rows: Vec<E>,
    /// The public evaluation point `r = (r_1, ..., r_l)`.
    pub point: Vec<E::Scalar>,
    /// Commitment to the evaluation `f(r)`.
    pub comm_eval: E,
}

impl<E: EllipticCurve> Statement<E> {
    /// Creates a new Quokka opening statement with validation.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - `point` has odd length
    /// - `comm_rows.len()` does not equal `2^(point.len()/2)`
    pub fn new(comm_rows: Vec<E>, point: Vec<E::Scalar>, comm_eval: E) -> Self {
        assert!(point.len().is_multiple_of(2), "point must have even length");
        let num_rows = 1usize << (point.len() / 2);
        assert_eq!(comm_rows.len(), num_rows, "comm_rows.len() != sqrt(N)");
        Self {
            comm_rows,
            point,
            comm_eval,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Witness<E: EllipticCurve> {
    /// The multilinear polynomial in evaluation form.
    pub poly: Multilinear<E::Scalar>,
    /// Blinding factors for each row commitment (sqrt(N) elements).
    pub openings: Vec<E::Scalar>,
    /// The evaluation `f(r)`.
    pub eval: E::Scalar,
    /// Blinding factor for `comm_eval`.
    pub r_eval: E::Scalar,
}

impl<E: EllipticCurve> Witness<E> {
    /// Creates a new Quokka witness with validation.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The polynomial has an odd number of variables
    /// - `openings.len()` does not equal `2^(num_vars/2)`
    pub fn new(
        poly: Multilinear<E::Scalar>,
        openings: Vec<E::Scalar>,
        eval: E::Scalar,
        r_eval: E::Scalar,
    ) -> Self {
        assert!(
            poly.num_vars().is_multiple_of(2),
            "poly must have even number of variables"
        );
        let num_rows = 1usize << (poly.num_vars() / 2);
        assert_eq!(openings.len(), num_rows, "openings.len() != sqrt(N)");
        Self {
            poly,
            openings,
            eval,
            r_eval,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = ""))]
pub struct Proof<E: EllipticCurve> {
    pub dp_proof: pedersen::dot_product::Proof<E>,
}

pub type Commitment<E> = Vec<E>;

/// Commit to a multilinear polynomial by arranging its evaluations into a √N × √N
/// matrix and vector-committing each row.
///
/// Returns √N row commitments. Requires an even number of variables.
/// `randomness` provides one blinding factor per row (the "openings").
pub fn commit<E: EllipticCurve>(
    poly: &Multilinear<E::Scalar>,
    randomness: &[E::Scalar],
    params: &PublicParams<E>,
) -> Commitment<E> {
    // test
    assert!(poly.num_vars().is_multiple_of(2));
    let num_rows = 1 << (poly.num_vars() / 2);
    assert_eq!(params.vec_gens.len(), num_rows);
    assert_eq!(randomness.len(), num_rows);

    poly.evals
        .chunks(num_rows)
        .zip(randomness)
        .map(|(chunk, &r)| {
            pedersen::vector_commit(chunk, r, &params.vec_gens, params.scalar_gens[1])
        })
        .collect()
}

/// Prove that the committed polynomial evaluates to the committed value at the
/// given public point.
///
/// Recall from project 2 that the evaluation `f(r)` can be decomposed as
/// `f(r) = <a, b^T * M>`, where `a = eq_tilde(r_bot)`, `b = eq_tilde(r_top)`,
/// and `M` is the evaluation matrix. The non-ZK prover sent `b^T * M` in the
/// clear; here, we must keep it hidden.
///
/// The key observation is that the row commitments are vector Pedersen
/// commitments, so `MSM(b, comm_rows)` is *already* a vector commitment to
/// `b^T * M` (think about why -- this follows from the homomorphic property).
/// You need to figure out what the corresponding randomness is.
///
/// Once you have a vector commitment to `b^T * M` and a scalar commitment to
/// the evaluation (given in the statement), the remaining task is to prove
/// a dot-product relation using the sigma protocol from `pedersen::dot_product`.
///
/// Both prover and verifier must append the same messages to the transcript
/// before invoking the dot product sub-protocol.
#[must_use]
pub fn prove<E: EllipticCurve>(
    params: &PublicParams<E>,
    statement: &Statement<E>,
    witness: &Witness<E>,
    trans: &mut Transcript,
    mut rng: impl rand::Rng,
) -> Proof<E> {
    trans.append_message("statement", statement);

    // Cross-consistency between statement and witness.
    assert_eq!(
        statement.point.len(),
        witness.poly.num_vars(),
        "point.len() != num_vars"
    );

    let point_dimension = statement.point.len();
    let half_dimension = point_dimension >> 1; // We know that it's a power of 2, so this is safe.
    let (r_bot, r_top) = statement.point.split_at(half_dimension);

    let a = Multilinear::eq_tilde(r_bot);
    let b = Multilinear::eq_tilde(r_top);

    let hidden_vec_commitment = E::msm(&b.evals, &statement.comm_rows);

    let m = point_dimension;
    let c = {
        let mut c = vec![E::Scalar::zero(); m];
        for i in 0..m {
            for j in 0..m {
                c[j] += b[i] * witness.poly.evals[i * m + j];
            }
        }
        c
    };

    // Looked up how to make the for loop idiomatic
    let oc: E::Scalar = witness
        .openings
        .iter()
        .zip(&b.evals)
        .map(|(&o, &b)| o * b)
        .sum();

    // Now, we can do a dot product proof that combined_commitment commits to <c, a>
    let proof = {
        let dp_params = pedersen::dot_product::PublicParams {
            scalar_gens: params.scalar_gens,
            vec_gens: params.vec_gens.clone(),
        };

        let dp_stmt = pedersen::dot_product::Statement {
            a: a.evals,
            comm_x: hidden_vec_commitment,
            comm_result: statement.comm_eval,
        };

        let dp_witness = pedersen::dot_product::Witness::<E> {
            x: c,
            r_x: oc,
            result: witness.eval,
            r_result: witness.r_eval,
        };

        pedersen::dot_product::prove(&dp_params, &dp_stmt, &dp_witness, trans, rng)
    };

    Proof { dp_proof: proof }
}

/// Verify an opening proof.
///
/// The verifier must reconstruct the same dot-product statement as the prover: compute `a` and `b`
/// from the evaluation point, derive the vector commitment to `b^T * M`  and then verify the
/// dot-product proof.
pub fn verify<E: EllipticCurve>(
    params: &PublicParams<E>,
    statement: &Statement<E>,
    proof: &Proof<E>,
    trans: &mut Transcript,
) -> Result<()> {
    trans.append_message("statement", statement);

    let point_dimension = statement.point.len();
    let half_dimension = point_dimension >> 1; // We know that it's a power of 2, so this is safe.
    let (r_bot, r_top) = statement.point.split_at(half_dimension);

    let a = Multilinear::eq_tilde(r_bot);
    let b = Multilinear::eq_tilde(r_top);

    let hidden_vec_commitment = E::msm(&b.evals, &statement.comm_rows);

    let dp_params = pedersen::dot_product::PublicParams {
        scalar_gens: params.scalar_gens,
        vec_gens: params.vec_gens.clone(),
    };

    let dp_stmt = pedersen::dot_product::Statement {
        a: a.evals,
        comm_x: hidden_vec_commitment,
        comm_result: statement.comm_eval,
    };

    pedersen::dot_product::verify(&dp_params, &dp_stmt, &proof.dp_proof, trans)
}
