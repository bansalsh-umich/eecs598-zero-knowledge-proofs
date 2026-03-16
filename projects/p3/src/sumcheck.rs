use std::os::macos::raw::stat;

use crate::{
    pedersen::{self, CommittedValue},
    quokka::commit,
    transcript::Transcript,
};
use anyhow::Result;
use itertools::Itertools;
use p1::{One, Random, Zero};
use p2::{combined::CombinedMLE, ec::EllipticCurve, sparsemat::SparseMatrix};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PublicParams<E> {
    /// Vector generators for committing round polynomial coefficients (`num_vars * (max_degree + 1)` elements).
    /// Each round uses a distinct chunk of `max_degree + 1` generators.
    pub vec_gens: Vec<E>,
    /// Scalar generators `[g, h]` for Pedersen commitments.
    pub scalar_gens: [E; 2],
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Statement<E> {
    /// Commitment to the claimed sum.
    pub comm_sum: E,
    /// Number of variables in the polynomial.
    pub num_vars: usize,
    /// Maximum degree of the polynomial in any single variable.
    pub max_degree: usize,
}

#[derive(Clone, Debug)]
pub struct Witness<E: EllipticCurve> {
    /// The polynomial to sum over the hypercube.
    pub polynomial: CombinedMLE<E::Scalar>,
    /// The claimed sum value.
    pub sum: E::Scalar,
    /// Blinding factor for `comm_sum`.
    pub r_sum: E::Scalar,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = ""))]
pub struct Proof<E: EllipticCurve> {
    /// One vector commitment per round (to the round polynomial coefficients).
    pub round_commitments: Vec<E>,
    /// Commitment to the final evaluation `g(r_0, ..., r_{n-1})`.
    pub comm_final: E,
    /// Dot product proof for the batched check.
    pub dp_proof: pedersen::dot_product::Proof<E>,
}

/// Produce a non-interactive ZK sumcheck proof.
///
/// The prover claims that the polynomial (given in the witness) sums to the
/// committed value over the boolean hypercube. The protocol proceeds in `n`
/// rounds (one per variable). Each round, the prover commits to the
/// coefficients of the round polynomial using `pedersen::vector_commit`,
/// derives a challenge from the transcript, and partially evaluates.
///
/// After all rounds, the prover commits to the final evaluation and
/// collapses all round checksinto a single dot-product relation, which is
/// proved via `pedersen::dot_product`.
///
/// Returns the proof, the challenge vector, and the blinding factor for the
/// final evaluation commitment (needed by the caller for consistency proofs).
#[must_use]
pub fn prove<E: EllipticCurve>(
    params: &PublicParams<E>,
    statement: &Statement<E>,
    witness: &Witness<E>,
    trans: &mut Transcript,
    mut rng: impl rand::Rng,
) -> (Proof<E>, Vec<E::Scalar>, E::Scalar) {
    trans.append_message("statement", statement);
    let prev = &witness.polynomial;
    let commitments = vec![];

    for i in 0..statement.num_vars {
        let poly = prev.to_univariate(0);
        let coefficients = poly.coeffs().to_vec();
        let sub_gens = params.vec_gens[0..i];
        let o_j = E::Scalar::random(rng);
    }

    todo!()
}

/// Verify a ZK sumcheck proof.
///
/// The verifier re-derives the challenges from the round commitments in the
/// proof, constructs the same batched check, and verifies the dot product
/// proof against the homomorphically-derived result commitment.
///
/// Returns the commitment to the final evaluation and the challenge vector,
/// which the caller needs for subsequent consistency checks (e.g., in Delphian).
pub fn verify<E: EllipticCurve>(
    params: &PublicParams<E>,
    statement: &Statement<E>,
    proof: &Proof<E>,
    trans: &mut Transcript,
) -> Result<(E, Vec<E::Scalar>)> {
    trans.append_message("statement", statement);

    let mut commitments = Vec::new();
    commitments.reserve(statement.num_vars);

    for i in 0..statement.num_vars {
        trans.append_message(format!("C{}", i).as_str(), proof.round_commitments[i]);
        let challenge_i: E::Scalar = trans.get_challenge(format!("challenge_{i}").as_str());
        commitments.push(challenge_i);
    }

    trans.append_message("comm_final", proof.comm_final);

    // Construct the verifier matrix M from Section 4.2.
    let mut entries: Vec<(usize, usize, E::Scalar)> = vec![];
    let block_offset = |round: usize| round * (statement.max_degree + 1);

    // Scalar Constants, to remove the final term
    for i in 0..statement.num_vars {
        for j in 0..=statement.max_degree {
            if j == 0 {
                entries.push((i, block_offset(i), E::Scalar::one()));
            }
            entries.push((i, block_offset(i) + j, E::Scalar::one()));
        }
    }

    // Random Challenges
    for i in 1..=statement.num_vars {
        let mut power = E::Scalar::one();
        for j in 0..=statement.max_degree {
            let term = if i < statement.num_vars {
                -power
            } else {
                power
            };
            entries.push((i, block_offset(i - 1) + j, term));
            power *= commitments[i - 1];
        }
    }

    let rows = statement.num_vars + 1;
    let cols = statement.num_vars * (statement.max_degree + 1);
    let batched_coefficients: SparseMatrix<E::Scalar> =
        SparseMatrix::from_entries(rows, cols, entries);

    let mut rho: Vec<E::Scalar> = Vec::with_capacity(rows);
    for i in 0..statement.num_vars + 1 {
        rho.push(trans.get_challenge(&format!("rho{}", i)));
    }

    let mut y = vec![E::Scalar::zero(); cols];
    for i in 0..rows {
        for (col, &coefficient) in batched_coefficients.row_iter(i) {
            y[col] += rho[col] * coefficient;
        }
    }

    let comm_combined: E = proof.round_commitments.iter().copied().sum();
    let comm_result = E::msm(
        &[rho[0], rho[statement.num_vars]],
        &[statement.comm_sum, proof.comm_final],
    );

    let dp_params = pedersen::dot_product::PublicParams {
        scalar_gens: params.scalar_gens,
        vec_gens: params.vec_gens.clone(),
    };

    let dp_statement = pedersen::dot_product::Statement {
        a: y,
        comm_x: comm_combined,
        comm_result,
    };

    pedersen::dot_product::verify(&dp_params, &dp_statement, &proof.dp_proof, trans)?;
    return Ok((proof.comm_final, commitments));
}
