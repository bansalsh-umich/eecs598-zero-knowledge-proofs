use std::os::macos::raw::stat;

use crate::{
    pedersen::{self, CommittedValue},
    quokka::commit,
    transcript::Transcript,
};
use anyhow::Result;
use itertools::Itertools;
use p1::{Field, One, Random, Zero};
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

pub fn create_sumcheck_matrix<F: Field>(
    challenges: &[F],
    num_vars: usize,
    max_degree: usize,
) -> SparseMatrix<F> {
    // Construct the verifier matrix M from Section 4.2.
    let mut entries: Vec<(usize, usize, F)> = vec![];
    let block_offset = |round: usize| round * (max_degree + 1);

    // Scalar Constants, to remove the final term
    for i in 0..num_vars {
        for j in 0..=max_degree {
            if j == 0 {
                entries.push((i, block_offset(i), F::one()));
            }
            entries.push((i, block_offset(i) + j, F::one()));
        }
    }

    // Random Challenges
    for i in 1..=num_vars {
        let mut power = F::one();
        for j in 0..=max_degree {
            let term = if i < num_vars { -power } else { power };
            entries.push((i, block_offset(i - 1) + j, term));
            power *= challenges[i - 1];
        }
    }

    let rows = num_vars + 1;
    let cols = num_vars * (max_degree + 1);

    SparseMatrix::from_entries(rows, cols, entries)
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
    trans.append_message("params", params);
    trans.append_message("statement", statement);
    let mut current_polynomial = witness.polynomial.clone();
    let mut round_commitments = Vec::with_capacity(statement.num_vars);
    let mut challenges = Vec::with_capacity(statement.num_vars);
    let d = statement.max_degree;
    let chunk_size = d + 1;
    let [g, h] = params.scalar_gens;

    // Final computational elements
    let mut r_x = E::Scalar::zero();
    let mut total_coefficients = Vec::with_capacity(statement.num_vars * chunk_size);
    // Round commitments
    for i in 0..statement.num_vars {
        let g_i = current_polynomial.to_univariate(0);
        let o_j = E::Scalar::random(&mut rng);
        let mut round_coefficients = vec![E::Scalar::zero(); chunk_size];
        for (j, c) in g_i.coeffs().iter().enumerate() {
            round_coefficients[j] = *c;
        }
        let chunk_generators = &params.vec_gens[i * chunk_size..(i + 1) * chunk_size];
        // Round commitment
        let c_i = pedersen::vector_commit(&round_coefficients, o_j, chunk_generators, h);
        round_commitments.push(c_i);
        // TO DO: Ask about this
        trans.append_message(format!("C{}", i).as_str(), &c_i);
        let r_i: E::Scalar = trans.get_challenge(format!("challenge_{i}").as_str());
        challenges.push(r_i);
        current_polynomial = current_polynomial.partial_eval(&[r_i]);
        // Increment final computation parameters
        r_x += o_j;
        total_coefficients.extend(round_coefficients);
    }
    // Do final commitment
    let final_eval = current_polynomial.evaluate(&[]);
    let r_final = E::Scalar::random(&mut rng);
    let comm_final = pedersen::commit(final_eval, r_final, &params.scalar_gens);
    trans.append_message("comm_final", comm_final);

    // Derive rho vector
    let rows = statement.num_vars + 1;
    let mut rho: Vec<E::Scalar> = Vec::with_capacity(rows);
    for i in 0..statement.num_vars + 1 {
        rho.push(trans.get_challenge(&format!("rho{}", i)));
    }
    // Dot product proof commitment values
    let c_x = round_commitments.iter().copied().sum();
    let c_res = statement.comm_sum * rho[0] + comm_final * rho[statement.num_vars];

    // Build Y (batched coefficients)
    let sumcheck_matrix = create_sumcheck_matrix(&challenges, statement.num_vars, d);
    let mut y = vec![E::Scalar::zero(); sumcheck_matrix.cols];
    for i in 0..rows {
        for (col, &coefficient) in sumcheck_matrix.row_iter(i) {
            y[col] += rho[i] * coefficient;
        }
    }

    // Dot product proof components
    let dp_statement = pedersen::dot_product::Statement {
        a: y,
        comm_x: c_x,
        comm_result: c_res,
    };
    let result = rho[0] * witness.sum + rho[statement.num_vars] * final_eval;
    let r_res = rho[0] * witness.r_sum + rho[statement.num_vars] * r_final;
    let dp_witness = pedersen::dot_product::Witness {
        x: total_coefficients,
        r_x: r_x,
        result: result,
        r_result: r_res,
    };
    let public_params = pedersen::dot_product::PublicParams {
        vec_gens: params.vec_gens.clone(),
        scalar_gens: params.scalar_gens,
    };
    let dp_proof =
        pedersen::dot_product::prove(&public_params, &dp_statement, &dp_witness, trans, rng);

    (
        Proof {
            round_commitments,
            comm_final,
            dp_proof,
        },
        challenges,
        r_final,
    )
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
    trans.append_message("params", params);
    trans.append_message("statement", statement);

    let mut challenges = Vec::new();
    challenges.reserve(statement.num_vars);

    for i in 0..statement.num_vars {
        trans.append_message(format!("C{}", i).as_str(), proof.round_commitments[i]);
        let challenge_i: E::Scalar = trans.get_challenge(format!("challenge_{i}").as_str());
        challenges.push(challenge_i);
    }

    trans.append_message("comm_final", proof.comm_final);

    let sumcheck_matrix =
        create_sumcheck_matrix(&challenges, statement.num_vars, statement.max_degree);
    let rows = sumcheck_matrix.rows;
    let cols = sumcheck_matrix.cols;

    let rho: Vec<E::Scalar> = (0..statement.num_vars + 1)
        .map(|i| trans.get_challenge(&format!("rho{}", i)))
        .collect();

    let mut y = vec![E::Scalar::zero(); cols];
    for i in 0..rows {
        for (col, &coefficient) in sumcheck_matrix.row_iter(i) {
            y[col] += rho[i] * coefficient;
        }
    }

    let comm_sum: E = proof.round_commitments.iter().copied().sum();
    let sumcheck_result = E::msm(
        &[rho[0], rho[statement.num_vars]],
        &[statement.comm_sum, proof.comm_final],
    );

    let dp_params = pedersen::dot_product::PublicParams {
        scalar_gens: params.scalar_gens,
        vec_gens: params.vec_gens.clone(),
    };

    let dp_statement = pedersen::dot_product::Statement {
        a: y,
        comm_x: comm_sum,
        comm_result: sumcheck_result,
    };

    pedersen::dot_product::verify(&dp_params, &dp_statement, &proof.dp_proof, trans)?;
    return Ok((proof.comm_final, challenges));
}
