use crate::{
    pedersen::{self, CommittedValue},
    transcript::Transcript,
};
use anyhow::Result;
use itertools::Itertools;
use p1::{Random, Zero};
use p2::{combined::CombinedMLE, ec::EllipticCurve};
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
/// collapses all round checks into a single dot-product relation, which is
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
    todo!()
}
