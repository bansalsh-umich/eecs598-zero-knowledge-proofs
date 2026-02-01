//! # Delphian Protocol
//!
//! This module implements the **Delphian SNARK**, an interactive proof system for
//! **R1CS (Rank-1 Constraint System)** satisfiability. R1CS is a standard representation
//! for NP statements used in many SNARK constructions.
//!
//! ## R1CS Background
//!
//! An R1CS instance consists of three sparse matrices `A`, `B`, `C` over a field `F`,
//! each of dimension `m × n`. A witness vector `w` satisfies the R1CS if there exists
//! a combined vector `z = (x || w)` (public input concatenated with private witness) such that:
//!
//! ```text
//! (A · z) ∘ (B · z) = C · z
//! ```
//!
//! where `∘` denotes the Hadamard (element-wise) product. This means for each row `i`:
//!
//! ```text
//! (A_i · z) × (B_i · z) = C_i · z
//! ```
//!
//! ## Protocol Overview
//!
//! The Delphian protocol reduces R1CS verification to polynomial evaluations using:
//!
//! 1. **Multilinear Extensions (MLEs)**: Convert the discrete R1CS check into polynomial
//!    identities over the field. The matrices `A`, `B`, `C` and vector `z` are lifted to
//!    their multilinear extensions `Ã`, `B̃`, `C̃`, `z̃`.
//!
//! 2. **Sumcheck Protocol**: The R1CS constraint `(Az) ∘ (Bz) = Cz` is equivalent to:
//!    ```text
//!    Σ_{τ ∈ {0,1}^log(m)} eq̃(r, τ) · [(Ãz̃)(τ) · (B̃z̃)(τ) - (C̃z̃)(τ)] = 0
//!    ```
//!    for a random `r`. This sum is verified using the sumcheck protocol.
//!
//! 3. **Polynomial Commitments**: The prover commits to `w̃` (the witness MLE) and later
//!    opens it at random points chosen by the verifier. This uses the Quokka commitment scheme.
#![allow(non_snake_case)]
use crate::{
    combined::CombinedMLE,
    ec::{EllipticCurve, ScalarOf},
    ip::{self, Comms, InteractiveProof},
    quokka,
    sparsemat::{SparseMatrix, SparseVector},
    sumcheck,
};
use anyhow::bail;
use p1::{One, Random, Zero, poly::Multilinear};
use std::marker::PhantomData;

/// Messages sent from the prover to the verifier in the Delphian protocol.
///
/// The prover sends two types of messages:
/// - **Polynomial commitments**: Used to commit to the witness polynomial `w̃` at the start.
/// - **Field values**: Used to send claimed evaluations (e.g., `v_A`, `v_B`, `v_C`) that
///   the verifier will later check via sumcheck and polynomial openings.
#[derive(Clone, Debug)]
pub enum ProverMessage<E: EllipticCurve> {
    /// A commitment to a multilinear polynomial using the Quokka scheme.
    PolyComm(quokka::Commitment<E>),
    /// A field element, typically a claimed polynomial evaluation.
    Value(E::Scalar),
}

/// Messages sent from the verifier to the prover.
///
/// The verifier sends vectors of random field elements as challenges. The primary use is
/// sending the random point `τ = (τ_1, ..., τ_log(m))` that determines which "row" of the
/// R1CS constraint is being checked (in a randomized, aggregated sense).
pub type VerifierMessage<E> = Vec<ScalarOf<E>>;

/// The public statement for the Delphian R1CS protocol.
///
/// This contains the R1CS instance (matrices `A`, `B`, `C`) and the public input `x`.
/// Both the prover and verifier have access to this information.
///
/// # R1CS Structure
///
/// The matrices define constraints of the form `(A·z) ∘ (B·z) = C·z` where:
/// - `z = (x || w)` is the concatenation of public input and private witness
/// - Each row represents one multiplicative constraint
/// - Columns correspond to variables in `z`
///
/// # Dimension Requirements
///
/// - All matrices must have the same dimensions: `m × n` where `m` is the number of
///   constraints and `n` is the number of variables.
/// - `m` and `n` must be powers of two (for MLE compatibility).
/// - `|x| + |w| = n` (public input size + witness size = number of columns).
#[derive(Clone, Debug)]
pub struct Statement<E: EllipticCurve> {
    /// The "left input" matrix. `A·z` gives the left operand of each multiplication gate.
    pub A: SparseMatrix<E::Scalar>,
    /// The "right input" matrix. `B·z` gives the right operand of each multiplication gate.
    pub B: SparseMatrix<E::Scalar>,
    /// The "output" matrix. `C·z` gives the expected result of each multiplication gate.
    pub C: SparseMatrix<E::Scalar>,
    /// The public input vector. This is known to both prover and verifier.
    pub x: SparseVector<E::Scalar>,
}

impl<E: EllipticCurve> Statement<E> {
    /// Creates a new R1CS statement with validation.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The matrices have mismatched dimensions
    /// - The public input size is not a power of two
    pub fn new(
        A: SparseMatrix<E::Scalar>,
        B: SparseMatrix<E::Scalar>,
        C: SparseMatrix<E::Scalar>,
        x: SparseVector<E::Scalar>,
    ) -> Self {
        // Check the A/B/C dimensions match up.
        assert_eq!(A.rows, B.rows);
        assert_eq!(A.rows, C.rows);
        assert_eq!(A.cols, B.cols);
        assert_eq!(A.cols, C.cols);
        assert!(x.size.is_power_of_two());

        Self { A, B, C, x }
    }

    /// Combines the public input `x` with the private witness `w` to form `z = (x || w)`.
    ///
    /// This is the full variable assignment vector used in the R1CS equations.
    /// The first `|x|` entries are the public input, and the remaining `|w|` entries
    /// are the private witness.
    ///
    /// # Panics
    ///
    /// Panics if `|x| + |w| ≠ number of columns` in the matrices.
    fn z(&self, wit: &Witness<E>) -> SparseVector<E::Scalar> {
        assert_eq!(self.x.size, wit.w.size);
        assert_eq!(self.x.size + wit.w.size, self.A.cols);

        SparseVector::from_entries(
            self.x.size + wit.w.size,
            self.x
                .iter()
                .map(|(i, v)| (i, *v))
                .chain(wit.w.iter().map(|(i, v)| (i + self.x.size, *v))),
        )
    }
}

/// The private witness for the Delphian R1CS protocol.
///
/// This contains the private portion of the variable assignment `z = (x || w)`.
/// Only the prover has access to the witness; the verifier never sees `w` directly
/// (though they can verify properties about it through the protocol).
///
/// # Structure
///
/// The witness `w` is a sparse vector of field elements. Combined with the public
/// input `x` from the statement, it forms the complete variable assignment `z`
/// that must satisfy the R1CS constraints.
#[derive(Clone, Debug)]
pub struct Witness<E: EllipticCurve> {
    /// The private witness vector. This is concatenated with the public input `x`
    /// to form the full assignment `z = (x || w)`.
    w: SparseVector<E::Scalar>,
}

impl<E: EllipticCurve> Witness<E> {
    /// Creates a new witness from a sparse vector.
    ///
    /// # Panics
    ///
    /// Panics if the witness size is not a power of two.
    pub fn new(w: SparseVector<E::Scalar>) -> Self {
        assert!(w.size.is_power_of_two());
        Self { w }
    }
}

/// Marker struct for the Delphian R1CS protocol.
///
/// This implements [`InteractiveProof`] and serves as a namespace for the
/// prover and verifier algorithms. The protocol is parameterized by an
/// elliptic curve `E` which determines the field and commitment scheme used.
pub struct Protocol<E>(PhantomData<E>);

/// Implementation of the Delphian R1CS interactive proof.
///
/// This protocol allows a prover to convince a verifier that they know a witness `w`
/// such that `z = (x || w)` satisfies the R1CS constraints `(A·z) ∘ (B·z) = C·z`.
///
/// # Protocol Flow
///
/// 1. **Commitment Phase**: Prover commits to the witness MLE `w̃`.
///
/// 2. **Main Sumcheck**: Verifier sends random `τ`, prover and verifier run sumcheck on
///    `h̃(X) = eq̃(τ, X) · [(Ãz̃)(X) · (B̃z̃)(X) - (C̃z̃)(X)]` to verify the R1CS constraint
///    holds at all points (in aggregate).
///
/// 3. **Matrix-Vector Sumchecks**: For each matrix `M ∈ {A, B, C}`:
///    - Prover claims `v_M = (M̃·z̃)(r')` where `r'` is from the main sumcheck.
///    - Run sumcheck on `p_M(X) = M̃(r', X) · z̃(X)` to verify the matrix-vector product.
///    - Prover opens `w̃` at the sumcheck's random point via Quokka.
///
/// 4. **Final Check**: Verifier confirms `h̃(r') = eq̃(τ, r') · (v_A · v_B - v_C)`.
impl<E: EllipticCurve> InteractiveProof for Protocol<E> {
    type ProverMessage = ProverMessage<E>;
    type VerifierMessage = VerifierMessage<E>;
    type Statement = Statement<E>;
    type Witness = Witness<E>;

    /// The prover produces no additional output beyond completing the protocol.
    ///
    /// All necessary information (the validity of the R1CS) is conveyed through
    /// the interactive messages themselves.
    type ProverOutput = ();

    /// The verifier produces no additional output beyond accepting/rejecting.
    ///
    /// If the protocol completes without error, the verifier is convinced that
    /// the prover knows a valid witness. Errors indicate rejection.
    type VerifierOutput = ();

    /// The Delphian prover algorithm.
    ///
    /// # Algorithm Overview
    ///
    /// 1. Compute the full assignment `z = (x || w)` and its MLE `z̃`.
    /// 2. Commit to the witness MLE `w̃` using Quokka and send the commitment.
    /// 3. Receive random challenge `τ` from the verifier.
    /// 4. Construct the combined polynomial `h̃ = eq̃(τ, ·) · [(Ãz̃) · (B̃z̃) - (C̃z̃)]`.
    /// 5. Run sumcheck on `h̃` with claimed sum 0 (the R1CS constraint).
    /// 6. For each matrix M ∈ {A, B, C}:
    ///    - Compute `v_M = Σ M̃(r', X) · z̃(X)` over the hypercube.
    ///    - Send `v_M` and run sumcheck to prove the matrix-vector product.
    ///    - Open the witness commitment at the resulting random point.
    ///
    /// # Arguments
    ///
    /// * `stmt` - The R1CS statement (matrices A, B, C and public input x).
    /// * `wit` - The private witness w.
    /// * `comms` - The communication channel.
    async fn prover(
        stmt: Self::Statement,
        wit: Self::Witness,
        mut comms: Comms<Self::ProverMessage, Self::VerifierMessage>,
    ) -> ip::Result<()> {
        let sub_comms = comms.establish_subprotocol::<String, i32>("").await?;
        let value = comms.recv().await?;
        todo!()
    }

    /// The Delphian verifier algorithm.
    ///
    /// # Algorithm Overview
    ///
    /// 1. Receive the prover's commitment to `w̃`.
    /// 2. Sample random challenge `τ` and send to prover.
    /// 3. Run sumcheck verification for the main R1CS polynomial `h̃` (claimed sum = 0).
    /// 4. For each matrix M ∈ {A, B, C}:
    ///    - Receive claimed value `v_M` from prover.
    ///    - Run sumcheck verification for `p_M(X) = M̃(r', X) · z̃(X)`.
    ///    - Verify the Quokka opening of `w̃` at the random point.
    ///    - Reconstruct `z̃(r'')` from the opened `w̃` value and the public input.
    ///    - Check that `p_M(r'') = M̃(r', r'') · z̃(r'')`.
    /// 5. Final check: verify `h̃(r') = eq̃(τ, r') · (v_A · v_B - v_C)`.
    ///
    /// # Arguments
    ///
    /// * `stmt` - The R1CS statement (matrices A, B, C and public input x).
    /// * `comms` - The communication channel.
    /// * `rng` - Random number generator for sampling challenges.
    ///
    /// # Errors
    ///
    /// Returns an error (rejection) if:
    /// - Any message has an unexpected type
    /// - Any sumcheck verification fails
    /// - Any polynomial commitment opening fails
    /// - The matrix-vector product check fails: `p_M(r'') ≠ M̃(r', r'') · z̃(r'')`
    /// - The final consistency check fails: `h̃(r') ≠ eq̃(τ, r') · (v_A · v_B - v_C)`
    async fn verifier<R: rand::Rng>(
        stmt: Self::Statement,
        mut comms: Comms<Self::VerifierMessage, Self::ProverMessage>,
        rng: &mut R,
    ) -> ip::Result<()> {
        todo!()
    }
}
