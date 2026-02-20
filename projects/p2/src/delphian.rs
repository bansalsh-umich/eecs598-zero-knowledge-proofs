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
use p1::{
    One, Random, Zero,
    poly::{Multilinear, Univariate},
};
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
        // let sub_comms = comms.establish_subprotocol::<String, i32>("").await?;
        // let value = comms.recv().await?;

        // 1. Compute Full Assignment
        let z = stmt.z(&wit);
        let z_num_vars = z.size.trailing_zeros() as usize;
        let z_tilde = Multilinear::new(z_num_vars, z.to_dense());

        // 2. Commit to the Witness MLE
        let w_num_vars = wit.w.size.trailing_zeros() as usize;
        let w_tilde = Multilinear::new(w_num_vars, wit.w.to_dense());

        // 2b. Send the commitment
        let (c_w_tilde, opening) = quokka::commit(&w_tilde);
        comms.send(ProverMessage::PolyComm(c_w_tilde.clone()))?;

        // 3. Receive random challenge τ from the verifier
        let tau = comms.recv().await?;

        // 4. Construc the combined polynomial
        let tau_eq_tilde = Multilinear::eq_tilde(&tau);

        let log_m = stmt.A.rows.trailing_zeros() as usize;
        let Az_tilde = Multilinear::new(log_m, stmt.A.mul_sparse(&z).to_dense());
        let Bz_tilde = Multilinear::new(log_m, stmt.B.mul_sparse(&z).to_dense());
        let Cz_tilde = Multilinear::new(log_m, stmt.C.mul_sparse(&z).to_dense());

        // Compute h(x) = eq_tilde(tau, X) * [(Az_tilde(X) * Bz_tilde(X)) - (Cz_tilde(X))]
        let h = CombinedMLE::new(
            3,
            |vals| vals[0] * (vals[1] * vals[2] - vals[3]),
            vec![
                tau_eq_tilde,
                Az_tilde.clone(),
                Bz_tilde.clone(),
                Cz_tilde.clone(),
            ],
        );

        let primary_sumcheck_comms = comms
            .establish_subprotocol::<Univariate<E::Scalar>, E::Scalar>("main_sumcheck")
            .await?;

        let primary_sumcheck_statement = sumcheck::Statement {
            claimed_sum: E::Scalar::zero(),
            num_vars: log_m,
            max_degree: 3,
        };

        let challenges =
            sumcheck::Protocol::prover(primary_sumcheck_statement, h, primary_sumcheck_comms)
                .await?;

        let matrices = [&stmt.A, &stmt.B, &stmt.C];
        let Mz_tildes = [&Az_tilde, &Bz_tilde, &Cz_tilde];
        let sumcheck_channel_names = vec!["A_sumcheck", "B_sumcheck", "C_sumcheck"];
        let quokka_channel_names = vec!["A_quokka", "B_quokka", "C_quokka"];

        for i in 0..matrices.len() {
            let v_M = Mz_tildes[i].evaluate(&challenges);
            comms.send(ProverMessage::Value(v_M))?;

            // p_M = f_M_tilde(r', X) * z_tilde(X)
            let f_M_tilde = matrices[i].multilinear_extension();
            let f_M_tilde_at_challenges = f_M_tilde.partial_eval(&challenges);
            let p_M = CombinedMLE::new(
                2,
                |vals| vals[0] * vals[1],
                vec![f_M_tilde_at_challenges.clone(), z_tilde.clone()],
            );

            // Run sumcheck on p_M with claimed sum v_M
            let sumcheck_comms = comms
                .establish_subprotocol::<Univariate<E::Scalar>, E::Scalar>(
                    sumcheck_channel_names[i],
                )
                .await?;

            let sumcheck_statement = sumcheck::Statement {
                claimed_sum: v_M,
                num_vars: z_num_vars,
                max_degree: 2,
            };

            let challenges_p_M =
                sumcheck::Protocol::prover(sumcheck_statement, p_M, sumcheck_comms).await?;

            let w_M = w_tilde.evaluate(&challenges_p_M[..&challenges_p_M.len() - 1]);
            comms.send(ProverMessage::Value(w_M))?;

            // PC.Open
            let quokka_comms = comms
                .establish_subprotocol::<quokka::ProverMessage<E>, quokka::VerifierMessage>(
                    quokka_channel_names[i],
                )
                .await?;
            let quokka_statement = quokka::Statement {
                comm: c_w_tilde.clone(),
                point: challenges_p_M[..challenges_p_M.len() - 1].to_vec(),
                value: w_M,
            };
            let quokka_witness = quokka::Witness {
                poly: w_tilde.clone(),
                _opening: opening.clone(),
            };

            quokka::OpenProtocol::<E>::prover(quokka_statement, quokka_witness, quokka_comms)
                .await?;
        }

        Ok(())
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
        let prover_commit = match comms.recv().await? {
        ProverMessage::PolyComm(comm) => comm,
        other => bail!("Got non-prover commit {:?}", other),
        };
        let m = stmt.A.rows;
        let logm = m.trailing_zeros() as usize;
        let n = stmt.A.cols; 
        let logn = n.trailing_zeros() as usize; 
        let mut tau = Vec::with_capacity(logm);
        for _ in 0..logm {
            tau.push(E::Scalar::random(rng));
        }
        comms.send(tau.clone())?;

        let sumcheck_comms = comms
            .establish_subprotocol::<E::Scalar, Univariate<E::Scalar>>("main_sumcheck")
            .await?;

        // Run sumcheck on main R1CS polynomial h (verify prover sumcheck)
        // TO DO: initialize the comms channel for the sumcheck protocol
        let sc1_statement = sumcheck::Statement {
            claimed_sum: E::Scalar::zero(),
            num_vars: logm,
            max_degree: 3,
        };
        let (h_prime, r_prime) =
            sumcheck::Protocol::<E::Scalar>::verifier(sc1_statement, sumcheck_comms, rng).await?;

        // Phase 2
        let mut v_vals = vec![];
        let matrices = [&stmt.A, &stmt.B, &stmt.C];
        let sumcheck_names = ["A_sumcheck", "B_sumcheck", "C_sumcheck"];
        let quokka_names   = ["A_quokka",   "B_quokka",   "C_quokka"];
        for i in 0..matrices.len() {
            let matrix = matrices[i];
            let claimed_value = match comms.recv().await? {
                ProverMessage::Value(v) => v,
                other => bail!("Claimed value != prover value"),
            };
            v_vals.push(claimed_value);
            // Define second sumcheck
            let num_cols = matrix.cols;
            let log_cols = num_cols.trailing_zeros() as usize;
            let sc_statement = sumcheck::Statement {
                claimed_sum: claimed_value,
                num_vars: log_cols,
                max_degree: 2,
            };
            let mv_sc_comms = comms
                .establish_subprotocol::<E::Scalar, Univariate<E::Scalar>>(sumcheck_names[i])
                .await?;
            let (p_eval, r_doubleprime) =
                sumcheck::Protocol::<E::Scalar>::verifier(sc_statement, mv_sc_comms, rng).await?;
            let w_eval = match comms.recv().await? {
            ProverMessage::Value(v) => v,
                other => bail!("Got non-value {:?}", other),
            };
            let r_top = &r_doubleprime[..log_cols-1]; 
            let t = r_doubleprime[log_cols-1];

            // Do quokka opening
            let mut quokka_comms = comms
            .establish_subprotocol::<(), Vec<E::Scalar>>(quokka_names[i])
            .await?;
            let quokka_statement = quokka::Statement {
                comm  : prover_commit.clone(),
                point : r_top.to_vec(), 
                value : w_eval,
            }; 
            quokka::OpenProtocol::<E>::verifier(quokka_statement, quokka_comms, rng).await?; 
            // Do check (pm(r_doubleprime) = M_tilde(r_prime, r_doubleprime) * Z_tilde(r_doubleprime))
            let x_dense = stmt.x.to_dense();        
            let x_mle = Multilinear::new(logn - 1, x_dense);
            let x_eval = x_mle.evaluate(r_top);
            let one = E::Scalar::one();
            let z_eval = (one - t) * x_eval + t * w_eval;
            let mut full_point = r_prime.clone();
            full_point.extend_from_slice(&r_doubleprime);
            let M_mle = matrix.multilinear_extension();
            let M_eval = M_mle.evaluate(&full_point);
            
            if p_eval != M_eval * z_eval {
             bail!("Matrix-vector product check failed");
            }
        }
        // Do final algebra check 
        let eq_mle = Multilinear::eq_tilde(&tau);
        let eq_eval = eq_mle.evaluate(&r_prime);

        let rhs = eq_eval * (v_vals[0] * v_vals[1] - v_vals[2]);

        if h_prime != rhs {
            bail!("Final consistency check failed");
        }
        // return no error if no bails are thrown 
        Ok(())
    }
}
