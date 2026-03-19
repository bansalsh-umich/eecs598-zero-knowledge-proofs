#![allow(non_snake_case)]
use crate::{
    pedersen::{self, CommittedValue},
    quokka, sumcheck,
    transcript::Transcript,
};
use anyhow::Result;
use p1::{One, Random, Zero, poly::Multilinear};
use p2::{
    combined::CombinedMLE,
    ec::EllipticCurve,
    sparsemat::{SparseMatrix, SparseVector},
};
use serde::{Deserialize, Serialize};

/// Public parameters for the ZK Delphian protocol.
///
/// Holds independent generator sets for each subprotocol, plus the shared
/// blinding generator `h` and scalar-commitment base `g`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = "E: serde::de::DeserializeOwned"))]
pub struct PublicParams<E> {
    /// Vector generators for Quokka row commitments (`sqrt(witness_size)` elements).
    pub quokka_gens: Vec<E>,
    /// Vector generators for the main (degree-3) sumcheck (`log_rows * 4` elements).
    pub phase1_sc_gens: Vec<E>,
    /// Vector generators for the matrix-vector (degree-2) sumchecks (`log_cols * 3` elements).
    pub phase2_sc_gens: Vec<E>,
    /// Scalar generators `[g, h]` shared across subprotocols.
    pub scalar_gens: [E; 2],
}

impl<E: EllipticCurve> PublicParams<E> {
    /// Creates new public parameters with generator count validation.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - `quokka_gens` is empty or its length is not a power of two
    /// - `phase1_sc_gens` length is not a positive multiple of 4 (`max_degree + 1`)
    /// - `phase2_sc_gens` length is not a positive multiple of 3 (`max_degree + 1`)
    pub fn new(
        quokka_gens: Vec<E>,
        phase1_sc_gens: Vec<E>,
        phase2_sc_gens: Vec<E>,
        scalar_gens: [E; 2],
    ) -> Self {
        assert!(!quokka_gens.is_empty(), "quokka_gens must be non-empty");
        assert!(
            quokka_gens.len().is_power_of_two(),
            "quokka_gens.len() must be power of two"
        );
        assert!(
            !phase1_sc_gens.is_empty() && phase1_sc_gens.len() % 4 == 0,
            "phase1_sc_gens.len() must be a positive multiple of 4 (max_degree+1), got {}",
            phase1_sc_gens.len()
        );
        assert!(
            !phase2_sc_gens.is_empty() && phase2_sc_gens.len() % 3 == 0,
            "phase2_sc_gens.len() must be a positive multiple of 3 (max_degree+1), got {}",
            phase2_sc_gens.len()
        );
        Self {
            quokka_gens,
            phase1_sc_gens,
            phase2_sc_gens,
            scalar_gens,
        }
    }

    fn quokka_params(&self) -> quokka::PublicParams<E> {
        pedersen::dot_product::PublicParams {
            vec_gens: self.quokka_gens.clone(),
            scalar_gens: self.scalar_gens,
        }
    }

    fn sc_phase1_params(&self) -> sumcheck::PublicParams<E> {
        sumcheck::PublicParams {
            vec_gens: self.phase1_sc_gens.clone(),
            scalar_gens: self.scalar_gens,
        }
    }

    fn sc_phase2_params(&self) -> sumcheck::PublicParams<E> {
        sumcheck::PublicParams {
            vec_gens: self.phase2_sc_gens.clone(),
            scalar_gens: self.scalar_gens,
        }
    }

    fn sigma_params(&self) -> pedersen::equals::PublicParams<E> {
        pedersen::equals::PublicParams {
            generators: self.scalar_gens,
        }
    }

    fn product_params(&self) -> pedersen::product::PublicParams<E> {
        pedersen::product::PublicParams {
            generators: self.scalar_gens,
        }
    }

    fn open_params(&self) -> pedersen::open::PublicParams<E> {
        pedersen::open::PublicParams {
            generators: self.scalar_gens,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = ""))]
pub struct Statement<E: EllipticCurve> {
    /// R1CS constraint matrix `A`.
    pub A: SparseMatrix<E::Scalar>,
    /// R1CS constraint matrix `B`.
    pub B: SparseMatrix<E::Scalar>,
    /// R1CS constraint matrix `C`.
    pub C: SparseMatrix<E::Scalar>,
    /// Public input vector.
    pub x: SparseVector<E::Scalar>,
}

impl<E: EllipticCurve> Statement<E> {
    /// Creates a new R1CS statement with dimension validation.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The matrices have mismatched dimensions
    /// - Rows or columns are not powers of two
    /// - The public input size is not a power of two
    pub fn new(
        A: SparseMatrix<E::Scalar>,
        B: SparseMatrix<E::Scalar>,
        C: SparseMatrix<E::Scalar>,
        x: SparseVector<E::Scalar>,
    ) -> Self {
        assert_eq!(A.rows, B.rows, "A.rows != B.rows");
        assert_eq!(A.rows, C.rows, "A.rows != C.rows");
        assert_eq!(A.cols, B.cols, "A.cols != B.cols");
        assert_eq!(A.cols, C.cols, "A.cols != C.cols");
        assert!(A.rows.is_power_of_two(), "rows must be power of two");
        assert!(A.cols.is_power_of_two(), "cols must be power of two");
        assert!(x.size.is_power_of_two(), "x.size must be power of two");
        Self { A, B, C, x }
    }
}

/// The prover's private witness.
#[derive(Clone, Debug)]
pub struct Witness<E: EllipticCurve> {
    /// Private witness vector.
    pub w: SparseVector<E::Scalar>,
}

impl<E: EllipticCurve> Witness<E> {
    /// Creates a new witness with validation.
    ///
    /// # Panics
    ///
    /// Panics if the witness size is not a power of two.
    pub fn new(w: SparseVector<E::Scalar>) -> Self {
        assert!(w.size.is_power_of_two(), "w.size must be power of two");
        Self { w }
    }
}

/// Proof elements for a single matrix-vector sumcheck (A, B, or C).
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = ""))]
pub struct MatrixProof<E: EllipticCurve> {
    /// Commitment to `v_M = sum_x M_tilde(r', x) * z_tilde(x)`.
    pub comm_v: E,
    /// ZK sumcheck proof for `p_M(x) = M_tilde(r', x) * z_tilde(x)`.
    pub sc_proof: sumcheck::Proof<E>,
    /// Commitment to `w_tilde(r''_partial)`.
    pub comm_w_m: E,
    /// Quokka opening proof for `w_tilde` at `r''_partial`.
    pub quokka_proof: quokka::Proof<E>,
    /// Proves `sc_proof.comm_final` and the homomorphically-derived commitment
    /// to `p_M(r'')` agree on the same underlying value.
    pub equals_proof: pedersen::equals::Proof<E>,
}

/// Full ZK Delphian proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(deserialize = ""))]
pub struct Proof<E: EllipticCurve> {
    /// Quokka commitment to `w_tilde`.
    pub comm_w: quokka::Commitment<E>,
    /// Main sumcheck proof (degree-3, over `log_rows` variables).
    pub sc_phase1_proof: sumcheck::Proof<E>,
    /// Per-matrix proofs for `A`, `B`, `C` (in that order).
    pub matrix_proofs: [MatrixProof<E>; 3],
    /// Commitment to `v_A * v_B`.
    pub comm_v_ab: E,
    /// Proves `v_A * v_B = v_AB` under the committed values.
    pub product_proof: pedersen::product::Proof<E>,
    // Proves that prover has an opening for Comm(v_C),
    pub open_proof: pedersen::open::Proof<E>,
    /// Proves the main sumcheck's final evaluation equals
    /// `eq_tilde(tau, r') * (v_AB - v_C)`.
    pub final_equals_proof: pedersen::equals::Proof<E>,
}

/// Produce a ZK proof that the witness satisfies the R1CS instance `(A, B, C, x)`.
///
/// The protocol has several phases, each building on the previous:
///
/// **Setup**: Concatenate the public input `x` and private witness `w` into `z`.
/// Compute multilinear extensions `z_tilde`, `w_tilde`, and `x_tilde`. Commit
/// to `w_tilde` using Quokka (generating random blinding factors for the row
/// commitments). Append the commitment and derive the random challenge vector
/// `tau` from the transcript.
///
/// **Phase 1 -- Main sumcheck**: Construct the degree-3 polynomial
/// `h(r') = eq_tilde(tau, r') * (Az_tilde(r') * Bz_tilde(r') - Cz_tilde(r'))`,
/// which sums to zero over the hypercube when the R1CS is satisfied. Run ZK
/// sumcheck on `h` with claimed sum = 0.
///
/// **Phase 2 -- Matrix-vector sumchecks**: For each matrix `M` in `{A, B, C}`:
///   - Define `p_M(x) = M_tilde(r', x) * z_tilde(x)`, a degree-2 polynomial
///     whose hypercube sum equals `v_M`. Commit to `v_M` and run ZK sumcheck.
///   - The sumcheck produces a random point `r''`. Use Quokka to open `w_tilde`
///     at a derived sub-point of `r''` (all but the last coordinate), proving
///     consistency between the committed polynomial and the sumcheck output.
///   - Use an equals proof to show that the sumcheck's final evaluation
///     commitment matches the value derivable from the Quokka opening and
///     the public input.
///
/// **Phase 3 -- Final consistency**: Prove `v_A * v_B = v_AB` via the product
/// sigma protocol. Then prove that the main sumcheck's final evaluation
/// commitment matches `eq_tilde(tau, r') * (v_AB - v_C)` via an equals proof.
#[must_use]
pub fn prove<E: EllipticCurve>(
    params: &PublicParams<E>,
    statement: &Statement<E>,
    witness: &Witness<E>,
    trans: &mut Transcript,
    mut rng: impl rand::Rng,
) -> Proof<E> {
    // Cross-consistency between statement and witness.
    assert_eq!(statement.x.size, witness.w.size, "x.size != w.size");
    assert_eq!(
        statement.x.size + witness.w.size,
        statement.A.cols,
        "|x| + |w| != cols"
    );

    let num_rows = statement.A.rows;
    let num_cols = statement.A.cols;
    let log_rows = num_rows.ilog2() as usize;
    let log_cols = num_cols.ilog2() as usize;

    let z = statement.x.concat(&witness.w);
    let z_tilde = z.multilinear_extension();
    let w_tilde = witness.w.multilinear_extension();
    let x_tilde = statement.x.multilinear_extension();

    let num_rows_w = 1 << (w_tilde.num_vars() / 2);

    let w_openings: Vec<E::Scalar> = (0..num_rows_w)
        .map(|_| E::Scalar::random(&mut rng))
        .collect();
    let comm_w = quokka::commit(&w_tilde, &w_openings, &params.quokka_params());
    trans.append_message("comm_w", comm_w);

    let r: Vec<E::Scalar> = (0..log_rows)
        .map(|i| trans.get_challenge(format!("r{i}").as_str()))
        .collect();

    let Az_tilde = statement.A.mul_sparse(&z).multilinear_extension();
    let Bz_tilde = statement.B.mul_sparse(&z).multilinear_extension();
    let Cz_tilde = statement.C.mul_sparse(&z).multilinear_extension();
    let r_eq_tilde = Multilinear::eq_tilde(&r);

    let h = CombinedMLE::new(
        3,
        |val| val[0] * (val[1] * val[2] - val[3]),
        vec![
            r_eq_tilde,
            Az_tilde.clone(),
            Bz_tilde.clone(),
            Cz_tilde.clone(),
        ],
    );

    let (sc_phase1_proof, r_prime, comm_h_r_prime) = {
        let sumcheck_statement = sumcheck::Statement {
            comm_sum: E::zero(),
            num_vars: log_rows,
            max_degree: 3,
        };
        let witness = sumcheck::Witness::<E> {
            polynomial: h,
            sum: E::Scalar::zero(),
            r_sum: E::Scalar::zero(),
        };
        sumcheck::prove(
            &params.sc_phase1_params(),
            &sumcheck_statement,
            &witness,
            trans,
            rng,
        )
    };

    let matrices = [&statement.A, &statement.B, &statement.C];
    let (p_ms, committed_vs): (Vec<_>, Vec<_>) = matrices
        .into_iter()
        .map(|matrix| {
            let m_at_r_prime = matrix.multilinear_extension().partial_eval(&r_prime);
            let p_m = CombinedMLE::new(
                2,
                |vals| vals[0] * vals[1],
                vec![m_at_r_prime, z_tilde.clone()],
            );

            let v_m = p_m.sum_over_hypercube();
            let cv_m = CommittedValue::<E>::new(v_m, &mut rng, &params.scalar_gens);

            (p_m, cv_m)
        })
        .unzip();

    let p_a = &p_ms[0];
    let p_b = &p_ms[1];
    let p_c = &p_ms[2];

    let cv_a = &committed_vs[0];
    let cv_b = &committed_vs[1];
    let cv_c = &committed_vs[2];

    let v_ab = cv_a.val * cv_b.val;
    let cv_ab = CommittedValue::<E>::new(v_ab, &mut rng, &params.scalar_gens);

    // product proof for v_A = v_B
    let proof = {
        let statement = pedersen::product::Statement {
            comm_x: *cv_a,
            comm_y: *cv_b,
            comm_z: cv_ab,
        };
    };

    todo!()
}

/// Verify a ZK Delphian proof.
///
/// The verifier mirrors the prover's transcript interactions without access
/// to the witness. It re-derives all challenges, runs the sumcheck and
/// sigma-protocol verifiers, and checks consistency at each stage:
///
/// 1. Derive `tau` from the transcript (after absorbing params, statement,
///    `comm_w`).
/// 2. Verify the main sumcheck (claimed sum = 0, degree 3, `log_rows`
///    variables).
/// 3. For each matrix `M` in `{A, B, C}`:
///    - Verify the matrix-vector sumcheck.
///    - Verify the Quokka opening of `w_tilde` at the derived point.
///    - Derive the expected final-evaluation commitment homomorphically from
///      the public matrix value `M_tilde(r', r'')`, the public input
///      `x_tilde(r'')`, and the Quokka-verified commitment to
///      `w_tilde(r''_partial)`. Verify it equals the sumcheck's final
///      commitment via the equals proof.
/// 4. Verify the product proof (`v_A * v_B = v_AB`).
/// 5. Verify the final equals proof linking the main sumcheck's output to
///    `eq_tilde(tau, r') * (v_AB - v_C)`.
pub fn verify<E: EllipticCurve>(
    params: &PublicParams<E>,
    statement: &Statement<E>,
    proof: Proof<E>,
    trans: &mut Transcript,
) -> Result<()> {
    let num_rows = statement.A.rows;
    let num_cols = statement.A.cols;
    let log_rows = num_rows.ilog2() as usize;
    let log_cols = num_cols.ilog2() as usize;

    // Step 1: Initial params
    let comm_w = proof.comm_w.clone();
    trans.append_message("parameters", params);
    trans.append_message("statement", statement);
    trans.append_message("comm_w", comm_w);
    let [g, h] = params.scalar_gens;
    let mut r: Vec<E::Scalar> = Vec::with_capacity(log_rows); // Also known as tau, the spec uses r and tau
    for _ in 0..log_rows {
    let t: E::Scalar = trans.get_challenge("tau");
    r.push(t);
    }
    // Step 2: Main sumcheck
    let main_params = sumcheck::PublicParams {
        vec_gens: params.phase1_sc_gens.clone(),
        scalar_gens: params.scalar_gens,
    };
    let main_statement = sumcheck::Statement {
        comm_sum: E::zero(),
        num_vars: log_rows,
        max_degree: 3,
    };
    let (C_h, r_prime) =
        sumcheck::verify(&main_params, &main_statement, &proof.sc_phase1_proof, trans)?;

    // Step 3: per matrix sumcheck
    let matrices = [&statement.A, &statement.B, &statement.C];
    for i in 0..matrices.len() {
        // First do the per round sumcheck verification
        let matrix = matrices[i];
        let matrix_proof = proof.matrix_proofs[i].clone();
        let round_params = sumcheck::PublicParams {
            vec_gens: params.phase2_sc_gens.clone(),
            scalar_gens: params.scalar_gens,
        };
        let round_statement = sumcheck::Statement {
            comm_sum: matrix_proof.comm_v,
            num_vars: log_cols,
            max_degree: 2,
        };
        let (round_commit, r_dblprime) = sumcheck::verify(
            &round_params,
            &round_statement,
            &matrix_proof.sc_proof,
            trans,
        )?;

        // Now do the per-round quokka opening check
        let r_top = &r_dblprime[..log_cols - 1];
        let quokka_params = quokka::PublicParams {
            vec_gens: params.quokka_gens.clone(),
            scalar_gens: params.scalar_gens,
        };
        let quokka_statement = quokka::Statement {
            comm_rows: proof.comm_w.clone(),
            point: r_top.to_vec(),
            comm_eval: matrix_proof.comm_w_m,
        };
        quokka::verify(
            &quokka_params,
            &quokka_statement,
            &matrix_proof.quokka_proof,
            trans,
        )?;

        // Lastly do the equality proofs between the committed values C_em and the committed sumcheck value C_pm (round commit)
        let x_mle = statement.x.multilinear_extension();
        let x_tilde = x_mle.evaluate(r_top);
        let r_last = r_dblprime[log_cols - 1];
        let C_zm: E = (g * x_tilde) * (E::Scalar::one() - r_last) + matrix_proof.comm_w_m * r_last;
        let mut matrix_point = r_prime.clone();
        matrix_point.extend_from_slice(&r_dblprime);
        let m_mle = matrix.multilinear_extension();
        let m_val = m_mle.evaluate(&matrix_point); // M_tilde formation
        let C_em: E = C_zm * m_val;
        let equals_statement = pedersen::equals::Statement {
            comm1: C_em,
            comm2: round_commit,
        };
        let equals_params = pedersen::equals::PublicParams {
            generators: params.scalar_gens,
        };
        pedersen::equals::verify(
            &equals_params,
            &equals_statement,
            &matrix_proof.equals_proof,
            trans,
        )?;
    }

    // Step 4: Final check: Product proof, Open proof, and lastly, the Equals proof
    let C_va = proof.matrix_proofs[0].comm_v;
    let C_vb = proof.matrix_proofs[1].comm_v;
    let C_vc = proof.matrix_proofs[2].comm_v;
    let prod_params = pedersen::product::PublicParams {
        generators: params.scalar_gens,
    };
    let prod_statement = pedersen::product::Statement {
        comm_x: C_va,
        comm_y: C_vb,
        comm_z: proof.comm_v_ab,
    };
    pedersen::product::verify(&prod_params, &prod_statement, &proof.product_proof, trans)?;
    let open_params = pedersen::open::PublicParams {
        generators: params.scalar_gens,
    };
    let open_statement = pedersen::open::Statement { commitment: C_vc };
    pedersen::open::verify(&open_params, &open_statement, &proof.open_proof, trans)?;
    let equals_params = pedersen::equals::PublicParams {
        generators: params.scalar_gens,
    };
    let eq_mle = Multilinear::eq_tilde(&r);
    let eq_eval = eq_mle.evaluate(&r_prime); // known as "e" in the spec
    let equals_statement = pedersen::equals::Statement {
        comm1: (proof.comm_v_ab - C_vc) * eq_eval,
        comm2: C_h,
    };
    pedersen::equals::verify(
        &equals_params,
        &equals_statement,
        &proof.final_equals_proof,
        trans,
    )?;

    Ok(())
}
