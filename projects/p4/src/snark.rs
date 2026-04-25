use crate::{Circuit, ProverMatrixifier};
use p2::ec::EllipticCurve;
use p2::sparsemat::{SparseMatrix, SparseVector};
use p3::delphian::{self, Proof, PublicParams};
use p3::transcript::Transcript;

/// Round up to the next power of two whose log is even (i.e., 4, 16, 64, 256, ...).
///
/// Quokka requires the witness polynomial to have an even number of variables,
/// so the witness vector size must be `2^(2k)` for some `k >= 1`.
fn pad_even_pow2(n: usize) -> usize {
    let p = n.max(4).next_power_of_two();
    if !p.ilog2().is_multiple_of(2) {
        p << 1
    } else {
        p
    }
}

/// Convert the raw R1CS output from [`ProverMatrixifier::into_statement_and_witness`]
/// into P3-compatible [`delphian::Statement`] and [`delphian::Witness`] with all
/// required padding.
pub fn circuit_to_r1cs<E: EllipticCurve>(
    matrices: [SparseMatrix<E::Scalar>; 3],
    x: SparseVector<E::Scalar>,
    w: SparseVector<E::Scalar>,
) -> (delphian::Statement<E>, delphian::Witness<E>) {
    let cur_pub = x.size;
    let n_rows = matrices[0].rows;

    let pad_size = pad_even_pow2(cur_pub.max(w.size));
    let rows_padded = n_rows.max(2).next_power_of_two();
    let cols_padded = 2 * pad_size;

    let padded_matrices = matrices.map(|mat| {
        let entries = mat.iter().map(|((row, col), &val)| {
            let new_col = if col >= cur_pub {
                col - cur_pub + pad_size
            } else {
                col
            };
            (row, new_col, val)
        });
        SparseMatrix::from_entries(rows_padded, cols_padded, entries)
    });

    let new_x = SparseVector::from_entries(pad_size, x.iter().map(|(i, &v)| (i, v)));
    let new_w = SparseVector::from_entries(pad_size, w.iter().map(|(i, &v)| (i, v)));

    let [a, b, c] = padded_matrices;
    (
        delphian::Statement::new(a, b, c, new_x),
        delphian::Witness::new(new_w),
    )
}

/// Generate [`PublicParams`] with the correct number of generators for a given
/// R1CS instance.
pub fn setup_params<E: EllipticCurve>(
    statement: &delphian::Statement<E>,
    witness: &delphian::Witness<E>,
) -> PublicParams<E> {
    let w_size = witness.w.size;
    let log_rows = statement.A.rows.ilog2() as usize;
    let log_cols = statement.A.cols.ilog2() as usize;

    let sqrt_w = 1usize << (w_size.ilog2() as usize / 2);
    let main_sc_num = log_rows * 4;
    let mv_sc_num = log_cols * 3;

    let quokka_gens: Vec<E> = (0..sqrt_w)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let main_sc_gens: Vec<E> = (sqrt_w..sqrt_w + main_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let mv_sc_gens: Vec<E> = (sqrt_w + main_sc_num..sqrt_w + main_sc_num + mv_sc_num)
        .map(|i| E::get_generator_from_seed(i as u64))
        .collect();
    let g = E::get_generator_from_seed(10001u64);
    let h = E::get_generator_from_seed(10000u64);

    PublicParams::new(quokka_gens, main_sc_gens, mv_sc_gens, [g, h])
}

/// Prove and verify a circuit end-to-end using P3's non-interactive ZK Delphian.
///
/// Returns the public statement and proof on success.
pub fn prove_and_verify<E: EllipticCurve, C: Circuit<E::Scalar>>(
    circuit: C,
    rng: &mut impl rand::Rng,
) -> anyhow::Result<(delphian::Statement<E>, Proof<E>)> {
    let mut matrixifier = ProverMatrixifier::<E::Scalar>::new();
    circuit.synthesize(&mut matrixifier)?;
    let (([a, b, c], x), w) = matrixifier.into_statement_and_witness();

    let (stmt, wit) = circuit_to_r1cs::<E>([a, b, c], x, w);
    let params = setup_params::<E>(&stmt, &wit);

    let mut trans_p = Transcript::new("zkdelphian");
    let proof = delphian::prove(&params, &stmt, &wit, &mut trans_p, &mut *rng);

    let mut trans_v = Transcript::new("zkdelphian");
    delphian::verify(&params, &stmt, proof.clone(), &mut trans_v)?;

    Ok((stmt, proof))
}
