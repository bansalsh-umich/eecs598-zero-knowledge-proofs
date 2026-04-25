#![allow(non_snake_case)]

mod common;

use common::{E, F};
use num_traits::Zero;
use p4::gadgets::SHA256;
use p4::{Circuit, ProverMatrixifier, VerifierMatrixifier};
fn reduced_sha256(input: &[u32; 8]) -> [u32; 8] {
    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const K: [u32; 4] = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5];

    // Build message schedule for single 32-byte block
    let mut w = [0u32; 16];
    w[..8].copy_from_slice(input);
    w[8] = 0x80000000;
    // w[9..14] = 0
    w[15] = 0x00000100; // 256 bits

    let (mut a, mut b, mut c, mut d) = (IV[0], IV[1], IV[2], IV[3]);
    let (mut e, mut f, mut g, mut h) = (IV[4], IV[5], IV[6], IV[7]);

    for i in 0..4 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(K[i])
            .wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let mj = (a & b) | (a & c) | (b & c);
        let t2 = s0.wrapping_add(mj);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    [
        a.wrapping_add(IV[0]),
        b.wrapping_add(IV[1]),
        c.wrapping_add(IV[2]),
        d.wrapping_add(IV[3]),
        e.wrapping_add(IV[4]),
        f.wrapping_add(IV[5]),
        g.wrapping_add(IV[6]),
        h.wrapping_add(IV[7]),
    ]
}

fn check_r1cs(m: ProverMatrixifier<F>) {
    let (([A, B, C], stmt_vec), witness) = m.into_statement_and_witness();
    let n_pub = stmt_vec.size;
    let mut z = vec![F::zero(); A.cols];
    for (i, &v) in stmt_vec.iter() {
        z[i] = v;
    }
    for (i, &v) in witness.iter() {
        z[n_pub + i] = v;
    }
    for row in 0..A.rows {
        let az: F = A.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
        let bz: F = B.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
        let cz: F = C.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
        assert_eq!(az * bz, cz, "R1CS not satisfied at row {row}");
    }
}
#[test]
fn sha256_circuit_zero_input_satisfies_r1cs() {
    let input = [0u32; 8];
    let output = reduced_sha256(&input);
    let circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut m = ProverMatrixifier::<F>::new();
    circuit.synthesize(&mut m).unwrap();
    check_r1cs(m);
}

#[test]
fn sha256_circuit_nonzero_input_satisfies_r1cs() {
    let input: [u32; 8] = [0x01020304, 0x05060708, 0x090a0b0c, 0x0d0e0f10, 0x11121314, 0x15161718, 0x191a1b1c, 0x1d1e1f20];
    let output = reduced_sha256(&input);
    let circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut m = ProverMatrixifier::<F>::new();
    circuit.synthesize(&mut m).unwrap();
    check_r1cs(m);
}

#[test]
fn sha256_circuit_wrong_output_fails_r1cs() {
    let input = [0u32; 8];
    let mut output = reduced_sha256(&input);
    output[0] ^= 1; // corrupt one output word

    let circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut m = ProverMatrixifier::<F>::new();
    circuit.synthesize(&mut m).unwrap();

    let (([A, B, C], stmt_vec), witness) = m.into_statement_and_witness();
    let n_pub = stmt_vec.size;
    let mut z = vec![F::zero(); A.cols];
    for (i, &v) in stmt_vec.iter() {
        z[i] = v;
    }
    for (i, &v) in witness.iter() {
        z[n_pub + i] = v;
    }

    let mut satisfied = true;
    for row in 0..A.rows {
        let az: F = A.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
        let bz: F = B.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
        let cz: F = C.iter().filter(|((r, _), _)| *r == row).map(|((_, c), &v)| v * z[c]).sum();
        if az * bz != cz {
            satisfied = false;
            break;
        }
    }
    assert!(!satisfied, "Wrong SHA-256 output should not satisfy R1CS");
}

#[test]
fn sha256_circuit_verifier_produces_matching_statement() {
    let input = [0u32; 8];
    let output = reduced_sha256(&input);

    // Prover path
    let prover_circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut pm = ProverMatrixifier::<F>::new();
    prover_circuit.synthesize(&mut pm).unwrap();
    let (prover_stmt, _) = pm.into_statement_and_witness();

    // Verifier path (no private input knowledge)
    let verifier_circuit = SHA256 {
        input: vec![None; 8],
        output: output.to_vec(),
    };
    let mut vm = VerifierMatrixifier::<F>::new();
    verifier_circuit.synthesize(&mut vm).unwrap();
    let verifier_stmt = vm.into_statement();

    // Matrices should have the same dimensions
    assert_eq!(prover_stmt.0[0].rows, verifier_stmt.0[0].rows);
    assert_eq!(prover_stmt.0[0].cols, verifier_stmt.0[0].cols);
    // Public vectors should match (same outputs, same Variable::one())
    assert_eq!(prover_stmt.1.size, verifier_stmt.1.size);
}

#[test]
fn sha256_circuit_structure() {
    let input = [0u32; 8];
    let output = reduced_sha256(&input);
    let circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut m = ProverMatrixifier::<F>::new();
    circuit.synthesize(&mut m).unwrap();
    let ((matrices, stmt_vec), _) = m.into_statement_and_witness();
    // Should have 1 (constant one) + 8 (output words) = 9 public variables
    assert_eq!(stmt_vec.size, 9);
    // Must have a non-trivial number of constraints (bit constraints + additions + ops)
    assert!(matrices[0].rows > 100, "SHA-256 circuit should have hundreds of constraints, got {}", matrices[0].rows);
}
#[test]
fn sha256_end_to_end_prove_and_verify() {
    let input = [1u32, 2, 3, 4, 5, 6, 7, 8];
    let output = reduced_sha256(&input);
    let circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut rng = common::test_rng();
    let result = p4::snark::prove_and_verify::<E, _>(circuit, &mut rng);
    assert!(result.is_ok(), "prove_and_verify failed: {:?}", result.err());
}

#[test]
fn sha256_end_to_end_wrong_output_fails() {
    let input = [1u32, 2, 3, 4, 5, 6, 7, 8];
    let mut output = reduced_sha256(&input);
    output[3] ^= 0xFF; // corrupt output

    let circuit = SHA256 {
        input: input.iter().map(|&v| Some(v)).collect(),
        output: output.to_vec(),
    };
    let mut rng = common::test_rng();
    let result = p4::snark::prove_and_verify::<E, _>(circuit, &mut rng);
    assert!(result.is_err(), "Corrupt output should fail verification");
}
