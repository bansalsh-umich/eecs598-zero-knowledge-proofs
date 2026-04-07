#![allow(non_snake_case)]

mod common;

use common::F;
use num_traits::Zero;
use p2::sparsemat::SparseMatrix;
use p4::ProverMatrixifier;
use p4::gadgets::{AllocatedBit, Boolean, UInt32};
use proptest::prelude::*;
struct R1csInstance {
    a: SparseMatrix<F>,
    b: SparseMatrix<F>,
    c: SparseMatrix<F>,
    z: Vec<F>,
    n_pub: usize,
}

impl R1csInstance {
    fn from_matrixifier(m: ProverMatrixifier<F>) -> Self {
        let (([a, b, c], stmt_vec), witness) = m.into_statement_and_witness();
        let n_pub = stmt_vec.size;
        let mut z = vec![F::zero(); a.cols];
        for (i, &v) in stmt_vec.iter() {
            z[i] = v;
        }
        for (i, &v) in witness.iter() {
            z[n_pub + i] = v;
        }
        Self { a, b, c, z, n_pub }
    }

    fn n_constraints(&self) -> usize {
        self.a.rows
    }

    fn is_satisfied(&self) -> bool {
        self.is_satisfied_with(&self.z)
    }

    fn is_satisfied_with(&self, z: &[F]) -> bool {
        for row in 0..self.a.rows {
            let az: F = self
                .a
                .iter()
                .filter(|((r, _), _)| *r == row)
                .map(|((_, c), &v)| v * z[c])
                .sum();
            let bz: F = self
                .b
                .iter()
                .filter(|((r, _), _)| *r == row)
                .map(|((_, c), &v)| v * z[c])
                .sum();
            let cz: F = self
                .c
                .iter()
                .filter(|((r, _), _)| *r == row)
                .map(|((_, c), &v)| v * z[c])
                .sum();
            if az * bz != cz {
                return false;
            }
        }
        true
    }

    fn satisfied_with_private_set_to(&self, priv_idx: usize, val: F) -> bool {
        let mut z = self.z.clone();
        z[self.n_pub + priv_idx] = val;
        self.is_satisfied_with(&z)
    }
}
#[test]
fn allocated_bit_only_zero_and_one_satisfy() {
    for val in [false, true] {
        let mut m = ProverMatrixifier::<F>::new();
        let bit = AllocatedBit::alloc(&mut m, Some(val)).unwrap();
        assert_eq!(bit.value, Some(val));
        let inst = R1csInstance::from_matrixifier(m);
        assert!(
            inst.n_constraints() >= 1,
            "AllocatedBit::alloc should add a boolean constraint"
        );
        assert!(inst.is_satisfied());
        assert!(inst.satisfied_with_private_set_to(bit.var.get_index(), F::from(0)));
        assert!(inst.satisfied_with_private_set_to(bit.var.get_index(), F::from(1)));
        for bad in [2u64, 3, 5, 100, 999] {
            assert!(
                !inst.satisfied_with_private_set_to(bit.var.get_index(), F::from(bad)),
                "value={bad} should violate the boolean constraint"
            );
        }
    }
}
#[test]
fn allocated_bit_xor_truth_table() {
    for (a, b) in [(false, false), (false, true), (true, false), (true, true)] {
        let mut m = ProverMatrixifier::<F>::new();
        let ba = AllocatedBit::alloc(&mut m, Some(a)).unwrap();
        let bb = AllocatedBit::alloc(&mut m, Some(b)).unwrap();
        let result = ba.xor(&mut m, &bb).unwrap();
        assert_eq!(result.value, Some(a ^ b), "xor({a}, {b})");
        let inst = R1csInstance::from_matrixifier(m);
        assert!(inst.is_satisfied());
        let wrong = if a ^ b { F::from(0) } else { F::from(1) };
        assert!(
            !inst.satisfied_with_private_set_to(result.var.get_index(), wrong),
            "wrong xor result should violate constraint for ({a}, {b})"
        );
    }
}
#[test]
fn boolean_chr_truth_table() {
    for a in [false, true] {
        for b in [false, true] {
            for c in [false, true] {
                let expected = (a & b) ^ (!a & c);
                let mut m = ProverMatrixifier::<F>::new();
                let ba = AllocatedBit::alloc(&mut m, Some(a)).unwrap();
                let bb = AllocatedBit::alloc(&mut m, Some(b)).unwrap();
                let bc = AllocatedBit::alloc(&mut m, Some(c)).unwrap();
                let r = Boolean::chr::<F, _>(
                    &Boolean::Is(ba),
                    &Boolean::Is(bb),
                    &Boolean::Is(bc),
                    &mut m,
                )
                .unwrap();
                assert_eq!(r.val(), Some(expected), "chr({a},{b},{c})");
                let inst = R1csInstance::from_matrixifier(m);
                assert!(inst.is_satisfied());
                if let Boolean::Is(ref rb) = r {
                    let wrong = if expected { F::from(0) } else { F::from(1) };
                    assert!(
                        !inst.satisfied_with_private_set_to(rb.var.get_index(), wrong),
                        "wrong chr result should violate constraint for ({a},{b},{c})"
                    );
                }
            }
        }
    }
}
#[test]
fn boolean_maj_truth_table() {
    for a in [false, true] {
        for b in [false, true] {
            for c in [false, true] {
                let expected = (a & b) | (a & c) | (b & c);
                let mut m = ProverMatrixifier::<F>::new();
                let ba = AllocatedBit::alloc(&mut m, Some(a)).unwrap();
                let bb = AllocatedBit::alloc(&mut m, Some(b)).unwrap();
                let bc = AllocatedBit::alloc(&mut m, Some(c)).unwrap();
                let r = Boolean::maj::<F, _>(
                    &Boolean::Is(ba),
                    &Boolean::Is(bb),
                    &Boolean::Is(bc),
                    &mut m,
                )
                .unwrap();
                assert_eq!(r.val(), Some(expected), "maj({a},{b},{c})");
                let inst = R1csInstance::from_matrixifier(m);
                assert!(inst.is_satisfied());
                if let Boolean::Is(ref rb) = r {
                    let wrong = if expected { F::from(0) } else { F::from(1) };
                    assert!(
                        !inst.satisfied_with_private_set_to(rb.var.get_index(), wrong),
                        "wrong maj result should violate constraint for ({a},{b},{c})"
                    );
                }
            }
        }
    }
}
#[test]
fn uint32_alloc_produces_32_constrained_bits() {
    let mut m = ProverMatrixifier::<F>::new();
    let w = UInt32::alloc(&mut m, Some(0)).unwrap();
    assert_eq!(w.value, Some(0));
    assert_eq!(w.bits.len(), 32);
    let inst = R1csInstance::from_matrixifier(m);
    assert!(
        inst.n_constraints() >= 32,
        "UInt32::alloc needs at least 32 boolean constraints"
    );
    assert!(inst.is_satisfied());
}

#[test]
fn uint32_alloc_constrains_each_bit_to_boolean() {
    let mut m = ProverMatrixifier::<F>::new();
    let w = UInt32::alloc(&mut m, Some(0)).unwrap();
    let inst = R1csInstance::from_matrixifier(m);
    // Spot-check several bits across the word
    for i in [0, 7, 15, 24, 31] {
        if let Boolean::Is(ref b) = w.bits[i] {
            assert!(
                !inst.satisfied_with_private_set_to(b.var.get_index(), F::from(2)),
                "bit {i} should reject non-boolean value"
            );
        } else {
            panic!("UInt32::alloc should produce Is() bits, not Const");
        }
    }
}

#[test]
fn uint32_alloc_little_endian_bit_order() {
    let mut m = ProverMatrixifier::<F>::new();
    // value = 1 means only bit 0 is set (little-endian)
    let w = UInt32::alloc(&mut m, Some(1)).unwrap();
    assert_eq!(w.bits[0].val(), Some(true));
    for i in 1..32 {
        assert_eq!(
            w.bits[i].val(),
            Some(false),
            "bit {i} should be false for value=1"
        );
    }
    // value with known pattern
    let mut m2 = ProverMatrixifier::<F>::new();
    let w2 = UInt32::alloc(&mut m2, Some(0b1010_0000_0000_0000_0000_0000_0000_0101)).unwrap();
    assert_eq!(w2.bits[0].val(), Some(true)); // bit 0
    assert_eq!(w2.bits[1].val(), Some(false)); // bit 1
    assert_eq!(w2.bits[2].val(), Some(true)); // bit 2
    assert_eq!(w2.bits[29].val(), Some(true)); // bit 29
    assert_eq!(w2.bits[31].val(), Some(true)); // bit 31
    let inst = R1csInstance::from_matrixifier(m2);
    assert!(inst.is_satisfied());
}
#[test]
fn uint32_rotr_is_zero_cost_permutation() {
    // rotr should not add any constraints — it just permutes Boolean references
    let mut m = ProverMatrixifier::<F>::new();
    let w = UInt32::alloc(&mut m, Some(0xDEADBEEF)).unwrap();
    let n_before = {
        // We can't peek at the constraint count mid-build, so check post-hoc:
        // alloc produces exactly 32 constraints, rotr should add zero
        let _ = w.rotr(7);
        // rotr returns a new UInt32 but doesn't touch the matrixifier
        m
    };
    let inst = R1csInstance::from_matrixifier(n_before);
    assert_eq!(
        inst.n_constraints(),
        32,
        "rotr should not add constraints beyond the initial alloc"
    );
}

#[test]
fn uint32_rotr_permutes_bits_correctly() {
    let mut m = ProverMatrixifier::<F>::new();
    let w = UInt32::alloc(&mut m, Some(1)).unwrap(); // only bit 0 is set
    let rotated = w.rotr(5);
    // rotr(5): new[i] = old[(i+5)%32], so new[27] = old[0] = true
    assert_eq!(rotated.bits[27].val(), Some(true));
    assert_eq!(rotated.bits[0].val(), Some(false));
    assert_eq!(rotated.value, Some(1u32.rotate_right(5)));
}
#[test]
fn uint32_xor_satisfies_and_constrains() {
    let mut m = ProverMatrixifier::<F>::new();
    let a = UInt32::alloc(&mut m, Some(0xFF00FF00)).unwrap();
    let b = UInt32::alloc(&mut m, Some(0x0F0F0F0F)).unwrap();
    let result = a.xor(&mut m, &b).unwrap();
    assert_eq!(result.value, Some(0xFF00FF00 ^ 0x0F0F0F0F));
    let inst = R1csInstance::from_matrixifier(m);
    // xor adds constraints beyond the 64 alloc constraints for a and b
    assert!(inst.n_constraints() > 64);
    assert!(inst.is_satisfied());
    // Flip one result bit — should break
    if let Boolean::Is(ref rb) = result.bits[0] {
        let cur = result.bits[0].val().unwrap();
        let wrong = F::from(!cur);
        assert!(!inst.satisfied_with_private_set_to(rb.var.get_index(), wrong));
    }
}
#[test]
fn uint32_add_no_overflow_satisfies_and_constrains() {
    let mut m = ProverMatrixifier::<F>::new();
    let a = UInt32::alloc(&mut m, Some(100)).unwrap();
    let b = UInt32::alloc(&mut m, Some(200)).unwrap();
    let result = a.add(&mut m, &b).unwrap();
    assert_eq!(result.value, Some(300));
    let inst = R1csInstance::from_matrixifier(m);
    assert!(inst.is_satisfied());
    // Flip a result bit — should violate the packing constraint
    if let Boolean::Is(ref rb) = result.bits[0] {
        let cur = result.bits[0].val().unwrap();
        let wrong = F::from(!cur);
        assert!(
            !inst.satisfied_with_private_set_to(rb.var.get_index(), wrong),
            "wrong add result bit should violate constraint"
        );
    }
}
#[test]
fn uint32_big_sigma0_satisfies_and_constrains() {
    let mut m = ProverMatrixifier::<F>::new();
    let val = 0xABCD1234u32;
    let w = UInt32::alloc(&mut m, Some(val)).unwrap();
    let result = w.big_sigma0(&mut m).unwrap();
    let expected = val.rotate_right(2) ^ val.rotate_right(13) ^ val.rotate_right(22);
    assert_eq!(result.value, Some(expected));
    let inst = R1csInstance::from_matrixifier(m);
    assert!(inst.is_satisfied());
    // Flip a result bit
    if let Boolean::Is(ref rb) = result.bits[0] {
        let cur = result.bits[0].val().unwrap();
        assert!(!inst.satisfied_with_private_set_to(rb.var.get_index(), F::from(!cur)));
    }
}

#[test]
fn uint32_big_sigma1_satisfies_and_constrains() {
    let mut m = ProverMatrixifier::<F>::new();
    let val = 0xABCD1234u32;
    let w = UInt32::alloc(&mut m, Some(val)).unwrap();
    let result = w.big_sigma1(&mut m).unwrap();
    let expected = val.rotate_right(6) ^ val.rotate_right(11) ^ val.rotate_right(25);
    assert_eq!(result.value, Some(expected));
    let inst = R1csInstance::from_matrixifier(m);
    assert!(inst.is_satisfied());
    if let Boolean::Is(ref rb) = result.bits[0] {
        let cur = result.bits[0].val().unwrap();
        assert!(!inst.satisfied_with_private_set_to(rb.var.get_index(), F::from(!cur)));
    }
}

#[test]
fn uint32_chr_word_satisfies_and_constrains() {
    let mut m = ProverMatrixifier::<F>::new();
    let (av, bv, cv) = (0x12345678u32, 0x9ABCDEF0u32, 0x0F0F0F0Fu32);
    let a = UInt32::alloc(&mut m, Some(av)).unwrap();
    let b = UInt32::alloc(&mut m, Some(bv)).unwrap();
    let c = UInt32::alloc(&mut m, Some(cv)).unwrap();
    let result = UInt32::chr_word(&a, &b, &c, &mut m).unwrap();
    let expected = (av & bv) ^ (!av & cv);
    assert_eq!(result.value, Some(expected));
    let inst = R1csInstance::from_matrixifier(m);
    assert!(inst.is_satisfied());
    // Flip a result bit
    if let Boolean::Is(ref rb) = result.bits[4] {
        let cur = result.bits[4].val().unwrap();
        assert!(!inst.satisfied_with_private_set_to(rb.var.get_index(), F::from(!cur)));
    }
}

#[test]
fn uint32_maj_word_satisfies_and_constrains() {
    let mut m = ProverMatrixifier::<F>::new();
    let (av, bv, cv) = (0x12345678u32, 0x9ABCDEF0u32, 0x0F0F0F0Fu32);
    let a = UInt32::alloc(&mut m, Some(av)).unwrap();
    let b = UInt32::alloc(&mut m, Some(bv)).unwrap();
    let c = UInt32::alloc(&mut m, Some(cv)).unwrap();
    let result = UInt32::maj_word(&a, &b, &c, &mut m).unwrap();
    let expected = (av & bv) | (av & cv) | (bv & cv);
    assert_eq!(result.value, Some(expected));
    let inst = R1csInstance::from_matrixifier(m);
    assert!(inst.is_satisfied());
    if let Boolean::Is(ref rb) = result.bits[4] {
        let cur = result.bits[4].val().unwrap();
        assert!(!inst.satisfied_with_private_set_to(rb.var.get_index(), F::from(!cur)));
    }
}
proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    #[test]
    fn uint32_alloc_roundtrip_with_r1cs(val: u32) {
        let mut m = ProverMatrixifier::<F>::new();
        let w = UInt32::alloc(&mut m, Some(val)).unwrap();
        prop_assert_eq!(w.value, Some(val));
        for i in 0..32 {
            let expected = (val >> i) & 1 == 1;
            prop_assert_eq!(w.bits[i].val(), Some(expected));
        }
        let inst = R1csInstance::from_matrixifier(m);
        prop_assert!(inst.is_satisfied());
    }

    #[test]
    fn uint32_rotr_involution(val: u32, shift in 0..32usize) {
        let mut m = ProverMatrixifier::<F>::new();
        let w = UInt32::alloc(&mut m, Some(val)).unwrap();
        let rotated = w.rotr(shift).rotr(32 - shift);
        prop_assert_eq!(rotated.value, Some(val));
    }

    #[test]
    fn uint32_add_matches_wrapping_with_r1cs(a_val: u32, b_val: u32) {
        let mut m = ProverMatrixifier::<F>::new();
        let a = UInt32::alloc(&mut m, Some(a_val)).unwrap();
        let b = UInt32::alloc(&mut m, Some(b_val)).unwrap();
        let result = a.add(&mut m, &b).unwrap();
        prop_assert_eq!(result.value, Some(a_val.wrapping_add(b_val)));
        let inst = R1csInstance::from_matrixifier(m);
        prop_assert!(inst.is_satisfied());
    }

    #[test]
    fn uint32_xor_matches_native_with_r1cs(a_val: u32, b_val: u32) {
        let mut m = ProverMatrixifier::<F>::new();
        let a = UInt32::alloc(&mut m, Some(a_val)).unwrap();
        let b = UInt32::alloc(&mut m, Some(b_val)).unwrap();
        let result = a.xor(&mut m, &b).unwrap();
        prop_assert_eq!(result.value, Some(a_val ^ b_val));
        let inst = R1csInstance::from_matrixifier(m);
        prop_assert!(inst.is_satisfied());
    }

    #[test]
    fn uint32_chr_word_matches_native_with_r1cs(av: u32, bv: u32, cv: u32) {
        let mut m = ProverMatrixifier::<F>::new();
        let a = UInt32::alloc(&mut m, Some(av)).unwrap();
        let b = UInt32::alloc(&mut m, Some(bv)).unwrap();
        let c = UInt32::alloc(&mut m, Some(cv)).unwrap();
        let result = UInt32::chr_word(&a, &b, &c, &mut m).unwrap();
        prop_assert_eq!(result.value, Some((av & bv) ^ (!av & cv)));
        let inst = R1csInstance::from_matrixifier(m);
        prop_assert!(inst.is_satisfied());
    }

    #[test]
    fn uint32_maj_word_matches_native_with_r1cs(av: u32, bv: u32, cv: u32) {
        let mut m = ProverMatrixifier::<F>::new();
        let a = UInt32::alloc(&mut m, Some(av)).unwrap();
        let b = UInt32::alloc(&mut m, Some(bv)).unwrap();
        let c = UInt32::alloc(&mut m, Some(cv)).unwrap();
        let result = UInt32::maj_word(&a, &b, &c, &mut m).unwrap();
        prop_assert_eq!(result.value, Some((av & bv) | (av & cv) | (bv & cv)));
        let inst = R1csInstance::from_matrixifier(m);
        prop_assert!(inst.is_satisfied());
    }
}
