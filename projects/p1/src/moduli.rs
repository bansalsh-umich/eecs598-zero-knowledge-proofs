/// This module defines type-level moduli. You can feel free to add more moduli
/// here for testing purposes, but there is no need for student modifications to this file.
use sfs_bigint::{U256, U512};
/// Represents a (prime) modulus at the type level. New moduli should be constructed via
/// `declare_const_modulus!` macro.
///
/// However, one must ensure that any such modulus is in fact prime.
pub trait PrimeModulus: Send + Sync + 'static {
    /// actual value of the modulus
    const VALUE: U256;

    // (VALUE - 1) / 2
    // `const` traits are not stable in rust yet, so we can't compute (VALUE - 1) / 2 in a const
    // context.
    // the best we can do is write a function that will compute (p-1)/2 exactly once
    fn legendre_exponent() -> &'static U256;

    // Montgomery constants (r = 2^256)
    //
    // Precomputed once per modulus (via LazyLock) and cached for the lifetime
    // of the program. Used by MontgomeryZq for fast modular multiplication.
    //
    // We choose r = 2^256 so that "mod r" is free (just take low 256 bits)
    // and "/ r" is free (just take high 256 bits of a U512). Every prime
    // modulus n is odd, so gcd(n, 2^256) = 1 as required.

    /// n' = n^(-1) mod 2^256.
    ///
    /// Used in REDC (Montgomery reduction) to find a multiple of n that
    /// cancels the low 256 bits of a product, so that dividing by r becomes
    /// a simple bit-shift rather than an expensive division by n.
    ///
    /// Computed via Newton's method, starting from n·1 ≡ 1 (mod 2¹):
    ///   inv ← inv · (2 − n · inv)    [all wrapping mod 2^256]
    /// Each iteration doubles the number of correct bits, so 8 iterations
    /// (1 → 2 → 4 → 8 → 16 → 32 → 64 → 128 → 256) suffice.
    fn montgomery_n_prime() -> &'static U256;

    /// r mod n = 2^256 mod n.
    ///
    /// This is the Montgomery representation of 1 (since 1·r mod n = r mod n),
    /// and serves as the multiplicative identity in Montgomery space.
    fn montgomery_r_mod_n() -> &'static U256;

    /// r² mod n = (2^256)² mod n.
    ///
    /// Used to convert a normal value x into Montgomery space efficiently:
    ///   x̄ = REDC(x · r²) = x · r² · r⁻¹ mod n = x · r mod n
    /// so one REDC call replaces what would otherwise be a full modular
    /// reduction of a 512-bit shifted value.
    fn montgomery_r2_mod_n() -> &'static U256;
}

#[macro_export]
macro_rules! declare_const_modulus {
    // INVARIANT: Modulus should be prime!
    ($mod_name: ident, $value_str:expr) => {
        declare_const_modulus!($mod_name, $value_str, 10);
    };
    ($mod_name:ident, $value_str:expr, $radix:expr) => {
        pub enum $mod_name {}

        impl $crate::moduli::PrimeModulus for $mod_name {
            const VALUE: sfs_bigint::U256 =
                sfs_bigint::U256::from_str_radix_const($value_str, $radix);
            fn legendre_exponent() -> &'static sfs_bigint::U256 {
                static LEGENDRE_EXPONENT: std::sync::LazyLock<sfs_bigint::U256> =
                    std::sync::LazyLock::new(|| {
                        (<$mod_name as $crate::moduli::PrimeModulus>::VALUE - 1.into()) / 2.into()
                    });
                &LEGENDRE_EXPONENT
            }

            fn montgomery_n_prime() -> &'static sfs_bigint::U256 {
                static N_PRIME: std::sync::LazyLock<sfs_bigint::U256> =
                    std::sync::LazyLock::new(|| {
                        use num_traits::One;
                        let n = <$mod_name as $crate::moduli::PrimeModulus>::VALUE;
                        // Newton's method for n⁻¹ mod 2^256.
                        // Invariant: after iteration i, n·inv ≡ 1 (mod 2^(2^i)).
                        // All arithmetic wraps mod 2^256 by taking the low half of
                        // widening products and ignoring borrow on subtraction.
                        let mut inv = sfs_bigint::U256::one();
                        for _ in 0..8 {
                            // product = n · inv  (mod 2^256)
                            let product = n.widening_mul(&inv).split().0;
                            // two_minus = 2 − product  (mod 2^256)
                            let two_minus = sfs_bigint::U256::from(2u64).borrowing_sub(&product).0;
                            // inv = inv · (2 − n·inv)  (mod 2^256)
                            inv = inv.widening_mul(&two_minus).split().0;
                        }
                        inv
                    });
                &N_PRIME
            }

            fn montgomery_r_mod_n() -> &'static sfs_bigint::U256 {
                static R_MOD_N: std::sync::LazyLock<sfs_bigint::U256> =
                    std::sync::LazyLock::new(|| {
                        use num_traits::One;
                        let n = <$mod_name as $crate::moduli::PrimeModulus>::VALUE;
                        // r mod n = 2^256 mod n.
                        // U256::MAX = 2^256 − 1, so (2^256 − 1) % n + 1 = 2^256 % n.
                        // Safe: n is an odd prime > 1, so 2^256 mod n ∈ [1, n−1],
                        // meaning the +1 never reaches n.
                        sfs_bigint::U256::MAX % n + sfs_bigint::U256::one()
                    });
                &R_MOD_N
            }

            fn montgomery_r2_mod_n() -> &'static sfs_bigint::U256 {
                static R2_MOD_N: std::sync::LazyLock<sfs_bigint::U256> =
                    std::sync::LazyLock::new(|| {
                        let n = <$mod_name as $crate::moduli::PrimeModulus>::VALUE;
                        let r_mod_n = *<$mod_name as $crate::moduli::PrimeModulus>::montgomery_r_mod_n();
                        // r² mod n = (r mod n)² mod n.
                        // Widening multiply gives the full 512-bit product,
                        // then reduce mod n (as a U512) and take the low half.
                        let product = r_mod_n.widening_mul(&r_mod_n);
                        (product % sfs_bigint::U512::from(n)).split().0
                    });
                &R2_MOD_N
            }
        }
    };
}

declare_const_modulus!(
    Ed25519,
    "57896044618658097711785492504343953926634992332820282019728792003956564819949"
);

// Useful for testing
declare_const_modulus!(Thirteen, "13");
//This is 3 mod 4 so use easy sqrt
declare_const_modulus!(
    P256,
    "115792089210356248762697446949407573530086143415290314195533631308867097853951"
);
//This is equal to one mod 4, so tonelli-shanks
declare_const_modulus!(
    P256CurveOrder,
    "115792089210356248762697446949407573529996955224135760342422259061068512044369"
);
