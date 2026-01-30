//! BN254 field element with ligetron's root1 as the two-adic generator.
//!
//! This type is identical to [`Bn254`](super::Bn254) except it uses a different
//! primitive 2^28-th root of unity. Ligetron uses root1 for k and 2k point NTTs.

use alloc::vec::Vec;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use core::{array, fmt, stringify};

use num_bigint::BigUint;
use p3_field::integers::QuotientMap;
use p3_field::op_assign_macros::{
    impl_add_assign, impl_div_methods, impl_mul_methods, impl_sub_assign, ring_sum,
};
use p3_field::{
    Field, InjectiveMonomial, Packable, PrimeCharacteristicRing, PrimeField, RawDataSerializable,
    TwoAdicField, quotient_map_small_int,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Deserializer, Serialize};

use crate::bn254::{BN254_MONTY_R_SQ, BN254_PRIME};
use crate::helpers::{
    gcd_inversion, halve_bn254, monty_mul, to_biguint, wrapping_add, wrapping_sub,
};

/// The BN254 curve scalar field with ligetron's root1 as the two-adic generator.
///
/// This is the same field as [`Bn254`](super::Bn254), but with a different primitive
/// 2^28-th root of unity. Ligetron uses root1 for k and 2k point NTTs.
#[derive(Copy, Clone, Default, Eq, PartialEq)]
#[must_use]
pub struct Bn254Root1 {
    /// The MONTY form of the field element, a 254-bit integer less than `P` saved as a collection of u64's using a little-endian order.
    pub(crate) value: [u64; 4],
}

impl Bn254Root1 {
    /// Create a new field element from any `[u64; 4]` in little-endian limb order.
    ///
    /// Any value is accepted and automatically reduced modulo P.
    #[inline]
    pub const fn new(value: [u64; 4]) -> Self {
        Self::new_monty(monty_mul(BN254_MONTY_R_SQ, value))
    }

    /// Convert a `[[u64; 4]; N]` array to an array of field elements.
    ///
    /// Const version of `input.map(Bn254Root1::new)`.
    #[inline]
    pub const fn new_array<const N: usize>(input: [[u64; 4]; N]) -> [Self; N] {
        let mut output = [Self::ZERO; N];
        let mut i = 0;
        while i < N {
            output[i] = Self::new(input[i]);
            i += 1;
        }
        output
    }

    /// Creates a new Bn254Root1 field element from an array of 4 u64's.
    ///
    /// The array is assumed to correspond to a 254-bit integer less than P and is interpreted as
    /// already being in Montgomery form.
    #[inline]
    pub(crate) const fn new_monty(value: [u64; 4]) -> Self {
        Self { value }
    }

    #[inline]
    #[allow(clippy::needless_pass_by_value)]
    pub fn from_biguint(value: BigUint) -> Option<Self> {
        let digits = value.to_u64_digits();
        let num_dig = digits.len();

        match num_dig {
            0 => Some(Self::ZERO),
            1..=4 => {
                let mut inner = [0; 4];
                inner[..num_dig].copy_from_slice(&digits);
                Some(Self::new_monty(monty_mul(BN254_MONTY_R_SQ, inner)))
            }
            _ => None,
        }
    }

    /// Converts the a byte array in little-endian order to a field element.
    ///
    /// Assumes the bytes correspond to the Montgomery form of the desired field element.
    ///
    /// Returns None if the byte array is not exactly 32 bytes long or if the value
    /// represented by the byte array is not less than the BN254 prime.
    #[inline]
    pub(crate) fn from_bytes_monty(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 32 {
            return None;
        }
        let value: [u64; 4] = array::from_fn(|i| {
            let start = i * 8;
            let end = start + 8;
            u64::from_le_bytes(bytes[start..end].try_into().unwrap())
        });
        if value.iter().rev().cmp(BN254_PRIME.iter().rev()) == core::cmp::Ordering::Less {
            Some(Self::new_monty(value))
        } else {
            None
        }
    }
}

impl Serialize for Bn254Root1 {
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.into_bytes())
    }
}

impl<'de> Deserialize<'de> for Bn254Root1 {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Deserialize::deserialize(d)?;
        Self::from_bytes_monty(&bytes)
            .ok_or_else(|| serde::de::Error::custom("Invalid field element"))
    }
}

impl Packable for Bn254Root1 {}

impl Hash for Bn254Root1 {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        for byte in self.value.as_ref() {
            state.write_u64(*byte);
        }
    }
}

impl Ord for Bn254Root1 {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.value.iter().rev().cmp(other.value.iter().rev())
    }
}

impl PartialOrd for Bn254Root1 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Bn254Root1 {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        core::fmt::Display::fmt(&self.as_canonical_biguint(), f)
    }
}

impl Debug for Bn254Root1 {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        core::fmt::Debug::fmt(&self.as_canonical_biguint(), f)
    }
}

impl PrimeCharacteristicRing for Bn254Root1 {
    type PrimeSubfield = Self;

    const ZERO: Self = Self::new_monty([0, 0, 0, 0]);

    const ONE: Self = Self::new_monty([
        0xac96341c4ffffffb,
        0x36fc76959f60cd29,
        0x666ea36f7879462e,
        0x0e0a77c19a07df2f,
    ]);

    const TWO: Self = Self::new_monty([
        0x592c68389ffffff6,
        0x6df8ed2b3ec19a53,
        0xccdd46def0f28c5c,
        0x1c14ef83340fbe5e,
    ]);

    const NEG_ONE: Self = Self::new_monty([
        0x974bc177a0000006,
        0xf13771b2da58a367,
        0x51e1a2470908122e,
        0x2259d6b14729c0fa,
    ]);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new_monty(halve_bn254(self.value))
    }
}

impl InjectiveMonomial<5> for Bn254Root1 {}

impl RawDataSerializable for Bn254Root1 {
    const NUM_BYTES: usize = 32;

    #[allow(refining_impl_trait)]
    #[inline]
    fn into_bytes(self) -> [u8; 32] {
        unsafe { transmute(self.value.map(|x| x.to_le_bytes())) }
    }

    #[inline]
    fn into_u32_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u32> {
        input.into_iter().flat_map(|x| {
            x.value
                .into_iter()
                .flat_map(|digit| [digit as u32, (digit >> 32) as u32])
        })
    }

    #[inline]
    fn into_u64_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u64> {
        input.into_iter().flat_map(|x| x.value)
    }

    #[inline]
    fn into_parallel_byte_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u8; N]> {
        input.into_iter().flat_map(|vector| {
            let bytes = vector.map(|elem| elem.into_bytes());
            (0..Self::NUM_BYTES).map(move |i| array::from_fn(|j| bytes[j][i]))
        })
    }

    #[inline]
    fn into_parallel_u32_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u32; N]> {
        input.into_iter().flat_map(|vector| {
            let u32s: [[u32; 8]; N] = vector
                .map(|elem| unsafe { transmute(elem.value.map(|x| [x as u32, (x >> 32) as u32])) });
            (0..(Self::NUM_BYTES / 4)).map(move |i| array::from_fn(|j| u32s[j][i]))
        })
    }

    #[inline]
    fn into_parallel_u64_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u64; N]> {
        input.into_iter().flat_map(|vector| {
            let u64s = vector.map(|elem| elem.value);
            (0..(Self::NUM_BYTES / 8)).map(move |i| array::from_fn(|j| u64s[j][i]))
        })
    }
}

impl Field for Bn254Root1 {
    type Packing = Self;

    const GENERATOR: Self = Self::new_monty([
        0x1b0d0ef99fffffe6,
        0xeaba68a3a32a913f,
        0x47d8eb76d8dd0689,
        0x15d0085520f5bbc3,
    ]);

    #[inline]
    fn is_zero(&self) -> bool {
        self.value.iter().all(|&x| x == 0)
    }

    #[inline]
    fn try_inverse(&self) -> Option<Self> {
        (!self.is_zero()).then(|| Self::new_monty(gcd_inversion(self.value)))
    }

    #[inline]
    fn order() -> BigUint {
        to_biguint(BN254_PRIME)
    }
}

quotient_map_small_int!(Bn254Root1, u128, [u8, u16, u32, u64]);
quotient_map_small_int!(Bn254Root1, i128, [i8, i16, i32, i64]);

impl QuotientMap<u128> for Bn254Root1 {
    #[inline]
    fn from_int(int: u128) -> Self {
        let monty_form = monty_mul(BN254_MONTY_R_SQ, [int as u64, (int >> 64) as u64, 0, 0]);
        Self::new_monty(monty_form)
    }

    #[inline]
    fn from_canonical_checked(int: u128) -> Option<Self> {
        Some(Self::from_int(int))
    }

    #[inline]
    unsafe fn from_canonical_unchecked(int: u128) -> Self {
        Self::from_int(int)
    }
}

impl QuotientMap<i128> for Bn254Root1 {
    #[inline]
    fn from_int(int: i128) -> Self {
        if int >= 0 {
            Self::from_int(int as u128)
        } else {
            -Self::from_int((-int) as u128)
        }
    }

    #[inline]
    fn from_canonical_checked(int: i128) -> Option<Self> {
        Some(Self::from_int(int))
    }

    #[inline]
    unsafe fn from_canonical_unchecked(int: i128) -> Self {
        Self::from_int(int)
    }
}

impl PrimeField for Bn254Root1 {
    #[inline]
    fn as_canonical_biguint(&self) -> BigUint {
        let out_val = monty_mul(self.value, [1, 0, 0, 0]);
        to_biguint(out_val)
    }
}

impl Add for Bn254Root1 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.value;
        let rhs = rhs.value;

        let (sum, overflow) = wrapping_add(lhs, rhs);
        debug_assert!(!overflow);

        let (sum_corr, underflow) = wrapping_sub(sum, BN254_PRIME);

        if underflow {
            Self::new_monty(sum)
        } else {
            Self::new_monty(sum_corr)
        }
    }
}

impl Sub for Bn254Root1 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.value;
        let rhs = rhs.value;

        let (mut sub, underflow) = wrapping_sub(lhs, rhs);

        if underflow {
            (sub, _) = wrapping_add(sub, BN254_PRIME);
        }

        Self::new_monty(sub)
    }
}

impl Neg for Bn254Root1 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::ZERO - self
    }
}

impl Mul for Bn254Root1 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::new_monty(monty_mul(self.value, rhs.value))
    }
}

impl_add_assign!(Bn254Root1);
impl_sub_assign!(Bn254Root1);
impl_mul_methods!(Bn254Root1);
ring_sum!(Bn254Root1);
impl_div_methods!(Bn254Root1, Bn254Root1);

impl Distribution<Bn254Root1> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Bn254Root1 {
        loop {
            let mut trial_element: [u8; 32] = rng.random();
            trial_element[31] &= (1_u8 << 6) - 1;
            let x = Bn254Root1::from_bytes_monty(&trial_element);
            if let Some(val) = x {
                return val;
            }
        }
    }
}

/// TWO_ADIC_GENERATOR is the primitive 2^28-th root of unity used by ligetron (root1).
///
/// Ligetron uses root1 for k and 2k point NTTs.
///
/// Standard form: 1748695177688661943023146337482803886740723238769601073607632802312037301404
/// Montgomery form: 13302640224962090080372469718276213809319545764099277440601762868024527421112
///
/// Verification in SageMath:
/// ```sage
/// P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
/// R = 2^256
/// root1_standard = 1748695177688661943023146337482803886740723238769601073607632802312037301404
/// root1_montgomery = (root1_standard * R) % P
/// assert root1_montgomery == 13302640224962090080372469718276213809319545764099277440601762868024527421112
/// assert pow(root1_standard, 2^28, P) == 1
/// assert pow(root1_standard, 2^27, P) == P - 1
/// ```
const TWO_ADIC_GENERATOR: [u64; 4] = [
    0x9632c7c5b639feb8,
    0x985ce3400d0ff299,
    0xb2dd880001b0ecd8,
    0x1d69070d6d98ce29,
];

impl TwoAdicField for Bn254Root1 {
    const TWO_ADICITY: usize = 28;

    #[inline]
    fn two_adic_generator(bits: usize) -> Self {
        let mut omega = Self::new_monty(TWO_ADIC_GENERATOR);
        for _ in bits..Self::TWO_ADICITY {
            omega = omega.square();
        }
        omega
    }
}

#[cfg(test)]
mod tests {
    use p3_field_testing::{test_field, test_field_json_serialization, test_prime_field};

    use super::*;
    use crate::helpers::to_biguint;

    type F = Bn254Root1;

    #[test]
    fn test_bn254_root1() {
        let big_int_100 = BigUint::from(100u32);
        let big_int_p = to_biguint(BN254_PRIME);
        let big_int_2_256_min_1 = to_biguint([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
        ]);
        let big_int_2_256_mod_p = to_biguint([
            0xac96341c4ffffffb,
            0x36fc76959f60cd29,
            0x666ea36f7879462e,
            0x0e0a77c19a07df2f,
        ]);

        let f_100 = F::from_biguint(big_int_100.clone()).unwrap();
        assert_eq!(f_100.as_canonical_biguint(), BigUint::from(100u32));
        assert_eq!(F::from_biguint(BigUint::ZERO), Some(F::ZERO));
        for i in 0_u32..6_u32 {
            assert_eq!(F::from_biguint(big_int_p.clone() * i), Some(F::ZERO));
            assert_eq!(
                F::from_biguint((big_int_100.clone() + big_int_p.clone()) * i),
                Some(f_100 * F::from_int(i))
            );
        }
        assert_eq!(F::from_biguint(big_int_p * 6_u32), None);
        assert_eq!(
            F::from_biguint(big_int_2_256_min_1).unwrap(),
            F::NEG_ONE + F::from_biguint(big_int_2_256_mod_p).unwrap()
        );

        let expected_multiplicative_group_generator = F::from_u8(5);
        assert_eq!(F::GENERATOR, expected_multiplicative_group_generator);
        assert_eq!(F::GENERATOR.as_canonical_biguint(), BigUint::from(5u32));

        let f_1 = F::ONE;
        let f_2 = F::TWO;
        let f_r_minus_1 = F::NEG_ONE;
        let f_r_minus_2 = F::NEG_ONE + F::NEG_ONE;

        test_field_json_serialization(&[f_100, f_1, f_2, f_r_minus_1, f_r_minus_2]);
    }

    const ZERO: Bn254Root1 = Bn254Root1::ZERO;
    const ONE: Bn254Root1 = Bn254Root1::ONE;

    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 10] {
        [
            (BigUint::from(2u8), 28),
            (BigUint::from(3u8), 2),
            (BigUint::from(13u8), 1),
            (BigUint::from(29u8), 1),
            (BigUint::from(983u16), 1),
            (BigUint::from(11003u16), 1),
            (BigUint::from(237073u32), 1),
            (BigUint::from(405928799u32), 1),
            (BigUint::from(1670836401704629u64), 1),
            (BigUint::from(13818364434197438864469338081u128), 1),
        ]
    }
    test_field!(
        crate::Bn254Root1,
        &[super::ZERO],
        &[super::ONE],
        &super::multiplicative_group_prime_factorization()
    );

    test_prime_field!(crate::Bn254Root1);
}

#[cfg(test)]
mod ligetron_compat_tests {
    use super::*;
    use p3_field::TwoAdicField;

    #[test]
    fn test_two_adic_generator_is_root_of_unity() {
        let omega = Bn254Root1::two_adic_generator(28);

        // omega^(2^28) should equal 1
        let mut result = omega;
        for _ in 0..28 {
            result = result.square();
        }
        assert_eq!(result, Bn254Root1::ONE, "omega^(2^28) should be 1");

        // omega^(2^27) should NOT equal 1 (primitive root test)
        let mut half_result = omega;
        for _ in 0..27 {
            half_result = half_result.square();
        }
        assert_ne!(
            half_result,
            Bn254Root1::ONE,
            "omega^(2^27) should NOT be 1 (primitive root)"
        );

        assert_eq!(
            half_result,
            Bn254Root1::NEG_ONE,
            "omega^(2^27) should be -1"
        );
    }

    #[test]
    fn test_two_adic_generator_matches_ligetron_root1() {
        // Ligetron's root1 in standard form
        let ligetron_root1_standard = BigUint::parse_bytes(
            b"1748695177688661943023146337482803886740723238769601073607632802312037301404",
            10,
        )
        .unwrap();

        let omega = Bn254Root1::two_adic_generator(28);

        let our_standard = omega.as_canonical_biguint();
        assert_eq!(
            our_standard, ligetron_root1_standard,
            "Our generator should match ligetron's root1"
        );
    }
}
