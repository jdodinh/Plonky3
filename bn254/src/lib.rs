//! The scalar field of the BN254 curve, defined as `F_P` where `P = 21888242871839275222246405745257275088548364400416034343698204186575808495617`.
//!
//! This crate provides the standard BN254 field plus two variants with ligetron-specific roots:
//! - [`Bn254`]: Standard Plonky3 BN254 (uses 5^((P-1)/2^28) as two-adic generator)
//! - [`Bn254Root1`]: Uses ligetron's root1 for k and 2k point NTTs
//! - [`Bn254Root2`]: Uses ligetron's root2 for n=4k point NTTs
#![no_std]

extern crate alloc;

mod bn254;
mod bn254_root1;
mod bn254_root2;
mod helpers;
mod poseidon2;

pub use bn254::*;
pub use bn254_root1::Bn254Root1;
pub use bn254_root2::Bn254Root2;
pub use poseidon2::Poseidon2Bn254;
