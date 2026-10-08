#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod util;

pub mod errors;
pub mod generators;
pub mod inner_product_proof;
pub mod inner_product_proof_alt;
pub mod msm;
pub mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::util::affine_from_bytes_tai;

pub mod hash_to_curve_pasta;
pub mod r1cs;

/// Transition alias for the host function. Use `ark_host_hash_to_curve_impl::host_batch_hash_to_curve`.
#[cfg(feature = "impl_host_hash_to_curve")]
pub use ark_host_hash_to_curve_impl::host_batch_hash_to_curve as batch_hash_to_curve;
