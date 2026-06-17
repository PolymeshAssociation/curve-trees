#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod util;

pub mod errors;
pub mod generators;
pub mod inner_product_proof;
pub mod msm;
pub mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::util::affine_from_bytes_tai;

pub mod hash_to_curve_pasta;
pub mod r1cs;

#[cfg(any(
    all(not(feature = "std"), feature = "host_hash_to_curve"),
    feature = "impl_host_hash_to_curve"
))]
pub mod host_hash_to_curve;
#[cfg(any(
    all(not(feature = "std"), feature = "host_hash_to_curve"),
    feature = "impl_host_hash_to_curve"
))]
pub use host_hash_to_curve::host_fn::*;
