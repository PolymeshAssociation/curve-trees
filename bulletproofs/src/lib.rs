#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod util;

pub mod errors;
pub mod generators;
mod inner_product_proof;
mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::util::affine_from_bytes_tai;

pub mod generators_pasta;
pub mod hash_to_curve_pasta;
pub mod r1cs;
