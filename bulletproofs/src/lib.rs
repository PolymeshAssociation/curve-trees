#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod util;

pub mod errors;
pub mod generators;
pub mod inner_product_proof;
pub mod transcript;

pub use crate::errors::ProofError;
pub use crate::generators::{BulletproofGens, BulletproofGensShare, PedersenGens};
pub use crate::util::affine_from_bytes_tai;

pub mod hash_to_curve_pasta;
pub mod r1cs;
