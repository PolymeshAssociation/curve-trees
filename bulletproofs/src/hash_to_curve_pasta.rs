//! Transition aliases. Use `HashToCurveConfig::hash_to_curve` from `ark_host_hash_to_curve`.

use ark_host_hash_to_curve::HashToCurveConfig;
use ark_pallas::{PallasConfig, Projective as PallasProjective};
use ark_vesta::{Projective as VestaProjective, VestaConfig};

/// Hash `message` to Pallas, using `dst` as the domain separation tag.
pub fn hash_to_pallas(dst: &[u8], message: &[u8]) -> PallasProjective {
    PallasConfig::hash_to_curve(dst, message).into()
}

/// Hash `message` to Vesta, using `dst` as the domain separation tag.
pub fn hash_to_vesta(dst: &[u8], message: &[u8]) -> VestaProjective {
    VestaConfig::hash_to_curve(dst, message).into()
}
