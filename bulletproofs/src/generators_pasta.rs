#![allow(non_snake_case)]

use crate::hash_to_curve_pasta::{hash_to_pallas, hash_to_vesta};
use crate::{BulletproofGens, PedersenGens};
use alloc::vec::Vec;
use ark_ec::CurveGroup;
use ark_pallas::{Affine as PallasAffine, Projective as PallasProjective};
use ark_vesta::{Affine as VestaAffine, Projective as VestaProjective};

macro_rules! impl_pedersen_gens_new_using_label {
    ($affine_type:ty, $hash_fn:ident, $dst:expr) => {
        impl PedersenGens<$affine_type> {
            /// Creates by hashing the label
            pub fn new_using_label(label: &[u8]) -> Self {
                let dst = $dst;

                let mut input = [label, b"-B"].concat();
                let B = $hash_fn(dst, input.as_ref());
                input.pop();
                input.pop();
                input.extend_from_slice(b"-B_blinding");
                let B_blinding = $hash_fn(dst, input.as_ref());
                Self {
                    B: B.into_affine(),
                    B_blinding: B_blinding.into_affine(),
                }
            }
        }
    };
}

macro_rules! impl_bulletproof_gens_new_using_label {
    ($affine_type:ty, $projective_type:ty, $hash_fn:ident, $dst_g:expr, $dst_h:expr) => {
        impl BulletproofGens<$affine_type> {
            /// Creates by hashing the label. Do not call `increase_capacity` as it doesn't call standard hash to curve
            pub fn new_using_label(
                label: &[u8],
                gens_capacity: usize,
                party_capacity: usize,
            ) -> Self {
                let dst_g = $dst_g;
                let dst_h = $dst_h;
                let mut G_vec = Vec::with_capacity(party_capacity);
                let mut H_vec = Vec::with_capacity(party_capacity);
                for i in 0..party_capacity as u32 {
                    let mut G = Vec::with_capacity(gens_capacity);
                    let mut H = Vec::with_capacity(gens_capacity);
                    let dst_g = [dst_g, i.to_le_bytes().as_slice()].concat();
                    for j in 0..gens_capacity as u32 {
                        G.push($hash_fn(
                            dst_g.as_slice(),
                            &[label, j.to_le_bytes().as_slice()].concat(),
                        ));
                        H.push($hash_fn(
                            dst_h.as_slice(),
                            &[label, j.to_le_bytes().as_slice()].concat(),
                        ));
                    }
                    G_vec.push(<$projective_type>::normalize_batch(&G));
                    H_vec.push(<$projective_type>::normalize_batch(&H));
                }
                Self {
                    gens_capacity,
                    party_capacity,
                    G_vec,
                    H_vec,
                }
            }
        }
    };
}

impl_pedersen_gens_new_using_label!(PallasAffine, hash_to_pallas, b"PedersenGens-Pallas");
impl_pedersen_gens_new_using_label!(VestaAffine, hash_to_vesta, b"PedersenGens-Vesta");

impl_bulletproof_gens_new_using_label!(
    PallasAffine,
    PallasProjective,
    hash_to_pallas,
    b"BulletproofGens-Pallas-G",
    b"BulletproofGens-Pallas-H"
);
impl_bulletproof_gens_new_using_label!(
    VestaAffine,
    VestaProjective,
    hash_to_vesta,
    b"BulletproofGens-Vesta-G",
    b"BulletproofGens-Vesta-H"
);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_aggregated_gens_iter_matches_flat_map {
        ($test_name:ident, $affine_type:ty, $label:expr) => {
            #[test]
            fn $test_name() {
                let gens = BulletproofGens::<$affine_type>::new_using_label($label, 64, 8);

                let helper = |n: usize, m: usize| {
                    let agg_G: Vec<$affine_type> = gens.G(n, m).copied().collect();
                    let flat_G: Vec<$affine_type> = gens
                        .G_vec
                        .iter()
                        .take(m)
                        .flat_map(move |G_j| G_j.iter().take(n))
                        .copied()
                        .collect();

                    let agg_H: Vec<$affine_type> = gens.H(n, m).copied().collect();
                    let flat_H: Vec<$affine_type> = gens
                        .H_vec
                        .iter()
                        .take(m)
                        .flat_map(move |H_j| H_j.iter().take(n))
                        .copied()
                        .collect();

                    assert_eq!(agg_G, flat_G);
                    assert_eq!(agg_H, flat_H);
                };

                helper(64, 8);
                helper(64, 4);
                helper(64, 2);
                helper(64, 1);
                helper(32, 8);
                helper(32, 4);
                helper(32, 2);
                helper(32, 1);
                helper(16, 8);
                helper(16, 4);
                helper(16, 2);
                helper(16, 1);

                // Test that share() method works correctly
                for party in 0..8 {
                    let share = gens.share(party);

                    // Test different sizes for this party's share
                    for n in [16, 32, 64] {
                        let share_G: Vec<$affine_type> = share.G(n).copied().collect();
                        let direct_G: Vec<$affine_type> =
                            gens.G_vec[party].iter().take(n).copied().collect();
                        assert_eq!(
                            share_G, direct_G,
                            "share({}).G({}) doesn't match direct access",
                            party, n
                        );

                        let share_H: Vec<$affine_type> = share.H(n).copied().collect();
                        let direct_H: Vec<$affine_type> =
                            gens.H_vec[party].iter().take(n).copied().collect();
                        assert_eq!(
                            share_H, direct_H,
                            "share({}).H({}) doesn't match direct access",
                            party, n
                        );
                    }
                }
            }
        };
    }

    macro_rules! test_small_gens_match_bigger_gens {
        ($test_name:ident, $affine_type:ty, $label:expr) => {
            #[test]
            fn $test_name() {
                let gens = BulletproofGens::<$affine_type>::new_using_label($label, 64, 8);
                let small_gens = BulletproofGens::<$affine_type>::new_using_label($label, 32, 8);

                // Verify that the first 32 generators in each party match
                for party in 0..8 {
                    let big_G: Vec<$affine_type> =
                        gens.G_vec[party].iter().take(32).copied().collect();
                    let small_G: Vec<$affine_type> =
                        small_gens.G_vec[party].iter().copied().collect();
                    assert_eq!(
                        big_G, small_G,
                        "G generators don't match for party {}",
                        party
                    );

                    let big_H: Vec<$affine_type> =
                        gens.H_vec[party].iter().take(32).copied().collect();
                    let small_H: Vec<$affine_type> =
                        small_gens.H_vec[party].iter().copied().collect();
                    assert_eq!(
                        big_H, small_H,
                        "H generators don't match for party {}",
                        party
                    );
                }
            }
        };
    }

    macro_rules! test_pedersen_gens_new_using_label {
        ($test_name:ident, $affine_type:ty, $label:expr) => {
            #[test]
            fn $test_name() {
                let gens = PedersenGens::<$affine_type>::new_using_label($label);

                // Verify that B and B_blinding are different points
                assert_ne!(
                    gens.B, gens.B_blinding,
                    "B and B_blinding should be different points"
                );

                // Verify that both points are valid (not zero/identity)
                use ark_ec::AffineRepr;
                assert!(!gens.B.is_zero(), "B should not be the zero point");
                assert!(
                    !gens.B_blinding.is_zero(),
                    "B_blinding should not be the zero point"
                );

                // Verify that both points are on the curve
                assert!(gens.B.is_on_curve(), "B should be on the curve");
                assert!(
                    gens.B_blinding.is_on_curve(),
                    "B_blinding should be on the curve"
                );

                // Verify that both points are in the correct subgroup
                assert!(
                    gens.B.is_in_correct_subgroup_assuming_on_curve(),
                    "B should be in correct subgroup"
                );
                assert!(
                    gens.B_blinding.is_in_correct_subgroup_assuming_on_curve(),
                    "B_blinding should be in correct subgroup"
                );
            }
        };
    }

    test_aggregated_gens_iter_matches_flat_map!(
        pallas_aggregated_gens_iter_matches_flat_map,
        PallasAffine,
        b"test-pallas"
    );
    test_aggregated_gens_iter_matches_flat_map!(
        vesta_aggregated_gens_iter_matches_flat_map,
        VestaAffine,
        b"test-vesta"
    );

    test_small_gens_match_bigger_gens!(
        pallas_small_gens_match_bigger_gens,
        PallasAffine,
        b"test-label"
    );
    test_small_gens_match_bigger_gens!(
        vesta_small_gens_match_bigger_gens,
        VestaAffine,
        b"test-label"
    );

    test_pedersen_gens_new_using_label!(
        pallas_pedersen_gens_new_using_label,
        PallasAffine,
        b"test-pedersen-pallas"
    );
    test_pedersen_gens_new_using_label!(
        vesta_pedersen_gens_new_using_label,
        VestaAffine,
        b"test-pedersen-vesta"
    );
}
