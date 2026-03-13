//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

extern crate alloc;

use crate::util;
use alloc::vec::Vec;
use ark_ec::hashing::curve_maps::swu::{SWUConfig, SWUMap};
use ark_ec::hashing::map_to_curve_hasher::MapToCurveBasedHasher;
use ark_ec::hashing::HashToCurve;
use ark_ec::short_weierstrass::{Affine as SWAffine, Projective as SWProjective};
use ark_ec::{AffineRepr, VariableBaseMSM, CurveGroup};
use ark_ff::field_hashers::DefaultFieldHasher;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use core::marker::PhantomData;
use ark_helios::HeliosConfig;
use ark_selene::SeleneConfig;
use ark_wei25519::Wei25519Config;
use digest::{ExtendableOutputDirty, Update, XofReader};
use sha2::Sha256;
use sha3::{Sha3XofReader, Shake256};
use ark_pallas::{Affine as PallasAffine, Projective as PallasProjective};
use ark_vesta::{Affine as VestaAffine, Projective as VestaProjective};
use crate::hash_to_curve_pasta::{hash_to_pallas, hash_to_vesta};

/// Represents a pair of base points for Pedersen commitments.
///
/// The Bulletproofs implementation and API is designed to support
/// pluggable bases for Pedersen commitments, so that the choice of
/// bases is not hard-coded.
///
/// The default generators are:
///
/// * `B`: the `ristretto255` basepoint;
/// * `B_blinding`: the result of `ristretto255` SHA3-512 // todo
///
/// hash-to-group on input `B_bytes`.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct PedersenGens<C: AffineRepr> {
    /// Bases for the committed values.
    pub B: C,
    /// Base for the blinding factor.
    pub B_blinding: C,
}

impl<C: AffineRepr> PedersenGens<C> {
    /// Creates a new `PedersenGens` object with the default base points.
    pub fn new() -> Option<Self> {
        let basepoint = C::generator();
        let mut buffer: Vec<u8> = Vec::new();
        basepoint.serialize_compressed(&mut buffer).ok()?;
        Some(PedersenGens {
            B: C::generator(),
            B_blinding: util::affine_from_bytes_tai(&buffer)?,
        })
    }

    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: C::ScalarField, blinding: C::ScalarField) -> C {
        C::Group::msm_unchecked(&[self.B, self.B_blinding], &[value, blinding]).into()
    }
}

/// Marker trait for curves that should use the generic SWU-based `new_using_label`.
pub trait PedersenGensSWU: SWUConfig {}

impl PedersenGensSWU for HeliosConfig {}

impl PedersenGensSWU for SeleneConfig {}

impl PedersenGensSWU for Wei25519Config {}

impl<C: PedersenGensSWU> PedersenGens<SWAffine<C>> {
    /// Creates by hashing the label using SWU algorithm from IETF draft on hash to curve
    pub fn new_using_label(label: &[u8]) -> Self {
        let hasher = MapToCurveBasedHasher::<
            SWProjective<C>,
            DefaultFieldHasher<Sha256, 128>,
            SWUMap<C>,
        >::new(b"PedersenGens")
        .unwrap();

        let mut input = [label, b"-B"].concat();
        let B = hasher.hash(&input).unwrap();

        input.pop();
        input.pop();
        input.extend_from_slice(b"-B_blinding");
        let B_blinding = hasher.hash(&input).unwrap();
        Self { B, B_blinding }
    }
}

impl<C: AffineRepr> Default for PedersenGens<C> {
    fn default() -> Self {
        Self::new().expect("Default PedersenGens should always succeed")
    }
}

/// The `GeneratorsChain` creates an arbitrary-long sequence of
/// orthogonal generators.  The sequence can be deterministically
/// produced starting with an arbitrary point.
struct GeneratorsChain<C: AffineRepr> {
    curve: PhantomData<C>,
    reader: Sha3XofReader,
}

impl<C: AffineRepr> GeneratorsChain<C> {
    /// Creates a chain of generators, determined by the hash of `label`.
    fn new(label: &[u8]) -> Self {
        let mut shake = Shake256::default();
        shake.update(b"GeneratorsChain");
        shake.update(label);

        GeneratorsChain {
            curve: PhantomData,
            reader: shake.finalize_xof_dirty(),
        }
    }

    /// Advances the reader n times, squeezing and discarding
    /// the result.
    fn fast_forward(mut self, n: u32) -> Self {
        for _ in 0..n {
            let mut buf = [0u8; 64];
            self.reader.read(&mut buf);
        }
        self
    }
}

impl<C: AffineRepr> Default for GeneratorsChain<C> {
    fn default() -> Self {
        Self::new(&[])
    }
}

impl<C: AffineRepr> Iterator for GeneratorsChain<C> {
    type Item = C;

    fn next(&mut self) -> Option<Self::Item> {
        let mut uniform_bytes = [0u8; 64];
        self.reader.read(&mut uniform_bytes);

        util::affine_from_bytes_tai(&uniform_bytes)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// The `BulletproofGens` struct contains all the generators needed
/// for aggregating up to `m` range proofs of up to `n` bits each.
///
/// # Extensible Generator Generation
///
/// Instead of constructing a single vector of size `m*n`, as
/// described in the Bulletproofs paper, we construct each party's
/// generators separately.
///
/// To construct an arbitrary-length chain of generators, we apply
/// SHAKE256 to a domain separator label, and feed each 64 bytes of
/// XOF output into the `ristretto255` hash-to-group function.
/// Each of the `m` parties' generators are constructed using a
/// different domain separation label, and proving and verification
/// uses the first `n` elements of the arbitrary-length chain.
///
/// This means that the aggregation size (number of
/// parties) is orthogonal to the rangeproof size (number of bits),
/// and allows using the same `BulletproofGens` object for different
/// proving parameters.
///
/// This construction is also forward-compatible with constraint
/// system proofs, which use a much larger slice of the generator
/// chain, and even forward-compatible to multiparty aggregation of
/// constraint system proofs, since the generators are namespaced by
/// their party index.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BulletproofGens<C: AffineRepr> {
    /// The maximum number of usable generators for each party.
    pub gens_capacity: u32,
    /// Number of values or parties
    pub party_capacity: u32,
    /// Precomputed \\(\mathbf G\\) generators for each party.
    pub(crate) G_vec: Vec<Vec<C>>,
    /// Precomputed \\(\mathbf H\\) generators for each party.
    pub(crate) H_vec: Vec<Vec<C>>,
}

// todo we are not using the multi party stuff
impl<C: AffineRepr> BulletproofGens<C> {
    /// Create a new `BulletproofGens` object.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the number of generators to precompute
    ///    for each party.  For rangeproofs, it is sufficient to pass
    ///    `64`, the maximum bitsize of the rangeproofs.  For circuit
    ///    proofs, the capacity must be greater than the number of
    ///    multipliers, rounded up to the next power of two.
    ///
    /// * `party_capacity` is the maximum number of parties that can
    ///    produce an aggregated proof.
    pub fn new(gens_capacity: u32, party_capacity: u32) -> Self {
        let mut gens = BulletproofGens {
            gens_capacity: 0,
            party_capacity,
            G_vec: (0..party_capacity).map(|_| Vec::new()).collect(),
            H_vec: (0..party_capacity).map(|_| Vec::new()).collect(),
        };
        gens.increase_capacity(gens_capacity);
        gens
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: u32) -> BulletproofGensShare<'_, C> {
        BulletproofGensShare {
            gens: self,
            share: j,
        }
    }

    /// Increases the generators' capacity to the amount specified.
    /// If less than or equal to the current capacity, does nothing.
    fn increase_capacity(&mut self, new_capacity: u32) {
        use byteorder::{ByteOrder, LittleEndian};

        if self.gens_capacity >= new_capacity {
            return;
        }

        for i in 0..self.party_capacity {
            let party_index = i;
            let mut label = [b'G', 0, 0, 0, 0];
            LittleEndian::write_u32(&mut label[1..5], party_index);
            self.G_vec[i as usize].extend(
                &mut GeneratorsChain::<C>::new(&label)
                    .fast_forward(self.gens_capacity)
                    .take((new_capacity - self.gens_capacity) as usize),
            );

            label[0] = b'H';
            self.H_vec[i as usize].extend(
                &mut GeneratorsChain::<C>::new(&label)
                    .fast_forward(self.gens_capacity)
                    .take((new_capacity - self.gens_capacity) as usize),
            );
        }
        self.gens_capacity = new_capacity;
    }

    /// Return an iterator over the aggregation of the parties' G generators with given size `n`.
    pub fn G(&self, n: u32, m: u32) -> impl Iterator<Item = &C> {
        AggregatedGensIter {
            n,
            m,
            array: &self.G_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the aggregation of the parties' H generators with given size `n`.
    pub fn H(&self, n: u32, m: u32) -> impl Iterator<Item = &C> {
        AggregatedGensIter {
            n,
            m,
            array: &self.H_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

/// Marker trait for curves that should use the generic SWU-based `new_using_label`.
pub trait BulletproofGensSWU: SWUConfig {}

impl BulletproofGensSWU for HeliosConfig {}

impl BulletproofGensSWU for SeleneConfig {}

impl BulletproofGensSWU for Wei25519Config {}

impl<C: BulletproofGensSWU> BulletproofGens<SWAffine<C>> {
    /// Creates by hashing the label using SWU algorithm from IETF draft on hash to curve
    pub fn new_using_label(label: &[u8], gens_capacity: u32, party_capacity: u32) -> Self {
        let hasher_g = MapToCurveBasedHasher::<
            SWProjective<C>,
            DefaultFieldHasher<Sha256, 128>,
            SWUMap<C>,
        >::new(b"BulletproofGens-G")
        .unwrap();

        let hasher_h = MapToCurveBasedHasher::<
            SWProjective<C>,
            DefaultFieldHasher<Sha256, 128>,
            SWUMap<C>,
        >::new(b"BulletproofGens-H")
        .unwrap();

        let mut G_vec = Vec::with_capacity(party_capacity as usize);
        let mut H_vec = Vec::with_capacity(party_capacity as usize);

        for i in 0..party_capacity {
            let mut G = Vec::with_capacity(gens_capacity as usize);
            let mut H = Vec::with_capacity(gens_capacity as usize);

            for j in 0..gens_capacity {
                let input = [
                    label,
                    i.to_le_bytes().as_slice(),
                    j.to_le_bytes().as_slice(),
                ]
                .concat();

                G.push(hasher_g.hash(&input).unwrap());
                H.push(hasher_h.hash(&input).unwrap());
            }

            G_vec.push(G);
            H_vec.push(H);
        }

        Self {
            gens_capacity,
            party_capacity,
            G_vec,
            H_vec,
        }
    }
}

struct AggregatedGensIter<'a, C: AffineRepr> {
    array: &'a Vec<Vec<C>>,
    n: u32,
    m: u32,
    party_idx: u32,
    gen_idx: u32,
}

impl<'a, C: AffineRepr> Iterator for AggregatedGensIter<'a, C> {
    type Item = &'a C;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            self.gen_idx = 0;
            self.party_idx += 1;
        }

        if self.party_idx >= self.m {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[self.party_idx as usize][cur_gen as usize])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.n * (self.m - self.party_idx) - self.gen_idx;
        let size = remaining as usize;
        (size, Some(size))
    }
}

/// Represents a view of the generators used by a specific party in an
/// aggregated proof.
///
/// The `BulletproofGens` struct represents generators for an aggregated
/// range proof `m` proofs of `n` bits each; the `BulletproofGensShare`
/// provides a view of the generators for one of the `m` parties' shares.
///
/// The `BulletproofGensShare` is produced by [`BulletproofGens::share()`].
#[derive(Copy, Clone)]
pub struct BulletproofGensShare<'a, C: AffineRepr> {
    /// The parent object that this is a view into
    gens: &'a BulletproofGens<C>,
    /// Which share we are
    share: u32,
}

impl<'a, C: AffineRepr> BulletproofGensShare<'a, C> {
    /// Return an iterator over this party's G generators with given size `n`.
    pub fn G(&self, n: u32) -> impl Iterator<Item = &'a C> {
        self.gens.G_vec[self.share as usize].iter().take(n as usize)
    }

    /// Return an iterator over this party's H generators with given size `n`.
    pub(crate) fn H(&self, n: u32) -> impl Iterator<Item = &'a C> {
        self.gens.H_vec[self.share as usize].iter().take(n as usize)
    }
}

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
            pub fn new_using_label(label: &[u8], gens_capacity: u32, party_capacity: u32) -> Self {
                let dst_g = $dst_g;
                let dst_h = $dst_h;
                let mut G_vec = Vec::with_capacity(party_capacity as usize);
                let mut H_vec = Vec::with_capacity(party_capacity as usize);
                for i in 0..party_capacity as u32 {
                    let mut G = Vec::with_capacity(gens_capacity as usize);
                    let mut H = Vec::with_capacity(gens_capacity as usize);
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
    use ark_ec::AffineRepr;
    use ark_helios::{Affine as HeliosAffine};
    use ark_selene::{Affine as SeleneAffine};
    use ark_wei25519::{Affine as Wei25519Affine};
    use ark_pallas::*;

    #[test]
    fn ped_gens_label() {
        fn check<C: PedersenGensSWU>(label: &[u8]) {
            let gens = PedersenGens::<SWAffine<C>>::new_using_label(label);
            assert!(!gens.B.is_zero());
            assert!(gens.B.is_on_curve());
            assert!(!gens.B_blinding.is_zero());
            assert!(gens.B_blinding.is_on_curve());
            assert!(gens.B != gens.B_blinding);
        }

        let label = b"test";

        check::<HeliosConfig>(label);
        check::<SeleneConfig>(label);
        check::<Wei25519Config>(label);
    }

    #[test]
    fn aggregated_gens_iter_matches_flat_map() {
        let gens = BulletproofGens::<Affine>::new(64, 8);

        let helper = |n: u32, m: u32| {
            let agg_G: Vec<Affine> = gens.G(n, m).copied().collect();
            let flat_G: Vec<Affine> = gens
                .G_vec
                .iter()
                .take(m as usize)
                .flat_map(move |G_j| G_j.iter().take(n as usize))
                .copied()
                .collect();

            let agg_H: Vec<Affine> = gens.H(n, m).copied().collect();
            let flat_H: Vec<Affine> = gens
                .H_vec
                .iter()
                .take(m as usize)
                .flat_map(move |H_j| H_j.iter().take(n as usize))
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
    }

    #[test]
    fn resizing_small_gens_matches_creating_bigger_gens() {
        let gens = BulletproofGens::<Affine>::new(64, 8);

        let mut gen_resized = BulletproofGens::<Affine>::new(32, 8);
        gen_resized.increase_capacity(64);

        let helper = |n: u32, m: u32| {
            let gens_G: Vec<Affine> = gens.G(n, m).copied().collect();
            let gens_H: Vec<Affine> = gens.H(n, m).copied().collect();

            let resized_G: Vec<Affine> = gen_resized.G(n, m).copied().collect();
            let resized_H: Vec<Affine> = gen_resized.H(n, m).copied().collect();

            assert_eq!(gens_G, resized_G);
            assert_eq!(gens_H, resized_H);
        };

        helper(64, 8);
        helper(32, 8);
        helper(16, 8);
    }

    macro_rules! test_aggregated_gens_iter_matches_flat_map {
        ($test_name:ident, $affine_type:ty, $label:expr) => {
            #[test]
            fn $test_name() {
                let gens = BulletproofGens::<$affine_type>::new_using_label($label, 64, 8);

                let helper = |n: u32, m: u32| {
                    let agg_G: Vec<$affine_type> = gens.G(n, m).copied().collect();
                    let flat_G: Vec<$affine_type> = gens
                        .G_vec
                        .iter()
                        .take(m as usize)
                        .flat_map(move |G_j| G_j.iter().take(n as usize))
                        .copied()
                        .collect();

                    let agg_H: Vec<$affine_type> = gens.H(n, m).copied().collect();
                    let flat_H: Vec<$affine_type> = gens
                        .H_vec
                        .iter()
                        .take(m as usize)
                        .flat_map(move |H_j| H_j.iter().take(n as usize))
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
                        let direct_G: Vec<$affine_type> = gens.G_vec[party as usize]
                            .iter()
                            .take(n as usize)
                            .copied()
                            .collect();
                        assert_eq!(
                            share_G, direct_G,
                            "share({}).G({}) doesn't match direct access",
                            party, n
                        );

                        let share_H: Vec<$affine_type> = share.H(n).copied().collect();
                        let direct_H: Vec<$affine_type> = gens.H_vec[party as usize]
                            .iter()
                            .take(n as usize)
                            .copied()
                            .collect();
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

    test_aggregated_gens_iter_matches_flat_map!(
        helios_aggregated_gens_iter_matches_flat_map,
        HeliosAffine,
        b"test-helios"
    );
    test_small_gens_match_bigger_gens!(
        helios_small_gens_match_bigger_gens,
        HeliosAffine,
        b"test-label"
    );
    test_pedersen_gens_new_using_label!(
        helios_pedersen_gens_new_using_label,
        HeliosAffine,
        b"test-pedersen-helios"
    );

    test_aggregated_gens_iter_matches_flat_map!(
        selene_aggregated_gens_iter_matches_flat_map,
        SeleneAffine,
        b"test-selene"
    );
    test_small_gens_match_bigger_gens!(
        selene_small_gens_match_bigger_gens,
        SeleneAffine,
        b"test-label"
    );
    test_pedersen_gens_new_using_label!(
        selene_pedersen_gens_new_using_label,
        SeleneAffine,
        b"test-pedersen-selene"
    );

    test_aggregated_gens_iter_matches_flat_map!(
        wei25519_aggregated_gens_iter_matches_flat_map,
        Wei25519Affine,
        b"test-wei25519"
    );
    test_small_gens_match_bigger_gens!(
        wei25519_small_gens_match_bigger_gens,
        Wei25519Affine,
        b"test-label"
    );
    test_pedersen_gens_new_using_label!(
        wei25519_pedersen_gens_new_using_label,
        Wei25519Affine,
        b"test-pedersen-wei25519"
    );
}
