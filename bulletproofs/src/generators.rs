//! The `generators` module contains API for producing a
//! set of generators for a rangeproof.

#![allow(non_snake_case)]
#![deny(missing_docs)]

extern crate alloc;

use crate::util;
use alloc::vec::Vec;
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use core::marker::PhantomData;
// use ark_ec::hashing::curve_maps::swu::SWUConfig;
// use ark_ec::hashing::HashToCurve;
use digest::{ExtendableOutputDirty, Update, XofReader};
use sha3::{Sha3XofReader, Shake256};
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

    // /// Creates by hashing the label
    // pub fn new_using_label(label: &[u8]) -> Self where C::Config: SWUConfig {
    //     // Initialize the SWU-based hash-to-curve hasher
    //     let hasher = MapToCurveBasedHasher::<
    //         SWProjective<C::Config>,
    //         // DefaultFieldHasher<sha3::Sha3_256, 128>,
    //         DefaultFieldHasher<Sha256, 128>,
    //         SWUMap<C::Config>,
    //     >::new(b"PedersenGens").expect("Failed to initialize SWU hash-to-curve");
    //
    //     let mut input = [label, b"-B"].concat();
    //     let B = hasher.hash(&input).unwrap();
    //
    //     input.pop();
    //     input.pop();
    //     input.extend_from_slice(b"-B_blinding");
    //     let B_blinding = hasher.hash(&input).unwrap();
    //     Self {B, B_blinding}
    // }

    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: C::ScalarField, blinding: C::ScalarField) -> C {
        C::Group::msm_unchecked(&[self.B, self.B_blinding], &[value, blinding]).into()
    }
}

// impl<C: SWUConfig> PedersenGens<SWAffine<C>>
// {
//     /// Creates by hashing the label
//     pub fn new_using_label(label: &[u8]) -> Self {
//         let hasher = MapToCurveBasedHasher::<
//             SWProjective<C>,
//             DefaultFieldHasher<Sha256, 128>,
//             SWUMap<C>,
//         >::new(b"PedersenGens").unwrap();
//
//         let mut input = [label, b"-B"].concat();
//         let B = hasher.hash(&input).unwrap();
//
//         input.pop();
//         input.pop();
//         input.extend_from_slice(b"-B_blinding");
//         let B_blinding = hasher.hash(&input).unwrap();
//         Self {B, B_blinding}
//     }
// }

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

#[cfg(test)]
mod tests {
    use super::*;
    use test_log::test;

    use ark_pallas::*;

    // use ark_bls12_381::G1Affine;

    // #[test]
    // fn ped_gens_label() {
    //     let label = b"test";
    //     let gens = PedersenGens::<G1Affine>::new_using_label(label);
    // }

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
}
