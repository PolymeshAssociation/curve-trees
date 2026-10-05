//! Fixed-base MSM tables for the Bulletproof verifier's final MSM. The verifier's check is
//! `sum(proof_dependent) + [B, B_blinding, G_0..G_{n-1}, H_0..H_{n-1}] . fixed_scalars`; the `G`/`H`
//! blocks are fixed across every proof, so a precomputed `FixedBaseMSM` over them replaces the bulk
//! of the variable-base MSM. Built at a chosen capacity; a proof of size `padded_n <= capacity` uses
//! the `G`/`H` prefixes.

#![allow(non_snake_case)]

use ark_ec::scalar_mul::fixed_base::FixedBaseMSM;
use ark_ec::scalar_mul::sw_pippenger::msm_batch_affine;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::Zero;
use ark_std::vec::Vec;
use ark_std::UniformRand;
use bulletproofs::r1cs::{combine_verification_tuples, R1CSError, VerificationTuple};
use bulletproofs::{BulletproofGens, PedersenGens};
use rand_core::{CryptoRng, RngCore};

/// Precomputed fixed-base tables over Bulletproof generator's `G` and `H`.
pub struct FixedBaseTables<P: SWCurveConfig> {
    g_table: FixedBaseMSM<P>,
    h_table: FixedBaseMSM<P>,
    capacity: usize,
}

impl<P: SWCurveConfig> FixedBaseTables<P> {
    /// Build tables over the full generator capacity.
    pub fn new(bp_gens: &BulletproofGens<Affine<P>>) -> Self {
        Self::with_capacity(bp_gens, bp_gens.gens_capacity)
    }

    /// Build tables over the first `capacity` generators.
    pub fn with_capacity(bp_gens: &BulletproofGens<Affine<P>>, capacity: u32) -> Self {
        let capacity = capacity.min(bp_gens.gens_capacity) as usize;
        let g: Vec<Affine<P>> = bp_gens.G(capacity as u32, 1).copied().collect();
        let h: Vec<Affine<P>> = bp_gens.H(capacity as u32, 1).copied().collect();
        Self {
            g_table: FixedBaseMSM::new(&g),
            h_table: FixedBaseMSM::new(&h),
            capacity,
        }
    }

    pub fn table_bytes(&self) -> usize {
        self.g_table.table_bytes() + self.h_table.table_bytes()
    }

    /// Verifies one tuple. Errors if its `padded_n` exceeds the table capacity.
    pub fn verify_tuple(
        &self,
        pc_gens: &PedersenGens<Affine<P>>,
        vt: VerificationTuple<Affine<P>>,
    ) -> Result<(), R1CSError> {
        let padded_n = vt.padded_n()? as usize;
        if padded_n > self.capacity {
            return Err(R1CSError::InvalidGeneratorsLength(
                self.capacity as u32,
                padded_n as u32,
            ));
        }

        let VerificationTuple {
            proof_dependent_points,
            proof_dependent_scalars,
            fixed_point_scalars,
        } = vt;

        let s_b = fixed_point_scalars[0];
        let s_b_blinding = fixed_point_scalars[1];
        let g_scalars = &fixed_point_scalars[2..2 + padded_n];
        let h_scalars = &fixed_point_scalars[2 + padded_n..2 + 2 * padded_n];

        let mut var_bases = proof_dependent_points;
        var_bases.push(pc_gens.B);
        var_bases.push(pc_gens.B_blinding);
        let mut var_scalars = proof_dependent_scalars;
        var_scalars.push(s_b);
        var_scalars.push(s_b_blinding);
        let result = self.g_table.msm(g_scalars)
            + self.h_table.msm(h_scalars)
            + msm_batch_affine::<P>(&var_bases, &var_scalars);

        if result.is_zero() {
            Ok(())
        } else {
            Err(R1CSError::VerificationError)
        }
    }

    /// Verifies `verification_tuples` together, each weighted by an independent random scalar.
    pub fn verify_tuples<R: RngCore + CryptoRng>(
        &self,
        pc_gens: &PedersenGens<Affine<P>>,
        verification_tuples: Vec<VerificationTuple<Affine<P>>>,
        rng: &mut R,
    ) -> Result<(), R1CSError> {
        if verification_tuples.is_empty() {
            return Err(R1CSError::NoVerificationTuple);
        }
        let combined = combine_verification_tuples(verification_tuples, |_| {
            let mut r = P::ScalarField::rand(rng);
            while r.is_zero() {
                r = P::ScalarField::rand(rng);
            }
            r
        })?;
        self.verify_tuple(pc_gens, combined)
    }
}

pub struct FixedBaseTablesPair<P0: SWCurveConfig, P1: SWCurveConfig> {
    pub even: FixedBaseTables<P0>,
    pub odd: FixedBaseTables<P1>,
}

impl<P0: SWCurveConfig, P1: SWCurveConfig> FixedBaseTablesPair<P0, P1> {
    /// Build both sides over their full generator capacities.
    pub fn new(
        even_bp: &BulletproofGens<Affine<P0>>,
        odd_bp: &BulletproofGens<Affine<P1>>,
    ) -> Self {
        Self {
            even: FixedBaseTables::new(even_bp),
            odd: FixedBaseTables::new(odd_bp),
        }
    }

    pub fn with_capacities(
        even_bp: &BulletproofGens<Affine<P0>>,
        odd_bp: &BulletproofGens<Affine<P1>>,
        even_capacity: u32,
        odd_capacity: u32,
    ) -> Self {
        Self {
            even: FixedBaseTables::with_capacity(even_bp, even_capacity),
            odd: FixedBaseTables::with_capacity(odd_bp, odd_capacity),
        }
    }

    /// Total bytes held by both tables.
    pub fn table_bytes(&self) -> usize {
        self.even.table_bytes() + self.odd.table_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{Affine as PallasAffine, Fr, PallasConfig};
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use bulletproofs::r1cs::{
        verify_given_verification_tuple, ConstraintSystem, LinearCombination, Prover, Verifier,
    };
    use dock_crypto_utils::transcript::MerlinTranscript;

    const LABEL: &[u8] = b"fixed_base_tables";

    /// `k` multipliers each constraining `a * b = c` for committed `a`, `b` and public `c`.
    fn circuit<CS: ConstraintSystem<Fr>>(
        cs: &mut CS,
        a: LinearCombination<Fr>,
        b: LinearCombination<Fr>,
        c: Fr,
        k: usize,
    ) {
        for _ in 0..k {
            let (_, _, o) = cs.multiply(a.clone(), b.clone());
            cs.constrain(o - c);
        }
    }

    /// Verification tuple for a proof of `a * b = c` (repeated `k` times) checked against
    /// `c_verifier`. The tuple is invalid when `c_verifier != a * b`.
    fn tuple(
        pc_gens: &PedersenGens<PallasAffine>,
        bp_gens: &BulletproofGens<PallasAffine>,
        k: usize,
        c_verifier: u64,
        rng: &mut StdRng,
    ) -> VerificationTuple<PallasAffine> {
        let (a, b) = (Fr::from(3u64), Fr::from(5u64));
        let mut prover = Prover::new(pc_gens, MerlinTranscript::new(LABEL));
        let (comm_a, var_a) = prover.commit(a, Fr::rand(rng));
        let (comm_b, var_b) = prover.commit(b, Fr::rand(rng));
        circuit(&mut prover, var_a.into(), var_b.into(), a * b, k);
        let proof = prover.prove(bp_gens).unwrap();

        let mut verifier = Verifier::new(MerlinTranscript::new(LABEL));
        let var_a = verifier.commit(comm_a);
        let var_b = verifier.commit(comm_b);
        circuit(
            &mut verifier,
            var_a.into(),
            var_b.into(),
            Fr::from(c_verifier),
            k,
        );
        verifier
            .verification_scalars_and_points_with_rng(&proof, rng)
            .unwrap()
    }

    fn setup() -> (
        PedersenGens<PallasAffine>,
        BulletproofGens<PallasAffine>,
        StdRng,
    ) {
        (
            PedersenGens::default(),
            BulletproofGens::new(16, 1),
            StdRng::seed_from_u64(0),
        )
    }

    #[test]
    fn verify_tuple_matches_msm_check() {
        let (pc_gens, bp_gens, mut rng) = setup();
        let tables = FixedBaseTables::<PallasConfig>::new(&bp_gens);
        for k in [1, 3, 8, 16] {
            let vt = tuple(&pc_gens, &bp_gens, k, 15, &mut rng);
            verify_given_verification_tuple(vt.clone(), &pc_gens, &bp_gens).unwrap();
            tables.verify_tuple(&pc_gens, vt).unwrap();

            let bad = tuple(&pc_gens, &bp_gens, k, 16, &mut rng);
            assert!(verify_given_verification_tuple(bad.clone(), &pc_gens, &bp_gens).is_err());
            assert!(matches!(
                tables.verify_tuple(&pc_gens, bad),
                Err(R1CSError::VerificationError)
            ));
        }
    }

    #[test]
    fn verify_tuple_rejects_tampered_scalars() {
        let (pc_gens, bp_gens, mut rng) = setup();
        let tables = FixedBaseTables::<PallasConfig>::new(&bp_gens);
        let vt = tuple(&pc_gens, &bp_gens, 4, 15, &mut rng);
        let padded_n = vt.padded_n().unwrap() as usize;
        // B, B_blinding, last G, last H and one proof dependent scalar.
        for i in [0, 1, 1 + padded_n, 1 + 2 * padded_n] {
            let mut t = vt.clone();
            t.fixed_point_scalars[i] += Fr::from(1u64);
            assert!(tables.verify_tuple(&pc_gens, t).is_err(), "index {i}");
        }
        let mut t = vt;
        t.proof_dependent_scalars[0] += Fr::from(1u64);
        assert!(tables.verify_tuple(&pc_gens, t).is_err());
    }

    #[test]
    fn capacity_prefix_and_overflow() {
        let (pc_gens, bp_gens, mut rng) = setup();
        let tables = FixedBaseTables::<PallasConfig>::with_capacity(&bp_gens, 8);
        let vt = tuple(&pc_gens, &bp_gens, 8, 15, &mut rng);
        tables.verify_tuple(&pc_gens, vt).unwrap();

        let vt = tuple(&pc_gens, &bp_gens, 9, 15, &mut rng);
        assert!(matches!(
            tables.verify_tuple(&pc_gens, vt.clone()),
            Err(R1CSError::InvalidGeneratorsLength(8, 16))
        ));
        assert!(matches!(
            tables.verify_tuples(&pc_gens, vec![vt], &mut rng),
            Err(R1CSError::InvalidGeneratorsLength(8, 16))
        ));
    }

    #[test]
    fn verify_tuples_mixed_sizes() {
        let (pc_gens, bp_gens, mut rng) = setup();
        let tables = FixedBaseTables::<PallasConfig>::new(&bp_gens);
        let good: Vec<_> = [1, 2, 5, 16]
            .into_iter()
            .map(|k| tuple(&pc_gens, &bp_gens, k, 15, &mut rng))
            .collect();
        tables
            .verify_tuples(&pc_gens, good.clone(), &mut rng)
            .unwrap();

        for bad_at in 0..good.len() {
            let mut batch = good.clone();
            let k = [1, 2, 5, 16][bad_at];
            batch[bad_at] = tuple(&pc_gens, &bp_gens, k, 16, &mut rng);
            assert!(
                tables.verify_tuples(&pc_gens, batch, &mut rng).is_err(),
                "bad tuple at {bad_at}"
            );
        }
    }

    #[test]
    fn verify_tuples_rejects_empty_batch() {
        let (pc_gens, bp_gens, mut rng) = setup();
        let tables = FixedBaseTables::<PallasConfig>::new(&bp_gens);
        assert!(matches!(
            tables.verify_tuples(&pc_gens, vec![], &mut rng),
            Err(R1CSError::NoVerificationTuple)
        ));
    }
}
