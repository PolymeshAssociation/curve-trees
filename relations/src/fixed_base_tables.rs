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
use ark_std::UniformRand;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{R1CSError, VerificationTuple};
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

    pub fn verify_tuples<R: RngCore + CryptoRng>(
        &self,
        pc_gens: &PedersenGens<Affine<P>>,
        verification_tuples: Vec<VerificationTuple<Affine<P>>>,
        rng: &mut R,
    ) -> Result<(), R1CSError> {
        if verification_tuples.is_empty() {
            return Ok(());
        }

        let mut max_padded_n = 0usize;
        let mut num_var = 0usize;
        for vt in &verification_tuples {
            let n = vt.padded_n()? as usize;
            if n > max_padded_n {
                max_padded_n = n;
            }
            num_var += vt.proof_dependent_scalars.len();
        }
        if max_padded_n > self.capacity {
            return Err(R1CSError::InvalidGeneratorsLength(
                self.capacity as u32,
                max_padded_n as u32,
            ));
        }

        let mut proof_points = Vec::with_capacity(num_var + 2);
        let mut proof_scalars = Vec::with_capacity(num_var + 2);
        let mut lc = vec![P::ScalarField::zero(); 2 * max_padded_n + 2];

        for mut vt in verification_tuples {
            let padded_n = vt.padded_n()? as usize;

            let mut r = P::ScalarField::rand(rng);
            while r.is_zero() {
                r = P::ScalarField::rand(rng);
            }

            proof_points.append(&mut vt.proof_dependent_points);
            for s in vt.proof_dependent_scalars.drain(..) {
                proof_scalars.push(s * r);
            }
            lc[0] += r * vt.fixed_point_scalars[0];
            lc[1] += r * vt.fixed_point_scalars[1];
            for i in 0..padded_n {
                lc[2 + i] += r * vt.fixed_point_scalars[2 + i];
            }
            for i in 0..padded_n {
                lc[2 + max_padded_n + i] += r * vt.fixed_point_scalars[2 + padded_n + i];
            }
        }

        proof_points.push(pc_gens.B);
        proof_points.push(pc_gens.B_blinding);
        proof_scalars.push(lc[0]);
        proof_scalars.push(lc[1]);
        let g_scalars = &lc[2..2 + max_padded_n];
        let h_scalars = &lc[2 + max_padded_n..2 + 2 * max_padded_n];

        let result = self.g_table.msm(g_scalars)
            + self.h_table.msm(h_scalars)
            + msm_batch_affine::<P>(&proof_points, &proof_scalars);

        if result.is_zero() {
            Ok(())
        } else {
            Err(R1CSError::VerificationError)
        }
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
