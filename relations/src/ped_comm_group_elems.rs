//! Pedersen commitment to "curve points". Commits to elliptic curve points by committing to their x-coordinate the
//! same way curve trees do. Then the knowledge of those committed points can be proved along with
//! generating a re-randomized version of each point.
//! Given points `P_i \in G` as `A = [P_0, P_1, ..., P_n]`. Commit to `A` in a Pedersen commitment of x-coordinate of
//! each `P_i`, i.e. `P_i.x` in `C = PedCom(P_0.x, P_1.x, ..., P_n.x) = \sum_{G_i*P_i.x}` where `C \in H` where `G, H`
//! are on 2 curves which form a 2-cycle (base field of one equals scalar field of other).
//!
//! 1. Prover randomizes each `P_i` to get `A_r = [{P_r}_0, {P_r}_1, ..., {P_r}_n]` where `A_r[i] = {P_r}_i = P_i + r_i*B` where
//! `B \in G` and `r_i` is chosen randomly.
//! 2. Prover proves `\forall i, P_i \in G`, i.e. `P_i.x, P_i.y` are x and y coordinates of a point which lies in group `G`.
//! 3. Prover proves `\forall i, A_r[i] = A[i] + r_i*B = P_i + r_i*B`
//!
//! The implementation adds a public element `delta` to each `P_i` as mentioned in the curve tree paper.
//!
//! ## Selective Dual Re-Randomization
//!
//! The `prove` and `verify` functions support selective dual re-randomization via `shared_dlog_indices: &BTreeSet<usize>`:
//!
//! ### For indices in the set
//! - Produces **two** re-randomized points using same blinding with different generators:
//!   - Primary: `P_i + B_blinding * r_i`
//!   - Secondary: `P_i + B * r_i`
//! - Uses `discrete_log_blinding_and_dlog` (mixed proof with shared scalar)
//!
//! ### For indices not in the set
//! - Produces **one** re-randomized point: `P_i + B_blinding * r_i`
//! - Uses standard `discrete_log_blinding`
//!
//! ## Example Usage
//!
//! ```rust,ignore
//! // Mixed mode: indices 0 and 2 get dual points, others get single points
//! let shared_dlog_indices: BTreeSet<usize> = [0, 2].into_iter().collect();
//! let (re_randomized, comms) = prove(..., parameters, bp_gens, &shared_dlog_indices)?;
//!
//! // re_randomized.primary: Vec of primary points (always present, one per input)
//! // re_randomized.secondary: BTreeMap with secondary points only for indices {0, 2}
//!
//! verify(..., re_randomized, comms, parameters, &shared_dlog_indices)?;
//! ```

use crate::curve::{curve_check, PointRepresentation};
use crate::error::Error;
use crate::parameters::{SingleLayerProofParameters, SingleLayerProofParametersNew};
use crate::prover::VC_LEN;
use crate::rerandomize::re_randomize;
use ark_dlog_gadget::dlog::{
    commit_witness_chunks_prover, commit_witness_chunks_prover_multi_gen,
    commit_witness_chunks_verifier, commit_witness_chunks_verifier_multi_gen,
    create_divisor_and_decomposition, create_divisor_and_decomposition_multi_gen,
    discrete_log_blinding_and_dlog_given_challenge, discrete_log_blinding_given_challenge,
    discrete_log_challenge, DiscreteLogParameters, DivisorComms,
};
use ark_dlog_gadget::utils::CurveSpec;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    cfg_iter,
    collections::{BTreeMap, BTreeSet},
    string::ToString,
    vec::Vec,
};
use bulletproofs::r1cs::{constant, ConstraintSystem, Prover, Variable, Verifier};
use bulletproofs::BulletproofGens;
use dock_crypto_utils::msm::multiply_field_elems_with_same_group_elem;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReRandomizedPoints<P: SWCurveConfig> {
    /// `points[i] + B_blinding * blindings[i]`
    pub re_randomized_points: Vec<Affine<P>>,
    /// `B * blindings[i]` for indices of the map
    pub blindings_with_different_gen: BTreeMap<usize, Affine<P>>,
}

impl<P: SWCurveConfig> ReRandomizedPoints<P> {
    pub fn len(&self) -> usize {
        self.re_randomized_points.len()
    }

    pub fn is_empty(&self) -> bool {
        self.re_randomized_points.is_empty()
    }
}

pub fn prove_naive<
    Fb: PrimeField,
    Fs: Field,
    P0: SWCurveConfig<BaseField = Fb, ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
>(
    prover: &mut Prover<MerlinTranscript, Affine<P0>>,
    points: Vec<Affine<P1>>,
    re_randomized_comm: &Affine<P0>,
    blinding_of_comm: P0::ScalarField,
    blindings_for_points: Vec<P1::ScalarField>,
    parameters: &SingleLayerProofParameters<P1>,
) -> Result<Vec<Affine<P1>>, Error> {
    let size = points.len();
    if blindings_for_points.len() != size {
        return Err(Error::MismatchedSize(blindings_for_points.len(), size));
    }

    // This could be stored once and reused.
    let points_plus_delta = cfg_iter!(points)
        .map(|n| *n + parameters.sl_params.delta)
        .collect::<Vec<_>>();
    let points_plus_delta = Projective::normalize_batch(&points_plus_delta);
    let x_coords = points_plus_delta.iter().map(|n| n.x).collect::<Vec<_>>();

    // For each nested, re-randomization nested_r[i] = nested[i] + B_blinding * blindings[i]
    let mut blinders = multiply_field_elems_with_same_group_elem(
        parameters.sl_params.pc_gens.B_blinding.into_group(),
        &blindings_for_points,
    );
    let re_randomized_points = (0..size)
        .map(|i| points[i] + blinders[i])
        .collect::<Vec<_>>();
    let re_randomized_points = Projective::normalize_batch(&re_randomized_points);

    Zeroize::zeroize(&mut blinders);

    // Allocate commitment to all x-coordinates
    let x_coord_vars =
        prover.vars_for_committed_vec(re_randomized_comm, &x_coords, blinding_of_comm);

    naive_gadget::<Fb, Fs, P0, P1, _>(
        prover,
        size,
        x_coord_vars,
        Some(points_plus_delta),
        re_randomized_points.clone(),
        Some(blindings_for_points),
        parameters,
    )?;
    Ok(re_randomized_points)
}

pub fn verify_naive<
    Fb: PrimeField,
    Fs: Field,
    P0: SWCurveConfig<BaseField = Fb, ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
>(
    verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
    re_randomized_comm: Affine<P0>,
    re_randomized_points: Vec<Affine<P1>>,
    parameters: &SingleLayerProofParameters<P1>,
) -> Result<(), Error> {
    let size = re_randomized_points.len();
    // Commit to all x-coordinates
    let x_coord_vars = verifier.commit_vec(size, re_randomized_comm);

    naive_gadget::<Fb, Fs, P0, P1, _>(
        verifier,
        size,
        x_coord_vars,
        None,
        re_randomized_points.clone(),
        None,
        parameters,
    )
}

pub fn naive_gadget<
    Fb: PrimeField,
    Fs: Field,
    P0: SWCurveConfig<BaseField = Fb, ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    CS: ConstraintSystem<Fs>,
>(
    cs: &mut CS,
    size: usize,
    x_coord_vars: Vec<Variable<P1::BaseField>>,
    points_plus_delta: Option<Vec<Affine<P1>>>,
    re_randomized_points: Vec<Affine<P1>>,
    blindings: Option<Vec<P1::ScalarField>>,
    parameters: &SingleLayerProofParameters<P1>,
) -> Result<(), Error> {
    let points_plus_delta_xy = if let Some(n) = points_plus_delta {
        n.into_iter()
            .map(|n| (Some(n), Some(n.y)))
            .collect::<Vec<_>>()
    } else {
        (0..size).map(|_| (None, None)).collect::<Vec<_>>()
    };

    let re_randomized_points_plus_delta = cfg_iter!(re_randomized_points)
        .map(|n| *n + parameters.sl_params.delta)
        .collect::<Vec<_>>();
    let re_randomized_points_plus_delta =
        Projective::normalize_batch(&re_randomized_points_plus_delta);

    let blindings = if let Some(n) = blindings {
        n.into_iter().map(|n| Some(n)).collect::<Vec<_>>()
    } else {
        (0..size).map(|_| None).collect::<Vec<_>>()
    };

    for i in 0..size {
        // For each "point", check its x and y lie on the curve
        let x_var = x_coord_vars[i];
        let y_var = cs.allocate(points_plus_delta_xy[i].1)?;
        // TODO: Can these be efficiently batch checked? No, since multiplications dominate the cost
        curve_check(cs, x_var.into(), y_var.into(), P1::COEFF_A, P1::COEFF_B);

        // Check that rerandomized_point_plus_delta = point_plus_delta + B_blinding * blindings[i]
        re_randomize(
            cs,
            &parameters.tables,
            PointRepresentation {
                x: x_var.into(),
                y: y_var.into(),
                point: points_plus_delta_xy[i].0,
            },
            constant(re_randomized_points_plus_delta[i].x),
            constant(re_randomized_points_plus_delta[i].y),
            blindings[i],
        )?;
    }

    Ok(())
}

/// For indices in `shared_dlog_indices`, produces 2 re-randomized points using same blinding with different generators.
/// For other indices, produces 1 re-randomized point.
pub fn prove<
    R: CryptoRngCore,
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: DivisorCurve<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    rng: &mut R,
    prover: &mut Prover<MerlinTranscript, Affine<P0>>,
    points: Vec<Affine<P1>>,
    re_randomized_comm: &Affine<P0>,
    blinding_of_comm: P0::ScalarField,
    blindings_for_points: Vec<P1::ScalarField>,
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
    bp_gens: &BulletproofGens<Affine<P0>>,
    shared_dlog_indices: BTreeSet<usize>,
) -> Result<(ReRandomizedPoints<P1>, Vec<DivisorComms<Affine<P0>>>), Error> {
    let size = points.len();
    if blindings_for_points.len() != size {
        return Err(Error::MismatchedSize(blindings_for_points.len(), size));
    }

    // This could be stored once and reused.
    let points_plus_delta = cfg_iter!(points)
        .map(|n| *n + parameters.sl_params.delta)
        .collect::<Vec<_>>();
    let points_plus_delta = Projective::normalize_batch(&points_plus_delta);
    let x_coords = points_plus_delta.iter().map(|n| n.x).collect::<Vec<_>>();

    // re-randomized points, `points[i] + B_blinding * blindings[i]`
    let blinding_base = parameters.sl_params.pc_gens.B_blinding.into_group();
    let mut blinders_b_blinding =
        multiply_field_elems_with_same_group_elem(blinding_base, &blindings_for_points);

    let mut re_randomized_points = Vec::with_capacity(size);
    let mut re_randomized_points_plus_delta = Vec::with_capacity(size);
    for i in 0..size {
        re_randomized_points.push(points[i] + blinders_b_blinding[i]);
        re_randomized_points_plus_delta.push(re_randomized_points[i] + parameters.sl_params.delta);
    }
    let re_randomized_points = Projective::normalize_batch(&re_randomized_points);
    let re_randomized_points_plus_delta =
        Projective::normalize_batch(&re_randomized_points_plus_delta);

    Zeroize::zeroize(&mut blinders_b_blinding);

    // compute blindings using same blinding but different generator, `B * blindings[i]`
    let other_base = parameters.sl_params.pc_gens.B.into_group();
    let mut blinding_points = BTreeMap::new();

    for idx in shared_dlog_indices.clone() {
        blinding_points.insert(idx, (other_base * blindings_for_points[idx]).into_affine());
    }

    let re_randomized_points = ReRandomizedPoints {
        re_randomized_points,
        blindings_with_different_gen: blinding_points,
    };

    // Allocate commitment to all x-coordinates
    let x_coord_vars =
        prover.vars_for_committed_vec(re_randomized_comm, &x_coords, blinding_of_comm);

    let cs = CurveSpec {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };

    // Commit all witnesses
    let mut all_comms = Vec::with_capacity(size);
    let mut blinds_single = BTreeMap::new();
    let mut blinds_multi = BTreeMap::new();

    let gen_table_refs = [&parameters.table_b_blinding, &parameters.table_b];

    for i in 0..size {
        if shared_dlog_indices.contains(&i) {
            let witness = create_divisor_and_decomposition_multi_gen::<_, P1, Parameters>(
                &gen_table_refs,
                -blindings_for_points[i],
            )?;
            let (comm_divisor, _, blinds) = commit_witness_chunks_prover_multi_gen::<
                _,
                _,
                _,
                Parameters,
            >(
                rng, prover, &witness, VC_LEN as usize, bp_gens
            )?;
            all_comms.push(comm_divisor);
            blinds_multi.insert(i, blinds);
        } else {
            let witness = create_divisor_and_decomposition::<_, P1, Parameters>(
                &parameters.table_b_blinding,
                -blindings_for_points[i],
            )?;
            let (comm_divisor, _, blind) = commit_witness_chunks_prover::<_, _, _, Parameters>(
                rng,
                prover,
                &witness,
                VC_LEN as usize,
                bp_gens,
            )?;
            all_comms.push(comm_divisor);
            blinds_single.insert(i, blind);
        }
    }

    let (challenge, challenge_gen) = discrete_log_challenge(
        prover,
        &cs,
        &[&parameters.table_b_blinding, &parameters.table_b],
    )?;

    // Enforce constraints
    for i in 0..size {
        let x_var = x_coord_vars[i];
        let y_var = prover.allocate(Some(points_plus_delta[i].y))?;

        let (re_rand_x_var, re_rand_y_var) = re_randomized_points_plus_delta[i].xy().unwrap();

        if shared_dlog_indices.contains(&i) {
            discrete_log_blinding_and_dlog_given_challenge(
                prover,
                (x_var, y_var),
                blinds_multi.remove(&i).unwrap(),
                (re_rand_x_var, re_rand_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
                &challenge_gen[1],
            )?;
        } else {
            discrete_log_blinding_given_challenge(
                prover,
                (x_var, y_var),
                *blinds_single.remove(&i).unwrap(),
                (re_rand_x_var, re_rand_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
            );
        }
    }

    Ok((re_randomized_points, all_comms))
}

pub fn verify<
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
    re_randomized_comm: Affine<P0>,
    re_randomized_points: ReRandomizedPoints<P1>,
    comms: Vec<DivisorComms<Affine<P0>>>,
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
    shared_dlog_indices: BTreeSet<usize>,
) -> Result<(), Error> {
    let size = re_randomized_points.len();

    if comms.len() != size {
        return Err(Error::MismatchedSize(comms.len(), size));
    }

    // Add delta to all re-randomized points
    let re_randomized_plus_delta: Vec<_> = re_randomized_points
        .re_randomized_points
        .iter()
        .map(|p| *p + parameters.sl_params.delta)
        .collect();
    let re_randomized_plus_delta = Projective::normalize_batch(&re_randomized_plus_delta);

    // Commit to all x-coordinates of the original points
    let x_coord_vars = verifier.commit_vec(size, re_randomized_comm);

    let cs = CurveSpec {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };

    let mut blinds_single = BTreeMap::new();
    let mut blinds_multi = BTreeMap::new();

    for (i, comm) in comms.iter().enumerate() {
        if shared_dlog_indices.contains(&i) {
            let blinds = commit_witness_chunks_verifier_multi_gen::<_, _, Parameters>(
                verifier,
                comm,
                VC_LEN as usize,
                2,
            );
            blinds_multi.insert(i, blinds);
        } else {
            let blind = commit_witness_chunks_verifier::<_, _, Parameters>(
                verifier,
                comm,
                VC_LEN as usize,
            )?;
            blinds_single.insert(i, blind);
        }
    }

    let (challenge, challenge_gen) = discrete_log_challenge(
        verifier,
        &cs,
        &[&parameters.table_b_blinding, &parameters.table_b],
    )?;

    // Enforce constraints
    for i in 0..size {
        let x_var = x_coord_vars[i];
        let y_var = verifier.allocate(None)?;

        let (re_rand_x_var, re_rand_y_var) = re_randomized_plus_delta[i].xy().unwrap();

        if shared_dlog_indices.contains(&i) {
            let blinds = blinds_multi.remove(&i).ok_or_else(|| {
                Error::MalformedProofInput("missing shared dlog witness".to_string())
            })?;
            discrete_log_blinding_and_dlog_given_challenge(
                verifier,
                (x_var, y_var),
                blinds,
                (re_rand_x_var, re_rand_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
                &challenge_gen[1],
            )?;
        } else {
            let blind = blinds_single.remove(&i).ok_or_else(|| {
                Error::MalformedProofInput("missing single dlog witness".to_string())
            })?;
            discrete_log_blinding_given_challenge(
                verifier,
                (x_var, y_var),
                *blind,
                (re_rand_x_var, re_rand_y_var),
                &cs,
                &challenge,
                &challenge_gen[0],
            );
        }
    }

    Ok(())
}

// pub fn gadget<
//     Fb: PrimeField,
//     Fs: Field,
//     P0: SWCurveConfig<BaseField = Fb, ScalarField = Fs> + Copy,
//     P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
//     CS: ConstraintSystem<Fs>,
// >(
//     cs: &mut CS,
//     size: usize,
//     x_coord_vars: Vec<Variable<P1::BaseField>>,
//     points_plus_delta: Option<Vec<Affine<P1>>>,
//     re_randomized_points: Vec<Affine<P1>>,
//     blindings: Option<Vec<P1::ScalarField>>,
//     parameters: &SingleLayerParameters<P1>,
// ) -> Result<(), Error> {
//     let points_plus_delta_xy = if let Some(n) = points_plus_delta {
//         n.into_iter()
//             .map(|n| (Some(n), Some(n.y)))
//             .collect::<Vec<_>>()
//     } else {
//         (0..size).map(|_| (None, None)).collect::<Vec<_>>()
//     };
//
//     let re_randomized_points_plus_delta = cfg_iter!(re_randomized_points)
//         .map(|n| *n + parameters.delta)
//         .collect::<Vec<_>>();
//     let re_randomized_points_plus_delta =
//         Projective::normalize_batch(&re_randomized_points_plus_delta);
//
//     let blindings = if let Some(n) = blindings {
//         n.into_iter().map(|n| Some(n)).collect::<Vec<_>>()
//     } else {
//         (0..size).map(|_| None).collect::<Vec<_>>()
//     };
//
//     for i in 0..size {
//         // For each "point", check its x and y lie on the curve
//         let x_var = x_coord_vars[i];
//         let y_var = cs.allocate(points_plus_delta_xy[i].1)?;
//         curve_check(
//             cs,
//             x_var.into(),
//             y_var.into(),
//             parameters.coeff_a,
//             parameters.coeff_b,
//         );
//     }
//
//     Ok(())
// }
