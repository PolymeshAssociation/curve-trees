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
//! The implementation adds a public element `delta` to each `P_i` as mentioned in the curve tree paper

use crate::curve::{curve_check, PointRepresentation};
use crate::error::Error;
use crate::rerandomize::re_randomize;
use crate::parameters::{SingleLayerProofParameters, SingleLayerProofParametersNew};use ark_std::vec;use ark_dlog_gadget::dlog::{
    commit_witness_chunks_prover, commit_witness_chunks_verifier, create_divisor_and_decomposition,
    discrete_log_blinding_given_challenge, DiscreteLogParameters,
    DivisorComms,
};
use ark_dlog_gadget::utils::{CurveSpec};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::{Field, PrimeField};
use ark_std::{cfg_into_iter, cfg_iter, vec::Vec};
use bulletproofs::r1cs::{constant, ConstraintSystem, Prover, Variable, Verifier};
use dock_crypto_utils::msm::multiply_field_elems_with_same_group_elem;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_core::CryptoRngCore;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::prover::{challenge, VC_LEN};
use zeroize::Zeroize;
use bulletproofs::BulletproofGens;

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
        curve_check(
            cs,
            x_var.into(),
            y_var.into(),
            P1::COEFF_A,
            P1::COEFF_B,
        );

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

pub fn prove<
    R: CryptoRngCore,
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<BaseField = Fb, ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    D: DivisorCurve<BaseField = Fs, ScalarField = Fb> + From<Projective<P1>>,
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
) -> Result<(Vec<Affine<P1>>, Vec<DivisorComms<Affine<P0>>>), Error> {
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
    let blinding_base = parameters.sl_params.pc_gens.B_blinding.into_group();
    let mut blinders =
        multiply_field_elems_with_same_group_elem(blinding_base, &blindings_for_points);
    let re_randomized_points = (0..size)
        .map(|i| points[i] + blinders[i])
        .collect::<Vec<_>>();
    let re_randomized_points = Projective::normalize_batch(&re_randomized_points);

    let mut items = vec![];

    let wits = cfg_into_iter!(blindings_for_points)
        .map(|b| create_divisor_and_decomposition::<_, D, Parameters>(&parameters.table, -b))
        .collect::<Vec<_>>();
    for witness in wits {
        items.push({
            commit_witness_chunks_prover(
                rng,
                prover,
                &witness?,
                VC_LEN as usize,
                bp_gens,
            )?
        });
    }

    // Allocate commitment to all x-coordinates
    let x_coord_vars =
        prover.vars_for_committed_vec(re_randomized_comm, &x_coords, blinding_of_comm);

    let cs = CurveSpec {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };

    let (challenge, challenge_gen) = challenge(prover, &cs, &parameters.table)?;

    let points_plus_delta_xy = points_plus_delta
        .into_iter()
        .map(|n| (Some(n), Some(n.y)))
        .collect::<Vec<_>>();
    let re_randomized_points_plus_delta = cfg_iter!(re_randomized_points)
        .map(|n| *n + parameters.sl_params.delta)
        .collect::<Vec<_>>();
    let re_randomized_points_plus_delta =
        Projective::normalize_batch(&re_randomized_points_plus_delta);

    let mut comms = vec![];
    for (i, (comm_divisor, _, p)) in items.into_iter().enumerate() {
        // For each "point", check its x and y lie on the curve
        let x_var = x_coord_vars[i];
        let y_var = prover.allocate(points_plus_delta_xy[i].1)?;
        let (x, y) = re_randomized_points_plus_delta[i].xy().unwrap();
        discrete_log_blinding_given_challenge(
            prover,
            (x_var, y_var),
            p,
            (x, y),
            &cs,
            &challenge,
            &challenge_gen,
        );
        comms.push(comm_divisor);
    }

    Zeroize::zeroize(&mut blinders);

    // gadget::<Fb, Fs, P0, P1, _>(
    //     prover,
    //     size,
    //     x_coord_vars,
    //     Some(points_plus_delta),
    //     re_randomized_points.clone(),
    //     Some(blindings_for_points),
    //     parameters,
    // )?;
    Ok((re_randomized_points, comms))
}

pub fn verify<
    Fb: PrimeField,
    Fs: PrimeField,
    P0: SWCurveConfig<BaseField = Fb, ScalarField = Fs> + Copy,
    P1: SWCurveConfig<BaseField = Fs, ScalarField = Fb> + Copy,
    Parameters: DiscreteLogParameters,
>(
    verifier: &mut Verifier<MerlinTranscript, Affine<P0>>,
    re_randomized_comm: Affine<P0>,
    re_randomized_points: Vec<Affine<P1>>,
    comms: Vec<DivisorComms<Affine<P0>>>,
    parameters: &SingleLayerProofParametersNew<P1, Parameters>,
) -> Result<(), Error> {
    let size = re_randomized_points.len();
    assert_eq!(comms.len(), size);

    let re_randomized_points_plus_delta = cfg_iter!(re_randomized_points)
        .map(|n| *n + parameters.sl_params.delta)
        .collect::<Vec<_>>();
    let re_randomized_points_plus_delta =
        Projective::normalize_batch(&re_randomized_points_plus_delta);

    let mut items = vec![];
    for comm in comms.into_iter() {
        items.push(commit_witness_chunks_verifier(verifier, &comm, VC_LEN as usize));
    }

    // Commit to all x-coordinates
    let x_coord_vars = verifier.commit_vec(size, re_randomized_comm);

    let cs = CurveSpec {
        a: P1::COEFF_A,
        b: P1::COEFF_B,
    };

    let (challenge, challenge_gen) = challenge(verifier, &cs, &parameters.table)?;

    for (i, p) in items.into_iter().enumerate() {
        // For each "point", check its x and y lie on the curve
        let x_var = x_coord_vars[i];
        let y_var = verifier.allocate(None)?;
        let (x, y) = re_randomized_points_plus_delta[i].xy().unwrap();
        discrete_log_blinding_given_challenge(
            verifier,
            (x_var, y_var),
            p,
            (x, y),
            &cs,
            &challenge,
            &challenge_gen,
        );
    }

    // naive_gadget::<Fb, Fs, P0, P1, _>(
    //     verifier,
    //     size,
    //     x_coord_vars,
    //     None,
    //     re_randomized_points.clone(),
    //     None,
    //     parameters,
    // )

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
