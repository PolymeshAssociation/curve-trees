use crate::curve::{curve_check, PointRepresentation};
use crate::error::Error;
use crate::parameters::SingleLayerProofParameters;
use crate::rerandomize::re_randomize;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_std::cfg_iter;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{constant, ConstraintSystem, Prover, Variable, Verifier};
use dock_crypto_utils::msm::multiply_field_elems_with_same_group_elem;
use dock_crypto_utils::transcript::MerlinTranscript;
use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

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
