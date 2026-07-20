use crate::curve::{curve_check, PointRepresentation};
use crate::error::Error;
use crate::parameters::SingleLayerProofParameters;
use crate::rerandomize::re_randomize;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_std::vec::Vec;
use bulletproofs::r1cs::{constant, ConstraintSystem, Prover, Variable, Verifier};
use dock_crypto_utils::msm::multiply_field_elems_with_same_group_elem;
use dock_crypto_utils::transcript::MerlinTranscript;
use zeroize::Zeroize;

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

    // [points[0].x, points[0].y, ..., points[n].x, points[n].y]
    let mut coords = Vec::with_capacity(2 * size);
    for p in &points {
        let (x, y) = p.xy().ok_or_else(|| Error::PointCantBeZero)?;
        coords.push(x);
        coords.push(y);
    }

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

    // Allocate commitment to both coordinates of all points
    let coord_vars = prover.vars_for_committed_vec(re_randomized_comm, &coords, blinding_of_comm);

    naive_gadget::<Fb, Fs, P0, P1, _>(
        prover,
        size,
        coord_vars,
        Some(points),
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
    // Commit to both coordinates of all points
    let coord_vars = verifier.commit_vec(2 * size, re_randomized_comm);

    naive_gadget::<Fb, Fs, P0, P1, _>(
        verifier,
        size,
        coord_vars,
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
    coord_vars: Vec<Variable<P1::BaseField>>,
    points: Option<Vec<Affine<P1>>>,
    re_randomized_points: Vec<Affine<P1>>,
    blindings: Option<Vec<P1::ScalarField>>,
    parameters: &SingleLayerProofParameters<P1>,
) -> Result<(), Error> {
    let points = if let Some(n) = points {
        n.into_iter().map(|n| Some(n)).collect::<Vec<_>>()
    } else {
        (0..size).map(|_| None).collect::<Vec<_>>()
    };

    let blindings = if let Some(n) = blindings {
        n.into_iter().map(|n| Some(n)).collect::<Vec<_>>()
    } else {
        (0..size).map(|_| None).collect::<Vec<_>>()
    };

    for i in 0..size {
        // For each "point", check its x and y lie on the curve
        let x_var = coord_vars[2 * i];
        let y_var = coord_vars[2 * i + 1];
        // TODO: Can these be efficiently batch checked? No, since multiplications dominate the cost
        curve_check(cs, x_var.into(), y_var.into(), P1::COEFF_A, P1::COEFF_B);

        // Check that rerandomized_point = point + B_blinding * blindings[i]
        let (re_rand_x, re_rand_y) = re_randomized_points[i]
            .xy()
            .ok_or_else(|| Error::PointCantBeZero)?;
        re_randomize(
            cs,
            &parameters.tables,
            PointRepresentation {
                x: x_var.into(),
                y: y_var.into(),
                point: points[i],
            },
            constant(re_rand_x),
            constant(re_rand_y),
            blindings[i],
        )?;
    }

    Ok(())
}
