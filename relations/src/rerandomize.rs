use bulletproofs::r1cs::*;

use crate::curve::*;
use crate::error::Error;
use crate::lookup::*;

use ark_ec::{
    models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine, AffineRepr, CurveGroup,
};
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_std::{vec::Vec, One, Zero};
use core::marker::PhantomData;

/// Return 1 lookup table per window for the windowed scalar multiplication
/// Each table has 2 columns, for x and y coordinates for the corresponding point of the table.
/// Implemented as per appendix B.7
pub fn build_tables<C: AffineRepr>(h: C) -> Result<Vec<Lookup3Bit<2, C::BaseField>>, Error> {
    if h.is_zero() {
        return Err(Error::PointCantBeZero);
    }
    let m = get_num_windows::<C::ScalarField>();

    /// Return `x * 8`
    fn times_8<C: AffineRepr>(x: &C::ScalarField) -> C::ScalarField {
        let mut x = x.double();
        x.double_in_place();
        x.double_in_place();
        x
    }

    // Define tables T_1 .. T_m, and witnesses
    let mut tables = Vec::with_capacity(m);
    let mut m_th_right_term = C::ScalarField::zero();
    // 2^(3*(i - 1))
    let mut j_term = C::ScalarField::one();
    for i in 1..m + 1 {
        let mut table = Lookup3Bit::<2, C::BaseField> {
            elems: [[C::BaseField::one(); WINDOW_ELEMS]; 2],
        };
        // `right_term` is added to each of the m-1 windows to ensure that none of the multiplications result
        // in "0" point since the coordinates can't be taken then.
        let right_term = if i < m {
            // 2^(3*i)
            let right_term = times_8::<C>(&j_term);
            // add right term to the sum in the mth iteration right term
            m_th_right_term += right_term;
            right_term
        } else {
            // subtract sum of all previous right terms: for i = 1..m-1 { 2^(3* i) }
            -m_th_right_term
        };
        for j in 0..WINDOW_ELEMS {
            // s = j * 2^(3*i) + right_term
            let s = (C::ScalarField::from(j as u64) * j_term) + right_term;
            // Multiply blinding by s
            let hs = h.mul(s).into_affine();
            table.elems[0][j] = hs
                .x()
                .ok_or_else(|| Error::GenerationError("Failed to get x coordinate".into()))?;
            table.elems[1][j] = hs
                .y()
                .ok_or_else(|| Error::GenerationError("Failed to get y coordinate".into()))?;
        }
        tables.push(table);
        // Last iteration doesn't matter
        j_term = right_term;
    }
    Ok(tables)
}

/// Scalar multiplication of point with its lookup table `base_tables` and the scalar `scalar`.
/// Returns the point, and linear combinations for its x and y coordinates. The resulting point is 0 for verifier
pub fn scalar_mult<
    F: Field,
    S: PrimeField,
    P: SWCurveConfig<BaseField = F, ScalarField = S>,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    base_tables: &[Lookup3Bit<2, F>],
    scalar: Option<S>,
) -> Result<(Affine<P>, LinearCombination<F>, LinearCombination<F>), Error> {
    let lambda = S::MODULUS_BIT_SIZE as usize;
    let num_windows = get_num_windows::<S>();
    assert_eq!(num_windows, base_tables.len());
    let s_bits = match scalar {
        None => None,
        Some(r) => {
            let r: S::BigInt = r.into();
            Some(r.to_bits_le())
        }
    };

    // This will finally be set to the blinding point, i.e. `H * randomness`
    let mut res = Affine::<P>::zero();

    // These correspond to x and y coordinates of the previous iteration's `res`
    let mut res_prev_x_lc: LinearCombination<F> = Variable::One(PhantomData).into();
    let mut res_prev_y_lc: LinearCombination<F> = Variable::One(PhantomData).into();

    // Define tables T_1 .. T_m, and witnesses
    for i in 1..num_windows + 1 {
        let table = base_tables[i - 1];

        // Add the point in `table` corresponding to `index` to `res`
        let (index, x_l_minus_x_r_inv, delta, res_x, res_y) = match &s_bits {
            None => (None, None, None, None, None),
            Some(bits) => {
                // bi is the starting bit index of this window
                let bi = (i - 1) * 3;

                // Value of index is the 3-bit value [bi + 2, bi + 1, bi] with bi being the LSB
                let mut index: usize = usize::from(bi < lambda && bits[bi]);
                if bi + 1 < lambda && bits[bi + 1] {
                    index += 2;
                };
                if bi + 2 < lambda && bits[bi + 2] {
                    index += 4;
                };

                let x_i_lookup = table.elems[0][index];
                let y_i_lookup = table.elems[1][index];

                // At infinity, both x and y are 0
                let (x_left, y_left) = (res.x, res.y);

                let x_right = x_i_lookup;
                let y_right = y_i_lookup;

                // y_l - y_r / x_l - x_r, 1 / x_l - x_r
                let (delta, x_left_minus_x_right_inv) = if i != 1 {
                    // x_left - x_right can't be 0 since the smallest point in this window is bigger than
                    // the sum of the largest points of all previous windows for the first m-1 windows and for
                    // the m-th window calculating sum of "right term" using geometric progression formula shows
                    // that "left term" + "right term" can't be 0
                    let (delta, x_left_minus_x_right_inv) =
                        delta::<F>(x_left, y_left, x_right, y_right);
                    (
                        Some(delta),
                        // Only needed for checked curve addition done in the last iteration
                        if i == num_windows {
                            Some(x_left_minus_x_right_inv)
                        } else {
                            None
                        },
                    )
                } else {
                    (None, None)
                };

                res = (res + Affine::<P>::new(x_i_lookup, y_i_lookup)).into();

                (
                    Some(index),
                    x_left_minus_x_right_inv,
                    delta,
                    Some(res.x),
                    Some(res.y),
                )
            }
        };

        let [x_table, y_table] = lookup(cs, &table, index)?;

        // Ensure that this table's correct element was added to `res` to get its new value
        // Allocate coordinates for the accumulated witness
        let res_x_lc: LinearCombination<F> = cs.allocate(res_x)?.into();
        let res_y_lc: LinearCombination<F> = cs.allocate(res_y)?.into();
        if i > 1 {
            // Enforce addition constraint:
            // R_i = R_{i-1} + (x_i, y_i)
            let prms = CurveAddition {
                x_l: res_prev_x_lc.clone(),
                y_l: res_prev_y_lc.clone(),
                x_r: x_table,
                y_r: y_table,
                x_o: res_x_lc.clone(),
                y_o: res_y_lc.clone(),
                delta,
            };
            if i == num_windows {
                // enforce checked curve addition
                checked_curve_addition(cs, &prms, x_l_minus_x_r_inv);
            } else {
                // enforce incomplete curve addition
                incomplete_curve_addition(cs, &prms);
            }
        }
        res_prev_x_lc = res_x_lc;
        res_prev_y_lc = res_y_lc;
    }

    Ok((res, res_prev_x_lc, res_prev_y_lc))
}

/// For proving that randomization of the point inside `commitment` is same as point represented by x and y coordinates
/// in `re_randomized_commitment_x_coord` and `re_randomized_commitment_y_coord` respectively.
/// Enforces `commitment.point + H * randomness = (re_randomized_commitment_x_coord, re_randomized_commitment_y_coord)`
/// where `tables` correspond to the lookup tables for `H`
pub fn re_randomize<
    F: Field,
    S: PrimeField,
    P: SWCurveConfig<BaseField = F, ScalarField = S>,
    Cs: ConstraintSystem<F>,
>(
    cs: &mut Cs,
    tables: &[Lookup3Bit<2, F>],
    commitment: PointRepresentation<F, Affine<P>>,
    re_randomized_commitment_x_coord: LinearCombination<F>,
    re_randomized_commitment_y_coord: LinearCombination<F>,
    randomness: Option<S>,
) -> Result<(), Error> {
    let (res, res_x_lc, res_y_lc) = scalar_mult::<F, S, P, Cs>(cs, tables, randomness)?;

    // Now `(res_x_lc, res_y_lc)` correspond to x and y coordinates of the blinding point, i.e. `H * randomness`
    // Enforce that sum of point in `commitment` + `(res_x_lc, res_y_lc)` equals `(re_randomized_commitment_x_coord, re_randomized_commitment_y_coord)`
    // constrain (x_tilde, y_tilde) = (x, y) + (R_m) - with checked addition
    let (delta, x_l_minus_x_r_inv) = match commitment.point {
        Some(commitment) => {
            let (delta, x_left_minus_x_right_inv) =
                delta::<F>(commitment.x, commitment.y, res.x, res.y);
            (Some(delta), Some(x_left_minus_x_right_inv))
        }
        _ => (None, None),
    };
    let prms = CurveAddition {
        x_l: commitment.x,
        y_l: commitment.y,
        x_r: res_x_lc,
        y_r: res_y_lc,
        x_o: re_randomized_commitment_x_coord,
        y_o: re_randomized_commitment_y_coord,
        delta,
    };
    checked_curve_addition(cs, &prms, x_l_minus_x_r_inv);

    Ok(())
}

/// compute slope delta as y_l - y_r / x_l - x_r. Return delta and 1 / x_l - x_r
fn delta<F: Field>(x_l: F, y_l: F, x_r: F, y_r: F) -> (F, F) {
    let x_l_minus_x_r_inv = F::one() / (x_l - x_r);
    let delta = (y_l - y_r) * x_l_minus_x_r_inv;
    (delta, x_l_minus_x_r_inv)
}

/// number of windows for 3-bit windows
fn get_num_windows<F: PrimeField>() -> usize {
    let lambda = F::MODULUS_BIT_SIZE as usize;
    // Need floor(lambda/3) + 1 rather than ceil(lambda/3) windows to adjust for the "right term" added to each window
    (lambda / 3) + 1
}

// pub fn re_randomize_new<
//     F: Field,
//     S: PrimeField,
//     P: SWCurveConfig<BaseField = F, ScalarField = S>,
//     Cs: ConstraintSystem<F>,
// >(
//     cs: &mut Cs,
//     tables: &[Lookup3Bit<2, F>],
//     commitment: PointRepresentation<F, Affine<P>>,
//     re_randomized_commitment_x_coord: LinearCombination<F>,
//     re_randomized_commitment_y_coord: LinearCombination<F>,
//     randomness: Option<S>,
// ) -> Result<(), Error> {
//     todo!()
// }

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::PallasConfig;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use std::time::{Duration, Instant};

    use ark_ec::CurveGroup;
    use ark_pallas::Affine as PallasA;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use ark_vesta::Affine as VestaA;
    use dock_crypto_utils::transcript::MerlinTranscript;

    type PallasScalar = <PallasA as AffineRepr>::ScalarField;

    #[test]
    fn test_scalar_mult_combined() {
        let mut rng = rand::thread_rng();

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(1 << 13, 1);

        let h = PallasA::rand(&mut rng);
        let tables = build_tables(h).expect("Failed to build tables");

        let mut modulus = <<PallasA as AffineRepr>::ScalarField as PrimeField>::MODULUS;
        modulus.sub_with_borrow(&<PallasScalar as PrimeField>::BigInt::from(1u64));
        let p_minus_1 = PallasScalar::from_bigint(modulus).unwrap();

        const LABEL: &[u8; 11] = b"scalar-mult";

        let mut proving_time = Duration::default();
        let mut verifying_time = Duration::default();

        let scalars = [
            PallasScalar::one(), // lowest value
            p_minus_1,           // highest value
            // Some random values
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
        ];

        let start = Instant::now();
        let mut transcript = MerlinTranscript::new(LABEL);
        let mut prover = Prover::new(&pc_gens, &mut transcript);

        for r in scalars {
            // println!("num constraints before mult = {:?}", prover.constraints.len());
            let (res, x_lc, y_lc): (PallasA, _, _) =
                scalar_mult(&mut prover, &tables, Some(r)).unwrap();

            assert_eq!(res, (h * r).into_affine());

            // println!("num constraints before curve check = {:?}", prover.constraints.len());
            curve_check(
                &mut prover,
                x_lc,
                y_lc,
                PallasConfig::COEFF_A,
                PallasConfig::COEFF_B,
            );
            // println!("num constraints after cc = {:?}", prover.constraints.len());
        }

        let proof = prover.prove(&bp_gens).unwrap();
        proving_time += start.elapsed();

        let start = Instant::now();
        let mut transcript = MerlinTranscript::new(LABEL);
        let mut verifier: Verifier<_, VestaA> = Verifier::new(&mut transcript);

        for _ in 0..scalars.len() {
            let (_, x_lc, y_lc): (PallasA, _, _) =
                scalar_mult(&mut verifier, &tables, None).unwrap();

            curve_check(
                &mut verifier,
                x_lc,
                y_lc,
                PallasConfig::COEFF_A,
                PallasConfig::COEFF_B,
            );
        }

        let num_constraints = verifier.constraints.len();
        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        verifying_time += start.elapsed();
        let proof_size = proof.compressed_size();

        println!(
            "For {} iterations, proving time: {:?} and verifying time {:?} and proof size = {proof_size} bytes and {num_constraints} constraints",
            scalars.len(), proving_time, verifying_time,
        );
    }

    #[test]
    fn test_scalar_mult() {
        let mut rng = rand::thread_rng();

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(1024, 1);

        let h = PallasA::rand(&mut rng);
        let tables = build_tables(h).expect("Failed to build tables");

        let mut modulus = <<PallasA as AffineRepr>::ScalarField as PrimeField>::MODULUS;
        modulus.sub_with_borrow(&<PallasScalar as PrimeField>::BigInt::from(1u64));
        let p_minus_1 = PallasScalar::from_bigint(modulus).unwrap();

        const LABEL: &[u8; 11] = b"scalar-mult";

        let mut proving_time = Duration::default();
        let mut verifiying_time = Duration::default();

        let scalars = [
            PallasScalar::one(), // lowest value
            p_minus_1,           // highest value
            // Some random values
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
        ];
        let mut proof_size = 0;
        for r in scalars {
            let start = Instant::now();
            let proof = {
                let mut transcript = MerlinTranscript::new(LABEL);
                let mut prover = Prover::new(&pc_gens, &mut transcript);

                let (res, x_lc, y_lc): (PallasA, _, _) =
                    scalar_mult(&mut prover, &tables, Some(r)).unwrap();

                assert_eq!(res, (h * r).into_affine());

                curve_check(
                    &mut prover,
                    x_lc,
                    y_lc,
                    PallasConfig::COEFF_A,
                    PallasConfig::COEFF_B,
                );

                let proof = prover.prove(&bp_gens).unwrap();
                proving_time += start.elapsed();
                if proof_size == 0 {
                    proof_size = proof.compressed_size();
                }
                proof
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(LABEL);
            let mut verifier: Verifier<_, VestaA> = Verifier::new(&mut transcript);

            let (_, x_lc, y_lc): (PallasA, _, _) =
                scalar_mult(&mut verifier, &tables, None).unwrap();

            curve_check(
                &mut verifier,
                x_lc,
                y_lc,
                PallasConfig::COEFF_A,
                PallasConfig::COEFF_B,
            );

            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
            verifiying_time += start.elapsed();
        }
        println!(
            "For {} iterations, proof size = {proof_size}, proving time: {:?} and verifying time {:?}",
            scalars.len(), proving_time, verifiying_time
        );
    }

    #[test]
    fn test_re_randomize_combined() {
        let mut rng = rand::thread_rng();

        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(1 << 13, 1);

        let h = PallasA::rand(&mut rng);
        let tables = build_tables(h).expect("Failed to build tables");

        let mut modulus = <<PallasA as AffineRepr>::ScalarField as PrimeField>::MODULUS;
        modulus.sub_with_borrow(&<PallasScalar as PrimeField>::BigInt::from(1u64));
        let p_minus_1 = PallasScalar::from_bigint(modulus).unwrap();

        const LABEL: &'static [u8; 12] = b"RerandGadget";

        let mut proving_time = Duration::default();
        let mut verifying_time = Duration::default();

        let scalars = [
            PallasScalar::one(), // lowest value
            p_minus_1,           // highest value
            // Some random values
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
        ];

        let start = Instant::now();
        let mut transcript = MerlinTranscript::new(LABEL);
        let mut prover = Prover::new(&pc_gens, &mut transcript);

        for r in scalars {
            let c = PallasA::rand(&mut rng);
            let blinding = h * r;
            let c_tilde = (c + blinding).into_affine();

            let c_x_var = prover.allocate(Some(c.x)).unwrap();
            let c_y_var = prover.allocate(Some(c.y)).unwrap();
            let c_x_tilde_var = prover.allocate(Some(c_tilde.x)).unwrap();
            let c_y_tilde_var = prover.allocate(Some(c_tilde.y)).unwrap();

            re_randomize(
                &mut prover,
                &tables,
                PointRepresentation {
                    x: c_x_var.into(),
                    y: c_y_var.into(),
                    point: Some(c),
                },
                c_x_tilde_var.into(),
                c_y_tilde_var.into(),
                Some(r),
            ).unwrap()
        }

        let proof = prover.prove(&bp_gens).unwrap();
        proving_time += start.elapsed();

        let start = Instant::now();
        let mut transcript = MerlinTranscript::new(LABEL);
        let mut verifier: Verifier<_, VestaA> = Verifier::new(&mut transcript);

        for _ in 0..scalars.len() {
            let c_x_var = verifier.allocate(None).unwrap();
            let c_y_var = verifier.allocate(None).unwrap();
            let c_x_tilde_var = verifier.allocate(None).unwrap();
            let c_y_tilde_var = verifier.allocate(None).unwrap();

            re_randomize::<_, _, PallasConfig, _>(
                &mut verifier,
                &tables,
                PointRepresentation {
                    x: c_x_var.into(),
                    y: c_y_var.into(),
                    point: None,
                },
                c_x_tilde_var.into(),
                c_y_tilde_var.into(),
                None,
            ).unwrap();
        }

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        verifying_time += start.elapsed();

        println!(
            "For {} iterations, proving time: {:?} and verifying time {:?}",
            scalars.len(), proving_time, verifying_time
        );
    }

    #[test]
    fn test_re_randomize() -> Result<(), Error> {
        let pc_gens = PedersenGens::<VestaA>::default();
        let bp_gens = BulletproofGens::<VestaA>::new(1024, 1);

        let mut rng = rand::thread_rng();
        let h = PallasA::rand(&mut rng);

        let tables = build_tables(h).expect("Failed to build tables");

        let mut modulus = <<PallasA as AffineRepr>::ScalarField as PrimeField>::MODULUS;
        modulus.sub_with_borrow(&<PallasScalar as PrimeField>::BigInt::from(1u64));
        let p_minus_1 = PallasScalar::from_bigint(modulus).unwrap();

        const LABEL: &'static [u8; 12] = b"RerandGadget";

        let mut proving_time = Duration::default();
        let mut verifying_time = Duration::default();

        let scalars = [
            PallasScalar::one(), // lowest value
            p_minus_1,           // highest value
            // Some random values
            PallasScalar::rand(&mut rng),
            PallasScalar::rand(&mut rng),
        ];
        for r in scalars {
            let c = PallasA::rand(&mut rng);
            let blinding = h * r;
            let c_tilde = (c + blinding).into_affine();

            let proof = {
                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(LABEL);
                let mut prover = Prover::new(&pc_gens, &mut transcript);
                let c_x_var = prover.allocate(Some(c.x))?;
                let c_y_var = prover.allocate(Some(c.y))?;
                let c_x_tilde_var = prover.allocate(Some(c_tilde.x))?;
                let c_y_tilde_var = prover.allocate(Some(c_tilde.y))?;

                // println!("num constrainsts before rand = {:?}", prover.constraints.len());
                re_randomize(
                    &mut prover,
                    &tables,
                    PointRepresentation {
                        x: c_x_var.into(),
                        y: c_y_var.into(),
                        point: Some(c),
                    },
                    c_x_tilde_var.into(),
                    c_y_tilde_var.into(),
                    Some(r),
                )
                .expect("Failed to re-randomize");
                // println!("num constrainsts after rand = {:?}", prover.constraints.len());

                let proof = prover.prove(&bp_gens)?;
                proving_time += start.elapsed();
                proof
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(LABEL);
            let mut verifier: Verifier<_, VestaA> = Verifier::new(&mut transcript);
            let c_x_var = verifier.allocate(None)?;
            let c_y_var = verifier.allocate(None)?;
            let c_x_tilde_var = verifier.allocate(None)?;
            let c_y_tilde_var = verifier.allocate(None)?;

            re_randomize::<_, _, PallasConfig, _>(
                &mut verifier,
                &tables,
                PointRepresentation {
                    x: c_x_var.into(),
                    y: c_y_var.into(),
                    point: None,
                },
                c_x_tilde_var.into(),
                c_y_tilde_var.into(),
                None,
            )
            .expect("Failed to re-randomize");

            verifier.verify(&proof, &pc_gens, &bp_gens)?;
            verifying_time += start.elapsed();
        }

        println!(
            "For {} iterations, proving time: {:?} and verifying time {:?}",
            scalars.len(), proving_time, verifying_time
        );

        Ok(())
    }

    #[test]
    fn test_tables() {
        let mut rng = rand::thread_rng();
        let h = PallasA::rand(&mut rng);
        let r: PallasScalar = <PallasA as AffineRepr>::ScalarField::rand(&mut rng);
        let h_r = h * r;

        let tables = build_tables(h).expect("Failed to build tables");
        let lambda = <PallasScalar as PrimeField>::MODULUS_BIT_SIZE as usize;
        let m = get_num_windows::<PallasScalar>();
        let r_bigint: <PallasScalar as PrimeField>::BigInt = r.into();
        let random_bits = r_bigint.to_bits_le();
        let mut h_r_acc = PallasA::zero();
        for i in 1..m + 1 {
            // n.b. i is 0 indexed
            let table = tables[i - 1];
            let bi = (i - 1) * 3;
            let mut index = if bi < lambda && random_bits[bi] {
                1usize
            } else {
                0
            };
            if bi + 1 < lambda && random_bits[bi + 1] {
                index += 2;
            };
            if bi + 2 < lambda && random_bits[bi + 2] {
                index += 4;
            };
            let x_i = table.elems[0][index];
            let y_i = table.elems[1][index];
            let t_i = PallasA::new(x_i, y_i);
            h_r_acc = (h_r_acc + &t_i).into();
        }
        assert_eq!(h_r, h_r_acc);
    }
}
