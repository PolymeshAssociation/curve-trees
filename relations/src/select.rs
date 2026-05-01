use ark_ff::Field;
use ark_std::vec::Vec;
use bulletproofs::r1cs::*;
use dock_crypto_utils::ff::powers;
use dock_crypto_utils::poly::poly_from_roots;

fn empty_input_error(description: &'static str) -> R1CSError {
    R1CSError::GadgetError {
        description: description.to_string(),
    }
}

/// Prove that a commitment x is one of the values committed to in vector commitment xs.
pub fn select<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    mut xs: impl Iterator<Item = LinearCombination<F>>,
) -> Result<(), R1CSError> {
    // (x_1 - x) * (x_2 - x) * ... * (x_n - x) = 0
    let first_factor: LinearCombination<F> = xs
        .next()
        .ok_or_else(|| empty_input_error("Cannot select from empty list."))?
        - x.clone(); // todo check if it adds an extra constraint to start from constant 1 and then use iterator
    let mut product: LinearCombination<F> = first_factor;
    for xi in xs {
        let (_, _, next_product) = cs.multiply(product, xi.clone() - x.clone());
        product = next_product.into();
    }
    cs.constrain(product);
    Ok(())
}

// TODO: This is broken because randomized constraints and vector commitments aren't supported yet
/// Prove that a commitments in `xs` are subset of the values committed to in vector commitment `ys`.
pub fn multi_select<F: Field, Cs: RandomizableConstraintSystem<F>>(
    cs: &mut Cs,
    mut xs: Vec<LinearCombination<F>>,
    ys: Vec<LinearCombination<F>>,
) -> Result<(), R1CSError> {
    if xs.is_empty() {
        return Err(empty_input_error("multi_select: `xs` cannot be empty"));
    }
    if ys.is_empty() {
        return Err(empty_input_error("multi_select: `ys` cannot be empty"));
    }
    cs.specify_randomized_constraints(move |cs| {
        let challenge = cs.challenge_scalar(b"challenge");
        let x = xs.remove(0);

        // (x_1 - x) * (x_2 - x) * ... * (x_n - x) = 0
        let first_factor: LinearCombination<F> = ys[0].clone() - x.clone(); // todo check if it adds an extra constraint to start from constant 1 and then use iterator
        let mut product = first_factor;
        for y_i in ys[1..].iter() {
            let (_, _, next_product) = cs.multiply(product, y_i.clone() - x.clone());
            product = next_product.into();
        }

        let mut r = challenge;
        for x_i in xs {
            for y_i in ys.iter() {
                let (_, _, next_product) = cs.multiply(product, y_i.clone() - x_i.clone());
                product = next_product * r;
            }
            r *= challenge;
        }

        cs.constrain(product);
        Ok(())
    })
}

/// Prove that a commitments in `xs` are subset of the values committed to in vector commitment `ys`.
pub fn multi_select_ext_challenge<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    mut xs: Vec<LinearCombination<F>>,
    ys: Vec<LinearCombination<F>>,
    challenge: F,
) -> Result<(), R1CSError> {
    if xs.is_empty() {
        return Err(empty_input_error(
            "multi_select_ext_challenge: `xs` cannot be empty",
        ));
    }
    if ys.is_empty() {
        return Err(empty_input_error(
            "multi_select_ext_challenge: `ys` cannot be empty",
        ));
    }

    let x = xs.remove(0);

    // (x_1 - x) * (x_2 - x) * ... * (x_n - x) = 0
    let first_factor: LinearCombination<F> = ys[0].clone() - x.clone(); // todo check if it adds an extra constraint to start from constant 1 and then use iterator
    let mut product = first_factor;
    for y_i in ys[1..].iter() {
        let (_, _, next_product) = cs.multiply(product, y_i.clone() - x.clone());
        product = next_product.into();
    }

    let mut r = challenge;
    for x_i in xs {
        for y_i in ys.iter() {
            let (_, _, next_product) = cs.multiply(product, y_i.clone() - x_i.clone());
            product = next_product * r;
        }
        r *= challenge;
    }

    cs.constrain(product);
    Ok(())
}

/// Naive implementation of [`multi_select`] that calls [`select`] in a loop for each x_i in `xs`.
pub fn multi_select_naive<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: Vec<LinearCombination<F>>,
) -> Result<(), R1CSError> {
    if xs.is_empty() {
        return Err(empty_input_error(
            "multi_select_naive: `xs` cannot be empty",
        ));
    }
    if ys.is_empty() {
        return Err(empty_input_error(
            "multi_select_naive: `ys` cannot be empty",
        ));
    }

    for x in xs {
        select(cs, x, ys.clone().into_iter())?;
    }

    Ok(())
}

/// Prove that a commitment `x` is one of the values in public set `xs`.
pub fn select_public_set<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    x: LinearCombination<F>,
    xs: &[F],
) -> Result<(), R1CSError> {
    if xs.is_empty() {
        return Err(empty_input_error("select_public_set: `xs` cannot be empty"));
    }

    let poly = poly_from_roots::<F>(xs);
    let mut eval: LinearCombination<F> = poly.coeffs[0].into();
    let mut x_power = x.clone();
    for i in 1..poly.coeffs.len() {
        eval = eval + (x_power.clone() * poly.coeffs[i].clone());
        if i == (poly.coeffs.len() - 1) {
            break;
        }
        let (_, _, o) = cs.multiply(x_power, x.clone());
        x_power = o.into();
    }

    cs.constrain(eval);
    Ok(())
}

pub fn multi_select_public_set_ext_challenge<F: Field, Cs: ConstraintSystem<F>>(
    cs: &mut Cs,
    xs: Vec<LinearCombination<F>>,
    ys: &[F],
    challenge: F,
) -> Result<(), R1CSError> {
    if xs.is_empty() {
        return Err(empty_input_error(
            "multi_select_public_set_ext_challenge: `xs` cannot be empty",
        ));
    }
    if ys.is_empty() {
        return Err(empty_input_error(
            "multi_select_public_set_ext_challenge: `ys` cannot be empty",
        ));
    }

    let poly = poly_from_roots::<F>(ys);
    let challenge_powers = powers(&challenge, xs.len() as u32);
    let mut eval: LinearCombination<F> =
        (poly.coeffs[0] * challenge_powers.iter().sum::<F>()).into();
    let mut xs_powers = xs.clone();
    for i in 1..poly.coeffs.len() {
        let mut eval_i = xs_powers[0].clone();
        for j in 1..challenge_powers.len() {
            eval_i = eval_i + (xs_powers[j].clone() * challenge_powers[j]);
        }
        eval = eval + (eval_i * poly.coeffs[i]);
        if i == (poly.coeffs.len() - 1) {
            break;
        }
        for j in 0..challenge_powers.len() {
            let (_, _, o) = cs.multiply(xs_powers[j].clone(), xs[j].clone());
            xs_powers[j] = o.into();
        }
    }
    cs.constrain(eval);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use ark_ec::AffineRepr;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use core::iter;
    use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
    use rand::prelude::SliceRandom;
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type PallasBase = <PallasA as AffineRepr>::BaseField;
    type VestaA = ark_vesta::Affine;
    type VestaScalar = <VestaA as AffineRepr>::ScalarField;

    #[test]
    fn test_select() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(set_size: usize, pg: &PedersenGens<VestaA>, bpg: &BulletproofGens<VestaA>) {
            let mut rng = rand::thread_rng();
            let (proof, xs_comm, x_comm) = {
                // have a prover commit to a vector of random elements in Pallas base field
                let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                    .take(set_size)
                    .collect();
                let index = 42;
                let x = xs[index];

                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
                let blinding_x = PallasBase::rand(&mut rng);
                let (x_comm, x_var) = prover.commit(x, blinding_x);

                select(
                    &mut prover,
                    x_var.into(),
                    xs_vars.into_iter().map(|v| v.into()),
                )
                .unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, xs_comm, x_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let xs_vars = verifier.commit_vec(set_size, xs_comm);
            let x_var = verifier.commit(x_comm);

            select(
                &mut verifier,
                x_var.into(),
                xs_vars.into_iter().map(|v| v.into()),
            )
            .unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, &pg, &bpg);
        check(1000, &pg, &bpg);
        check(2000, &pg, &bpg);
    }

    #[test]
    fn test_select_public_set() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(set_size: usize, pg: &PedersenGens<VestaA>, bpg: &BulletproofGens<VestaA>) {
            let mut rng = rand::thread_rng();

            // Generate a public set of random elements
            let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                .take(set_size)
                .collect();
            let index = 42;
            let x = xs[index];

            let (proof, x_comm) = {
                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);

                // Only commit to x, not to xs (public set)
                let blinding_x = PallasBase::rand(&mut rng);
                let (x_comm, x_var) = prover.commit(x, blinding_x);

                select_public_set(&mut prover, x_var.into(), xs.as_slice()).unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, x_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let x_var = verifier.commit(x_comm);

            // Verifier uses the same public set xs
            select_public_set(&mut verifier, x_var.into(), xs.as_slice()).unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, &pg, &bpg);
        check(1000, &pg, &bpg);
        check(2000, &pg, &bpg);
    }

    #[test]
    fn test_multi_select_naive() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(
            set_size: usize,
            subset_size: usize,
            pg: &PedersenGens<VestaA>,
            bpg: &BulletproofGens<VestaA>,
        ) {
            let mut rng = rand::thread_rng();
            let (proof, ys_comm, xs_comm) = {
                let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                    .take(set_size)
                    .collect();
                let xs = ys
                    .choose_multiple(&mut rng, subset_size)
                    .cloned()
                    .collect::<Vec<_>>();

                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
                let blinding_ys = PallasBase::rand(&mut rng);
                let (ys_comm, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                multi_select_naive(
                    &mut prover,
                    xs_vars.clone().into_iter().map(|v| v.into()).collect(),
                    ys_vars.clone().into_iter().map(|v| v.into()).collect(),
                )
                .unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, ys_comm, xs_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let ys_vars = verifier.commit_vec(set_size, ys_comm);
            let xs_vars = verifier.commit_vec(subset_size, xs_comm);

            multi_select_naive(
                &mut verifier,
                xs_vars.clone().into_iter().map(|v| v.into()).collect(),
                ys_vars.clone().into_iter().map(|v| v.into()).collect(),
            )
            .unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, 2, &pg, &bpg);
        check(512, 3, &pg, &bpg);
        check(512, 4, &pg, &bpg);
    }

    #[ignore]
    #[test]
    fn test_multi_select() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(
            set_size: usize,
            subset_size: usize,
            pg: &PedersenGens<VestaA>,
            bpg: &BulletproofGens<VestaA>,
        ) {
            let mut rng = rand::thread_rng();
            let (proof, ys_comm, xs_comm) = {
                let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                    .take(set_size)
                    .collect();
                let xs = ys
                    .choose_multiple(&mut rng, subset_size)
                    .cloned()
                    .collect::<Vec<_>>();

                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
                let blinding_ys = PallasBase::rand(&mut rng);
                let (ys_comm, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                multi_select(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys_vars.into_iter().map(|v| v.into()).collect(),
                )
                .unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, ys_comm, xs_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let ys_vars = verifier.commit_vec(set_size, ys_comm);
            let xs_vars = verifier.commit_vec(subset_size, xs_comm);

            multi_select(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys_vars.into_iter().map(|v| v.into()).collect(),
            )
            .unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, 2, &pg, &bpg);
        check(512, 3, &pg, &bpg);
        check(512, 4, &pg, &bpg);
    }

    #[test]
    fn test_multi_select_ext_challenge() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(
            set_size: usize,
            subset_size: usize,
            pg: &PedersenGens<VestaA>,
            bpg: &BulletproofGens<VestaA>,
        ) {
            let mut rng = rand::thread_rng();
            let (proof, ys_comm, xs_comm) = {
                let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                    .take(set_size)
                    .collect();
                let xs = ys
                    .choose_multiple(&mut rng, subset_size)
                    .cloned()
                    .collect::<Vec<_>>();

                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);
                let blinding_ys = PallasBase::rand(&mut rng);
                let (ys_comm, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                let c = prover.transcript().challenge_scalar(b"challenge");

                multi_select_ext_challenge(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys_vars.into_iter().map(|v| v.into()).collect(),
                    c,
                )
                .unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, ys_comm, xs_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let ys_vars = verifier.commit_vec(set_size, ys_comm);
            let xs_vars = verifier.commit_vec(subset_size, xs_comm);

            let c = verifier.transcript().challenge_scalar(b"challenge");

            multi_select_ext_challenge(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys_vars.into_iter().map(|v| v.into()).collect(),
                c,
            )
            .unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, 2, &pg, &bpg);
        check(512, 3, &pg, &bpg);
        check(512, 4, &pg, &bpg);
    }

    #[test]
    fn test_multi_select_public_set_ext_challenge() {
        let pg = PedersenGens::<VestaA>::default();
        let bpg = BulletproofGens::<VestaA>::new(1 << 12, 1);

        fn check(
            set_size: usize,
            subset_size: usize,
            pg: &PedersenGens<VestaA>,
            bpg: &BulletproofGens<VestaA>,
        ) {
            let mut rng = rand::thread_rng();

            // Generate a public set ys and a subset xs from it
            let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
                .take(set_size)
                .collect();
            let xs = ys
                .choose_multiple(&mut rng, subset_size)
                .cloned()
                .collect::<Vec<_>>();

            let (proof, xs_comm) = {
                let start = Instant::now();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);

                // Commit to xs elements
                let blinding_xs = PallasBase::rand(&mut rng);
                let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                let c = prover.transcript().challenge_scalar(b"challenge");

                multi_select_public_set_ext_challenge(
                    &mut prover,
                    xs_vars.into_iter().map(|v| v.into()).collect(),
                    ys.as_slice(),
                    c,
                )
                .unwrap();

                let proof = prover.prove(&bpg).unwrap();
                println!("For set size = {set_size}, subset size = {subset_size}");
                println!("Prover time {:?}", start.elapsed());
                println!("Proof size {}", proof.compressed_size());

                (proof, xs_comm)
            };

            let start = Instant::now();
            let mut transcript = MerlinTranscript::new(b"select");
            let mut verifier = Verifier::new(&mut transcript);

            let xs_vars = verifier.commit_vec(subset_size, xs_comm);

            let c = verifier.transcript().challenge_scalar(b"challenge");

            multi_select_public_set_ext_challenge(
                &mut verifier,
                xs_vars.into_iter().map(|v| v.into()).collect(),
                ys.as_slice(),
                c,
            )
            .unwrap();

            verifier.verify(&proof, pg, bpg).unwrap();
            println!("Verifier time {:?}", start.elapsed());
        }

        check(512, 2, &pg, &bpg);
        check(512, 3, &pg, &bpg);
        check(512, 4, &pg, &bpg);
    }

    #[test]
    fn test_empty_inputs_return_error() {
        let pg = PedersenGens::<VestaA>::default();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut prover: Prover<_, VestaA> = Prover::new(&pg, &mut transcript);

        let (x_comm, x_var) = prover.commit(VestaScalar::from(5u64), PallasBase::from(7u64));
        let _ = x_comm;

        assert!(select(
            &mut prover,
            x_var.into(),
            core::iter::empty::<LinearCombination<VestaScalar>>(),
        )
        .is_err());

        assert!(multi_select(
            &mut prover,
            vec![],
            vec![LinearCombination::<VestaScalar>::from(x_var)],
        )
        .is_err());

        assert!(multi_select_ext_challenge(
            &mut prover,
            vec![LinearCombination::<VestaScalar>::from(x_var)],
            vec![],
            VestaScalar::from(11u64),
        )
        .is_err());

        assert!(multi_select_naive(
            &mut prover,
            vec![],
            vec![LinearCombination::<VestaScalar>::from(x_var)],
        )
        .is_err());

        assert!(select_public_set(&mut prover, x_var.into(), &[]).is_err());

        assert!(multi_select_public_set_ext_challenge(
            &mut prover,
            vec![],
            &[VestaScalar::from(13u64)],
            VestaScalar::from(17u64),
        )
        .is_err());
    }
}
