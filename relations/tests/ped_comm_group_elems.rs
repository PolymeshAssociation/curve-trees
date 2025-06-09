mod common;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{One, PrimeField, Zero};
use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::{constant, ConstraintSystem, LinearCombination, Prover, Verifier};
use common::prove;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand::prelude::SliceRandom;
use relations::curve_tree::{CurveTree, SelRerandParameters};
use relations::ped_comm_group_elems::{prove_naive, verify_naive};
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

#[test]
pub fn commitment_naive() {
    check_naive::<2, PallasBase, PallasConfig, VestaConfig>(Some(4), 13, 16, 1, 4);
    check_naive::<8, PallasBase, PallasConfig, VestaConfig>(Some(4), 14, 4096, 1, 8);
    check_naive::<8, PallasBase, PallasConfig, VestaConfig>(Some(4), 14, 4096, 1, 5);
    check_naive::<8, PallasBase, PallasConfig, VestaConfig>(Some(4), 14, 4096, 1, 3);
}

#[test]
pub fn commitment() {
    check::<2, PallasBase, PallasConfig, VestaConfig>(Some(4), 13, 16, 1, 4);
}

pub fn check_naive<
    const L: usize,
    F0: PrimeField,
    P0: SWCurveConfig<BaseField = F0> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
    nesting_size: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length);

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeMap::new();
    while proof_indices.len() < num_proofs {
        let nested = (0..nesting_size)
            .map(|_| Affine::<P1>::rand(&mut rng))
            .collect::<Vec<_>>();
        let x_coords = nested
            .iter()
            .map(|n| (*n + sr_params.odd_parameters.delta).into_affine().x)
            .collect::<Vec<_>>();
        let comm =
            sr_params
                .even_parameters
                .commit(x_coords.as_slice(), P0::ScalarField::zero(), 0);
        proof_indices.insert(
            possible_proof_indices.choose(&mut rng).unwrap(),
            (nested, comm),
        );
    }

    let mut set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    for (i, (_, c)) in &proof_indices {
        set[**i] = *c;
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    for (leaf_index, (nested, comm)) in proof_indices {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let clock = Instant::now();
        let path = curve_tree.get_path_to_leaf_for_proof(*leaf_index, 0);
        let (mut path_commitments, re_randomization_of_leaf) = path
            .select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_params,
                &mut rng,
            );

        let re_randomized_nested = prove_naive(
            &mut rng,
            &mut pallas_prover,
            nested,
            &path_commitments.re_randomized_leaf,
            re_randomization_of_leaf,
            &sr_params.odd_parameters,
        );

        let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover, &sr_params).unwrap();

        prover_time += clock.elapsed();

        assert_eq!(
            path_commitments.re_randomized_leaf,
            comm + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
                .into_affine()
        );

        println!(
            "Proof size: {}",
            path_commitments.compressed_size()
                + re_randomized_nested.compressed_size()
                + pallas_proof.compressed_size()
                + vesta_proof.compressed_size()
        );

        {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let clock = Instant::now();

            let rerandomized_leaf = path_commitments.select_and_rerandomize_verifier_gadget(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_params,
            );

            verify_naive(
                &mut pallas_verifier,
                rerandomized_leaf,
                re_randomized_nested,
                &sr_params.odd_parameters,
            );

            let vesta_res = vesta_verifier.verify(
                &vesta_proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            );
            let pallas_res = pallas_verifier.verify(
                &pallas_proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            );
            verifier_time += clock.elapsed();

            assert!(vesta_res.is_ok());
            assert!(pallas_res.is_ok());
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index)
                    + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
            )
        }
    }

    println!("For tree with {num_leaves} leaves, nesting size {nesting_size}, {num_proofs} proofs took {:?} prover time and {:?} verifier time", prover_time, verifier_time);
}

pub fn check<
    const L: usize,
    F0: PrimeField,
    P0: SWCurveConfig<BaseField = F0> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
    nesting_size: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length);

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeMap::new();
    while proof_indices.len() < num_proofs {
        let nested = (0..nesting_size)
            .map(|_| Affine::<P1>::rand(&mut rng))
            .collect::<Vec<_>>();
        let x_coords = nested
            .iter()
            .map(|n| (*n + sr_params.odd_parameters.delta).into_affine().x)
            .collect::<Vec<_>>();
        let comm =
            sr_params
                .even_parameters
                .commit(x_coords.as_slice(), P0::ScalarField::zero(), 0);
        proof_indices.insert(
            possible_proof_indices.choose(&mut rng).unwrap(),
            (nested, comm),
        );
    }

    let mut set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    for (i, (_, c)) in &proof_indices {
        set[**i] = *c;
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    for (leaf_index, (_, comm)) in proof_indices {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let clock = Instant::now();
        let (mut path_commitments, re_randomization_of_leaf) = curve_tree
            .select_and_rerandomize_prover_gadget(
                *leaf_index,
                0,
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_params,
                &mut rng,
            );

        assert_eq!(
            path_commitments.re_randomized_leaf,
            comm + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
                .into_affine()
        );

        // TODO:

        let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover, &sr_params).unwrap();

        prover_time += clock.elapsed();

        {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let clock = Instant::now();

            let rerandomized_leaf = path_commitments.select_and_rerandomize_verifier_gadget(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &sr_params,
            );

            let vesta_res = vesta_verifier.verify(
                &vesta_proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            );
            let pallas_res = pallas_verifier.verify(
                &pallas_proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            );
            verifier_time += clock.elapsed();

            assert!(vesta_res.is_ok());
            assert!(pallas_res.is_ok());
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index)
                    + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
            )
        }
    }

    println!("For tree with {num_leaves} leaves, nesting size {nesting_size}, {num_proofs} proofs took {:?} prover time and {:?} verifier time", prover_time, verifier_time);
}
