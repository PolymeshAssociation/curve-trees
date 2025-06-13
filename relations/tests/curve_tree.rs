extern crate bulletproofs;
extern crate relations;
use ark_ec::{
    short_weierstrass::{Affine, SWCurveConfig},
    AffineRepr, CurveGroup,
};
use ark_ff::PrimeField;
use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::*;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::prelude::SliceRandom;
use rand::thread_rng;
use relations::curve_tree::*;
use std::collections::BTreeSet;
use std::time::{Duration, Instant};

mod common;
use common::prove;

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type PallasP = ark_pallas::Projective;

#[test]
pub fn test_curve_tree_even_depth() {
    test_curve_tree_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(4, 11);
    test_curve_tree_with_parameters::<32, SecpBase, SecpConfig, SecqConfig>(4, 11);
}

#[test]
pub fn test_curve_tree_odd_depth() {
    test_curve_tree_with_parameters::<32, PallasBase, PallasConfig, VestaConfig>(3, 11);
    test_curve_tree_with_parameters::<32, SecpBase, SecpConfig, SecqConfig>(3, 11);
}

#[test]
pub fn test_curve_tree_even_depth_new() {
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        8,
        3,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        4,
        3,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        16,
        5,
    );
}

#[test]
pub fn test_curve_tree_even_depth_large() {
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        64,
        15,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        128,
        15,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(4),
        11,
        256,
        15,
    );

    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        None, 11, 64, 15,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        None, 11, 128, 15,
    );
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        None, 11, 256, 15,
    );
}

#[test]
pub fn test_curve_tree_odd_depth_large() {
    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        Some(3),
        11,
        64,
        10,
    );
    test_curve_tree_with_parameters_new::<32, SecpBase, SecpConfig, SecqConfig>(
        Some(3),
        11,
        128,
        10,
    );

    test_curve_tree_with_parameters_new::<32, PallasBase, PallasConfig, VestaConfig>(
        None, 11, 64, 10,
    );
    test_curve_tree_with_parameters_new::<32, SecpBase, SecpConfig, SecqConfig>(None, 11, 128, 10);
}

#[test]
pub fn test_curve_tree_small() {
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 2, 2);
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 4, 2);
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 8, 2);
    test_curve_tree_with_parameters_new::<2, PallasBase, PallasConfig, VestaConfig>(
        None, 11, 16, 2,
    );
}

#[test]
pub fn curve_tree_get_update() {
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 2, 2);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 4, 2);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 11, 8, 5);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 12, 16, 10);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 12, 32, 10);
    test_curve_tree_get_update::<2, PallasBase, PallasConfig, VestaConfig>(None, 12, 64, 10);
}

pub fn test_curve_tree_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length);

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let some_point = Affine::<P0>::rand(&mut rng);
    let set = vec![some_point];
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let (mut path_commitments, re_randomization_of_leaf) = curve_tree
        .select_and_rerandomize_prover_gadget(
            0,
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rng,
        );

    let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover, &sr_params).unwrap();

    let root = curve_tree.root_node();

    {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

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
        assert_eq!(vesta_res, pallas_res);
        assert_eq!(vesta_res, Ok(()));
        assert_eq!(
            rerandomized_leaf.into_group(),
            curve_tree.get_leaf(0)
                + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
        )
    }
}

pub fn test_curve_tree_with_parameters_new<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_proofs: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length);

    let set = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let possible_proof_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();
    let mut proof_indices = BTreeSet::new();
    while proof_indices.len() < num_proofs {
        proof_indices.insert(possible_proof_indices.choose(&mut rng).unwrap());
    }

    let root = curve_tree.root_node();

    let mut prover_time = Duration::default();
    let mut verifier_time = Duration::default();

    for leaf_index in proof_indices {
        let clock = Instant::now();

        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (mut path_commitments, re_randomization_of_leaf) = curve_tree
            .select_and_rerandomize_prover_gadget(
                *leaf_index,
                0,
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_params,
                &mut rng,
            );

        let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover, &sr_params).unwrap();

        prover_time += clock.elapsed();

        {
            let clock = Instant::now();
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

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

    println!(
        "For tree with {} leaves, {} proofs took {:?} prover time and {:?} verifier time",
        num_leaves, num_proofs, prover_time, verifier_time
    );
}

pub fn test_curve_tree_get_update<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: Option<usize>,
    generators_length_log_2: usize,
    num_leaves: usize,
    num_updates: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length);

    let leaves = (0..num_leaves)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    let mut curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&leaves, &sr_params, depth);
    if let Some(d) = depth {
        assert_eq!(curve_tree.height(), d);
    }

    let possible_indices = (0..num_leaves).map(|i| i).collect::<Vec<_>>();

    let mut update_indices = BTreeSet::new();
    while update_indices.len() < num_updates {
        update_indices.insert(possible_indices.choose(&mut rng).unwrap());
    }

    /*// Keep `num_same` number of indices same, meaning their value isn't updated
    let num_same = if num_leaves > num_updates {if (num_leaves - num_updates) > 10 {10} else {num_leaves - num_updates}} else {0};
    let mut same_indices = BTreeSet::new();
    while same_indices.len() < num_same {
        let i = possible_indices.choose(&mut rng).unwrap();
        if !update_indices.contains(i) {
            same_indices.insert(i);
        }
    }*/

    for leaf_index in &possible_indices {
        if !update_indices.contains(leaf_index) {
            let leaf = curve_tree.get_leaf(*leaf_index);
            assert_eq!(leaves[*leaf_index], leaf);
        }
    }

    for leaf_index in update_indices.clone() {
        let leaf = curve_tree.get_leaf(*leaf_index);
        assert_eq!(leaves[*leaf_index], leaf);
        let new_leaf = Affine::<P0>::rand(&mut rng);
        curve_tree.update_leaf(*leaf_index, 0, new_leaf, &sr_params);
        let leaf = curve_tree.get_leaf(*leaf_index);
        assert_eq!(leaf, new_leaf);
    }

    let root = curve_tree.root_node();

    for leaf_index in update_indices.clone() {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (mut path_commitments, re_randomization_of_leaf) = curve_tree
            .select_and_rerandomize_prover_gadget(
                *leaf_index,
                0,
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_params,
                &mut rng,
            );

        let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover, &sr_params).unwrap();

        {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

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
            assert!(vesta_res.is_ok());
            assert!(pallas_res.is_ok());
            assert_eq!(
                rerandomized_leaf.into_group(),
                curve_tree.get_leaf(*leaf_index)
                    + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
            )
        }
    }
}

#[test]
pub fn test_curve_tree_batch_verification() {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << 12;

    let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
    );

    let some_point = PallasP::rand(&mut rng).into_affine();
    let set = vec![some_point];
    let curve_tree = CurveTree::<32, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &sr_params,
        Some(4),
    );
    assert_eq!(curve_tree.height(), 4);

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<PallasParameters>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (path_commitments, _) = curve_tree.select_and_rerandomize_prover_gadget(
        0,
        0,
        &mut pallas_prover,
        &mut vesta_prover,
        &sr_params,
        &mut thread_rng(),
    );

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    let (pvt1, vvt1) = {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _rerandomized_leaf = curve_tree.select_and_rerandomize_verifier_gadget(
            &mut pallas_verifier,
            &mut vesta_verifier,
            path_commitments.clone(),
            &sr_params,
        );
        let vesta_verification_tuples = vesta_verifier
            .verification_scalars_and_points(&vesta_proof)
            .unwrap();
        let pallas_verification_tuples = pallas_verifier
            .verification_scalars_and_points(&pallas_proof)
            .unwrap();
        (pallas_verification_tuples, vesta_verification_tuples)
    };
    let (pvt2, vvt2) = {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _rerandomized_leaf = curve_tree.select_and_rerandomize_verifier_gadget(
            &mut pallas_verifier,
            &mut vesta_verifier,
            path_commitments,
            &sr_params,
        );
        let vesta_verification_tuples = vesta_verifier
            .verification_scalars_and_points(&vesta_proof)
            .unwrap();
        let pallas_verification_tuples = pallas_verifier
            .verification_scalars_and_points(&pallas_proof)
            .unwrap();
        (pallas_verification_tuples, vesta_verification_tuples)
    };
    let pallas_res = batch_verify(
        vec![pvt1, pvt2],
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
    );
    let vesta_res = batch_verify(
        vec![vvt1, vvt2],
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
    );
    assert_eq!(pallas_res, vesta_res);
    assert_eq!(pallas_res, Ok(()));
}
