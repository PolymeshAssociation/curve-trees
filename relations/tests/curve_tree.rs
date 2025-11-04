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
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::UniformRand;
use ark_vesta::{Fq as VestaBase, VestaConfig};
use bulletproofs::r1cs::*;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::prelude::SliceRandom;
use rand::thread_rng;
use relations::curve_tree::*;
use std::collections::BTreeSet;
use std::time::{Duration, Instant};

mod common;
use common::prove;
use relations::curve_tree_prover::CurveTreeWitnessPath;

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

#[test]
pub fn test_curve_tree_using_params_generated_by_hash_to_curve() {
    let generators_length = 1 << 11;

    // Test with Pallas as P0, Vesta as P1
    let sr_params_pallas = SelRerandParameters::<PallasConfig, VestaConfig>::new_using_label(
        b"curve_tree_test_pallas_p0",
        generators_length,
        generators_length,
    )
    .expect("Failed to create SelRerandParameters with Pallas as P0");

    test_curve_tree_inner::<32, PallasBase, PallasConfig, VestaConfig>(&sr_params_pallas, 4);

    // Test with Vesta as P0, Pallas as P1
    let sr_params_vesta = SelRerandParameters::<VestaConfig, PallasConfig>::new_using_label(
        b"curve_tree_test_vesta_p0",
        generators_length,
        generators_length,
    )
    .expect("Failed to create SelRerandParameters with Vesta as P0");

    test_curve_tree_inner::<32, VestaBase, VestaConfig, PallasConfig>(&sr_params_vesta, 4);
}

fn test_curve_tree_inner<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    sr_params: &SelRerandParameters<P0, P1>,
    depth: usize,
) where
    Affine<P0>: UniformRand,
{
    let mut rng = thread_rng();
    let even_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut even_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, even_transcript);

    let odd_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut odd_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, odd_transcript);

    let some_point = Affine::<P0>::rand(&mut rng);
    let set = vec![some_point];
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    let path = curve_tree.get_path_to_leaf_for_proof(0, 0);
    let (path_commitments, re_randomization_of_leaf) = path.select_and_rerandomize_prover_gadget(
        &mut even_prover,
        &mut odd_prover,
        &sr_params,
        &mut rng,
    );

    let (pallas_proof, vesta_proof) = prove(even_prover, odd_prover, &sr_params).unwrap();

    let root = curve_tree.root_node();

    {
        let even_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut even_verifier = Verifier::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut odd_verifier = Verifier::new(odd_transcript);

        let rerandomized_leaf = path_commitments.select_and_rerandomize_verifier_gadget(
            &root,
            &mut even_verifier,
            &mut odd_verifier,
            &sr_params,
        );
        odd_verifier
            .verify(
                &vesta_proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            )
            .unwrap();
        even_verifier
            .verify(
                &pallas_proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            )
            .unwrap();
        assert_eq!(
            rerandomized_leaf.into_group(),
            curve_tree.get_leaf(0)
                + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
        )
    }
}

pub fn test_curve_tree_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) where
    Affine<P0>: UniformRand,
{
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    test_curve_tree_inner::<L, F, P0, P1>(&sr_params, depth);
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
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

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

    let mut proof_size_printed = false;

    for leaf_index in proof_indices {
        let clock = Instant::now();

        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let path = curve_tree.get_path_to_leaf_for_proof(*leaf_index, 0);
        let (path_commitments, re_randomization_of_leaf) = path
            .select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_params,
                &mut rng,
            );

        let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover, &sr_params).unwrap();

        prover_time += clock.elapsed();

        if !proof_size_printed {
            println!(
                "Proof size for L={L}, height={}: {} bytes",
                curve_tree.height(),
                pallas_proof.serialized_size(Compress::Yes)
                    + vesta_proof.serialized_size(Compress::Yes)
            );
            proof_size_printed = true;
        }

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

            #[cfg(feature = "parallel")]
            let (vesta_res, pallas_res) = rayon::join(
                || {
                    vesta_verifier.verify(
                        &vesta_proof,
                        &sr_params.odd_parameters.pc_gens,
                        &sr_params.odd_parameters.bp_gens,
                    )
                },
                || {
                    pallas_verifier.verify(
                        &pallas_proof,
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                    )
                },
            );

            #[cfg(not(feature = "parallel"))]
            let (vesta_res, pallas_res) = (
                vesta_verifier.verify(
                    &vesta_proof,
                    &sr_params.odd_parameters.pc_gens,
                    &sr_params.odd_parameters.bp_gens,
                ),
                pallas_verifier.verify(
                    &pallas_proof,
                    &sr_params.even_parameters.pc_gens,
                    &sr_params.even_parameters.bp_gens,
                ),
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
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

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

        let path = curve_tree.get_path_to_leaf_for_proof(*leaf_index, 0);
        let (path_commitments, re_randomization_of_leaf) = path
            .select_and_rerandomize_prover_gadget(
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
    let mut rng = thread_rng();
    let generators_length = 1 << 12;

    let sr_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        generators_length,
        generators_length,
    )
    .expect("Failed to create SelRerandParameters");

    let batch_size = 5;

    let set = (0..batch_size)
        .map(|_| PallasP::rand(&mut rng).into_affine())
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<32, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &sr_params,
        Some(4),
    );

    let labels = [
        b"select_and_rerandomize_1",
        b"select_and_rerandomize_2",
        b"select_and_rerandomize_3",
    ];

    println!("Batch size = {batch_size}");

    let mut path_commitments = Vec::with_capacity(batch_size);
    let mut pallas_proofs = Vec::with_capacity(batch_size);
    let mut vesta_proofs = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        // Choosing arbitrary labels
        let label = labels[i % labels.len()];
        let pallas_transcript = MerlinTranscript::new(label);
        let mut pallas_prover: Prover<_, Affine<PallasParameters>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(label);
        let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let path = curve_tree.get_path_to_leaf_for_proof(i, 0);
        let (path_commitment, _) = path.select_and_rerandomize_prover_gadget(
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
        path_commitments.push(path_commitment);
        pallas_proofs.push(pallas_proof);
        vesta_proofs.push(vesta_proof);
    }

    let start = Instant::now();
    let mut pallas_vt = Vec::with_capacity(batch_size);
    let mut vesta_vt = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        // Choosing same label as prover
        let label = labels[i % labels.len()];
        let pallas_transcript = MerlinTranscript::new(label);
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(label);
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _ = path_commitments[i].select_and_rerandomize_verifier_gadget(
            &curve_tree.root_node(),
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_params,
        );
        let pallas_verification_tuples = pallas_verifier
            .verification_scalars_and_points(&pallas_proofs[i])
            .unwrap();
        let vesta_verification_tuples = vesta_verifier
            .verification_scalars_and_points(&vesta_proofs[i])
            .unwrap();
        pallas_vt.push(pallas_verification_tuples);
        vesta_vt.push(vesta_verification_tuples);
    }

    let pallas_res = batch_verify(
        pallas_vt,
        &sr_params.even_parameters.pc_gens,
        &sr_params.even_parameters.bp_gens,
    );
    let vesta_res = batch_verify(
        vesta_vt,
        &sr_params.odd_parameters.pc_gens,
        &sr_params.odd_parameters.bp_gens,
    );

    assert_eq!(pallas_res, Ok(()));
    assert_eq!(vesta_res, Ok(()));

    println!("Batch verification took {:?}", start.elapsed());

    let start = Instant::now();
    for i in 0..batch_size {
        // Choosing same label as prover
        let label = labels[i % labels.len()];
        let pallas_transcript = MerlinTranscript::new(label);
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(label);
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _ = path_commitments[i].select_and_rerandomize_verifier_gadget(
            &curve_tree.root_node(),
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_params,
        );
        let vesta_res = vesta_verifier.verify(
            &vesta_proofs[i],
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        );
        let pallas_res = pallas_verifier.verify(
            &pallas_proofs[i],
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
        );
        assert_eq!(pallas_res, Ok(()));
        assert_eq!(vesta_res, Ok(()));
    }
    println!("Regular verification took {:?}", start.elapsed());
}

#[test]
pub fn test_combined_vs_common_root_path_proofs() {
    check_combined_vs_common_root_proofs_with_parameters::<512, PallasBase, PallasConfig, VestaConfig>(4, 14, 2);
    check_combined_vs_common_root_proofs_with_parameters::<512, PallasBase, PallasConfig, VestaConfig>(4, 14, 3);
    check_combined_vs_common_root_proofs_with_parameters::<512, PallasBase, PallasConfig, VestaConfig>(4, 14, 4);
}

pub fn check_combined_vs_common_root_proofs_with_parameters<
    const L: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
    num_paths: usize,
) {
    let mut rng = thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..num_paths {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    println!("For {num_paths} leaves, width {L}, height {depth}");
    
    println!("Combined Proof");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);
    
    let mut path_commitments_list: Vec<SelectAndRerandomizePath<L, P0, P1>> = Vec::new();
    for i in 0..num_paths {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0);
        let (path_commitments, _) = path.select_and_rerandomize_prover_gadget(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rng,
        );
        path_commitments_list.push(path_commitments);
    }

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    let combined_proof_size = path_commitments_list.compressed_size() + pallas_proof.compressed_size() + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", combined_proof_size);
    
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    
    for path_commitments in &path_commitments_list {
        let _ = path_commitments.select_and_rerandomize_verifier_gadget(
            &curve_tree.root_node(),
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_params,
        );
    }

    vesta_verifier
        .verify(
            &vesta_proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        )
        .unwrap();
    pallas_verifier
        .verify(
            &pallas_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
        )
        .unwrap();
    println!("Verification time: {:?}", clock.elapsed());

    println!("Common root Proofs");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let mut paths = Vec::new();
    for i in 0..num_paths {
        let path = curve_tree.get_path_to_leaf_for_proof(i, 0);
        paths.push(path);
    }
    
    let root_children_coords = CurveTreeWitnessPath::process_root_nodes_for_given_paths_with_common_root(
        &paths,
        &mut pallas_prover,
        &mut vesta_prover,
        &sr_params,
    ).unwrap();
    
    let (path_commitments_list, _) = CurveTreeWitnessPath::process_non_root_nodes_for_given_paths_with_common_root(
        &paths,
        &mut pallas_prover,
        &mut vesta_prover,
        &sr_params,
        root_children_coords,
        &mut rng,
    ).unwrap();

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    let multi_path_proof_size = path_commitments_list.compressed_size() + pallas_proof.compressed_size() + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", multi_path_proof_size);

    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);
    
    let _rerandomized_leaves = SelectAndRerandomizePath::select_and_rerandomize_verifier_gadget_multi_path(
        &path_commitments_list,
        &mut pallas_verifier,
        &mut vesta_verifier,
        &sr_params,
        &curve_tree.root_node(),
    );

    vesta_verifier
        .verify(
            &vesta_proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        )
        .unwrap();
    pallas_verifier
        .verify(
            &pallas_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
        )
        .unwrap();
    println!("Verification time: {:?}", clock.elapsed());
}
