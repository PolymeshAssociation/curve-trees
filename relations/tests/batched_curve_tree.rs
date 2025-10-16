extern crate bulletproofs;
extern crate relations;

use ark_ff::PrimeField;
use bulletproofs::r1cs::*;
use std::time::Instant;

use relations::curve_tree::*;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_std::UniformRand;

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_secp256k1::{Config as SecpConfig, Fq as SecpBase};
use ark_secq256k1::Config as SecqConfig;
use ark_serialize::CanonicalSerialize;
use dock_crypto_utils::transcript::MerlinTranscript;

#[test]
pub fn test_batched_curve_tree_even_depth() {
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(4, 12);
    test_batched_curve_tree_with_parameters::<32, 2, SecpBase, SecpConfig, SecqConfig>(4, 12);
}

#[test]
pub fn test_batched_curve_tree_odd_depth() {
    test_batched_curve_tree_with_parameters::<32, 2, PallasBase, PallasConfig, VestaConfig>(3, 12);
    test_batched_curve_tree_with_parameters::<32, 2, SecpBase, SecpConfig, SecqConfig>(3, 12);
}

pub fn test_batched_curve_tree_with_parameters<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let mut set = Vec::<Affine<P0>>::new();
    let mut indices = [0usize; M];
    for i in 0..M {
        set.push(Affine::<P0>::rand(&mut rng));
        indices[i] = i;
    }
    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    log::debug!("For batch size {M}, width {L} and height {depth}");
    let clock = Instant::now();
    let (path_commitments, _) = curve_tree
        .batched_select_and_rerandomize_prover_gadget(
            indices,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rng,
        )
        .expect("Failed to prove batched select and rerandomize");

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();
    log::debug!("Proving time: {:?}", clock.elapsed());
    log::debug!(
        "Proof size: {}",
        path_commitments.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size()
    );

    {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let clock = Instant::now();
        let _rerandomized_leaves = curve_tree.batched_select_and_rerandomize_verifier_gadget(
            &mut pallas_verifier,
            &mut vesta_verifier,
            path_commitments,
            &sr_params,
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
        log::debug!("Verifying time: {:?}", clock.elapsed());
    }
}

#[test]
pub fn test_individual_vs_batched_proofs() {
    check_individual_vs_batched_proofs_with_parameters::<512, 2, PallasBase, PallasConfig, VestaConfig>(4, 14);
    check_individual_vs_batched_proofs_with_parameters::<512, 3, PallasBase, PallasConfig, VestaConfig>(4, 14);
}

pub fn check_individual_vs_batched_proofs_with_parameters<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    // Create leaves for both trees
    let mut set = Vec::<Affine<P0>>::new();
    for _ in 0..M {
        set.push(Affine::<P0>::rand(&mut rng));
    }

    // Create curve tree with batch support
    let batched_curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(batched_curve_tree.height(), depth);

    // For individual proofs and combined proof, using a non-batched curve tree
    let curve_tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &sr_params, Some(depth));
    assert_eq!(curve_tree.height(), depth);

    println!("For {M} leaves, width {L}, height {depth}");

    // Create individual proofs for each leaf
    println!("Individual Proofs");
    let mut individual_proofs = Vec::new();
    let mut total_individual_proof_size = 0;

    let clock = Instant::now();
    for i in 0..M {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let path = curve_tree.get_path_to_leaf_for_proof(i, 0);
        let (path_commitments, _) = path.select_and_rerandomize_prover_gadget(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rng,
        );

        let pallas_proof = pallas_prover
            .prove(&sr_params.even_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&sr_params.odd_parameters.bp_gens)
            .unwrap();

        total_individual_proof_size += path_commitments.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size();
        individual_proofs.push((path_commitments, pallas_proof, vesta_proof));
    }

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", total_individual_proof_size);

    // Verify individual proofs
    let clock = Instant::now();
    for (path_commitments, pallas_proof, vesta_proof) in &individual_proofs {
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let _ = path_commitments.select_and_rerandomize_verifier_gadget(
            &curve_tree.root_node(),
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_params,
        );

        vesta_verifier
            .verify(
                vesta_proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            )
            .unwrap();
        pallas_verifier
            .verify(
                pallas_proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
            )
            .unwrap();
    }
    println!("Verification time: {:?}", clock.elapsed());

    // Create single combined proof (call select_and_rerandomize_prover_gadget for each leaf but prove() only once)
    println!("Combined Proof");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    // Call select_and_rerandomize_prover_gadget for each leaf to accumulate constraints
    let mut path_commitments_list: Vec<SelectAndRerandomizePath<L, P0, P1>> = Vec::new();
    for i in 0..M {
        let (path_commitments, _) = curve_tree.select_and_rerandomize_prover_gadget(
            i,
            0,
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

    // Verify combined proof
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    // For verification, we need to call the verifier gadget for each leaf too
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

    // Create proper batched proof using batched_select_and_rerandomize_prover_gadget
    println!("Batched Proof");

    let clock = Instant::now();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);


    // Use the batched curve tree and call batched_select_and_rerandomize_prover_gadget
    let mut indices = [0usize; M];
    for i in 0..M {
        indices[i] = i;
    }

    let (path_commitments, _) = batched_curve_tree
        .batched_select_and_rerandomize_prover_gadget(
            indices,
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            &mut rng,
        )
        .expect("Failed to prove batched select and rerandomize");

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    let batched_proof_size = path_commitments.compressed_size()
        + pallas_proof.compressed_size()
        + vesta_proof.compressed_size();

    println!("Proving time: {:?}", clock.elapsed());
    println!("Proof size: {} bytes", batched_proof_size);

    // Verify batched proof
    let clock = Instant::now();
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_verifier = Verifier::new(pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_verifier = Verifier::new(vesta_transcript);

    let _ = batched_curve_tree.batched_select_and_rerandomize_verifier_gadget(
        &mut pallas_verifier,
        &mut vesta_verifier,
        path_commitments,
        &sr_params,
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
