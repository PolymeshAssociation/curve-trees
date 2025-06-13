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

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length);

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

    println!("For batch size {M}, width {L} and height {depth}");
    let clock = Instant::now();
    let (path_commitments, _) = curve_tree.batched_select_and_rerandomize_prover_gadget(
        indices,
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
    println!("Proving time: {:?}", clock.elapsed());
    println!(
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
        println!("Verifying time: {:?}", clock.elapsed());
    }
}
