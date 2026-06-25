#[macro_use]
extern crate criterion;

use criterion::{BenchmarkId, Criterion};
use std::hint::black_box;
use std::time::Duration;

extern crate bulletproofs;
use bulletproofs::r1cs::{Prover, Verifier};

extern crate relations;
use relations::curve_tree::*;
use relations::utils::{prove, verify};

use ark_ec::short_weierstrass::Affine;
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::PallasConfig;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use dock_crypto_utils::transcript::MerlinTranscript;
use lazy_static::lazy_static;
use relations::parameters::SelRerandParameters;
use relations::parameters::SelRerandProofParametersNew;

type PallasParameters = PallasConfig;
type VestaParameters = VestaConfig;

lazy_static! {
    static ref SRParamsPallasLeaf: SelRerandParameters<PallasParameters, VestaParameters> = {
        let generators_length = 1 << 18;
        SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            generators_length,
        )
        .expect("Failed to create SelRerandParameters")
    };
    static ref SRProofParamsNewPallasLeaf: SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams> = {
        SelRerandProofParametersNew::<PallasParameters, VestaParameters, PallasParams, VestaParams>::from_sr_params((*SRParamsPallasLeaf).clone())
    };
}

fn bench_batched_curve_tree_varying_batch_size_new(c: &mut Criterion) {
    bench_batched_curve_tree_with_varying_batch_size_new::<256, 32>(c, 4);
}

fn bench_batched_curve_tree_with_varying_batch_size_new<const L: usize, const M: usize>(
    c: &mut Criterion,
    depth: usize,
) {
    let mut rng = rand::thread_rng();

    // Create the curve tree once with max batch size M
    let set = (0..M)
        .map(|_| Affine::<PallasConfig>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<L, M, PallasConfig, VestaConfig>::from_leaves(
        &set,
        &*SRParamsPallasLeaf,
        Some(depth),
    );

    let prefix_string = format!("BatchedCurveTreeNew_Curves:L:{L}_D:{depth}_M:{M}");

    // Batch sizes to benchmark
    let batch_sizes = vec![2, 3, 4, 5, 8, 10, 20, 30, 32];

    for batch_size in batch_sizes {
        assert!(batch_size <= M);

        let group_name = format!("{}_batch_size_{}", &prefix_string, batch_size);
        let mut group = c.benchmark_group(&group_name);

        group.bench_with_input(
            BenchmarkId::new("prove", batch_size),
            &batch_size,
            |b, &bs| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_prover: Prover<_, Affine<PallasConfig>> = Prover::new(
                        &SRParamsPallasLeaf.even_parameters.pc_gens,
                        pallas_transcript,
                    );

                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
                        Prover::new(&SRParamsPallasLeaf.odd_parameters.pc_gens, vesta_transcript);

                    let indices: Vec<u32> = (0..bs as u32).collect();
                    let paths = curve_tree.get_paths_to_leaves(indices.as_slice()).unwrap();

                    let (path_commitments, _) = paths
                    .batched_select_and_rerandomize_prover_gadget_new::<
                        _,
                        PallasParams,
                        VestaParams,
                    >(
                        &mut pallas_prover,
                        &mut vesta_prover,
                        &*SRProofParamsNewPallasLeaf,
                        &mut rng,
                        None,
                    )
                    .expect("Failed to prove batched select and rerandomize");

                    let (pallas_proof, vesta_proof) = prove(
                        pallas_prover,
                        vesta_prover,
                        &SRProofParamsNewPallasLeaf.even_parameters.bp_gens(),
                        &SRProofParamsNewPallasLeaf.odd_parameters.bp_gens(),
                        &mut rng,
                    )
                    .unwrap();

                    black_box((path_commitments, pallas_proof, vesta_proof))
                });
            },
        );

        let (path_commitments, pallas_proof, vesta_proof) = {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_prover: Prover<_, Affine<PallasConfig>> = Prover::new(
                &SRParamsPallasLeaf.even_parameters.pc_gens,
                pallas_transcript,
            );

            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_prover: Prover<_, Affine<VestaConfig>> =
                Prover::new(&SRParamsPallasLeaf.odd_parameters.pc_gens, vesta_transcript);

            let indices: Vec<u32> = (0..batch_size as u32).collect();
            let paths = curve_tree.get_paths_to_leaves(indices.as_slice()).unwrap();

            let (path_commitments, _) = paths
                .batched_select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
                    &mut pallas_prover,
                    &mut vesta_prover,
                    &*SRProofParamsNewPallasLeaf,
                    &mut rng,
                    None,
                )
                .expect("Failed to prove batched select and rerandomize");

            let (pallas_proof, vesta_proof) = prove(
                pallas_prover,
                vesta_prover,
                &SRProofParamsNewPallasLeaf.even_parameters.bp_gens(),
                &SRProofParamsNewPallasLeaf.odd_parameters.bp_gens(),
                &mut rng,
            )
            .unwrap();

            (path_commitments, pallas_proof, vesta_proof)
        };

        let proof_size = path_commitments.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size();
        println!(
            "{}_batch_size_{}_proof_size: {} bytes",
            &prefix_string, batch_size, proof_size
        );

        group.bench_with_input(
            BenchmarkId::new("verify", batch_size),
            &batch_size,
            |b, _| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);

                    let root = curve_tree.root_node();
                    path_commitments
                        .batched_select_and_rerandomize_verifier_gadget::<
                            PallasParams,
                            VestaParams,
                        >(
                            &root,
                            &mut pallas_verifier,
                            &mut vesta_verifier,
                            &*SRProofParamsNewPallasLeaf,
                        )
                        .unwrap();

                    verify(
                        pallas_verifier,
                        vesta_verifier,
                        &pallas_proof,
                        &vesta_proof,
                        &SRParamsPallasLeaf.even_parameters.pc_gens,
                        &SRParamsPallasLeaf.even_parameters.bp_gens,
                        &SRParamsPallasLeaf.odd_parameters.pc_gens,
                        &SRParamsPallasLeaf.odd_parameters.bp_gens,
                        &mut rng,
                    )
                    .unwrap();
                });
            },
        );
    }
}

criterion_group! {
    name = batched_curve_tree_new_benches;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(60));
    targets =
    bench_batched_curve_tree_varying_batch_size_new,
}

criterion_main!(batched_curve_tree_new_benches);
