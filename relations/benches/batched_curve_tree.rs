#[macro_use]
extern crate criterion;

use std::time::Duration;
use ark_ff::PrimeField;
use criterion::{BenchmarkId, Criterion};

extern crate bulletproofs;
use bulletproofs::r1cs::{Prover, Verifier};

extern crate relations;
use relations::curve_tree::*;
use relations::utils::{prove, verify};

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

use dock_crypto_utils::transcript::MerlinTranscript;

fn bench_batched_curve_tree_varying_batch_size(c: &mut Criterion) {
    // Benchmark with L=256, M=32, height=4, varying batch sizes
    bench_batched_curve_tree_with_varying_batch_size::<
        256,
        32,
        PallasBase,
        PallasConfig,
        VestaConfig,
    >(c, 4, 18);
}

fn bench_batched_curve_tree_with_varying_batch_size<
    const L: usize,
    const M: usize,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    c: &mut Criterion,
    depth: usize,
    generators_length_log_2: usize,
) {
    let mut rng = rand::thread_rng();
    let generators_length = 1 << generators_length_log_2;

    let sr_params = SelRerandParameters::<P0, P1>::new(generators_length, generators_length)
        .expect("Failed to create SelRerandParameters");

    // Create the curve tree once with max batch size M
    let set = (0..M)
        .map(|_| Affine::<P0>::rand(&mut rng))
        .collect::<Vec<_>>();
    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&set, &sr_params, Some(depth));

    let prefix_string = format!("BatchedCurveTree_Curves:L:{L}_D:{depth}_M:{M}");

    // Batch sizes to benchmark
    let batch_sizes = vec![2, 3, 4, 5, 8, 10, 20, 30, 32];

    for batch_size in batch_sizes {
        assert!(batch_size <= M);

        let group_name = format!(
            "{}_batch_size_{}",
            &prefix_string, batch_size
        );
        let mut group = c.benchmark_group(&group_name);

        group.bench_with_input(
            BenchmarkId::new("prove", batch_size),
            &batch_size,
            |b, &bs| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_prover: Prover<_, Affine<P0>> =
                        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_prover: Prover<_, Affine<P1>> =
                        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

                    let indices: Vec<u32> = (0..bs as u32).collect();

                    let (path_commitments, _) = curve_tree
                        .batched_select_and_rerandomize_prover_gadget(
                            indices.as_slice(),
                            &mut pallas_prover,
                            &mut vesta_prover,
                            &sr_params,
                            &mut rng,
                        )
                        .expect("Failed to prove batched select and rerandomize");

                    let (pallas_proof, vesta_proof) = prove(
                        pallas_prover,
                        vesta_prover,
                        &sr_params,
                        &mut rng,
                    ).unwrap();

                    (path_commitments, pallas_proof, vesta_proof)
                });
            },
        );

        let (path_commitments, pallas_proof, vesta_proof) = {
            let mut rng_local = rand::thread_rng();

            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_prover: Prover<_, Affine<P0>> =
                Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_prover: Prover<_, Affine<P1>> =
                Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

            let indices: Vec<u32> = (0..batch_size as u32).collect();

            let (path_commitments, _) = curve_tree
                .batched_select_and_rerandomize_prover_gadget(
                    indices.as_slice(),
                    &mut pallas_prover,
                    &mut vesta_prover,
                    &sr_params,
                    &mut rng,
                )
                .expect("Failed to prove batched select and rerandomize");

            let (pallas_proof, vesta_proof) = prove(
                pallas_prover,
                vesta_prover,
                &sr_params,
                &mut rng,
            ).unwrap();

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

                    let _ = curve_tree.batched_select_and_rerandomize_verifier_gadget(
                        &mut pallas_verifier,
                        &mut vesta_verifier,
                        path_commitments.clone(),
                        &sr_params,
                    );

                    verify(
                        pallas_verifier,
                        vesta_verifier,
                        &pallas_proof,
                        &vesta_proof,
                        &sr_params,
                        &mut rng,
                    ).unwrap();
                });
            },
        );
    }
}

criterion_group! {
    name = batched_curve_tree_benches;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(60));
    targets =
    bench_batched_curve_tree_varying_batch_size,
}

criterion_main!(batched_curve_tree_benches);


