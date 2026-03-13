#[macro_use]
extern crate criterion;

use ark_ff::PrimeField;
use criterion::{BenchmarkId, Criterion};
use std::hint::black_box;
use std::time::Duration;

extern crate bulletproofs;
use bulletproofs::r1cs::{Prover, Verifier};

extern crate relations;
use relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use relations::curve_tree::*;
use relations::utils::{prove, verify};

use ark_pallas::{Fq as PallasBase, PallasConfig};
use ark_vesta::VestaConfig;

use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

use dock_crypto_utils::transcript::MerlinTranscript;
use relations::parameters::{SelRerandParameters, SelRerandProofParameters};

fn bench_batched_curve_tree_varying_batch_size(c: &mut Criterion) {
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
    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

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

        let group_name = format!("{}_batch_size_{}", &prefix_string, batch_size);
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
                            &sr_proof_params,
                            &mut rng,
                        )
                        .expect("Failed to prove batched select and rerandomize");

                    let (pallas_proof, vesta_proof) = prove(
                        pallas_prover,
                        vesta_prover,
                        &sr_params.even_parameters.bp_gens,
                        &sr_params.odd_parameters.bp_gens,
                        &mut rng,
                    )
                    .unwrap();

                    (path_commitments, pallas_proof, vesta_proof)
                });
            },
        );

        let (path_commitments, pallas_proof, vesta_proof) = {
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
                    &sr_proof_params,
                    &mut rng,
                )
                .expect("Failed to prove batched select and rerandomize");

            let (pallas_proof, vesta_proof) = prove(
                pallas_prover,
                vesta_prover,
                &sr_params.even_parameters.bp_gens,
                &sr_params.odd_parameters.bp_gens,
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
                        .batched_select_and_rerandomize_verifier_gadget(
                            &root,
                            &mut pallas_verifier,
                            &mut vesta_verifier,
                            &sr_proof_params,
                        )
                        .unwrap();

                    verify(
                        pallas_verifier,
                        vesta_verifier,
                        &pallas_proof,
                        &vesta_proof,
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                        &sr_params.odd_parameters.pc_gens,
                        &sr_params.odd_parameters.bp_gens,
                        &mut rng,
                    )
                    .unwrap();
                });
            },
        );
    }
}

fn bench_combined_vs_common_root(c: &mut Criterion) {
    bench_combined_vs_common_root_with_parameters::<512, 4, PallasBase, PallasConfig, VestaConfig>(
        c, 4, 17,
    );
}

fn bench_combined_vs_common_root_with_parameters<
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
    let sr_proof_params = SelRerandProofParameters::try_from(sr_params.clone()).unwrap();

    let group_name = format!("combined_vs_common_root_L{}_M{}_D{}", L, M, depth);
    let mut group = c.benchmark_group(group_name);

    let path_counts = [10, 20, 30, 40];
    let mut leaves = Vec::<Affine<P0>>::new();
    for _ in 0..*path_counts.iter().max().unwrap() {
        leaves.push(Affine::<P0>::rand(&mut rng));
    }
    let curve_tree = CurveTree::<L, M, P0, P1>::from_leaves(&leaves, &sr_params, Some(depth));

    for num_paths in path_counts {
        // ceil(num_paths/M)
        let mut paths = vec![];
        for indices in (0..num_paths).collect::<Vec<_>>().chunks(M) {
            paths.push(curve_tree.get_paths_to_leaves(&indices).unwrap());
        }

        // Benchmark Combined Proof - Proving
        group.bench_with_input(
            BenchmarkId::new("combined_prove", num_paths),
            &num_paths,
            |b, _| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_prover: Prover<_, Affine<P0>> =
                        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_prover: Prover<_, Affine<P1>> =
                        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

                    let mut path_commitments_list: Vec<
                        SelectAndRerandomizeMultiPath<L, M, P0, P1>,
                    > = vec![];
                    for p in &paths {
                        let (path_commitments, _) = p
                            .batched_select_and_rerandomize_prover_gadget(
                                &mut pallas_prover,
                                &mut vesta_prover,
                                &sr_proof_params,
                                &mut rng,
                            )
                            .unwrap();
                        path_commitments_list.push(path_commitments);
                    }

                    let p = prove(
                        pallas_prover,
                        vesta_prover,
                        &sr_params.even_parameters.bp_gens,
                        &sr_params.odd_parameters.bp_gens,
                        &mut rng,
                    )
                    .unwrap();
                    black_box(p);
                });
            },
        );

        // Pre-generate combined proof for verification benchmark
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let mut path_commitments_list: Vec<SelectAndRerandomizeMultiPath<L, M, P0, P1>> = vec![];
        for p in &paths {
            let (path_commitments, _) = p
                .batched_select_and_rerandomize_prover_gadget(
                    &mut pallas_prover,
                    &mut vesta_prover,
                    &sr_proof_params,
                    &mut rng,
                )
                .unwrap();
            path_commitments_list.push(path_commitments);
        }

        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();

        println!("For {num_paths} paths");
        println!(
            "Combined proof size = {} bytes",
            pallas_proof.compressed_size() + vesta_proof.compressed_size()
        );

        group.bench_with_input(
            BenchmarkId::new("combined_verify", num_paths),
            &num_paths,
            |b, _| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);

                    let root = curve_tree.root_node();
                    for path_commitments in &path_commitments_list {
                        path_commitments
                            .batched_select_and_rerandomize_verifier_gadget(
                                &root,
                                &mut pallas_verifier,
                                &mut vesta_verifier,
                                &sr_proof_params,
                            )
                            .unwrap();
                    }

                    verify(
                        pallas_verifier,
                        vesta_verifier,
                        &pallas_proof,
                        &vesta_proof,
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                        &sr_params.odd_parameters.pc_gens,
                        &sr_params.odd_parameters.bp_gens,
                        &mut rng,
                    )
                    .unwrap();
                });
            },
        );

        // Benchmark Common Root Proof
        group.bench_with_input(
            BenchmarkId::new("common_root_prove", num_paths),
            &num_paths,
            |b, _| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_prover: Prover<_, Affine<P0>> =
                        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_prover: Prover<_, Affine<P1>> =
                        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

                    let _ = CurveTreeWitnessMultiPath::batched_select_and_rerandomize_prover_gadget_for_common_root(
                        &paths,
                        &mut pallas_prover,
                        &mut vesta_prover,
                        &sr_proof_params,
                        &mut rng,
                    )
                    .unwrap();

                    let p = prove(pallas_prover, vesta_prover, &sr_params.even_parameters.bp_gens, &sr_params.odd_parameters.bp_gens, &mut rng).unwrap();
                    black_box(p);
                });
            },
        );

        // Pre-generate common root proof for verification benchmark
        let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<P0>> =
            Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);

        let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<P1>> =
            Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

        let (path_commitments_common, _) =
            CurveTreeWitnessMultiPath::batched_select_and_rerandomize_prover_gadget_for_common_root(
                &paths,
                &mut pallas_prover,
                &mut vesta_prover,
                &sr_proof_params,
                &mut rng,
            )
            .unwrap();

        let (pallas_proof, vesta_proof) = prove(
            pallas_prover,
            vesta_prover,
            &sr_params.even_parameters.bp_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng,
        )
        .unwrap();

        println!(
            "Common root proof size = {} bytes",
            pallas_proof.compressed_size() + vesta_proof.compressed_size()
        );

        group.bench_with_input(
            BenchmarkId::new("common_root_verify", num_paths),
            &num_paths,
            |b, _| {
                b.iter(|| {
                    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut pallas_verifier = Verifier::new(pallas_transcript);
                    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
                    let mut vesta_verifier = Verifier::new(vesta_transcript);

                    let root = curve_tree.root_node();
                    SelectAndRerandomizeMultiPath::batched_select_and_rerandomize_verifier_gadget_for_common_root(
                        &path_commitments_common,
                        &root,
                        &mut pallas_verifier,
                        &mut vesta_verifier,
                        &sr_proof_params,
                    )
                    .unwrap();

                    verify(
                        pallas_verifier,
                        vesta_verifier,
                        &pallas_proof,
                        &vesta_proof,
                        &sr_params.even_parameters.pc_gens,
                        &sr_params.even_parameters.bp_gens,
                        &sr_params.odd_parameters.pc_gens,
                        &sr_params.odd_parameters.bp_gens,
                        &mut rng,
                    )
                    .unwrap();
                });
            },
        );
    }

    group.finish();
}

criterion_group! {
    name = batched_curve_tree_benches;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(60));
    targets =
    bench_batched_curve_tree_varying_batch_size,
    bench_combined_vs_common_root,
}

criterion_main!(batched_curve_tree_benches);
