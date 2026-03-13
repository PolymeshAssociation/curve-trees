#[macro_use]
extern crate criterion;
use criterion::{BenchmarkId, Criterion};

extern crate bulletproofs;
use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier};

extern crate relations;
use relations::select::*;

use ark_pallas::Fq as PallasBase;
use ark_vesta::Affine as VestaAffine;

use ark_ec::AffineRepr;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};

use core::iter;
use rand::seq::SliceRandom;

type VestaScalar = <VestaAffine as AffineRepr>::ScalarField;

fn bench_select(c: &mut Criterion) {
    let pg = PedersenGens::<VestaAffine>::default();
    let bpg = BulletproofGens::<VestaAffine>::new(1 << 12, 1);

    let mut group = c.benchmark_group("select");

    for set_size in [512, 1000, 2000].iter() {
        let mut rng = rand::thread_rng();
        let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(*set_size)
            .collect();
        let index = 42;
        let x = xs[index];

        // Prove benchmark
        group.bench_with_input(BenchmarkId::new("prove", set_size), set_size, |b, _| {
            b.iter(|| {
                let mut rng = rand::thread_rng();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
                let blinding_xs = PallasBase::rand(&mut rng);
                let (_, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
                let blinding_x = PallasBase::rand(&mut rng);
                let (_, x_var) = prover.commit(x, blinding_x);

                select(
                    &mut prover,
                    x_var.into(),
                    xs_vars.into_iter().map(|v| v.into()),
                );

                prover.prove(&bpg).unwrap();
            });
        });

        // Generate proof for verification
        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
        let blinding_xs = PallasBase::rand(&mut rng);
        let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);
        let blinding_x = PallasBase::rand(&mut rng);
        let (x_comm, x_var) = prover.commit(x, blinding_x);

        select(
            &mut prover,
            x_var.into(),
            xs_vars.into_iter().map(|v| v.into()),
        );

        let proof = prover.prove(&bpg).unwrap();
        println!(
            "select (set_size={}): proof size = {} bytes",
            set_size,
            proof.compressed_size()
        );

        // Verify benchmark
        group.bench_with_input(BenchmarkId::new("verify", set_size), set_size, |b, _| {
            b.iter(|| {
                let mut transcript = MerlinTranscript::new(b"select");
                let mut verifier: Verifier<_, VestaAffine> = Verifier::new(&mut transcript);
                let xs_vars = verifier.commit_vec(*set_size, xs_comm.clone());
                let x_var = verifier.commit(x_comm.clone());

                select(
                    &mut verifier,
                    x_var.into(),
                    xs_vars.into_iter().map(|v| v.into()),
                );

                verifier.verify(&proof, &pg, &bpg).unwrap();
            });
        });
    }
    group.finish();
}

fn bench_select_public_set(c: &mut Criterion) {
    let pg = PedersenGens::<VestaAffine>::default();
    let bpg = BulletproofGens::<VestaAffine>::new(1 << 12, 1);

    let mut group = c.benchmark_group("select_public_set");

    for set_size in [512, 1000, 2000].iter() {
        let mut rng = rand::thread_rng();
        let xs: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(*set_size)
            .collect();
        let index = 42;
        let x = xs[index];

        // Prove benchmark
        group.bench_with_input(BenchmarkId::new("prove", set_size), set_size, |b, _| {
            b.iter(|| {
                let mut rng = rand::thread_rng();
                let mut transcript = MerlinTranscript::new(b"select");
                let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
                let blinding_x = PallasBase::rand(&mut rng);
                let (_, x_var) = prover.commit(x, blinding_x);

                select_public_set(&mut prover, x_var.into(), xs.as_slice());

                prover.prove(&bpg).unwrap();
            });
        });

        // Generate proof for verification
        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
        let blinding_x = PallasBase::rand(&mut rng);
        let (x_comm, x_var) = prover.commit(x, blinding_x);

        select_public_set(&mut prover, x_var.into(), xs.as_slice());

        let proof = prover.prove(&bpg).unwrap();
        println!(
            "select_public_set (set_size={}): proof size = {} bytes",
            set_size,
            proof.compressed_size()
        );

        // Verify benchmark
        group.bench_with_input(BenchmarkId::new("verify", set_size), set_size, |b, _| {
            b.iter(|| {
                let mut transcript = MerlinTranscript::new(b"select");
                let mut verifier: Verifier<_, VestaAffine> = Verifier::new(&mut transcript);
                let x_var = verifier.commit(x_comm.clone());

                select_public_set(&mut verifier, x_var.into(), xs.as_slice());

                verifier.verify(&proof, &pg, &bpg).unwrap();
            });
        });
    }
    group.finish();
}

fn bench_multi_select_naive(c: &mut Criterion) {
    let pg = PedersenGens::<VestaAffine>::default();
    let bpg = BulletproofGens::<VestaAffine>::new(1 << 12, 1);

    let mut group = c.benchmark_group("multi_select_naive");

    for (set_size, subset_size) in [(512, 2), (512, 3), (512, 4)].iter() {
        let label = format!("set_{}_subset_{}", set_size, subset_size);

        let mut rng = rand::thread_rng();
        let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(*set_size)
            .collect();
        let xs = ys
            .choose_multiple(&mut rng, *subset_size)
            .cloned()
            .collect::<Vec<_>>();

        // Prove benchmark
        group.bench_with_input(
            BenchmarkId::new("prove", &label),
            &(set_size, subset_size),
            |b, _| {
                b.iter(|| {
                    let mut rng = rand::thread_rng();
                    let mut transcript = MerlinTranscript::new(b"select");
                    let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
                    let blinding_ys = PallasBase::rand(&mut rng);
                    let (_, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
                    let blinding_xs = PallasBase::rand(&mut rng);
                    let (_, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                    multi_select_naive(
                        &mut prover,
                        xs_vars.into_iter().map(|v| v.into()).collect(),
                        ys_vars.into_iter().map(|v| v.into()).collect(),
                    );

                    prover.prove(&bpg).unwrap();
                });
            },
        );

        // Generate proof for verification
        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
        let blinding_ys = PallasBase::rand(&mut rng);
        let (ys_comm, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
        let blinding_xs = PallasBase::rand(&mut rng);
        let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

        multi_select_naive(
            &mut prover,
            xs_vars.into_iter().map(|v| v.into()).collect(),
            ys_vars.into_iter().map(|v| v.into()).collect(),
        );

        let proof = prover.prove(&bpg).unwrap();
        println!(
            "multi_select_naive (set_size={}, subset_size={}): proof size = {} bytes",
            set_size,
            subset_size,
            proof.compressed_size()
        );

        // Verify benchmark
        group.bench_with_input(
            BenchmarkId::new("verify", &label),
            &(set_size, subset_size),
            |b, _| {
                b.iter(|| {
                    let mut transcript = MerlinTranscript::new(b"select");
                    let mut verifier: Verifier<_, VestaAffine> = Verifier::new(&mut transcript);
                    let ys_vars = verifier.commit_vec(*set_size, ys_comm.clone());
                    let xs_vars = verifier.commit_vec(*subset_size, xs_comm.clone());

                    multi_select_naive(
                        &mut verifier,
                        xs_vars.into_iter().map(|v| v.into()).collect(),
                        ys_vars.into_iter().map(|v| v.into()).collect(),
                    );

                    verifier.verify(&proof, &pg, &bpg).unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_multi_select_ext_challenge(c: &mut Criterion) {
    let pg = PedersenGens::<VestaAffine>::default();
    let bpg = BulletproofGens::<VestaAffine>::new(1 << 12, 1);

    let mut group = c.benchmark_group("multi_select_ext_challenge");

    for (set_size, subset_size) in [(512, 2), (512, 3), (512, 4)].iter() {
        let label = format!("set_{}_subset_{}", set_size, subset_size);

        let mut rng = rand::thread_rng();
        let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(*set_size)
            .collect();
        let xs = ys
            .choose_multiple(&mut rng, *subset_size)
            .cloned()
            .collect::<Vec<_>>();

        // Prove benchmark
        group.bench_with_input(
            BenchmarkId::new("prove", &label),
            &(set_size, subset_size),
            |b, _| {
                b.iter(|| {
                    let mut rng = rand::thread_rng();
                    let mut transcript = MerlinTranscript::new(b"select");
                    let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
                    let blinding_ys = PallasBase::rand(&mut rng);
                    let (_, ys_vars) = prover.commit_vec(ys.as_slice(), blinding_ys, &bpg);
                    let blinding_xs = PallasBase::rand(&mut rng);
                    let (_, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                    let c = prover.transcript().challenge_scalar(b"challenge");

                    multi_select_ext_challenge(
                        &mut prover,
                        xs_vars.into_iter().map(|v| v.into()).collect(),
                        ys_vars.into_iter().map(|v| v.into()).collect(),
                        c,
                    );

                    prover.prove(&bpg).unwrap();
                });
            },
        );

        // Generate proof for verification
        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
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
        );

        let proof = prover.prove(&bpg).unwrap();
        println!(
            "multi_select_ext_challenge (set_size={}, subset_size={}): proof size = {} bytes",
            set_size,
            subset_size,
            proof.compressed_size()
        );

        // Verify benchmark
        group.bench_with_input(
            BenchmarkId::new("verify", &label),
            &(set_size, subset_size),
            |b, _| {
                b.iter(|| {
                    let mut transcript = MerlinTranscript::new(b"select");
                    let mut verifier: Verifier<_, VestaAffine> = Verifier::new(&mut transcript);
                    let ys_vars = verifier.commit_vec(*set_size, ys_comm.clone());
                    let xs_vars = verifier.commit_vec(*subset_size, xs_comm.clone());

                    let c = verifier.transcript().challenge_scalar(b"multi_select");

                    multi_select_ext_challenge(
                        &mut verifier,
                        xs_vars.into_iter().map(|v| v.into()).collect(),
                        ys_vars.into_iter().map(|v| v.into()).collect(),
                        c,
                    );

                    verifier.verify(&proof, &pg, &bpg).unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_multi_select_public_set_ext_challenge(c: &mut Criterion) {
    let pg = PedersenGens::<VestaAffine>::default();
    let bpg = BulletproofGens::<VestaAffine>::new(1 << 12, 1);

    let mut group = c.benchmark_group("multi_select_public_set_ext_challenge");

    for (set_size, subset_size) in [(512, 2), (512, 3), (512, 4)].iter() {
        let label = format!("set_{}_subset_{}", set_size, subset_size);

        let mut rng = rand::thread_rng();
        let ys: Vec<_> = iter::from_fn(|| Some(VestaScalar::rand(&mut rng)))
            .take(*set_size)
            .collect();
        let xs = ys
            .choose_multiple(&mut rng, *subset_size)
            .cloned()
            .collect::<Vec<_>>();

        // Prove benchmark
        group.bench_with_input(
            BenchmarkId::new("prove", &label),
            &(set_size, subset_size),
            |b, _| {
                b.iter(|| {
                    let mut rng = rand::thread_rng();
                    let mut transcript = MerlinTranscript::new(b"select");
                    let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
                    let blinding_xs = PallasBase::rand(&mut rng);
                    let (_, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

                    let c = prover.transcript().challenge_scalar(b"challenge");

                    multi_select_public_set_ext_challenge(
                        &mut prover,
                        xs_vars.into_iter().map(|v| v.into()).collect(),
                        ys.as_slice(),
                        c,
                    );

                    prover.prove(&bpg).unwrap();
                });
            },
        );

        // Generate proof for verification
        let mut rng = rand::thread_rng();
        let mut transcript = MerlinTranscript::new(b"select");
        let mut prover: Prover<_, VestaAffine> = Prover::new(&pg, &mut transcript);
        let blinding_xs = PallasBase::rand(&mut rng);
        let (xs_comm, xs_vars) = prover.commit_vec(xs.as_slice(), blinding_xs, &bpg);

        let c = prover.transcript().challenge_scalar(b"challenge");

        multi_select_public_set_ext_challenge(
            &mut prover,
            xs_vars.into_iter().map(|v| v.into()).collect(),
            ys.as_slice(),
            c,
        );

        let proof = prover.prove(&bpg).unwrap();
        println!("multi_select_public_set_ext_challenge (set_size={}, subset_size={}): proof size = {} bytes", set_size, subset_size, proof.compressed_size());

        // Verify benchmark
        group.bench_with_input(
            BenchmarkId::new("verify", &label),
            &(set_size, subset_size),
            |b, _| {
                b.iter(|| {
                    let mut transcript = MerlinTranscript::new(b"select");
                    let mut verifier: Verifier<_, VestaAffine> = Verifier::new(&mut transcript);
                    let xs_vars = verifier.commit_vec(*subset_size, xs_comm.clone());

                    let c = verifier.transcript().challenge_scalar(b"multi_select");

                    multi_select_public_set_ext_challenge(
                        &mut verifier,
                        xs_vars.into_iter().map(|v| v.into()).collect(),
                        ys.as_slice(),
                        c,
                    );

                    verifier.verify(&proof, &pg, &bpg).unwrap();
                });
            },
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_select,
    bench_select_public_set,
    bench_multi_select_naive,
    bench_multi_select_ext_challenge,
    bench_multi_select_public_set_ext_challenge
);
criterion_main!(benches);
