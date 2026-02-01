use ark_ec::AffineRepr;
use ark_pallas::PallasConfig;
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::*;
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::{thread_rng, Rng};
use relations::parameters::SelRerandParameters;
use relations::range_proof::range_proof;

type VestaA = ark_vesta::Affine;
type VestaScalar = <VestaA as AffineRepr>::ScalarField;
type VestaAffine = ark_ec::short_weierstrass::Affine<VestaConfig>;

fn range_proof_prove(c: &mut Criterion, n: usize) {
    let mut rng = thread_rng();
    let generators_length = 1 << 11; // 2048 generators should be enough

    let sr_params =
        SelRerandParameters::<PallasConfig, VestaConfig>::new(generators_length, generators_length)
            .expect("Failed to create SelRerandParameters");

    let value: u128 = if n <= 64 {
        (rng.gen::<u64>() as u128) % (1u128 << n)
    } else {
        rng.gen::<u128>() % (1u128 << n)
    };
    let blinding = VestaScalar::rand(&mut rng);

    let bench_name = format!("range_proof_prove_n{}", n);
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let mut transcript = MerlinTranscript::new(b"range_proof");
            let mut prover: Prover<_, VestaAffine> =
                Prover::new(&sr_params.odd_parameters.pc_gens, &mut transcript);

            let (_, var) = prover.commit(value.into(), blinding);

            range_proof(&mut prover, var.into(), Some(value), n).unwrap();

            let proof = prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();

            black_box(proof)
        })
    });
}

fn range_proof_verify(c: &mut Criterion, n: usize) {
    let mut rng = thread_rng();
    let generators_length = 1 << 11;

    let sr_params =
        SelRerandParameters::<PallasConfig, VestaConfig>::new(generators_length, generators_length)
            .expect("Failed to create SelRerandParameters");

    let value: u128 = if n <= 64 {
        (rng.gen::<u64>() as u128) % (1u128 << n)
    } else {
        rng.gen::<u128>() % (1u128 << n)
    };

    let mut transcript = MerlinTranscript::new(b"range_proof");
    let mut prover: Prover<_, VestaAffine> =
        Prover::new(&sr_params.odd_parameters.pc_gens, &mut transcript);
    let blinding = VestaScalar::rand(&mut rng);
    let (commitment, var) = prover.commit(value.into(), blinding);
    range_proof(&mut prover, var.into(), Some(value), n).unwrap();
    let proof = prover.prove(&sr_params.odd_parameters.bp_gens).unwrap();

    println!(
        "Proof size for n={}: {} bytes",
        n,
        proof.serialized_size(Compress::Yes)
    );

    let bench_name = format!("range_proof_verify_n{}", n);
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let mut transcript = MerlinTranscript::new(b"range_proof");
            let mut verifier = Verifier::<_, VestaAffine>::new(&mut transcript);
            let var = verifier.commit(commitment);
            range_proof(&mut verifier, var.into(), None, n).unwrap();

            let result = verifier.verify(
                &proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
            ).unwrap();
            black_box(result)
        })
    });
}

fn range_proof_prove_n30(c: &mut Criterion) {
    range_proof_prove(c, 30);
}

fn range_proof_verify_n30(c: &mut Criterion) {
    range_proof_verify(c, 30);
}

fn range_proof_prove_n32(c: &mut Criterion) {
    range_proof_prove(c, 32);
}

fn range_proof_verify_n32(c: &mut Criterion) {
    range_proof_verify(c, 32);
}

fn range_proof_prove_n34(c: &mut Criterion) {
    range_proof_prove(c, 34);
}

fn range_proof_verify_n34(c: &mut Criterion) {
    range_proof_verify(c, 34);
}

fn range_proof_prove_n36(c: &mut Criterion) {
    range_proof_prove(c, 36);
}

fn range_proof_verify_n36(c: &mut Criterion) {
    range_proof_verify(c, 36);
}

fn range_proof_verify_n40(c: &mut Criterion) {
    range_proof_verify(c, 40);
}

fn range_proof_verify_n50(c: &mut Criterion) {
    range_proof_verify(c, 50);
}

fn range_proof_verify_n58(c: &mut Criterion) {
    range_proof_verify(c, 58);
}

fn range_proof_verify_n64(c: &mut Criterion) {
    range_proof_verify(c, 64);
}

criterion_group!(
    range_proof_benches,
    range_proof_prove_n30,
    range_proof_verify_n30,
    range_proof_prove_n32,
    range_proof_verify_n32,
    range_proof_prove_n34,
    range_proof_verify_n34,
    range_proof_prove_n36,
    range_proof_verify_n36,
    range_proof_verify_n40,
    range_proof_verify_n50,
    range_proof_verify_n58,
    range_proof_verify_n64,
);

criterion_main!(range_proof_benches);
