use ark_dlog_gadget::dlog::{
    DiscreteLogParameters, commit_witness_chunks_prover, commit_witness_chunks_verifier,
    create_divisor_and_decomposition, discrete_log_blinding,
};
use ark_dlog_gadget::utils::CurveSpec;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ec_divisors::DivisorCurve;
use ark_ec_divisors::curves::helios::{HeliosParams, Point as HeliosPoint};
use ark_ec_divisors::curves::pallas::{PallasParams, Point as PallasPoint};
use ark_ec_divisors::curves::selene::{Point as SelenePoint, SeleneParams};
use ark_ec_divisors::curves::vesta::{Point as VestaPoint, VestaParams};
use ark_ec_divisors::util::GeneratorTable;
use ark_ff::PrimeField;
use ark_helios::{Affine as HeliosAffine, Fq as HeliosFq, Fr as HeliosFr};
use ark_pallas::{Affine as PallasAffine, Fq, Fr};
use ark_selene::Affine as SeleneAffine;
use ark_serialize::CanonicalSerialize;
use ark_vesta::Affine as VestaAffine;
use bulletproofs::r1cs::{Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use criterion::{Criterion, criterion_group, criterion_main};
use dock_crypto_utils::transcript::MerlinTranscript;
use generic_array::ArrayLength;
use generic_array::typenum::{Sum, U1};
use rand::prelude::StdRng;
use rand_core::SeedableRng;
use std::hint::black_box;
use std::ops::Add;

type PallasBase = Fq;
type PallasScalar = Fr;
type VestaBase = Fr;
type VestaScalar = Fq;
type HeliosBase = HeliosFq;
type HeliosScalar = HeliosFr;
type SeleneBase = HeliosFr;
type SeleneScalar = HeliosFq;

fn bench_blinding_with_discrete_log_prove<C, Params, B, S, BP>(
    c: &mut Criterion,
    curve_name: &str,
    count: usize,
    vc_len: usize,
) where
    C: DivisorCurve<BaseField = B, ScalarField = S>,
    Params: DiscreteLogParameters,
    B: PrimeField,
    S: PrimeField,
    BP: AffineRepr<ScalarField = B>,
    C::Config: SWCurveConfig,
    Params::ScalarBits: Add<U1>,
    Sum<Params::ScalarBits, U1>: ArrayLength,
{
    let mut rng = StdRng::seed_from_u64(0);
    let curve = CurveSpec::<B> {
        a: C::Config::COEFF_A,
        b: C::Config::COEFF_B,
    };
    let pc_gens = PedersenGens::<BP>::default();
    let bp_gens = BulletproofGens::<BP>::new(512, 1);

    let t = C::random(&mut rng);
    let t_table = GeneratorTable::<B, Params>::new(t);

    let bench_name = format!(
        "{}_dlog_prove_count={},vc_len={}",
        curve_name, count, vc_len
    );
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            for _ in 0..count {
                let o = S::rand(&mut rng);
                let o_blind_point = t.mul(o);
                let o_point = C::generator().mul(S::rand(&mut rng));
                // O_tilde = o_point - o_blind_point
                let o_tilde_point = o_point.add(o_blind_point.neg());
                let (o_tilde_x, o_tilde_y) = C::to_xy(o_tilde_point).unwrap();
                let (o_x, o_y) = C::to_xy(o_point).unwrap();

                let transcript = MerlinTranscript::new(b"bench");
                let mut prover = Prover::new(&pc_gens, transcript);

                let (comm_orig, mut vars_orig) =
                    prover.commit_vec(&[o_x, o_y], B::rand(&mut rng), &bp_gens);
                let o_y_var = vars_orig.pop().unwrap();
                let o_x_var = vars_orig.pop().unwrap();

                let (comms, o_blind_claim) = {
                    let witness =
                        create_divisor_and_decomposition::<_, C, Params>(&t_table, o).unwrap();
                    let (comms, _, o_blind_claim) =
                        commit_witness_chunks_prover::<_, _, _, Params>(
                            &mut rng,
                            &mut prover,
                            &witness,
                            vc_len,
                            &bp_gens,
                        )
                        .unwrap();

                    (comms, o_blind_claim)
                };

                discrete_log_blinding(
                    &mut prover,
                    (o_x_var, o_y_var),
                    o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&t_table],
                )
                .unwrap();

                let proof = prover.prove(&bp_gens).unwrap();
                black_box(proof);
                black_box(comms);
                black_box(comm_orig);
            }
        })
    });
}

fn bench_blinding_with_discrete_log_verify<C, Params, B, S, BP>(
    c: &mut Criterion,
    curve_name: &str,
    count: usize,
    vc_len: usize,
) where
    C: DivisorCurve<BaseField = B, ScalarField = S>,
    Params: DiscreteLogParameters,
    B: PrimeField,
    S: PrimeField,
    BP: AffineRepr<ScalarField = B>,
    C::Config: SWCurveConfig,
    Params::ScalarBits: Add<U1>,
    Sum<Params::ScalarBits, U1>: ArrayLength,
{
    let mut rng = StdRng::seed_from_u64(0);
    let curve = CurveSpec::<B> {
        a: C::Config::COEFF_A,
        b: C::Config::COEFF_B,
    };
    let pc_gens = PedersenGens::<BP>::default();
    let bp_gens = BulletproofGens::<BP>::new(512, 1);

    let t = C::random(&mut rng);
    let t_table = GeneratorTable::<B, Params>::new(t);

    let mut all_o_tilde_points = Vec::new();
    let mut all_proofs = Vec::new();
    let mut all_divisor_commitments = Vec::new();
    let mut all_comm_orig = Vec::new();

    let mut proof_size = 0;
    for _ in 0..count {
        let o = S::rand(&mut rng);
        let o_blind_point = t.mul(o);
        let o_point = C::generator().mul(S::rand(&mut rng));
        // O_tilde = o_point - o_blind_point
        let o_tilde_point = o_point.add(o_blind_point.neg());
        let (o_tilde_x, o_tilde_y) = C::to_xy(o_tilde_point).unwrap();
        let (o_x, o_y) = C::to_xy(o_point).unwrap();

        let transcript = MerlinTranscript::new(b"bench");
        let mut prover = Prover::new(&pc_gens, transcript);

        let (comm_orig, mut vars_orig) =
            prover.commit_vec(&[o_x, o_y], B::rand(&mut rng), &bp_gens);
        let o_y_var = vars_orig.pop().unwrap();
        let o_x_var = vars_orig.pop().unwrap();

        let (comms, o_blind_claim) = {
            let witness = create_divisor_and_decomposition::<_, C, Params>(&t_table, o).unwrap();
            let (comms, _, o_blind_claim) = commit_witness_chunks_prover::<_, _, _, Params>(
                &mut rng,
                &mut prover,
                &witness,
                vc_len,
                &bp_gens,
            )
            .unwrap();

            (comms, o_blind_claim)
        };

        discrete_log_blinding(
            &mut prover,
            (o_x_var, o_y_var),
            o_blind_claim,
            (o_tilde_x, o_tilde_y),
            &curve,
            &[&t_table],
        )
        .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();
        if proof_size == 0 {
            proof_size =
                proof.compressed_size() + comms.compressed_size() + comm_orig.compressed_size();
        }
        all_proofs.push(proof);
        all_divisor_commitments.push(comms);
        all_comm_orig.push(comm_orig);
        all_o_tilde_points.push(o_tilde_point);
    }

    println!("{curve_name} - Proof size (single) for vc len={vc_len}: {proof_size}");

    let bench_name = format!(
        "{}_dlog_verify_count={},vc_len={}",
        curve_name, count, vc_len
    );
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            for i in 0..count {
                let (o_tilde_x, o_tilde_y) = C::to_xy(all_o_tilde_points[i]).unwrap();

                let transcript = MerlinTranscript::new(b"bench");
                let mut verifier = Verifier::new(transcript);

                let mut vars_orig = verifier.commit_vec(2, all_comm_orig[i]);
                let o_y_var = vars_orig.pop().unwrap();
                let o_x_var = vars_orig.pop().unwrap();

                let o_blind_claim = commit_witness_chunks_verifier::<_, _, Params>(
                    &mut verifier,
                    &all_divisor_commitments[i],
                    vc_len,
                );

                discrete_log_blinding(
                    &mut verifier,
                    (o_x_var, o_y_var),
                    o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&t_table],
                )
                .unwrap();

                let result = verifier.verify(&all_proofs[i], &pc_gens, &bp_gens).unwrap();
                black_box(result);
            }
        })
    });
}

fn bench_blinding_with_discrete_log_combined_prove<C, Params, B, S, BP>(
    c: &mut Criterion,
    curve_name: &str,
    count: usize,
    vc_len: usize,
) where
    C: DivisorCurve<BaseField = B, ScalarField = S>,
    Params: DiscreteLogParameters,
    B: PrimeField,
    S: PrimeField,
    BP: AffineRepr<ScalarField = B>,
    C::Config: SWCurveConfig,
    Params::ScalarBits: Add<U1>,
    Sum<Params::ScalarBits, U1>: ArrayLength,
{
    let mut rng = StdRng::seed_from_u64(0);
    let curve = CurveSpec::<B> {
        a: C::Config::COEFF_A,
        b: C::Config::COEFF_B,
    };
    let pc_gens = PedersenGens::<BP>::default();
    let bp_gens = BulletproofGens::<BP>::new(512, 1);

    let t = C::random(&mut rng);
    let t_table = GeneratorTable::<B, Params>::new(t);

    let bench_name = format!(
        "{}_dlog_combined_prove_count={},vc_len={}",
        curve_name, count, vc_len
    );
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let transcript = MerlinTranscript::new(b"bench");
            let mut prover = Prover::new(&pc_gens, transcript);

            let mut all_o = Vec::new();
            let mut all_o_coords = Vec::new();
            for _ in 0..count {
                let o_point = C::generator().mul(S::rand(&mut rng));
                all_o.push(o_point);
                let (o_x, o_y) = C::to_xy(o_point).unwrap();
                all_o_coords.push(o_x);
                all_o_coords.push(o_y);
            }

            let (comm_orig, all_o_vars) =
                prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

            let mut all_o_blind_claims = Vec::new();
            let mut all_o_tilde_points = Vec::new();
            let mut all_divisor_commitments = Vec::new();

            for i in 0..count {
                let o = S::rand(&mut rng);
                let o_blind_point = t.mul(o);
                let o_point = &all_o[i];
                let o_tilde_point = o_point.add(o_blind_point.neg());
                let (o_tilde_x, o_tilde_y) = C::to_xy(o_tilde_point).unwrap();
                all_o_tilde_points.push((o_tilde_x, o_tilde_y));

                let (comms, o_blind_claim) = {
                    let witness =
                        create_divisor_and_decomposition::<_, C, Params>(&t_table, o).unwrap();
                    let (comms, _, o_blind_claim) =
                        commit_witness_chunks_prover::<_, _, _, Params>(
                            &mut rng,
                            &mut prover,
                            &witness,
                            vc_len,
                            &bp_gens,
                        )
                        .unwrap();

                    (comms, o_blind_claim)
                };

                all_divisor_commitments.push(comms);
                all_o_blind_claims.push(o_blind_claim);
            }

            for (i, o_blind_claim) in all_o_blind_claims.into_iter().enumerate() {
                let (o_x_var, o_y_var) = (all_o_vars[2 * i], all_o_vars[2 * i + 1]);
                let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
                discrete_log_blinding(
                    &mut prover,
                    (o_x_var, o_y_var),
                    o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&t_table],
                )
                .unwrap();
            }

            let proof = prover.prove(&bp_gens).unwrap();
            black_box(proof);
            black_box(comm_orig);
            black_box(all_divisor_commitments);
        })
    });
}

fn bench_blinding_with_discrete_log_combined_verify<C, Params, B, S, BP>(
    c: &mut Criterion,
    curve_name: &str,
    count: usize,
    vc_len: usize,
) where
    C: DivisorCurve<BaseField = B, ScalarField = S>,
    Params: DiscreteLogParameters,
    B: PrimeField,
    S: PrimeField,
    BP: AffineRepr<ScalarField = B>,
    C::Config: SWCurveConfig,
    Params::ScalarBits: Add<U1>,
    Sum<Params::ScalarBits, U1>: ArrayLength,
{
    let mut rng = StdRng::seed_from_u64(0);
    let curve = CurveSpec::<B> {
        a: C::Config::COEFF_A,
        b: C::Config::COEFF_B,
    };
    let pc_gens = PedersenGens::<BP>::default();
    let bp_gens = BulletproofGens::<BP>::new(512, 1);

    let t = C::random(&mut rng);
    let t_table = GeneratorTable::<B, Params>::new(t);

    let transcript = MerlinTranscript::new(b"bench");
    let mut prover = Prover::new(&pc_gens, transcript);

    let mut all_o = Vec::new();
    let mut all_o_coords = Vec::new();
    for _ in 0..count {
        let o_point = C::generator().mul(S::rand(&mut rng));
        all_o.push(o_point);
        let (o_x, o_y) = C::to_xy(o_point).unwrap();
        all_o_coords.push(o_x);
        all_o_coords.push(o_y);
    }

    let (comm_orig, all_o_vars) = prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

    let mut all_o_blind_claims = Vec::new();
    let mut all_divisor_commitments = Vec::new();
    let mut all_o_tilde_points = Vec::new();

    for i in 0..count {
        let o = S::rand(&mut rng);
        let o_blind_point = t.mul(o);
        let o_point = &all_o[i];
        // O_tilde = o_point - o_blind_point
        let o_tilde_point = o_point.add(o_blind_point.neg());
        let (o_tilde_x, o_tilde_y) = C::to_xy(o_tilde_point).unwrap();
        all_o_tilde_points.push((o_tilde_x, o_tilde_y));

        let (comms, o_blind_claim) = {
            let witness = create_divisor_and_decomposition::<_, C, Params>(&t_table, o).unwrap();
            let (comms, _, o_blind_claim) = commit_witness_chunks_prover::<_, _, _, Params>(
                &mut rng,
                &mut prover,
                &witness,
                vc_len,
                &bp_gens,
            )
            .unwrap();

            (comms, o_blind_claim)
        };

        all_divisor_commitments.push(comms);
        all_o_blind_claims.push(o_blind_claim);
    }

    for (i, o_blind_claim) in all_o_blind_claims.into_iter().enumerate() {
        let (o_x_var, o_y_var) = (all_o_vars[2 * i], all_o_vars[2 * i + 1]);
        let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
        discrete_log_blinding(
            &mut prover,
            (o_x_var, o_y_var),
            o_blind_claim,
            (o_tilde_x, o_tilde_y),
            &curve,
            &[&t_table],
        )
        .unwrap();
    }

    let proof = prover.prove(&bp_gens).unwrap();
    println!(
        "{} - For {count} discrete log proofs, vc len={vc_len}, proof size: {}",
        curve_name,
        proof.compressed_size()
            + comm_orig.compressed_size()
            + all_divisor_commitments.compressed_size(),
    );

    let bench_name = format!(
        "{}_dlog_combined_verify_count={},vc_len={}",
        curve_name, count, vc_len
    );
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let transcript = MerlinTranscript::new(b"bench");
            let mut verifier = Verifier::new(transcript);

            let vars_orig = verifier.commit_vec(2 * count, comm_orig);

            let mut all_o_blind_claims = Vec::new();

            for i in 0..count {
                let o_x_var = vars_orig[2 * i + 0];
                let o_y_var = vars_orig[2 * i + 1];

                let o_blind_claim = commit_witness_chunks_verifier::<_, _, Params>(
                    &mut verifier,
                    &all_divisor_commitments[i],
                    vc_len,
                );
                all_o_blind_claims.push((o_blind_claim, o_x_var, o_y_var));
            }

            for (i, (o_blind_claim, o_x_var, o_y_var)) in all_o_blind_claims.into_iter().enumerate()
            {
                let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
                discrete_log_blinding(
                    &mut verifier,
                    (o_x_var, o_y_var),
                    o_blind_claim,
                    (o_tilde_x, o_tilde_y),
                    &curve,
                    &[&t_table],
                )
                .unwrap();
            }

            let result = verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
            black_box(result);
        })
    });
}

fn dlog_prove_1_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 1, 32);
}
fn dlog_verify_1_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 1, 32);
}
fn dlog_prove_5_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 32);
}
fn dlog_verify_5_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 32);
}
fn dlog_prove_1_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 1, 64);
}
fn dlog_verify_1_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 1, 64);
}
fn dlog_prove_5_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 64);
}
fn dlog_verify_5_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 64);
}
fn dlog_combined_prove_5_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 32);
}
fn dlog_combined_verify_5_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 32);
}
fn dlog_combined_prove_10_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 10, 32);
}
fn dlog_combined_verify_10_32_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 10, 32);
}
fn dlog_combined_prove_5_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 64);
}
fn dlog_combined_verify_5_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 64);
}
fn dlog_combined_prove_10_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 10, 64);
}
fn dlog_combined_verify_10_64_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 10, 64);
}
fn dlog_prove_1_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 1, 128);
}
fn dlog_verify_1_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 1, 128);
}
fn dlog_prove_5_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 128);
}
fn dlog_verify_5_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 128);
}
fn dlog_combined_prove_5_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 128);
}
fn dlog_combined_verify_5_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 5, 128);
}
fn dlog_combined_prove_10_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 10, 128);
}
fn dlog_combined_verify_10_128_pallas(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        PallasPoint,
        PallasParams,
        PallasBase,
        PallasScalar,
        VestaAffine,
    >(c, "pallas", 10, 128);
}

fn dlog_prove_1_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 1, 32);
}
fn dlog_verify_1_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 1, 32);
}
fn dlog_prove_5_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 32);
}
fn dlog_verify_5_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 32);
}
fn dlog_prove_1_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 1, 64);
}
fn dlog_verify_1_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 1, 64);
}
fn dlog_prove_5_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 64);
}
fn dlog_verify_5_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 64);
}
fn dlog_combined_prove_5_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 32);
}
fn dlog_combined_verify_5_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 32);
}
fn dlog_combined_prove_10_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 10, 32);
}
fn dlog_combined_verify_10_32_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 10, 32);
}
fn dlog_combined_prove_5_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 64);
}
fn dlog_combined_verify_5_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 64);
}
fn dlog_combined_prove_10_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 10, 64);
}
fn dlog_combined_verify_10_64_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 10, 64);
}
fn dlog_prove_1_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 1, 128);
}
fn dlog_verify_1_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 1, 128);
}
fn dlog_prove_5_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 128);
}
fn dlog_verify_5_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 128);
}
fn dlog_combined_prove_5_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 128);
}
fn dlog_combined_verify_5_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 5, 128);
}
fn dlog_combined_prove_10_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 10, 128);
}
fn dlog_combined_verify_10_128_vesta(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        VestaPoint,
        VestaParams,
        VestaBase,
        VestaScalar,
        PallasAffine,
    >(c, "vesta", 10, 128);
}

fn dlog_prove_1_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 1, 32);
}
fn dlog_verify_1_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 1, 32);
}
fn dlog_prove_5_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 32);
}
fn dlog_verify_5_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 32);
}
fn dlog_prove_1_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 1, 64);
}
fn dlog_verify_1_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 1, 64);
}
fn dlog_prove_5_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 64);
}
fn dlog_verify_5_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 64);
}
fn dlog_combined_prove_5_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 32);
}
fn dlog_combined_verify_5_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 32);
}
fn dlog_combined_prove_10_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 10, 32);
}
fn dlog_combined_verify_10_32_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 10, 32);
}
fn dlog_combined_prove_5_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 64);
}
fn dlog_combined_verify_5_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 64);
}
fn dlog_combined_prove_10_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 10, 64);
}
fn dlog_combined_verify_10_64_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 10, 64);
}
fn dlog_prove_1_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 1, 128);
}
fn dlog_verify_1_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 1, 128);
}
fn dlog_prove_5_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 128);
}
fn dlog_verify_5_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 128);
}
fn dlog_combined_prove_5_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 128);
}
fn dlog_combined_verify_5_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 5, 128);
}
fn dlog_combined_prove_10_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 10, 128);
}
fn dlog_combined_verify_10_128_helios(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        HeliosPoint,
        HeliosParams,
        HeliosBase,
        HeliosScalar,
        SeleneAffine,
    >(c, "helios", 10, 128);
}

fn dlog_prove_1_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 1, 32);
}
fn dlog_verify_1_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 1, 32);
}
fn dlog_prove_5_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 32);
}
fn dlog_verify_5_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 32);
}
fn dlog_prove_1_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 1, 64);
}
fn dlog_verify_1_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 1, 64);
}
fn dlog_prove_5_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 64);
}
fn dlog_verify_5_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 64);
}
fn dlog_combined_prove_5_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 32);
}
fn dlog_combined_verify_5_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 32);
}
fn dlog_combined_prove_10_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 10, 32);
}
fn dlog_combined_verify_10_32_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 10, 32);
}
fn dlog_combined_prove_5_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 64);
}
fn dlog_combined_verify_5_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 64);
}
fn dlog_combined_prove_10_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 10, 64);
}
fn dlog_combined_verify_10_64_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 10, 64);
}
fn dlog_prove_1_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 1, 128);
}
fn dlog_verify_1_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 1, 128);
}
fn dlog_prove_5_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 128);
}
fn dlog_verify_5_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 128);
}
fn dlog_combined_prove_5_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 128);
}
fn dlog_combined_verify_5_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 5, 128);
}
fn dlog_combined_prove_10_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_prove::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 10, 128);
}
fn dlog_combined_verify_10_128_selene(c: &mut Criterion) {
    bench_blinding_with_discrete_log_combined_verify::<
        SelenePoint,
        SeleneParams,
        SeleneBase,
        SeleneScalar,
        HeliosAffine,
    >(c, "selene", 10, 128);
}

criterion_group!(
    dlog_pallas,
    dlog_prove_1_32_pallas,
    dlog_verify_1_32_pallas,
    dlog_prove_5_32_pallas,
    dlog_verify_5_32_pallas,
    dlog_prove_1_64_pallas,
    dlog_verify_1_64_pallas,
    dlog_prove_5_64_pallas,
    dlog_verify_5_64_pallas,
    dlog_prove_1_128_pallas,
    dlog_verify_1_128_pallas,
    dlog_prove_5_128_pallas,
    dlog_verify_5_128_pallas,
    dlog_combined_prove_5_32_pallas,
    dlog_combined_verify_5_32_pallas,
    dlog_combined_prove_10_32_pallas,
    dlog_combined_verify_10_32_pallas,
    dlog_combined_prove_5_64_pallas,
    dlog_combined_verify_5_64_pallas,
    dlog_combined_prove_10_64_pallas,
    dlog_combined_verify_10_64_pallas,
    dlog_combined_prove_5_128_pallas,
    dlog_combined_verify_5_128_pallas,
    dlog_combined_prove_10_128_pallas,
    dlog_combined_verify_10_128_pallas,
);

criterion_group!(
    dlog_vesta,
    dlog_prove_1_32_vesta,
    dlog_verify_1_32_vesta,
    dlog_prove_5_32_vesta,
    dlog_verify_5_32_vesta,
    dlog_prove_1_64_vesta,
    dlog_verify_1_64_vesta,
    dlog_prove_5_64_vesta,
    dlog_verify_5_64_vesta,
    dlog_prove_1_128_vesta,
    dlog_verify_1_128_vesta,
    dlog_prove_5_128_vesta,
    dlog_verify_5_128_vesta,
    dlog_combined_prove_5_32_vesta,
    dlog_combined_verify_5_32_vesta,
    dlog_combined_prove_10_32_vesta,
    dlog_combined_verify_10_32_vesta,
    dlog_combined_prove_5_64_vesta,
    dlog_combined_verify_5_64_vesta,
    dlog_combined_prove_10_64_vesta,
    dlog_combined_verify_10_64_vesta,
    dlog_combined_prove_5_128_vesta,
    dlog_combined_verify_5_128_vesta,
    dlog_combined_prove_10_128_vesta,
    dlog_combined_verify_10_128_vesta,
);

criterion_group!(
    dlog_helios,
    dlog_prove_1_32_helios,
    dlog_verify_1_32_helios,
    dlog_prove_5_32_helios,
    dlog_verify_5_32_helios,
    dlog_prove_1_64_helios,
    dlog_verify_1_64_helios,
    dlog_prove_5_64_helios,
    dlog_verify_5_64_helios,
    dlog_prove_1_128_helios,
    dlog_verify_1_128_helios,
    dlog_prove_5_128_helios,
    dlog_verify_5_128_helios,
    dlog_combined_prove_5_32_helios,
    dlog_combined_verify_5_32_helios,
    dlog_combined_prove_10_32_helios,
    dlog_combined_verify_10_32_helios,
    dlog_combined_prove_5_64_helios,
    dlog_combined_verify_5_64_helios,
    dlog_combined_prove_10_64_helios,
    dlog_combined_verify_10_64_helios,
    dlog_combined_prove_5_128_helios,
    dlog_combined_verify_5_128_helios,
    dlog_combined_prove_10_128_helios,
    dlog_combined_verify_10_128_helios,
);

criterion_group!(
    dlog_selene,
    dlog_prove_1_32_selene,
    dlog_verify_1_32_selene,
    dlog_prove_5_32_selene,
    dlog_verify_5_32_selene,
    dlog_prove_1_64_selene,
    dlog_verify_1_64_selene,
    dlog_prove_5_64_selene,
    dlog_verify_5_64_selene,
    dlog_prove_1_128_selene,
    dlog_verify_1_128_selene,
    dlog_prove_5_128_selene,
    dlog_verify_5_128_selene,
    dlog_combined_prove_5_32_selene,
    dlog_combined_verify_5_32_selene,
    dlog_combined_prove_10_32_selene,
    dlog_combined_verify_10_32_selene,
    dlog_combined_prove_5_64_selene,
    dlog_combined_verify_5_64_selene,
    dlog_combined_prove_10_64_selene,
    dlog_combined_verify_10_64_selene,
    dlog_combined_prove_5_128_selene,
    dlog_combined_verify_5_128_selene,
    dlog_combined_prove_10_128_selene,
    dlog_combined_verify_10_128_selene,
);

criterion_main!(dlog_pallas, dlog_vesta, dlog_helios, dlog_selene);
