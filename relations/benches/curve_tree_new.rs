use ark_ec::short_weierstrass::{Affine};
use ark_ec_divisors::curves::{
    pallas::PallasParams, pallas::Point as PallasPoint, vesta::Point as VestaPoint,
    vesta::VestaParams,
};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use bulletproofs::r1cs::*;
use criterion::{criterion_group, criterion_main, Criterion};
use dock_crypto_utils::transcript::MerlinTranscript;
use lazy_static::lazy_static;
use rand::thread_rng;
use relations::curve_tree::*;
use std::hint::black_box;
use relations::parameters::{SelRerandParameters, SelRerandProofParametersNew};

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;

lazy_static! {
    static ref SRParamsPallasLeaf: SelRerandParameters<PallasParameters, VestaParameters> = {
        let generators_length = 1 << 13;
        SelRerandParameters::<PallasParameters, VestaParameters>::new(
            generators_length,
            generators_length,
        )
        .expect("Failed to create SelRerandParameters")
    };
    static ref SRProofParamsNewPallasLeaf: SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams> = {
        SelRerandProofParametersNew::<PallasParameters, VestaParameters, PallasParams, VestaParams>::from_sr_params::<PallasPoint, VestaPoint>((*SRParamsPallasLeaf).clone())
    };
}

// Tree will have only this many leaves as proof cost doesn't depend on it significantly
const NUM_LEAVES: usize = 10;

fn prove(
    even_prover: Prover<MerlinTranscript, Affine<PallasParameters>>,
    odd_prover: Prover<MerlinTranscript, Affine<VestaParameters>>,
) -> Result<
    (
        R1CSProof<Affine<PallasParameters>>,
        R1CSProof<Affine<VestaParameters>>,
    ),
    R1CSError,
> {
    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove(&SRParamsPallasLeaf.even_parameters.bp_gens),
        || odd_prover.prove(&SRParamsPallasLeaf.odd_parameters.bp_gens),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove(&SRParamsPallasLeaf.even_parameters.bp_gens),
        odd_prover.prove(&SRParamsPallasLeaf.odd_parameters.bp_gens),
    );

    let (even_proof, odd_proof) = (even_proof?, odd_proof?);
    Ok((even_proof, odd_proof))
}

#[allow(type_alias_bounds)]
type NewSetupData<const L: usize> = (
    CurveTree<L, 1, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    SelectAndRerandomizePathWithDivisorComms<L, PallasParameters, VestaParameters>,
    R1CSProof<Affine<PallasParameters>>,
    R1CSProof<Affine<VestaParameters>>,
);

fn setup_curve_tree_data_new<const L: usize>(height: usize) -> NewSetupData<L> {
    let mut rng = thread_rng();

    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasParameters>::rand(&mut rng))
        .collect::<Vec<_>>();

    let curve_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &*SRParamsPallasLeaf,
        Some(height),
    );

    let root = curve_tree.root_node();

    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
        &SRParamsPallasLeaf.even_parameters.pc_gens,
        pallas_transcript,
    );

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
        Prover::new(&SRParamsPallasLeaf.odd_parameters.pc_gens, vesta_transcript);

    let path = curve_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let (
        path_commitments,
        _,
    ) = path.select_and_rerandomize_prover_gadget_new::<
        _,
        PallasPoint,
        VestaPoint,
        PallasParams,
        VestaParams,
    >(
        &mut pallas_prover,
        &mut vesta_prover,
        &SRProofParamsNewPallasLeaf,
        &mut rng,
    ).unwrap();

    let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover).unwrap();

    (
        curve_tree,
        root,
        path_commitments,
        pallas_proof,
        vesta_proof,
    )
}

fn curve_tree_verify_new<const L: usize>(c: &mut Criterion, height: usize) {
    let (_, root, path_commitments, pallas_proof, vesta_proof) =
        setup_curve_tree_data_new::<L>(height);

    let bench_name = format!("curve_tree_verify_new_{}_{}", L, height);
    println!(
        "Proof size for L={L}, height={height}: {} bytes",
        pallas_proof.compressed_size()
            + vesta_proof.compressed_size()
            + path_commitments.compressed_size()
    );
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            path_commitments
                .select_and_rerandomize_verifier_gadget::<PallasParams, VestaParams>(
                    &root,
                    &mut pallas_verifier,
                    &mut vesta_verifier,
                    &SRProofParamsNewPallasLeaf,
                );

            #[cfg(feature = "parallel")]
            let (vesta_res, pallas_res) = rayon::join(
                || {
                    vesta_verifier.verify(
                        &vesta_proof,
                        &SRParamsPallasLeaf.odd_parameters.pc_gens,
                        &SRParamsPallasLeaf.odd_parameters.bp_gens,
                    )
                },
                || {
                    pallas_verifier.verify(
                        &pallas_proof,
                        &SRParamsPallasLeaf.even_parameters.pc_gens,
                        &SRParamsPallasLeaf.even_parameters.bp_gens,
                    )
                },
            );

            #[cfg(not(feature = "parallel"))]
            let (vesta_res, pallas_res) = (
                vesta_verifier.verify(
                    &vesta_proof,
                    &SRParamsPallasLeaf.odd_parameters.pc_gens,
                    &SRParamsPallasLeaf.odd_parameters.bp_gens,
                ),
                pallas_verifier.verify(
                    &pallas_proof,
                    &SRParamsPallasLeaf.even_parameters.pc_gens,
                    &SRParamsPallasLeaf.even_parameters.bp_gens,
                ),
            );

            black_box((vesta_res.unwrap(), pallas_res.unwrap()))
        })
    });
}

fn curve_tree_prove_new<const L: usize>(c: &mut Criterion, height: usize) {
    let mut rng = thread_rng();

    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasParameters>::rand(&mut rng))
        .collect::<Vec<_>>();

    let curve_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &*SRParamsPallasLeaf,
        Some(height),
    );

    let bench_name = format!("curve_tree_prove_new_{}_{}", L, height);
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
                &SRParamsPallasLeaf.even_parameters.pc_gens,
                pallas_transcript,
            );

            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
                Prover::new(&SRParamsPallasLeaf.odd_parameters.pc_gens, vesta_transcript);

            let path = curve_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let result_gadget = path.select_and_rerandomize_prover_gadget_new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut pallas_prover,
                &mut vesta_prover,
                &SRProofParamsNewPallasLeaf,
                &mut rng,
            );

            let result_proof = prove(pallas_prover, vesta_prover);
            black_box((result_gadget, result_proof))
        })
    });
}

fn verify_32_7(c: &mut Criterion) {
    curve_tree_verify_new::<32>(c, 7);
}

fn prove_32_7(c: &mut Criterion) {
    curve_tree_prove_new::<32>(c, 7);
}

fn verify_64_5(c: &mut Criterion) {
    curve_tree_verify_new::<64>(c, 5);
}

fn prove_64_5(c: &mut Criterion) {
    curve_tree_prove_new::<64>(c, 5);
}

fn verify_64_6(c: &mut Criterion) {
    curve_tree_verify_new::<64>(c, 6);
}

fn prove_64_6(c: &mut Criterion) {
    curve_tree_prove_new::<64>(c, 6);
}

fn verify_128_4(c: &mut Criterion) {
    curve_tree_verify_new::<128>(c, 4);
}

fn prove_128_4(c: &mut Criterion) {
    curve_tree_prove_new::<128>(c, 4);
}

fn verify_128_5(c: &mut Criterion) {
    curve_tree_verify_new::<128>(c, 5);
}

fn prove_128_5(c: &mut Criterion) {
    curve_tree_prove_new::<128>(c, 5);
}

fn verify_256_4(c: &mut Criterion) {
    curve_tree_verify_new::<256>(c, 4);
}

fn prove_256_4(c: &mut Criterion) {
    curve_tree_prove_new::<256>(c, 4);
}

fn verify_512_4(c: &mut Criterion) {
    curve_tree_verify_new::<512>(c, 4);
}

fn prove_512_4(c: &mut Criterion) {
    curve_tree_prove_new::<512>(c, 4);
}

fn verify_1000_2(c: &mut Criterion) {
    curve_tree_verify_new::<1000>(c, 2);
}

fn prove_1000_2(c: &mut Criterion) {
    curve_tree_prove_new::<1000>(c, 2);
}

fn verify_1000_3(c: &mut Criterion) {
    curve_tree_verify_new::<1000>(c, 3);
}

fn prove_1000_3(c: &mut Criterion) {
    curve_tree_prove_new::<1000>(c, 3);
}

fn verify_2000_2(c: &mut Criterion) {
    curve_tree_verify_new::<2000>(c, 2);
}

fn prove_2000_2(c: &mut Criterion) {
    curve_tree_prove_new::<2000>(c, 2);
}

fn verify_2000_3(c: &mut Criterion) {
    curve_tree_verify_new::<2000>(c, 3);
}

fn prove_2000_3(c: &mut Criterion) {
    curve_tree_prove_new::<2000>(c, 3);
}

criterion_group!(
    curve_tree_new_benches,
    verify_32_7,
    prove_32_7,
    verify_64_5,
    prove_64_5,
    verify_64_6,
    prove_64_6,
    verify_128_4,
    prove_128_4,
    verify_128_5,
    prove_128_5,
    verify_256_4,
    prove_256_4,
    verify_512_4,
    prove_512_4,
    verify_1000_2,
    prove_1000_2,
    verify_1000_3,
    prove_1000_3,
    verify_2000_2,
    prove_2000_2,
    verify_2000_3,
    prove_2000_3
);

criterion_main!(curve_tree_new_benches);
