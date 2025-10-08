use ark_ec::short_weierstrass::Affine;
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::UniformRand;
use bulletproofs::r1cs::*;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use dock_crypto_utils::transcript::MerlinTranscript;
use lazy_static::lazy_static;
use rand::thread_rng;
use relations::curve_tree::*;

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

fn setup_curve_tree_data<const L: usize>(
    height: usize,
) -> (
    CurveTree<L, 1, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    SelectAndRerandomizePath<L, PallasParameters, VestaParameters>,
    R1CSProof<Affine<PallasParameters>>,
    R1CSProof<Affine<VestaParameters>>,
) {
    let mut rng = thread_rng();

    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasParameters>::rand(&mut rng))
        .collect::<Vec<_>>();

    let curve_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &SRParamsPallasLeaf,
        Some(height),
    );

    let root = curve_tree.root_node();

    // Create a single proof to use for verification benchmarks
    let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
        &SRParamsPallasLeaf.even_parameters.pc_gens,
        pallas_transcript,
    );

    let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
    let mut vesta_prover: Prover<_, Affine<VestaParameters>> =
        Prover::new(&SRParamsPallasLeaf.odd_parameters.pc_gens, vesta_transcript);

    let path = curve_tree.get_path_to_leaf_for_proof(0, 0);
    let (path_commitments, _) = path.select_and_rerandomize_prover_gadget(
        &mut pallas_prover,
        &mut vesta_prover,
        &SRParamsPallasLeaf,
        &mut rng,
    );

    let (pallas_proof, vesta_proof) = prove(pallas_prover, vesta_prover).unwrap();

    (
        curve_tree,
        root,
        path_commitments,
        pallas_proof,
        vesta_proof,
    )
}

fn curve_tree_verify<const L: usize>(c: &mut Criterion, height: usize) {
    let (_curve_tree, root, path_commitments, pallas_proof, vesta_proof) =
        setup_curve_tree_data::<L>(height);

    println!(
        "Proof size for L={L}, height={height}: {} bytes",
        pallas_proof.serialized_size(Compress::Yes) + vesta_proof.serialized_size(Compress::Yes)
    );

    let bench_name = format!("curve_tree_verify_{}_{}", L, height);
    c.bench_function(&bench_name, |b| {
        b.iter(|| {
            let pallas_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::new(pallas_transcript);
            let vesta_transcript = MerlinTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::new(vesta_transcript);

            let _ = path_commitments.select_and_rerandomize_verifier_gadget(
                &root,
                &mut pallas_verifier,
                &mut vesta_verifier,
                &SRParamsPallasLeaf,
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

            black_box((vesta_res, pallas_res))
        })
    });
}

/// Generic curve tree proving benchmark
fn curve_tree_prove<const L: usize>(c: &mut Criterion, height: usize) {
    let mut rng = thread_rng();

    let set = (0..NUM_LEAVES)
        .map(|_| Affine::<PallasParameters>::rand(&mut rng))
        .collect::<Vec<_>>();

    let curve_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &SRParamsPallasLeaf,
        Some(height),
    );

    let bench_name = format!("curve_tree_prove_{}_{}", L, height);
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

            let path = curve_tree.get_path_to_leaf_for_proof(0, 0);
            let (path_commitments, _) = path.select_and_rerandomize_prover_gadget(
                &mut pallas_prover,
                &mut vesta_prover,
                &SRParamsPallasLeaf,
                &mut rng,
            );

            let result = prove(pallas_prover, vesta_prover);
            black_box((path_commitments, result))
        })
    });
}

fn verify_512_4(c: &mut Criterion) {
    curve_tree_verify::<512>(c, 4);
}

fn prove_512_4(c: &mut Criterion) {
    curve_tree_prove::<512>(c, 4);
}

fn verify_1000_2(c: &mut Criterion) {
    curve_tree_verify::<1000>(c, 2);
}

fn prove_1000_2(c: &mut Criterion) {
    curve_tree_prove::<1000>(c, 2);
}

fn verify_1000_3(c: &mut Criterion) {
    curve_tree_verify::<1000>(c, 3);
}

fn prove_1000_3(c: &mut Criterion) {
    curve_tree_prove::<1000>(c, 3);
}

fn verify_2000_2(c: &mut Criterion) {
    curve_tree_verify::<2000>(c, 2);
}

fn prove_2000_2(c: &mut Criterion) {
    curve_tree_prove::<2000>(c, 2);
}

fn verify_2000_3(c: &mut Criterion) {
    curve_tree_verify::<2000>(c, 3);
}

fn prove_2000_3(c: &mut Criterion) {
    curve_tree_prove::<2000>(c, 3);
}

criterion_group!(
    curve_tree_benches,
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

criterion_main!(curve_tree_benches);
