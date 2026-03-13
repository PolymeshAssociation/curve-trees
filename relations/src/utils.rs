use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use bulletproofs::r1cs::{Prover, R1CSError, R1CSProof, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_chacha::ChaChaRng;
use rand_core::CryptoRngCore;
use rand_core::SeedableRng;

/// Feature-gated parallel proving for even and odd provers.
pub fn prove<
    R: CryptoRngCore,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    even_prover: Prover<MerlinTranscript, Affine<P0>>,
    odd_prover: Prover<MerlinTranscript, Affine<P1>>,
    even_bp_gens: &BulletproofGens<Affine<P0>>,
    odd_bp_gens: &BulletproofGens<Affine<P1>>,
    rng: &mut R,
) -> Result<(R1CSProof<Affine<P0>>, R1CSProof<Affine<P1>>), R1CSError> {
    // Create separate RNGs from seeds for parallel execution
    let (mut rng_even, mut rng_odd) = get_2_rngs_from_one(rng);

    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove_with_rng(even_bp_gens, &mut rng_even),
        || odd_prover.prove_with_rng(odd_bp_gens, &mut rng_odd),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove_with_rng(even_bp_gens, &mut rng_even),
        odd_prover.prove_with_rng(odd_bp_gens, &mut rng_odd),
    );

    let (even_proof, odd_proof) = (even_proof?, odd_proof?);
    Ok((even_proof, odd_proof))
}

/// Feature-gated parallel verification for even and odd verifiers.
pub fn verify<
    R: CryptoRngCore,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<P0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<P1>>,
    even_proof: &R1CSProof<Affine<P0>>,
    odd_proof: &R1CSProof<Affine<P1>>,
    even_pc_gens: &PedersenGens<Affine<P0>>,
    even_bp_gens: &BulletproofGens<Affine<P0>>,
    odd_pc_gens: &PedersenGens<Affine<P1>>,
    odd_bp_gens: &BulletproofGens<Affine<P1>>,
    rng: &mut R,
) -> Result<(), R1CSError> {
    // Create separate RNGs from seeds for parallel execution
    let (mut rng_even, mut rng_odd) = get_2_rngs_from_one(rng);

    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || even_verifier.verify_with_rng(even_proof, even_pc_gens, even_bp_gens, &mut rng_even),
        || odd_verifier.verify_with_rng(odd_proof, odd_pc_gens, odd_bp_gens, &mut rng_odd),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        even_verifier.verify_with_rng(even_proof, even_pc_gens, even_bp_gens, &mut rng_even),
        odd_verifier.verify_with_rng(odd_proof, odd_pc_gens, odd_bp_gens, &mut rng_odd),
    );

    even_res?;
    odd_res?;
    Ok(())
}

pub fn get_2_rngs_from_one<R: CryptoRngCore>(rng: &mut R) -> (ChaChaRng, ChaChaRng) {
    let mut buf_1 = [0u8; 32];
    rng.fill_bytes(&mut buf_1);
    let rng_1 = ChaChaRng::from_seed(buf_1);

    let mut buf_2 = [0u8; 32];
    rng.fill_bytes(&mut buf_2);
    let rng_2 = ChaChaRng::from_seed(buf_2);
    (rng_1, rng_2)
}
