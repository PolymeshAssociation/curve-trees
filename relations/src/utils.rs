use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use bulletproofs::r1cs::{Prover, R1CSError, R1CSProof, Verifier};
use dock_crypto_utils::transcript::MerlinTranscript;
use crate::curve_tree::SelRerandParameters;
use rand_core::CryptoRngCore;
use rand_chacha::ChaChaRng;
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
    sr_params: &SelRerandParameters<P0, P1>,
    rng: &mut R,
) -> Result<(R1CSProof<Affine<P0>>, R1CSProof<Affine<P1>>), R1CSError> {
    // Create separate RNGs from seeds for parallel execution
    let mut buf_even = [0u8; 32];
    rng.fill_bytes(&mut buf_even);
    let mut rng_even = ChaChaRng::from_seed(buf_even);

    let mut buf_odd = [0u8; 32];
    rng.fill_bytes(&mut buf_odd);
    let mut rng_odd = ChaChaRng::from_seed(buf_odd);

    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng_even),
        || odd_prover.prove_with_rng(&sr_params.odd_parameters.bp_gens, &mut rng_odd),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove_with_rng(&sr_params.even_parameters.bp_gens, &mut rng_even),
        odd_prover.prove_with_rng(&sr_params.odd_parameters.bp_gens, &mut rng_odd),
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
    sr_params: &SelRerandParameters<P0, P1>,
    rng: &mut R,
) -> Result<(), R1CSError> {
    // Create separate RNGs from seeds for parallel execution
    let mut buf_even = [0u8; 32];
    rng.fill_bytes(&mut buf_even);
    let mut rng_even = ChaChaRng::from_seed(buf_even);

    let mut buf_odd = [0u8; 32];
    rng.fill_bytes(&mut buf_odd);
    let mut rng_odd = ChaChaRng::from_seed(buf_odd);

    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            even_verifier.verify_with_rng(
                even_proof,
                &sr_params.even_parameters.pc_gens,
                &sr_params.even_parameters.bp_gens,
                &mut rng_even,
            )
        },
        || {
            odd_verifier.verify_with_rng(
                odd_proof,
                &sr_params.odd_parameters.pc_gens,
                &sr_params.odd_parameters.bp_gens,
                &mut rng_odd,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        even_verifier.verify_with_rng(
            even_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
            &mut rng_even,
        ),
        odd_verifier.verify_with_rng(
            odd_proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
            &mut rng_odd,
        ),
    );

    even_res?;
    odd_res?;
    Ok(())
}

