use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use bulletproofs::r1cs::{Prover, R1CSError, R1CSProof, Verifier};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::RngCore;
use relations::curve_tree::{Root, SelRerandParameters};
use relations::curve_tree_prover::CurveTreeWitnessPath;

#[allow(dead_code)]
const PROOF_LABEL: &'static [u8; 22] = b"select_and_rerandomize";

#[allow(dead_code)]
pub fn prove<
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    even_prover: Prover<MerlinTranscript, Affine<P0>>,
    odd_prover: Prover<MerlinTranscript, Affine<P1>>,
    sr_params: &SelRerandParameters<P0, P1>,
) -> Result<(R1CSProof<Affine<P0>>, R1CSProof<Affine<P1>>), R1CSError> {
    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove(&sr_params.even_parameters.bp_gens),
        || odd_prover.prove(&sr_params.odd_parameters.bp_gens),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove(&sr_params.even_parameters.bp_gens),
        odd_prover.prove(&sr_params.odd_parameters.bp_gens),
    );

    let (even_proof, odd_proof) = (even_proof?, odd_proof?);
    Ok((even_proof, odd_proof))
}

#[allow(dead_code)]
pub fn check_proof<
    const L: usize,
    R: RngCore,
    F: PrimeField,
    P0: SWCurveConfig<BaseField = F> + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
>(
    rng: &mut R,
    leaf: Affine<P0>,
    path: CurveTreeWitnessPath<L, P0, P1>,
    root: &Root<L, 1, P0, P1>,
    sr_params: &SelRerandParameters<P0, P1>,
) {
    let pallas_transcript = MerlinTranscript::new(PROOF_LABEL);
    let mut pallas_prover: Prover<_, Affine<P0>> =
        Prover::new(&sr_params.even_parameters.pc_gens, pallas_transcript);
    let vesta_transcript = MerlinTranscript::new(PROOF_LABEL);
    let mut vesta_prover: Prover<_, Affine<P1>> =
        Prover::new(&sr_params.odd_parameters.pc_gens, vesta_transcript);

    let (mut path_commitments, re_randomization_of_leaf) = path
        .select_and_rerandomize_prover_gadget(
            &mut pallas_prover,
            &mut vesta_prover,
            &sr_params,
            rng,
        );

    let pallas_proof = pallas_prover
        .prove(&sr_params.even_parameters.bp_gens)
        .unwrap();
    let vesta_proof = vesta_prover
        .prove(&sr_params.odd_parameters.bp_gens)
        .unwrap();

    {
        let pallas_transcript = MerlinTranscript::new(PROOF_LABEL);
        let mut pallas_verifier = Verifier::new(pallas_transcript);
        let vesta_transcript = MerlinTranscript::new(PROOF_LABEL);
        let mut vesta_verifier = Verifier::new(vesta_transcript);

        let rerandomized_leaf = path_commitments.select_and_rerandomize_verifier_gadget(
            &root,
            &mut pallas_verifier,
            &mut vesta_verifier,
            &sr_params,
        );

        #[cfg(feature = "parallel")]
        let (pallas_res, vesta_res) = rayon::join(
            || {
                pallas_verifier.verify(
                    &pallas_proof,
                    &sr_params.even_parameters.pc_gens,
                    &sr_params.even_parameters.bp_gens,
                )
            },
            || {
                vesta_verifier.verify(
                    &vesta_proof,
                    &sr_params.odd_parameters.pc_gens,
                    &sr_params.odd_parameters.bp_gens,
                )
            },
        );

        #[cfg(not(feature = "parallel"))]
        let (pallas_res, vesta_res) = {
            (
                pallas_verifier.verify(
                    &pallas_proof,
                    &sr_params.even_parameters.pc_gens,
                    &sr_params.even_parameters.bp_gens,
                ),
                vesta_verifier.verify(
                    &vesta_proof,
                    &sr_params.odd_parameters.pc_gens,
                    &sr_params.odd_parameters.bp_gens,
                ),
            )
        };

        assert!(vesta_res.is_ok());
        assert!(pallas_res.is_ok());
        assert_eq!(
            rerandomized_leaf.into_group(),
            leaf + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
        )
    }
}
