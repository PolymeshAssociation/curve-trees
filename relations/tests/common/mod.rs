use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use bulletproofs::r1cs::{Prover, Verifier};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::RngCore;
use relations::curve_tree::{Root, SelRerandParameters};
use relations::curve_tree_prover::CurveTreeWitnessPath;

const PROOF_LABEL: &'static [u8; 22] = b"select_and_rerandomize";

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

        let vesta_res = vesta_verifier.verify(
            &vesta_proof,
            &sr_params.odd_parameters.pc_gens,
            &sr_params.odd_parameters.bp_gens,
        );
        let pallas_res = pallas_verifier.verify(
            &pallas_proof,
            &sr_params.even_parameters.pc_gens,
            &sr_params.even_parameters.bp_gens,
        );

        assert!(vesta_res.is_ok());
        assert!(pallas_res.is_ok());
        assert_eq!(
            rerandomized_leaf.into_group(),
            leaf + (sr_params.even_parameters.pc_gens.B_blinding * re_randomization_of_leaf)
        )
    }
}
