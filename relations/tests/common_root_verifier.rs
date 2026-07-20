use ark_ec::short_weierstrass::Affine;
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::PallasConfig;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::{Prover, Verifier};
use dock_crypto_utils::poly::poly_from_roots;
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::thread_rng;
use relations::curve_tree::{CurveTree, Root};
use relations::parameters::{SelRerandParametersRef, SelRerandProofParametersNew};
use relations::verifier_common_root::RootChildrenPoly;
use std::time::{Duration, Instant};

type P0 = PallasConfig;
type P1 = VestaConfig;
const L: usize = 64;

#[test]
fn common_root_verifier_perf_impact() {
    let depth = 4;
    let gens: u32 = 1 << 13;
    let num_proofs = 12;

    let mut rng = thread_rng();
    let params =
        SelRerandProofParametersNew::<P0, P1, PallasParams, VestaParams>::new(gens, gens).unwrap();

    // One tree, one root, shared by all proofs.
    let set: Vec<Affine<P0>> = (0..L).map(|_| Affine::<P0>::rand(&mut rng)).collect();
    let tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &params, Some(depth));
    let root = tree.root_node();

    let mut proofs = Vec::with_capacity(num_proofs);
    for i in 0..num_proofs {
        let leaf_index = i % set.len();
        let path = tree.get_path_to_leaf_for_proof(leaf_index, 0).unwrap();

        let mut p0_prover: Prover<_, Affine<P0>> = Prover::new(
            &params.even_parameters().pc_gens,
            MerlinTranscript::new(b"sr"),
        );
        let mut p1_prover: Prover<_, Affine<P1>> = Prover::new(
            &params.odd_parameters().pc_gens,
            MerlinTranscript::new(b"sr"),
        );
        let (pc, _re_rand) = path
            .select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
                &mut p0_prover,
                &mut p1_prover,
                &params,
                &mut rng,
                None,
            )
            .unwrap();
        let p0_proof = p0_prover.prove(&params.even_parameters().bp_gens).unwrap();
        let p1_proof = p1_prover.prove(&params.odd_parameters().bp_gens).unwrap();
        proofs.push((pc, p0_proof, p1_proof));
    }

    let mut base_gadget = Duration::ZERO;
    let mut base_verify = Duration::ZERO;
    for (pc, p0_proof, p1_proof) in &proofs {
        let mut v0 = Verifier::new(MerlinTranscript::new(b"sr"));
        let mut v1 = Verifier::new(MerlinTranscript::new(b"sr"));

        let t = Instant::now();
        pc.select_and_rerandomize_verifier_gadget(&root, &mut v0, &mut v1, &params)
            .unwrap();
        base_gadget += t.elapsed();

        let t = Instant::now();
        v1.verify(
            p1_proof,
            &params.odd_parameters().pc_gens,
            &params.odd_parameters().bp_gens,
        )
        .unwrap();
        v0.verify(
            p0_proof,
            &params.even_parameters().pc_gens,
            &params.even_parameters().bp_gens,
        )
        .unwrap();
        base_verify += t.elapsed();
    }

    let t = Instant::now();
    let root_poly = RootChildrenPoly::from_root(&root).unwrap();
    let poly_precompute = t.elapsed();

    let mut cr_gadget = Duration::ZERO;
    let mut cr_verify = Duration::ZERO;
    for (pc, p0_proof, p1_proof) in &proofs {
        let mut v0 = Verifier::new(MerlinTranscript::new(b"sr"));
        let mut v1 = Verifier::new(MerlinTranscript::new(b"sr"));

        let t = Instant::now();
        pc.select_and_rerandomize_verifier_gadget_common_root(
            &root, &root_poly, &mut v0, &mut v1, &params,
        )
        .unwrap();
        cr_gadget += t.elapsed();

        let t = Instant::now();
        v1.verify(
            p1_proof,
            &params.odd_parameters().pc_gens,
            &params.odd_parameters().bp_gens,
        )
        .unwrap();
        v0.verify(
            p0_proof,
            &params.even_parameters().pc_gens,
            &params.even_parameters().bp_gens,
        )
        .unwrap();
        cr_verify += t.elapsed();
    }

    let root_xs: Vec<_> = match &root {
        Root::Even(n) => n.x_coord_children[0].to_vec(),
        Root::Odd(_) => panic!("expected even root for this config"),
    };
    let iters = 200u32;
    let _ = poly_from_roots(&root_xs); // warm up
    let t = Instant::now();
    for _ in 0..iters {
        let _ = poly_from_roots(&root_xs);
    }
    let one_poly = t.elapsed() / iters;

    let n = num_proofs as u32;
    let saved_per_proof = (base_gadget.saturating_sub(cr_gadget)) / n;
    let base_gadget_pp = base_gadget / n;
    let base_full_pp = (base_gadget + base_verify) / n;

    println!("common-root verifier perf (Pallas/Vesta, L={L}, depth={depth}, N={num_proofs})");
    println!(
        "root set size = {} poly degree = {}",
        root_xs.len(),
        root_xs.len()
    );
    println!("one poly_from_roots(L): {one_poly:?} poly precompute (once): {poly_precompute:?}");
    println!(
        "  baseline {:?}/proof   cached-poly {:?}/proof   saved {saved_per_proof:?}/proof  ({:.1}% of gadget phase)",
        base_gadget_pp,
        cr_gadget / n,
        100.0 * saved_per_proof.as_secs_f64() / base_gadget_pp.as_secs_f64().max(1e-12),
    );
    println!(
        "  baseline {:?}/proof   cached-poly {:?}/proof",
        base_verify / n,
        cr_verify / n
    );
    println!(
        "  baseline {base_full_pp:?}/proof   saving {saved_per_proof:?}/proof = {:.2}% of full verify  (amortized poly precompute {poly_precompute:?} once over N)",
        100.0 * saved_per_proof.as_secs_f64() / base_full_pp.as_secs_f64().max(1e-12),
    );
    println!();
}
