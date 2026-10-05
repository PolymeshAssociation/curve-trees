//! Compares the verifier's final MSM done three ways, on curve-tree `VerificationTuple`s
//! (Pallas/Vesta, both sides). All compute the same point,
//! `sum over proof_dependent_points + [B, B_blinding, G_0..G_{n-1}, H_0..H_{n-1}]`:

//! `fixed_point_scalars` is ordered `[B, B_blinding, G(padded_n), H(padded_n)]`, so it aligns
//! with a fixed base set built in that order. The fixed set (`2 + 2 padded_n` bases) is identical
//! across all proofs against the same generators.
//!

#![allow(non_snake_case)]

use ark_ec::scalar_mul::fixed_base::FixedBaseMSM;
use ark_ec::scalar_mul::sw_pippenger::msm_batch_affine;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_ff::{PrimeField, Zero};
use ark_pallas::PallasConfig;
use ark_std::UniformRand;
use ark_vesta::VestaConfig;
use bulletproofs::r1cs::{
    verify_given_verification_tuple, Prover, R1CSProof, VerificationTuple, Verifier,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand::thread_rng;
use relations::curve_tree::CurveTree;
use relations::parameters::{SelRerandProofParametersNew, SelRerandProofParametersRef};
use std::hint::black_box;
use std::time::{Duration, Instant};

type P0 = PallasConfig;
type P1 = VestaConfig;
const L: usize = 64;

/// The verifier's fixed MSM base set, in the order `fixed_point_scalars` expects:
/// `[B, B_blinding, G_0..G_{n-1}, H_0..H_{n-1}]`. `bp_gens.G/H(n, 1)` (m=1) is the public form of
/// the `bp_gens.share(0).G/H(n)` used inside `bases_and_scalars`.
fn fixed_bases<C: AffineRepr>(
    pc_gens: &PedersenGens<C>,
    bp_gens: &BulletproofGens<C>,
    padded_n: u32,
) -> Vec<C> {
    use core::iter;
    iter::once(pc_gens.B)
        .chain(iter::once(pc_gens.B_blinding))
        .chain(bp_gens.G(padded_n, 1).copied())
        .chain(bp_gens.H(padded_n, 1).copied())
        .collect()
}

struct Report {
    padded_n: u32,
    n_fixed: usize,
    n_var: usize,
    window: usize,
    num_windows: usize,
    num_buckets: usize,
    table_len: usize,
    table_bytes: usize,
    precompute: Duration,
    baseline_verify: Duration,
    baseline_msm: Duration,
    split_fixed: Duration,
    split_var: Duration,
    split_total: Duration,
    batch_affine: Duration,
}

/// Benchmarks both MSM approaches for one curve side over the given tuples.
fn bench_side<P: SWCurveConfig>(
    tuples: &[VerificationTuple<Affine<P>>],
    pc_gens: &PedersenGens<Affine<P>>,
    bp_gens: &BulletproofGens<Affine<P>>,
    reps: usize,
) -> Report {
    let padded_n = tuples[0].padded_n().unwrap();
    let fb = fixed_bases(pc_gens, bp_gens, padded_n);
    let n_fixed = fb.len();
    let n_var = tuples[0].proof_dependent_points.len();

    // One-time precompute: the fixed-base table, reused across every proof.
    let t = Instant::now();
    let fixed_msm = FixedBaseMSM::<P>::new(&fb);
    let precompute = t.elapsed();

    // Warm up both paths.
    {
        verify_given_verification_tuple(tuples[0].clone(), pc_gens, bp_gens).unwrap();
        let _ = fixed_msm.msm(&tuples[0].fixed_point_scalars);
    }

    let mut baseline_verify = Duration::ZERO;
    let mut baseline_msm = Duration::ZERO;
    let mut split_fixed = Duration::ZERO;
    let mut split_var = Duration::ZERO;
    let mut split_total = Duration::ZERO;
    let mut batch_affine = Duration::ZERO;

    for _ in 0..reps {
        for vt in tuples {
            // baseline: msm_unchecked
            let mut bases = vt.proof_dependent_points.clone();
            bases.extend_from_slice(&fb);
            let mut scalars = vt.proof_dependent_scalars.clone();
            scalars.extend_from_slice(&vt.fixed_point_scalars);
            let t = Instant::now();
            let z = Projective::<P>::msm_unchecked(&bases, &scalars);
            baseline_verify += t.elapsed();
            assert!(z.is_zero());

            let t = Instant::now();
            let z = Projective::<P>::msm_unchecked_full_width(&bases, &scalars);
            baseline_msm += t.elapsed();
            assert!(z.is_zero());

            let t = Instant::now();
            let z = msm_batch_affine::<P>(&bases, &scalars);
            batch_affine += t.elapsed();
            assert!(
                z.is_zero(),
                "batch-affine combined MSM did not reach identity"
            );

            // Split: fixed-base table + variable-base MSM
            let fixed_big: Vec<_> = vt
                .fixed_point_scalars
                .iter()
                .map(|s| s.into_bigint())
                .collect();

            let t = Instant::now();
            let r_fixed = fixed_msm.msm_bigint(&fixed_big);
            let f = t.elapsed();

            let t = Instant::now();
            let r_var = Projective::<P>::msm_unchecked_full_width(
                &vt.proof_dependent_points,
                &vt.proof_dependent_scalars,
            );
            let sum = r_fixed + r_var;
            let v = t.elapsed();

            split_fixed += f;
            split_var += v;
            split_total += f + v;
            assert!(sum.is_zero(), "split MSM did not reach identity");
        }
    }

    let fixed_msm_ref = &fixed_msm;
    Report {
        padded_n,
        n_fixed,
        n_var,
        window: fixed_msm_ref.window(),
        num_windows: fixed_msm_ref.num_windows(),
        num_buckets: fixed_msm_ref.num_buckets(),
        table_len: fixed_msm_ref.table_len(),
        table_bytes: fixed_msm_ref.table_bytes(),
        precompute,
        baseline_verify,
        baseline_msm,
        split_fixed,
        split_var,
        split_total,
        batch_affine,
    }
}

fn print_report(label: &str, r: &Report, samples: u32) {
    let per = |d: Duration| d / samples;
    let bl_verify = per(r.baseline_verify);
    let bl_msm = per(r.baseline_msm);
    let sp_fixed = per(r.split_fixed);
    let sp_var = per(r.split_var);
    let sp_total = per(r.split_total);
    let ba = per(r.batch_affine);

    let saving = bl_msm.as_secs_f64() - sp_total.as_secs_f64();
    let speedup = bl_msm.as_secs_f64() / sp_total.as_secs_f64().max(1e-12);
    let ba_speedup = bl_msm.as_secs_f64() / ba.as_secs_f64().max(1e-12);
    let break_even = if saving > 0.0 {
        Some((r.precompute.as_secs_f64() / saving).ceil() as u64)
    } else {
        None
    };

    println!("\n--- {label} ---");
    println!(
        "  padded_n={}   bases: fixed={} (2 + 2 padded_n), variable={}",
        r.padded_n, r.n_fixed, r.n_var
    );
    println!("  FixedBaseMSM table (persistent memory):");
    println!(
        "    window c={}  num_windows W={}  num_buckets={}  entries n*W={}",
        r.window, r.num_windows, r.num_buckets, r.table_len
    );
    println!(
        "    table_bytes = {} B  = {:.2} MB",
        r.table_bytes,
        r.table_bytes as f64 / (1024.0 * 1024.0)
    );
    println!("  one-time precompute (build table): {:?}", r.precompute);
    println!("  per proof:");
    println!("    (verify production path)          : {bl_verify:?}");
    println!("    combined msm_unchecked_full_width : {bl_msm:?}   (1.00x)");
    println!(
        "    B  fixed split total              : {sp_total:?}   ({speedup:.2}x)   [fixed {sp_fixed:?} + var {sp_var:?}]"
    );
    println!("    C  combined msm_batch_affine      : {ba:?}   ({ba_speedup:.2}x)");
    match break_even {
        Some(k) => println!(
            "  saving = {:?}/proof  =>  break-even after {k} proofs (precompute / saving)",
            Duration::from_secs_f64(saving.max(0.0))
        ),
        None => println!("  split is not faster on this side; no break-even"),
    }
}

#[test]
#[ignore = "profiling: timings are only meaningful run alone in release with --nocapture"]
fn fixed_base_msm_vs_combined_msm() {
    let depth = 4;
    let gens: u32 = 1 << 13;
    let num_proofs = 4;
    let reps = 10;

    let mut rng = thread_rng();
    let params =
        SelRerandProofParametersNew::<P0, P1, PallasParams, VestaParams>::new(gens, gens).unwrap();
    let even_pc = params.even_parameters().pc_gens();
    let even_bp = params.even_parameters().bp_gens();
    let odd_pc = params.odd_parameters().pc_gens();
    let odd_bp = params.odd_parameters().bp_gens();

    // Shared, fixed batching randomness.
    let r0 = ark_pallas::Fr::rand(&mut rng);
    let r1 = ark_vesta::Fr::rand(&mut rng);

    // One tree, N independent proofs against it.
    let set: Vec<Affine<P0>> = (0..L).map(|_| Affine::<P0>::rand(&mut rng)).collect();
    let tree = CurveTree::<L, 1, P0, P1>::from_leaves(&set, &params, Some(depth));
    let root = tree.root_node();

    let mut proofs = Vec::with_capacity(num_proofs);
    for i in 0..num_proofs {
        let leaf_index = i % set.len();
        let path = tree.get_path_to_leaf_for_proof(leaf_index, 0).unwrap();
        let mut p0_prover: Prover<_, Affine<P0>> =
            Prover::new(even_pc, MerlinTranscript::new(b"sr"));
        let mut p1_prover: Prover<_, Affine<P1>> =
            Prover::new(odd_pc, MerlinTranscript::new(b"sr"));
        let (pc, _re_rand) = path
            .select_and_rerandomize_prover_gadget_new::<_, PallasParams, VestaParams>(
                &mut p0_prover,
                &mut p1_prover,
                &params,
                &mut rng,
                None,
            )
            .unwrap();
        let p0_proof = p0_prover.prove(even_bp).unwrap();
        let p1_proof = p1_prover.prove(odd_bp).unwrap();
        proofs.push((pc, p0_proof, p1_proof));
    }

    // Build the even/odd VerificationTuples once; the MSM comparison reuses them across reps.
    let build_tuples =
        |pc: &relations::curve_tree::SelectAndRerandomizePathWithDivisorComms<L, P0, P1>,
         p0_proof: &R1CSProof<Affine<P0>>,
         p1_proof: &R1CSProof<Affine<P1>>|
         -> (VerificationTuple<Affine<P0>>, VerificationTuple<Affine<P1>>) {
            let mut v0 = Verifier::new(MerlinTranscript::new(b"sr"));
            let mut v1 = Verifier::new(MerlinTranscript::new(b"sr"));
            pc.select_and_rerandomize_verifier_gadget(&root, &mut v0, &mut v1, &params)
                .unwrap();
            let vt0 = v0
                .verification_scalars_and_points_with_given_randomness(p0_proof, r0)
                .unwrap();
            let vt1 = v1
                .verification_scalars_and_points_with_given_randomness(p1_proof, r1)
                .unwrap();
            (vt0, vt1)
        };

    let mut tuples0 = Vec::with_capacity(num_proofs);
    let mut tuples1 = Vec::with_capacity(num_proofs);
    for (pc, p0, p1) in &proofs {
        let (vt0, vt1) = build_tuples(pc, p0, p1);
        tuples0.push(vt0);
        tuples1.push(vt1);
    }

    let samples = (num_proofs * reps) as u32;
    let rep0 = bench_side(&tuples0, even_pc, even_bp, reps);
    let rep1 = bench_side(&tuples1, odd_pc, odd_bp, reps);

    println!("\n=== FixedBaseMSM split vs combined MSM (L={L}, depth={depth}, gens=2^{}, N={num_proofs}, reps={reps}) ===", gens.trailing_zeros());
    println!(
        "ark-ec MSM regime: {}   (rayon threads = {})",
        msm_desc(),
        rayon_threads()
    );
    print_report("Pallas (even)", &rep0, samples);
    print_report("Vesta (odd)", &rep1, samples);

    // Combined summary: total table memory, and per-proof both-sides figures.
    let per = |d: Duration| d / samples;
    let both_baseline = per(rep0.baseline_msm) + per(rep1.baseline_msm);
    let both_split = per(rep0.split_total) + per(rep1.split_total);
    let both_batch = per(rep0.batch_affine) + per(rep1.batch_affine);
    let both_verify = per(rep0.baseline_verify) + per(rep1.baseline_verify);
    let total_table = rep0.table_bytes + rep1.table_bytes;
    let both_precompute = rep0.precompute + rep1.precompute;
    let saving = both_baseline.as_secs_f64() - both_split.as_secs_f64();
    println!("\n--- per proof, even+odd summed ---");
    println!(
        "  B table memory (persistent) : {:.2} MB",
        total_table as f64 / (1024.0 * 1024.0)
    );
    println!("  B one-time precompute       : {both_precompute:?}");
    println!("  (verify production path)    : {both_verify:?}");
    println!("  A combined msm_bigint       : {both_baseline:?}   (1.00x)");
    println!(
        "  B fixed split total         : {both_split:?}   ({:.2}x)",
        both_baseline.as_secs_f64() / both_split.as_secs_f64().max(1e-12)
    );
    println!(
        "  C combined msm_batch_affine : {both_batch:?}   ({:.2}x)",
        both_baseline.as_secs_f64() / both_batch.as_secs_f64().max(1e-12)
    );
    if saving > 0.0 {
        println!(
            "  B break-even                : {} proofs",
            (both_precompute.as_secs_f64() / saving).ceil() as u64
        );
    }
    println!();
}

// Scaling benchmark: padded_n = 2^13, 2^14, 2^15, 2^16.

fn mb(bytes: usize) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

/// Rayon's thread count, or 1 without the `parallel` feature.
fn rayon_threads() -> usize {
    #[cfg(feature = "parallel")]
    {
        rayon::current_num_threads()
    }
    #[cfg(not(feature = "parallel"))]
    {
        1
    }
}

/// Whether ark-ec's MSM (and the `FixedBaseMSM` table evaluation) is parallelized.
fn msm_desc() -> &'static str {
    if cfg!(feature = "parallel_full") {
        "PARALLEL (ark-ec/parallel via parallel_full)"
    } else {
        "SERIAL (ark-ec not parallelized; build with --features parallel_full for the parallel regime)"
    }
}

/// Per-curve scaling result. Timings are per-proof averages.
struct CompResult {
    n_fixed: usize,
    point_size: usize,
    window: usize,
    num_windows: usize,
    table_len: usize,
    table_bytes: usize,
    gen_bytes: usize,
    precompute: Duration,
    baseline_msm: Duration,
    split_fixed: Duration,
    split_var: Duration,
    split_total: Duration,
    batch_affine: Duration,
}

/// Runs all three MSM approaches for one curve at the given `padded_n`.
fn compare<P: SWCurveConfig>(
    padded_n: u32,
    pc_gens: &PedersenGens<Affine<P>>,
    bp_gens: &BulletproofGens<Affine<P>>,
    reps: usize,
) -> CompResult {
    let mut rng = thread_rng();
    let fb = fixed_bases(pc_gens, bp_gens, padded_n);
    let n_fixed = fb.len();
    let n_var = 2 * padded_n.trailing_zeros() as usize + 32;

    let var_points: Vec<Affine<P>> = (0..n_var).map(|_| Affine::<P>::rand(&mut rng)).collect();
    let var_scalars: Vec<P::ScalarField> =
        (0..n_var).map(|_| P::ScalarField::rand(&mut rng)).collect();
    let fixed_scalars: Vec<P::ScalarField> = (0..n_fixed)
        .map(|_| P::ScalarField::rand(&mut rng))
        .collect();

    // One-time precompute: the fixed-base table.
    let t = Instant::now();
    let fixed_msm = FixedBaseMSM::<P>::new(&fb);
    let precompute = t.elapsed();

    let fixed_big: Vec<_> = fixed_scalars.iter().map(|s| s.into_bigint()).collect();
    let mut combined_bases = var_points.clone();
    combined_bases.extend_from_slice(&fb);
    let mut combined_scalars = var_scalars.clone();
    combined_scalars.extend_from_slice(&fixed_scalars);

    // Warm up + correctness: split (B) and batch-affine (C) must equal the combined MSM (A).
    let combined = Projective::<P>::msm_unchecked_full_width(&combined_bases, &combined_scalars);
    let split = fixed_msm.msm_bigint(&fixed_big)
        + Projective::<P>::msm_unchecked_full_width(&var_points, &var_scalars);
    assert_eq!(split, combined, "split MSM disagrees with combined MSM");
    assert_eq!(
        msm_batch_affine::<P>(&combined_bases, &combined_scalars),
        combined,
        "batch-affine MSM disagrees with combined MSM"
    );

    let mut baseline_msm = Duration::ZERO;
    let mut split_fixed = Duration::ZERO;
    let mut split_var = Duration::ZERO;
    let mut split_total = Duration::ZERO;
    let mut batch_affine = Duration::ZERO;

    for _ in 0..reps {
        //  combined msm_unchecked_full_width.
        let t = Instant::now();
        let res = Projective::<P>::msm_unchecked_full_width(&combined_bases, &combined_scalars);
        baseline_msm += t.elapsed();
        let _ = black_box(res);

        //  fixed-base table + variable-base.
        let t = Instant::now();
        let r_fixed = fixed_msm.msm_bigint(&fixed_big);
        let f = t.elapsed();
        let t = Instant::now();
        let r_var = Projective::<P>::msm_unchecked_full_width(&var_points, &var_scalars);
        let v = t.elapsed();
        let _ = black_box(r_fixed + r_var);
        split_fixed += f;
        split_var += v;
        split_total += f + v;

        //  combined msm_batch_affine.
        let t = Instant::now();
        let res = msm_batch_affine::<P>(&combined_bases, &combined_scalars);
        batch_affine += t.elapsed();
        let _ = black_box(res);
    }

    let r = reps as u32;
    CompResult {
        n_fixed,
        point_size: core::mem::size_of::<Affine<P>>(),
        window: fixed_msm.window(),
        num_windows: fixed_msm.num_windows(),
        table_len: fixed_msm.table_len(),
        table_bytes: fixed_msm.table_bytes(),
        gen_bytes: n_fixed * core::mem::size_of::<Affine<P>>(),
        precompute,
        baseline_msm: baseline_msm / r,
        split_fixed: split_fixed / r,
        split_var: split_var / r,
        split_total: split_total / r,
        batch_affine: batch_affine / r,
    }
}

#[test]
#[ignore = "profiling: timings are only meaningful run alone in release with --nocapture"]
fn fixed_base_msm_scaling() {
    let sizes: [u32; 4] = [1 << 13, 1 << 14, 1 << 15, 1 << 16];
    let max_cap = *sizes.iter().max().unwrap();

    // Build generators once at the largest capacity; smaller sizes use the prefix.
    let even_pc = PedersenGens::<Affine<P0>>::default();
    let odd_pc = PedersenGens::<Affine<P1>>::default();
    let even_bp = BulletproofGens::<Affine<P0>>::new(max_cap, 1);
    let odd_bp = BulletproofGens::<Affine<P1>>::new(max_cap, 1);

    println!("\n=== FixedBaseMSM split vs combined MSM: scaling (Pallas+Vesta = 2 BPs per curve tree) ===");
    println!(
        "ark-ec MSM regime: {}   (rayon threads = {})",
        msm_desc(),
        rayon_threads()
    );

    // (padded_n, tables MB, gens MB, precompute, A, B, C, B-speedup, C-speedup, B-break-even)
    #[allow(clippy::type_complexity)]
    let mut rows: Vec<(
        u32,
        f64,
        f64,
        Duration,
        Duration,
        Duration,
        Duration,
        f64,
        f64,
        Option<u64>,
    )> = Vec::new();

    for &padded_n in &sizes {
        let reps = if padded_n <= (1 << 14) { 8 } else { 4 };
        let e = compare(padded_n, &even_pc, &even_bp, reps);
        let o = compare(padded_n, &odd_pc, &odd_bp, reps);

        let table_both = e.table_bytes + o.table_bytes;
        let gens_both = e.gen_bytes + o.gen_bytes;
        let precompute_both = e.precompute + o.precompute;
        let a_both = e.baseline_msm + o.baseline_msm;
        let b_both = e.split_total + o.split_total;
        let c_both = e.batch_affine + o.batch_affine;
        let b_speedup = a_both.as_secs_f64() / b_both.as_secs_f64().max(1e-12);
        let c_speedup = a_both.as_secs_f64() / c_both.as_secs_f64().max(1e-12);
        let saving = a_both.as_secs_f64() - b_both.as_secs_f64();
        let break_even =
            (saving > 0.0).then(|| (precompute_both.as_secs_f64() / saving).ceil() as u64);

        println!(
            "\n--- padded_n = 2^{} ({}) ---",
            padded_n.trailing_zeros(),
            padded_n
        );
        println!(
            "  per curve: fixed bases = {} (2 + 2 padded_n), point size = {} B, table c={} W={} entries n*W={}",
            e.n_fixed, e.point_size, e.window, e.num_windows, e.table_len
        );
        println!("  memory (both BPs summed):");
        println!(
            "    generators (A and C store these)   : {:.1} MB   ({} + {} pts)",
            mb(gens_both),
            e.n_fixed,
            o.n_fixed
        );
        println!(
            "    B fixed-base tables (extra)        : {:.1} MB   ({}x generators)",
            mb(table_both),
            e.num_windows
        );
        println!("  B one-time precompute (both tables)  : {precompute_both:?}");
        println!("  per proof (both BPs summed):");
        println!("    A combined msm_unchecked_full_width   : {a_both:?}   (1.00x)");
        println!(
            "    B fixed split total                : {b_both:?}   ({b_speedup:.2}x)   [fixed {:?} + {:?}, var {:?} + {:?}]",
            e.split_fixed, o.split_fixed, e.split_var, o.split_var
        );
        println!("    C combined msm_batch_affine        : {c_both:?}   ({c_speedup:.2}x)");
        match break_even {
            Some(k) => println!("    B break-even                       : {k} proofs"),
            None => println!("    B not faster than A; no break-even"),
        }

        rows.push((
            padded_n,
            mb(table_both),
            mb(gens_both),
            precompute_both,
            a_both,
            b_both,
            c_both,
            b_speedup,
            c_speedup,
            break_even,
        ));
    }

    println!("\n=== summary (per proof, both BPs summed per curve tree) ===");
    println!("  A = combined msm_unchecked_full_width (current)   B = FixedBaseMSM split   C = combined msm_batch_affine");
    println!(
        "{:>9} | {:>9} | {:>8} | {:>11} | {:>11} | {:>11} | {:>11} | {:>7} | {:>7} | {:>9}",
        "padded_n",
        "tables MB",
        "gens MB",
        "precompute",
        "A",
        "B",
        "C",
        "B x",
        "C x",
        "B break-even"
    );
    for (n, tmb, gmb, pc, a, b, c, bx, cx, be) in &rows {
        println!(
            "{:>9} | {:>9.1} | {:>8.1} | {:>11} | {:>11} | {:>11} | {:>11} | {:>6.2}x | {:>6.2}x | {:>9}",
            format!("2^{}", n.trailing_zeros()),
            tmb,
            gmb,
            format!("{:?}", pc),
            format!("{:?}", a),
            format!("{:?}", b),
            format!("{:?}", c),
            bx,
            cx,
            be.map(|k| format!("{k}")).unwrap_or_else(|| "-".to_string()),
        );
    }
    println!();
}

// ===================================================================================================
// Window-size sweep for FixedBaseMSM table (memory/traffic vs the modeled addition count).
//
// `FixedBaseMSM::new` picks the window `c` minimizing modeled additions `n*ceil(bits/c) + 2^{c-1}`,
// which ignores that at these sizes the table (n*W points, hundreds of MB) is far past cache, so
// table memory traffic — not additions — bounds the evaluation. A larger `c` shrinks `W=ceil(255/c)`
// (smaller table, less traffic) until the `2^{c-1}` bucket array dominates (more per-bucket overhead
// and larger transient offset/position arrays). This sweeps `c` around and above the `new()` choice
// so the persistent table size, transient bucket-array size, precompute cost, and fixed-base
// evaluation time can be compared. Reference: the variable-base MSM over the same fixed set (what B's
// fixed part costs with no table at all). Reported summed over both BPs (Pallas + Vesta).
// ===================================================================================================

const SWEEP_SIZES: &[u32] = &[1 << 13, 1 << 16];
const SWEEP_WINDOWS: &[usize] = &[8, 10, 12, 14, 16, 17, 18];

/// Per-window row for one curve: (c, W, num_buckets, table_bytes, precompute, fixed_eval_avg).
struct CompFixedBase {
    n_fixed: usize,
    default_c: usize,
    varbase_ref: Duration,
    rows: Vec<(usize, usize, usize, usize, Duration, Duration)>,
}

fn compare_fixed_base<P: SWCurveConfig>(
    padded_n: u32,
    pc_gens: &PedersenGens<Affine<P>>,
    bp_gens: &BulletproofGens<Affine<P>>,
    windows: &[usize],
    reps: usize,
) -> CompFixedBase {
    let mut rng = thread_rng();
    let fb = fixed_bases(pc_gens, bp_gens, padded_n);
    let n_fixed = fb.len();
    let fixed_scalars: Vec<P::ScalarField> = (0..n_fixed)
        .map(|_| P::ScalarField::rand(&mut rng))
        .collect();
    let fixed_big: Vec<_> = fixed_scalars.iter().map(|s| s.into_bigint()).collect();

    // The window `new()` would pick, and the variable-base reference over the same fixed set.
    let default_c = FixedBaseMSM::<P>::new(&fb).window();
    let expected = Projective::<P>::msm_unchecked_full_width(&fb, &fixed_scalars);
    let mut varbase_ref = Duration::ZERO;
    for _ in 0..reps {
        let t = Instant::now();
        let res = Projective::<P>::msm_unchecked_full_width(&fb, &fixed_scalars);
        varbase_ref += t.elapsed();
        let _ = black_box(res);
    }
    let varbase_ref = varbase_ref / reps as u32;

    let mut rows = Vec::with_capacity(windows.len());
    for &c in windows {
        let t = Instant::now();
        let msm = FixedBaseMSM::<P>::new_given_window_size(&fb, c);
        let precompute = t.elapsed();

        // Correctness + warm up.
        assert_eq!(msm.msm_bigint(&fixed_big), expected, "window {c} disagrees");

        let mut eval = Duration::ZERO;
        for _ in 0..reps {
            let t = Instant::now();
            let res = msm.msm_bigint(&fixed_big);
            eval += t.elapsed();
            let _ = black_box(res);
        }
        rows.push((
            c,
            msm.num_windows(),
            msm.num_buckets(),
            msm.table_bytes(),
            precompute,
            eval / reps as u32,
        ));
    }

    CompFixedBase {
        n_fixed,
        default_c,
        varbase_ref,
        rows,
    }
}

#[test]
#[ignore = "long: builds a fixed-base table per window per curve (minutes, up to ~hundreds of MB); run explicitly"]
fn fixed_base_msm_window_sweep() {
    let max_cap = *SWEEP_SIZES.iter().max().unwrap();
    let even_pc = PedersenGens::<Affine<P0>>::default();
    let odd_pc = PedersenGens::<Affine<P1>>::default();
    let even_bp = BulletproofGens::<Affine<P0>>::new(max_cap, 1);
    let odd_bp = BulletproofGens::<Affine<P1>>::new(max_cap, 1);

    println!("\n=== FixedBaseMSM window sweep: memory vs fixed-base eval time (Pallas+Vesta = 2 BPs) ===");
    println!(
        "ark-ec MSM regime: {}   (rayon threads = {})",
        msm_desc(),
        rayon_threads()
    );
    println!(
        "point size = {} B; table = n*W points; num_buckets = 2^(c-1) (capped by modulus)",
        core::mem::size_of::<Affine<P0>>()
    );

    for &padded_n in SWEEP_SIZES {
        let reps = if padded_n <= (1 << 14) { 6 } else { 3 };
        let e = compare_fixed_base(padded_n, &even_pc, &even_bp, SWEEP_WINDOWS, reps);
        let o = compare_fixed_base(padded_n, &odd_pc, &odd_bp, SWEEP_WINDOWS, reps);

        let varbase_both = e.varbase_ref + o.varbase_ref;
        println!(
            "\n--- padded_n = 2^{} ({}) : fixed bases = {} (+{}) per side, new() picks c={} ---",
            padded_n.trailing_zeros(),
            padded_n,
            e.n_fixed,
            o.n_fixed,
            e.default_c
        );
        println!(
            "  reference: variable-base msm over the fixed set (no table) = {varbase_both:?}   (1.00x, 0 MB)"
        );
        println!(
            "{:>4} | {:>3} | {:>11} | {:>10} | {:>12} | {:>13} | {:>8} | {:>6}",
            "c", "W", "num_buckets", "table MB", "precompute", "fixed-eval", "vs base", "note"
        );
        for i in 0..SWEEP_WINDOWS.len() {
            let (c, w, nb, tb, _, _) = e.rows[i];
            let (_, _, _, tb_o, _, _) = o.rows[i];
            let precompute_both = e.rows[i].4 + o.rows[i].4;
            let eval_both = e.rows[i].5 + o.rows[i].5;
            let table_both = tb + tb_o;
            let speedup = varbase_both.as_secs_f64() / eval_both.as_secs_f64().max(1e-12);
            let note = if c == e.default_c { "new()" } else { "" };
            println!(
                "{:>4} | {:>3} | {:>11} | {:>10.1} | {:>12} | {:>13} | {:>7.2}x | {:>6}",
                c,
                w,
                nb,
                mb(table_both),
                format!("{:?}", precompute_both),
                format!("{:?}", eval_both),
                speedup,
                note,
            );
        }
    }
    println!();
}
