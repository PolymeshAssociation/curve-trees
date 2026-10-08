//! Profiles the zakura "deferred IPA generator fold" on curve-trees.
//!
//! Round 1 of the Bulletproofs IPA generator fold multiplies the fixed public `BulletproofGens`
//! by challenge-derived scalars: `G'_i = s0_i * G_L[i] + s1_i * G_R[i]`. Because the bases are known
//! ahead of time and reused across every proof, a precomputed fixed-base window table (one per base)
//! replaces the per-element JSF 2-scalar mul (which pays ~255 doublings). Rounds 2+ fold
//! proof-specific generators and cannot use the table.
//!
//! This measures, at DART sizes on this machine:
//!   - (A) the current full-width JSF 2-scalar fold per element (baseline),
//!   - (FB) the fixed-base windowed fold at several window sizes (table build NOT timed: amortized
//!     across proofs), with per-base table memory,
//! then extrapolates to the whole generator fold (round 1 only is fixed-base-eligible).
//!
//! Run: cargo test -p relations --release --test fold_fixed_base_profile -- --nocapture

use std::time::Instant;

use ark_ec::scalar_mul::BatchMulPreprocessing;
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::{PrimeField, Zero};
use ark_pallas::{Fr, PallasConfig};
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;

use bulletproofs::msm::binary_scalar_mul_jsf_affine;

type C = PallasConfig;
type Aff = Affine<C>;
type Proj = Projective<C>;

/// Round-1 fold ops for one generator vector of size 2*N (each op consumes G_L[i], G_R[i]).
/// DART IPA ~2^12 generators/vector => N = 2048 fold ops/vector. Use 4096 for stable timing.
const N: usize = 4096;

/// Build a per-base fixed-base table sized for `num_scalars_hint`, which selects the arkworks
/// window via `BatchMulPreprocessing::compute_window_size`. Returns the tables and the chosen window.
fn build_tables(
    bases: &[Aff],
    num_scalars_hint: usize,
) -> (Vec<BatchMulPreprocessing<Proj>>, usize) {
    let tables: Vec<BatchMulPreprocessing<Proj>> = bases
        .iter()
        .map(|b| BatchMulPreprocessing::new(b.into_group(), num_scalars_hint))
        .collect();
    let window = tables[0].window;
    (tables, window)
}

#[test]
#[ignore = "profiling: timings are only meaningful run alone in release with --nocapture"]
fn profile_fixed_base_fold() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(7);

    let gl: Vec<Aff> = (0..N).map(|_| Aff::rand(&mut rng)).collect();
    let gr: Vec<Aff> = (0..N).map(|_| Aff::rand(&mut rng)).collect();
    let s0: Vec<Fr> = (0..N).map(|_| Fr::rand(&mut rng)).collect();
    let s1: Vec<Fr> = (0..N).map(|_| Fr::rand(&mut rng)).collect();

    let warm = |acc: &mut Proj, v: Proj| *acc += v;

    // (A) current full-width JSF 2-scalar fold. Warm + min-of-reps, same as the FB variants.
    const REPS_A: usize = 5;
    {
        let mut acc = Proj::zero();
        for i in 0..N {
            warm(
                &mut acc,
                binary_scalar_mul_jsf_affine(&gl[i], s0[i], &gr[i], s1[i]),
            );
        }
        let _ = std::hint::black_box(acc);
    }
    let mut a_ns = f64::MAX;
    for _ in 0..REPS_A {
        let t = Instant::now();
        let mut acc = Proj::zero();
        for i in 0..N {
            warm(
                &mut acc,
                binary_scalar_mul_jsf_affine(&gl[i], s0[i], &gr[i], s1[i]),
            );
        }
        a_ns = a_ns.min(t.elapsed().as_nanos() as f64 / N as f64);
        let _ = std::hint::black_box(acc);
    }

    let aff_bytes = std::mem::size_of::<Aff>();

    println!("\n============ FIXED-BASE IPA GENERATOR FOLD (zakura #361/#363, serial, release) ============");
    println!(
        "N = {N} fold ops ( = round 1 of a {} -generator vector )",
        2 * N
    );
    println!("affine point in-memory size = {aff_bytes} bytes");
    println!("--- 2-scalar fold element (s0*G_L + s1*G_R), min of {REPS_A} reps ---");
    println!("  (A) full-width JSF (current):        {a_ns:>9.1} ns/elem   1.00x");

    // (FB-*) fixed-base windowed fold. num_scalars hints chosen to sweep the arkworks window.
    // Each window is isolated (tables dropped before the next) so one window's working set does
    // not pollute the next. Warm up, then report min AND max of REPS reps: min ~= arithmetic-bound
    // best case, the min/max spread exposes how memory-bandwidth-bound (hence fragile) it is.
    const REPS: usize = 5;
    let mut best: Option<(usize, f64)> = None; // (window, min ns)
    for &hint in &[1usize, 64, 200, 400, 3000] {
        let (tl, window) = build_tables(&gl, hint);
        let (tr, _) = build_tables(&gr, hint);

        // Correctness: sample a few elements against the naive 2-scalar mul.
        for &i in &[0usize, 1, N / 2, N - 1] {
            let got = tl[i].windowed_mul(&s0[i]) + tr[i].windowed_mul(&s1[i]);
            let want = gl[i].into_group() * s0[i] + gr[i].into_group() * s1[i];
            assert_eq!(got, want, "fixed-base mismatch at {i} (window {window})");
        }

        // COLD pass: the first read right after build. The build wrote the whole table (evicting
        // it from cache at these sizes), so this first pass reads cold from DRAM -- exactly the
        // prover's round-1 access pattern (each base's table is touched for ONE scalar, never reused).
        let cold_ns = {
            let t = Instant::now();
            let mut acc = Proj::zero();
            for i in 0..N {
                warm(
                    &mut acc,
                    tl[i].windowed_mul(&s0[i]) + tr[i].windowed_mul(&s1[i]),
                );
            }
            let ns = t.elapsed().as_nanos() as f64 / N as f64;
            let _ = std::hint::black_box(acc);
            ns
        };

        // WARM: min over further reps, tables now (partly) resident. Optimistic upper bound.
        let mut warm_min = f64::MAX;
        for _ in 0..REPS {
            let t = Instant::now();
            let mut acc = Proj::zero();
            for i in 0..N {
                warm(
                    &mut acc,
                    tl[i].windowed_mul(&s0[i]) + tr[i].windowed_mul(&s1[i]),
                );
            }
            let ns = t.elapsed().as_nanos() as f64 / N as f64;
            let _ = std::hint::black_box(acc);
            warm_min = warm_min.min(ns);
        }
        // Extrapolate from the COLD (realistic) number.
        if best.map_or(true, |(_, b)| cold_ns < b) {
            best = Some((window, cold_ns));
        }

        // Per-base table: outerc rows of 2^window points (affine).
        let outerc = (Fr::MODULUS_BIT_SIZE as usize).div_ceil(window);
        let pts_per_base = outerc * (1usize << window);
        let per_base_kib = pts_per_base * aff_bytes / 1024;
        // Full prover: 8192 bases (n=4096 generators for G + 4096 for H, each tabled once).
        let full_bases = 8192usize;
        let full_mib = (pts_per_base * aff_bytes) as f64 * full_bases as f64 / (1024.0 * 1024.0);

        println!(
            "  (FB w={window}) COLD {cold_ns:>9.1} ns ({:.2}x)  |  warm-min {warm_min:>9.1} ns ({:.2}x)   [table {per_base_kib} KiB/base, {full_mib:.0} MiB for {full_bases} bases]",
            a_ns / cold_ns,
            a_ns / warm_min,
        );
    }

    // ---- Whole generator-fold extrapolation (serial, one curve) ----
    // Per vector: total fold ops = n-1 (n/2 + n/4 + ... + 1); round 1 = n/2 (the only fixed-base
    // round). So whole fold ~= half FB-eligible + half JSF, times 2 vectors (G and H). Use the
    // FASTEST measured fixed-base window.
    let (window, t_fb) = best.unwrap();
    let t_jsf = a_ns;
    println!("  (best fixed-base window for extrapolation: w={window} at {t_fb:.1} ns/elem)");

    // n generators/vector; ops = n-1 total, n/2 in round 1.
    // GLV-NAF (sibling harness, this machine ~1.23x) applies to ALL rounds with zero extra memory.
    let glv_naf_speedup = 1.23_f64;
    for &n_gen in &[1024usize, 4096] {
        let total_ops = (n_gen - 1) as f64;
        let r1_ops = (n_gen / 2) as f64;
        let rest_ops = total_ops - r1_ops;
        let per_vec_all_jsf = total_ops * t_jsf;
        let per_vec_fb_r1 = r1_ops * t_fb + rest_ops * t_jsf;
        let two_vec_jsf = 2.0 * per_vec_all_jsf / 1e6;
        let two_vec_fb = 2.0 * per_vec_fb_r1 / 1e6;
        let two_vec_glv = two_vec_jsf / glv_naf_speedup;
        // Stacked: fixed-base round 1, GLV-NAF rounds 2+.
        let two_vec_stack = 2.0 * (r1_ops * t_fb + rest_ops * t_jsf / glv_naf_speedup) / 1e6;
        println!(
            "  [extrapolation n={n_gen}] whole fold (G+H): all-JSF {two_vec_jsf:.2} ms | FB-round1(w={window}) {two_vec_fb:.2} ms ({:.2}x, +table) | GLV-NAF-all {two_vec_glv:.2} ms ({:.2}x, 0 mem) | FB-r1+GLV-rest {two_vec_stack:.2} ms ({:.2}x)",
            two_vec_jsf / two_vec_fb,
            two_vec_jsf / two_vec_glv,
            two_vec_jsf / two_vec_stack,
        );
    }

    // ---- Context: a single end-level MSM for the same n, to size the fold against the dominant cost ----
    for &m in &[4096usize] {
        let bases: Vec<Aff> = (0..m).map(|_| Aff::rand(&mut rng)).collect();
        let scls: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let _ = Proj::msm_unchecked(&bases, &scls);
        let reps = 20;
        let t = Instant::now();
        let mut acc = Proj::zero();
        for _ in 0..reps {
            acc += Proj::msm_unchecked(&bases, &scls);
        }
        let d = t.elapsed();
        let _ = std::hint::black_box(acc);
        println!(
            "  [context] one msm_unchecked n={m}: {:.1} us/call",
            d.as_micros() as f64 / reps as f64
        );
    }
}
