//! Profiling for "is GLV-decomposing the IPA fold worthwhile?" decision.
//! Measures, at DART sizes, on this machine:
//!   - the current full-width JSF 2-scalar fold per element,
//!   - GLV variants (naive 4-base plain-bit, 4-base NAF), split by whether scalar_decomposition
//!     is counted, to isolate the num-bigint decomposition overhead,
//!   - new_divisor over 256 points (one per in-circuit scalar mul).
//! Run: cargo test -p relations --release --test fold_vs_divisor_profile -- --nocapture

use core::borrow::Borrow;
use std::time::Instant;

use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ec::{AdditiveGroup, VariableBaseMSM};
use ark_ff::{BigInteger, PrimeField, Zero};
use ark_pallas::{Fr, PallasConfig};
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;

use bulletproofs::msm::binary_scalar_mul_jsf_affine;

use ark_ec_divisors::{new_divisor, DivisorCurve};

type C = PallasConfig;
type Aff = Affine<C>;
type Proj = Projective<C>;

const N: usize = 4096; // one IPA round-1 vector (DART's IPA is ~2^12); whole fold ~= 2*N elements per G/H

/// MSB-first non-adjacent form (width-2 NAF) digits of a scalar's magnitude, as i8 in {-1,0,1}.
fn naf(k: Fr) -> Vec<i8> {
    let mut d = k.into_bigint();
    let mut out = Vec::with_capacity(130);
    // LSB-first, then reverse.
    while !d.is_zero() {
        let mut z = 0i8;
        if d.is_odd() {
            // low two bits
            let m = (d.as_ref()[0] & 3) as i8;
            z = 2 - m; // {1,3} -> {1,-1}
            if z == 1 {
                d.sub_with_borrow(&<Fr as PrimeField>::BigInt::from(1u64));
            } else {
                d.add_with_carry(&<Fr as PrimeField>::BigInt::from(1u64));
            }
        }
        out.push(z);
        d.div2();
    }
    out.reverse();
    out
}

/// GLV 4-base multi-scalar `b1*k1 + b2*k2` using per-base NAF over the two ~128-bit halves,
/// sharing doublings. `decomp` toggles whether scalar_decomposition is included in timing (caller
/// passes pre-decomposed data when false).
fn glv_fold_naf(gl: &Aff, k1: Fr, gr: &Aff, k2: Fr) -> Proj {
    // Decompose both scalars: k = a + lambda*b.
    let ((s_a1, a1), (s_b1, b1)) = C::scalar_decomposition(k1);
    let ((s_a2, a2), (s_b2, b2)) = C::scalar_decomposition(k2);

    // Four signed bases.
    let mut base_a1 = *gl;
    let mut base_b1 = C::endomorphism_affine(gl);
    let mut base_a2 = *gr;
    let mut base_b2 = C::endomorphism_affine(gr);
    if !s_a1 {
        base_a1 = -base_a1;
    }
    if !s_b1 {
        base_b1 = -base_b1;
    }
    if !s_a2 {
        base_a2 = -base_a2;
    }
    if !s_b2 {
        base_b2 = -base_b2;
    }

    let d_a1 = naf(a1);
    let d_b1 = naf(b1);
    let d_a2 = naf(a2);
    let d_b2 = naf(b2);
    let len = d_a1.len().max(d_b1.len()).max(d_a2.len()).max(d_b2.len());

    let get = |d: &[i8], pos: usize| -> i8 {
        // align MSB-first vectors of differing lengths
        let off = len - d.len();
        if pos < off {
            0
        } else {
            d[pos - off]
        }
    };

    let mut res = Proj::zero();
    for pos in 0..len {
        res.double_in_place();
        for (d, base) in [
            (&d_a1, &base_a1),
            (&d_b1, &base_b1),
            (&d_a2, &base_a2),
            (&d_b2, &base_b2),
        ] {
            match get(d, pos) {
                1 => res += base,
                -1 => res -= base,
                _ => {}
            }
        }
    }
    res
}

/// GLV 4-base with plain bits (naive: 4 conditional adds per bit, no NAF).
fn glv_fold_plainbits(gl: &Aff, k1: Fr, gr: &Aff, k2: Fr) -> Proj {
    let ((s_a1, a1), (s_b1, b1)) = C::scalar_decomposition(k1);
    let ((s_a2, a2), (s_b2, b2)) = C::scalar_decomposition(k2);
    let mut base_a1 = *gl;
    let mut base_b1 = C::endomorphism_affine(gl);
    let mut base_a2 = *gr;
    let mut base_b2 = C::endomorphism_affine(gr);
    if !s_a1 {
        base_a1 = -base_a1;
    }
    if !s_b1 {
        base_b1 = -base_b1;
    }
    if !s_a2 {
        base_a2 = -base_a2;
    }
    if !s_b2 {
        base_b2 = -base_b2;
    }
    let bits_a1 = a1.into_bigint().to_bits_be();
    let bits_b1 = b1.into_bigint().to_bits_be();
    let bits_a2 = a2.into_bigint().to_bits_be();
    let bits_b2 = b2.into_bigint().to_bits_be();
    // trim to first set bit among all
    let total = bits_a1.len();
    let first = (0..total)
        .find(|&i| bits_a1[i] || bits_b1[i] || bits_a2[i] || bits_b2[i])
        .unwrap_or(total);
    let mut res = Proj::zero();
    for i in first..total {
        res.double_in_place();
        if bits_a1[i] {
            res += base_a1;
        }
        if bits_b1[i] {
            res += base_b1;
        }
        if bits_a2[i] {
            res += base_a2;
        }
        if bits_b2[i] {
            res += base_b2;
        }
    }
    res
}

#[test]
#[ignore = "profiling: timings are only meaningful run alone in release with --nocapture"]
fn profile_fold_and_divisor() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(7);

    //  Fold inputs
    let gl: Vec<Aff> = (0..N).map(|_| Aff::rand(&mut rng)).collect();
    let gr: Vec<Aff> = (0..N).map(|_| Aff::rand(&mut rng)).collect();
    let s0: Vec<Fr> = (0..N).map(|_| Fr::rand(&mut rng)).collect();
    let s1: Vec<Fr> = (0..N).map(|_| Fr::rand(&mut rng)).collect();

    // Correctness cross-check on a sample: all three must agree.
    for i in [0usize, 1, 100, 4095] {
        let a = binary_scalar_mul_jsf_affine(&gl[i], s0[i], &gr[i], s1[i]);
        let b = glv_fold_naf(&gl[i], s0[i], &gr[i], s1[i]);
        let c = glv_fold_plainbits(&gl[i], s0[i], &gr[i], s1[i]);
        assert_eq!(a, b, "naf mismatch at {i}");
        assert_eq!(a, c, "plainbits mismatch at {i}");
    }

    let warm = |acc: &mut Proj, v: Proj| *acc += v;

    // (A) current full-width JSF 2-scalar fold.
    let t = Instant::now();
    let mut acc = Proj::zero();
    for i in 0..N {
        warm(
            &mut acc,
            binary_scalar_mul_jsf_affine(&gl[i], s0[i], &gr[i], s1[i]),
        );
    }
    let a_dur = t.elapsed();
    std::hint::black_box(acc);

    // (dec) scalar_decomposition overhead alone: 2 per element.
    let t = Instant::now();
    let mut sink = 0u64;
    for i in 0..N {
        let ((_, x), (_, y)) = C::scalar_decomposition(s0[i]);
        let ((_, z), (_, w)) = C::scalar_decomposition(s1[i]);
        sink ^= x.into_bigint().as_ref()[0]
            ^ y.into_bigint().as_ref()[0]
            ^ z.into_bigint().as_ref()[0]
            ^ w.into_bigint().as_ref()[0];
    }
    let dec_dur = t.elapsed();
    std::hint::black_box(sink);

    // (B) GLV 4-base NAF (incl decomposition).
    let t = Instant::now();
    let mut acc = Proj::zero();
    for i in 0..N {
        warm(&mut acc, glv_fold_naf(&gl[i], s0[i], &gr[i], s1[i]));
    }
    let b_dur = t.elapsed();
    std::hint::black_box(acc);

    // (C) GLV 4-base plain bits (incl decomposition).
    let t = Instant::now();
    let mut acc = Proj::zero();
    for i in 0..N {
        warm(&mut acc, glv_fold_plainbits(&gl[i], s0[i], &gr[i], s1[i]));
    }
    let c_dur = t.elapsed();
    std::hint::black_box(acc);

    //  Divisor: new_divisor over 256 points summing to zero (one per in-circuit scalar mul).
    let num_bits = Fr::MODULUS_BIT_SIZE as usize; // 255 -> 256 points
    let n_pts = num_bits + 1;
    let n_div = 32usize;
    let mut div_sets: Vec<Vec<Proj>> = Vec::with_capacity(n_div);
    for _ in 0..n_div {
        let mut pts: Vec<Proj> = (0..n_pts - 1).map(|_| Proj::rand(&mut rng)).collect();
        let s: Proj = pts.iter().copied().sum();
        pts.push(-s); // force sum to identity
        div_sets.push(pts);
    }
    let interp = C::interpolator_for_scalar_mul();
    // warm + correctness
    let _ = new_divisor::<C>(&div_sets[0], interp.borrow()).expect("divisor build");
    let t = Instant::now();
    let mut dsink = 0usize;
    for set in &div_sets {
        let d = new_divisor::<C>(set, interp.borrow()).expect("divisor build");
        std::hint::black_box(&d);
        dsink += 1;
    }
    let div_dur = t.elapsed();
    std::hint::black_box(dsink);

    //  MSM
    let mut msm_lines = Vec::new();
    for &m in &[1024usize, 4096, 16384] {
        let bases: Vec<Aff> = (0..m).map(|_| Aff::rand(&mut rng)).collect();
        let scls: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let _ = Proj::msm_unchecked(&bases, &scls); // warm
        let reps = if m <= 4096 { 20 } else { 8 };
        let t = Instant::now();
        let mut acc = Proj::zero();
        for _ in 0..reps {
            acc += Proj::msm_unchecked(&bases, &scls);
        }
        let d = t.elapsed();
        let _ = std::hint::black_box(acc);
        msm_lines.push((m, d.as_micros() as f64 / reps as f64));
    }

    //  Report
    let per = |d: std::time::Duration, n: usize| d.as_nanos() as f64 / n as f64;
    println!("\n================ FOLD vs DIVISOR PROFILE (serial, release) ================");
    println!(
        "N per timed batch = {N}  (DART IPA ~2^12; whole fold ~= 2*N elems for G + 2*N for H)"
    );
    println!("--- 2-scalar fold element (b1*k1 + b2*k2) ---");
    println!(
        "  (A) full-width JSF (current):     {:>8.1} ns/elem   total {:?}",
        per(a_dur, N),
        a_dur
    );
    println!(
        "  (B) GLV 4-base NAF   (+decomp):   {:>8.1} ns/elem   total {:?}   [{:.2}x vs A]",
        per(b_dur, N),
        b_dur,
        a_dur.as_nanos() as f64 / b_dur.as_nanos() as f64
    );
    println!(
        "  (C) GLV 4-base plain (+decomp):   {:>8.1} ns/elem   total {:?}   [{:.2}x vs A]",
        per(c_dur, N),
        c_dur,
        a_dur.as_nanos() as f64 / c_dur.as_nanos() as f64
    );
    println!(
        "  (dec) scalar_decomposition x2:    {:>8.1} ns/elem   total {:?}   ({:.0}% of B)",
        per(dec_dur, N),
        dec_dur,
        100.0 * dec_dur.as_nanos() as f64 / b_dur.as_nanos() as f64
    );
    println!(
        "  => GLV-NAF minus decomposition:   {:>8.1} ns/elem   [{:.2}x vs A]",
        per(b_dur, N) - per(dec_dur, N),
        a_dur.as_nanos() as f64 / (b_dur.as_nanos() as f64 - dec_dur.as_nanos() as f64)
    );
    println!("--- divisor (one per in-circuit scalar mul) ---");
    println!(
        "  new_divisor over {n_pts} pts:        {:>8.1} us/divisor  total {:?} for {n_div}",
        per(div_dur, n_div) / 1000.0,
        div_dur
    );
    println!("--- msm_unchecked ---");
    for (m, us) in &msm_lines {
        println!("  msm n={:<6}                    {:>8.1} us/call", m, us);
    }

    //  Whole-proof extrapolation (serial)
    let fold_elems_total = 2.0 * 2.0 * (N as f64); // G and H, sum over rounds ~= N each => 2N; times 2 vectors
    let fold_a_ms = per(a_dur, N) * fold_elems_total / 1e6;
    let fold_c_ms = per(c_dur, N) * fold_elems_total / 1e6;
    for d in [8usize, 12, 20] {
        let div_ms = per(div_dur, n_div) * d as f64 / 1e6;
        println!(
            "  [extrapolation] fold(JSF)={:.1} ms  fold(GLV-plain)={:.1} ms  |  {d} divisors={:.1} ms  (serial, one curve)",
            fold_a_ms, fold_c_ms, div_ms
        );
    }
    println!("===========================================================================\n");
}
