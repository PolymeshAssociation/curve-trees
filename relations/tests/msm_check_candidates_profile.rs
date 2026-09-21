//! Which MSM function should `r1cs::verifier::msm_check` call?
//!
//! Run: cargo test -p relations --release --test msm_check_candidates_profile -- --nocapture

use std::time::{Duration, Instant};

use ark_ec::scalar_mul::variable_base::{msm_bigint, msm_bigint_wnaf};
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_pallas::{Fr, PallasConfig};
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;

type C = PallasConfig;
type Aff = Affine<C>;
type Proj = Projective<C>;

fn min_ns(reps: usize, mut f: impl FnMut() -> Proj) -> (f64, Proj) {
    let r = f(); // warm
    let mut best = Duration::MAX;
    for _ in 0..reps {
        let t = Instant::now();
        let x = f();
        best = best.min(t.elapsed());
        let _ = std::hint::black_box(x);
    }
    (best.as_nanos() as f64, r)
}

#[test]
fn profile_msm_check_candidates() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(7);
    let threads = {
        #[cfg(feature = "parallel")]
        {
            rayon::current_num_threads()
        }
        #[cfg(not(feature = "parallel"))]
        {
            1usize
        }
    };
    println!("rayon threads = {threads}");

    for &n in &[256usize, 1024, 4096, 16384] {
        let bases: Vec<Aff> = (0..n).map(|_| Aff::rand(&mut rng)).collect();
        let scalars: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let bigints: Vec<_> = scalars.iter().map(|s| s.into_bigint()).collect();

        let reps = if n <= 4096 { 30 } else { 12 };

        // (current) free msm_bigint = classic unsigned Pippenger.
        let (cur, r0) = min_ns(reps, || msm_bigint::<Proj>(&bases, &bigints));
        // free msm_bigint_wnaf (full-width signed).
        let (wnaf, r1) = min_ns(reps, || msm_bigint_wnaf::<Proj>(&bases, &bigints));
        // trait msm_bigint_full_width -> wnaf for Pallas (NEGATION_IS_CHEAP).
        let (fw, r2) = min_ns(reps, || Proj::msm_bigint_full_width(&bases, &bigints));
        // trait msm_bigint -> msm_signed (size-partition + wnaf for full-width class).
        let (signed, r3) = min_ns(reps, || Proj::msm_bigint(&bases, &bigints));
        // trait msm_unchecked (takes scalars: try_msm_small + into_bigint + msm_signed).
        let (unchecked, r4) = min_ns(reps, || Proj::msm_unchecked(&bases, &scalars));

        assert_eq!(r0, r1);
        assert_eq!(r0, r2);
        assert_eq!(r0, r3);
        assert_eq!(r0, r4);

        let us = |ns: f64| ns / 1000.0;
        let x = |ns: f64| cur / ns;
        println!("\n n = {n}");
        println!(
            "   free msm_bigint (CURRENT)      {:>9.1} us   1.00x",
            us(cur)
        );
        println!(
            "   free msm_bigint_wnaf           {:>9.1} us   {:.2}x",
            us(wnaf),
            x(wnaf)
        );
        println!(
            "   trait msm_bigint_full_width    {:>9.1} us   {:.2}x",
            us(fw),
            x(fw)
        );
        println!(
            "   trait msm_bigint (->signed)    {:>9.1} us   {:.2}x",
            us(signed),
            x(signed)
        );
        println!(
            "   trait msm_unchecked            {:>9.1} us   {:.2}x",
            us(unchecked),
            x(unchecked)
        );
    }
}
