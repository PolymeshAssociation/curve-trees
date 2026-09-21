use ark_ec::short_weierstrass::Projective;
use ark_ec_divisors::narrow::{new_divisor_narrow, new_divisors_narrow_multi};
use ark_ec_divisors::{new_divisor, DivisorCurve};
use ark_ff::Zero;
use ark_std::borrow::Borrow;
use ark_std::UniformRand;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::StdRng;
use rand_core::SeedableRng;
use std::hint::black_box;

/// `n` random points summing to the point at infinity.
fn random_zero_sum_set<C: DivisorCurve>(n: usize, rng: &mut StdRng) -> Vec<Projective<C>> {
    let mut pts: Vec<Projective<C>> = (0..n - 1).map(|_| Projective::<C>::rand(rng)).collect();
    let sum = pts.iter().copied().reduce(|a, b| a + b).unwrap();
    pts.push(-sum);
    debug_assert!(pts.iter().copied().reduce(|a, b| a + b).unwrap().is_zero());
    pts
}

fn bench_curve<C: DivisorCurve>(c: &mut Criterion, curve_name: &str) {
    let mut rng = StdRng::seed_from_u64(0);
    let interp = C::interpolator_for_scalar_mul();
    let interp = interp.borrow();

    let mut group = c.benchmark_group(format!("new_divisor/{curve_name}"));
    for &n in &[2usize, 4, 8, 17, 64, 129, 256] {
        let points = random_zero_sum_set::<C>(n, &mut rng);

        group.bench_with_input(BenchmarkId::new("fixed", n), &points, |bench, points| {
            bench.iter(|| black_box(new_divisor::<C>(points, interp).unwrap()))
        });
        group.bench_with_input(BenchmarkId::new("narrow", n), &points, |bench, points| {
            bench.iter(|| black_box(new_divisor_narrow::<C>(points, interp).unwrap()))
        });
    }
    group.finish();
}

/// Batched `new_divisors_narrow_multi` vs looping the single-divisor paths over the same `k` sets.
fn bench_multi<C: DivisorCurve>(c: &mut Criterion, curve_name: &str) {
    let mut rng = StdRng::seed_from_u64(0);
    let interp = C::interpolator_for_scalar_mul();
    let interp = interp.borrow();
    let k = 16usize;

    let mut group = c.benchmark_group(format!("new_divisors_multi/{curve_name}/k{k}"));
    for &n in &[8usize, 64, 256] {
        let sets: Vec<Vec<Projective<C>>> = (0..k)
            .map(|_| random_zero_sum_set::<C>(n, &mut rng))
            .collect();
        let refs: Vec<&[Projective<C>]> = sets.iter().map(|v| v.as_slice()).collect();

        group.bench_with_input(BenchmarkId::new("loop_fixed", n), &sets, |bench, sets| {
            bench.iter(|| {
                for s in sets {
                    black_box(new_divisor::<C>(s, interp).unwrap());
                }
            })
        });
        group.bench_with_input(BenchmarkId::new("loop_narrow", n), &sets, |bench, sets| {
            bench.iter(|| {
                for s in sets {
                    black_box(new_divisor_narrow::<C>(s, interp).unwrap());
                }
            })
        });
        group.bench_with_input(BenchmarkId::new("batched", n), &refs, |bench, refs| {
            bench.iter(|| black_box(new_divisors_narrow_multi::<C>(refs, interp).unwrap()))
        });
    }
    group.finish();
}

fn benchmarks(c: &mut Criterion) {
    bench_curve::<ark_pallas::PallasConfig>(c, "pallas");
    bench_curve::<ark_vesta::VestaConfig>(c, "vesta");
    bench_multi::<ark_pallas::PallasConfig>(c, "pallas");
    bench_multi::<ark_vesta::VestaConfig>(c, "vesta");
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
