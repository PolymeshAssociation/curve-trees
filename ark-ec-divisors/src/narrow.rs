//! Experimental degree-aware divisor construction.
//!
//! Changes merge arithmetic so that each node's eval buffer is sized to its degree + 1 instead
//! of the full `required_evaluations` width. When a narrow operand feeds a wider product it
//! is first extended by finite differences, which use addition/subtraction only, no field
//! multiplications. Narrow buffers remove most of the pointwise multiplications of full-width
//! merges and pay finite-difference additions instead.

use crate::divisor::{deg_after_mul, mul_mod_slices, mul_mod_small_slices, DivisorEvals};
use crate::error::Error;
use crate::{
    batch_to_xy, build_pairs, leaf_lines_and_denoms, lines_and_denoms, slopes_and_intercepts,
    DivisorCurve, DivisorLines, DivisorPoly, Interpolator, LeafLines, LineArgs, Merges,
};
use ark_ec::short_weierstrass::Projective;
use ark_ff::{batch_inversion, PrimeField, Zero};
use ark_std::{
    borrow::{Borrow, Cow},
    vec,
    vec::Vec,
};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// A divisor `A(x) - y B(x)` in evaluation form, sized to `max(deg A, deg B) + 1` points.
#[derive(Debug, Clone, Zeroize, ZeroizeOnDrop)]
struct NarrowDivisor<F: PrimeField> {
    a: Vec<F>,
    b: Vec<F>,
    a_deg: u16,
    b_deg: u16,
}

impl<F: PrimeField> NarrowDivisor<F> {
    /// Leaf line `A(x) = slope*x + intercept` (deg 1), `B(x) = y` (deg 0), width 2.
    fn leaf(slope: F, intercept: F, y: F) -> Self {
        Self {
            a: vec![intercept, intercept + slope], // evals of A(x) at x=0, x=1
            b: vec![y, y],                         // evals of B(x) at x=0, x=1
            a_deg: 1,
            b_deg: 0,
        }
    }

    fn extend_to(&mut self, new_size: usize) {
        extend_evals(&mut self.a, self.a_deg, new_size);
        extend_evals(&mut self.b, self.b_deg, new_size);
    }

    /// Numerator of a merge: `(self * other) * line` mod the curve poly, evaluated at the
    /// numerator width `w`. `modulus` holds the full-width curve-poly evals (sliced by `w`).
    /// Similar to `DivisorEvals::merge_numerator`
    fn merge_numerator(
        mut self,
        mut other: Self,
        line: (F, F, F),
        modulus: &[F],
        w: usize,
    ) -> Self {
        self.extend_to(w);
        other.extend_to(w);

        // self <- self.mul_mod(other). Buffers are w long after extend_to; modulus is at
        // least w, so the zips run exactly w times.
        let (na, nb) = deg_after_mul((self.a_deg, self.b_deg), (other.a_deg, other.b_deg));
        mul_mod_slices(&mut self.a, &mut self.b, &other.a, &other.b, &modulus[..w]);
        self.a_deg = na;
        self.b_deg = nb;

        // self <- self.mul_mod_small(line), with A2(x) = lx*x + lz filled by running sum.
        let (lx, lz, ly) = line;
        let (na, nb) = deg_after_mul((self.a_deg, self.b_deg), (1, 0));
        mul_mod_small_slices(&mut self.a, &mut self.b, &modulus[..w], lx, lz, ly);
        self.a_deg = na;
        self.b_deg = nb;
        self
    }

    /// Pointwise-divide by a pre-inverted degree-2 denominator slice.
    fn apply_inv_denom(&mut self, inv: &[F]) {
        debug_assert_eq!(self.a.len(), inv.len());
        for ((a, b), d) in self.a.iter_mut().zip(self.b.iter_mut()).zip(inv) {
            *a *= d;
            *b *= d;
        }
        self.a_deg -= 2;
        self.b_deg -= 2;
    }

    fn truncate_to(&mut self, size: usize) {
        self.a.truncate(size);
        self.b.truncate(size);
    }
}

/// Evals of at least `required` evals, reusing the cached curve-poly evals `base`. The
/// curve poly has degree 3, so a wider modulus (a larger interpolator than the scalar-mul
/// default, e.g. divisors of more than the usual point count) is an extension of the cached prefix.
fn extend_curve_poly_evals_if_needed<F: PrimeField>(base: &[F], required: usize) -> Cow<'_, [F]> {
    if required <= base.len() {
        Cow::Borrowed(base)
    } else {
        let mut m = base.to_vec();
        extend_evals(&mut m, 3, required);
        Cow::Owned(m)
    }
}

/// Per-merge numerator evaluation counts and output degrees of the merge polynomials.
fn num_evals_and_degrees(leaf_count: usize) -> (Vec<usize>, Vec<(u16, u16)>) {
    // Each leaf is a line divisor of degree A=1, B=0
    let mut degs: Vec<(u16, u16)> = vec![(1, 0); leaf_count];
    let mut num_evals = Vec::with_capacity(leaf_count);
    let mut degrees = Vec::with_capacity(leaf_count);
    while degs.len() > 1 {
        let mut next = Vec::with_capacity(degs.len() / 2 + 1);
        if degs.len() % 2 == 1 {
            next.push(degs.pop().unwrap());
        }
        while let Some(a) = degs.pop() {
            let b = degs.pop().unwrap();
            // Degrees after multiplying divisors D_a * D_b and the merge line
            let num = deg_after_mul(deg_after_mul(a, b), (1, 0));
            // Degrees after dividing by the denominator (degree drops by 2)
            let merged = (num.0 - 2, num.1 - 2);
            // +1 as i need 1 more evaluation point
            num_evals.push(num.0.max(num.1) as usize + 1);
            degrees.push(merged);
            next.push(merged);
        }
        degs = next;
    }
    (num_evals, degrees)
}

/// All divisors' merge denominators, each at its numerator width, concatenated but not inverted,
/// plus the prefix-sum offsets.
fn build_denoms_concat<F: PrimeField>(
    merges: &Merges<F>,
    num_evals: &[usize],
) -> (Vec<F>, Vec<usize>) {
    let mut denoms: Vec<F> = Vec::new();
    let mut offsets = Vec::with_capacity(merges.len() + 1);
    offsets.push(0usize);
    for (i, (_, (x1, x2))) in merges.iter().enumerate() {
        denoms.extend(DivisorEvals::<F>::removal_denominator_evals(
            *x1,
            *x2,
            num_evals[i] as u16,
        ));
        offsets.push(denoms.len());
    }
    (denoms, offsets)
}

/// Run one divisor's narrow merge tree to a `DivisorPoly`, given pre-inverted denominators
/// (`inv_denoms[offsets[k]..offsets[k+1]]` are merge `k`'s denominator).
fn merge_to_poly<C: DivisorCurve>(
    leaf_lines: &LeafLines<C::BaseField>,
    merges: &Merges<C::BaseField>,
    curve_poly_evals: &[C::BaseField],
    inv_denoms: &[C::BaseField],
    offsets: &[usize],
    num_evals: &[usize],
    degrees: &[(u16, u16)],
    interpolator: &Interpolator<C::BaseField>,
    points_len: usize,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    // Every numerator must fit
    if let Some(&n) = num_evals.iter().max() {
        if n > curve_poly_evals.len() {
            return Err(Error::DegreeExceedsInterpolator(
                n as u16 - 1,
                interpolator.degree(),
            ));
        }
    }

    // Compute line divisors for points
    let mut divs: Vec<NarrowDivisor<C::BaseField>> = leaf_lines
        .iter()
        .map(|l| {
            let (slope, intercept, y) = l.coeffs();
            NarrowDivisor::leaf(slope, intercept, y)
        })
        .collect();

    // Compute divisors for merges
    let mut k = 0;
    while divs.len() > 1 {
        let mut next = Vec::with_capacity(divs.len() / 2 + 1);
        if divs.len() % 2 == 1 {
            next.push(divs.pop().unwrap());
        }
        while let Some(a) = divs.pop() {
            let b = divs.pop().unwrap();
            let w = num_evals[k];
            let line = merges[k].0.coeffs();
            let mut merged = a.merge_numerator(b, line, curve_poly_evals, w);
            merged.apply_inv_denom(&inv_denoms[offsets[k]..offsets[k + 1]]);
            merged.truncate_to(degrees[k].0.max(degrees[k].1) as usize + 1);
            next.push(merged);
            k += 1;
        }
        divs = next;
    }

    let mut root = divs.remove(0);
    let max_deg = root.a_deg.max(root.b_deg);
    if max_deg > interpolator.degree() {
        return Err(Error::DegreeExceedsInterpolator(
            max_deg,
            interpolator.degree(),
        ));
    }
    root.extend_to(interpolator.required_evaluations() as usize);
    let a_coeffs = interpolator.interpolate(&root.a)?;
    let b_coeffs = interpolator.interpolate(&root.b)?;

    let mut divisor = DivisorPoly {
        zero_coefficient: a_coeffs[0],
        x_coefficients: a_coeffs[1..].to_vec(),
        yx_coefficients: b_coeffs[1..].to_vec(),
        y_coefficient: b_coeffs[0],
    };
    divisor
        .yx_coefficients
        .truncate(points_len.div_ceil(2).saturating_sub(2));
    divisor.x_coefficients.truncate(points_len / 2);
    Ok(divisor)
}

/// Degree-aware analogue of `new_divisor`.
pub fn new_divisor_narrow<C: DivisorCurve>(
    points: &[Projective<C>],
    interpolator: &Interpolator<C::BaseField>,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    // Cached per curve, extended only if a wider interpolator is passed.
    let curve_poly_evals = C::evaluation_of_curve_poly();
    let curve_poly_evals = curve_poly_evals.borrow().as_slice();
    let curve_poly_evals = extend_curve_poly_evals_if_needed(
        curve_poly_evals,
        interpolator.required_evaluations() as usize,
    );
    let (leaf_lines, merges) = lines_and_denoms::<C>(points)?;
    let (num_evals, degrees) = num_evals_and_degrees(leaf_lines.len());
    debug_assert_eq!(num_evals.len(), merges.len());
    let (mut all_denoms, offsets) = build_denoms_concat(&merges, &num_evals);
    // Extremely unlikely but just incase
    if all_denoms.iter().any(|d| d.is_zero()) {
        return Err(Error::InvertingZero);
    }
    batch_inversion(&mut all_denoms);
    merge_to_poly::<C>(
        &leaf_lines,
        &merges,
        &curve_poly_evals,
        &all_denoms,
        &offsets,
        &num_evals,
        &degrees,
        interpolator,
        points.len(),
    )
}

/// Column-major line construction for many divisors at once (perf item "B1"): one
/// `normalize_batch` and one slope `batch_inversion` shared across all `point_sets`.
/// Returns `(leaf_lines, merges)` per set.
fn lines_and_denoms_multi<C: DivisorCurve>(
    point_sets: &[&[Projective<C>]],
) -> Result<Vec<DivisorLines<C::BaseField>>, Error> {
    let g: Projective<C> = C::GENERATOR.into();

    // Per divisor: build the pair tree and sanitize each pair (degenerate-pair handling).
    let all_args: Vec<Vec<LineArgs<C>>> = point_sets
        .iter()
        .map(|points| {
            build_pairs::<C>(points)
                .iter()
                .map(|[a, b]| LineArgs::new(*a, *b, &g))
                .collect()
        })
        .collect();

    // One affine conversion for every divisor's points. Each divisor occupies a contiguous
    // [a's | b's] block.
    let total_args = all_args.iter().map(|a| a.len()).sum::<usize>();
    let (all_a_xy, all_b_xy) = {
        let mut pts = vec![Projective::zero(); 2 * total_args];
        let mut i = 0;
        for args in &all_args {
            for la in args {
                pts[i] = la.a;
                pts[total_args + i] = la.b;
                i += 1;
            }
        }
        let mut a_xy = batch_to_xy::<C>(&pts);
        let b_xy = a_xy.split_off(total_args);
        (a_xy, b_xy)
    };

    let all_slopes_and_intercepts = slopes_and_intercepts::<C>(&all_a_xy, &all_b_xy)?;

    let mut result = Vec::with_capacity(point_sets.len());
    let mut cursor = 0;
    for (i, args) in all_args.iter().enumerate() {
        let count = args.len();
        let a_xy = &all_a_xy[cursor..cursor + count];
        let b_xy = &all_b_xy[cursor..cursor + count];
        let slopes_and_intercepts = &all_slopes_and_intercepts[cursor..cursor + count];
        let num_leaves = point_sets[i].len().div_ceil(2);

        let div_lines =
            leaf_lines_and_denoms::<C>(num_leaves, args, a_xy, b_xy, slopes_and_intercepts);
        result.push(div_lines);
        cursor += count;
    }
    Ok(result)
}

/// Builds one divisor per set, sharing a single `normalize_batch`, slope `batch_inversion`, and denominator
/// `batch_inversion` across all `point_sets` (vs one of each per divisor).
pub fn new_divisors_narrow_multi<C: DivisorCurve>(
    point_sets: &[&[Projective<C>]],
    interpolator: &Interpolator<C::BaseField>,
) -> Result<Vec<DivisorPoly<C::BaseField>>, Error> {
    let curve_poly = C::evaluation_of_curve_poly();
    let base = curve_poly.borrow().as_slice();
    let curve_poly_evals =
        extend_curve_poly_evals_if_needed(base, interpolator.required_evaluations() as usize);
    let divisor_lines = lines_and_denoms_multi::<C>(point_sets)?;

    // Concatenate every divisor's denominators into one buffer and invert the whole thing once.

    // num_evals, degrees, offsets and starting index for this divisor's denominators in `all_denoms`
    let mut div_lines_info: Vec<(Vec<usize>, Vec<(u16, u16)>, Vec<usize>, usize)> =
        Vec::with_capacity(divisor_lines.len());

    let mut all_denoms = Vec::new();

    for (leaf_lines, merges) in &divisor_lines {
        let (num_evals, degrees) = num_evals_and_degrees(leaf_lines.len());
        let (denoms, offsets) = build_denoms_concat(merges, &num_evals);
        let start = all_denoms.len();
        all_denoms.extend(denoms);
        div_lines_info.push((num_evals, degrees, offsets, start));
    }
    // Extremely unlikely but just incase
    if all_denoms.iter().any(|d| d.is_zero()) {
        return Err(Error::InvertingZero);
    }
    batch_inversion(&mut all_denoms);

    let mut res = Vec::with_capacity(divisor_lines.len());
    for (i, ((leaf_lines, merges), info)) in
        divisor_lines.into_iter().zip(div_lines_info).enumerate()
    {
        let (num_evals, degrees, offsets, start) = info;
        let len = *offsets.last().unwrap();
        let inv = &all_denoms[start..start + len];
        res.push(merge_to_poly::<C>(
            &leaf_lines,
            &merges,
            &curve_poly_evals,
            inv,
            &offsets,
            &num_evals,
            &degrees,
            interpolator,
            point_sets[i].len(),
        )?);
    }
    Ok(res)
}

/// Extend `evals`, the values of a degree-`degree` polynomial at `0, 1, .., len-1`, to
/// `new_len` points by finite differences, using additions and subtractions only. With `D`
/// the forward-difference operator (`(D v)[i] = v[i+1] - v[i]`), a degree-`d` polynomial
/// has constant `D^d v`, so from the trailing diagonal `r[j] = (D^j v)[last-j]` of the
/// difference table each next value costs `d` additions: `r[j] = r[j] + r[j+1]` for
/// `j = d-1, .., 0`, after which `r[0]` is the evaluation at the next point. Newton
/// forward differences: <https://en.wikipedia.org/wiki/Finite_difference#Newton's_series>.
/// Tabulation by constant `d`-th differences (Babbage's difference engine):
/// <https://en.wikipedia.org/wiki/Difference_engine#Method_of_differences>.
/// Requires `evals.len() >= degree + 1`.
fn extend_evals<F: PrimeField>(evals: &mut Vec<F>, degree: u16, new_len: usize) {
    let cur = evals.len();
    if new_len <= cur {
        return;
    }
    let d = degree as usize;
    debug_assert!(cur > d, "need degree+1 points to extend");

    // Difference triangle over the last d+1 values, in place, keeping the trailing
    // diagonal (bottom edge of triangle). After pass i, r[j] = (D^i v)[p+j] for j <= d-i and r[j]
    // for j > d-i keeps its pass-(d-j) value, so the final r[j] = (D^(d-j) v)[p+j]. Reversed, that is
    // r[j] = (D^j v)[cur-1-j].
    let p = cur - 1 - d;
    let mut r: Vec<F> = evals[p..=p + d].to_vec();
    for i in 1..=d {
        for j in 0..=(d - i) {
            r[j] = r[j + 1] - r[j];
        }
    }
    r.reverse();

    // Each sweep advances the diagonal's anchor by one point: r[j] + r[j+1] (the latter
    // already advanced) = (D^j v) at the next anchor, for j = d-1 down to 0; r[d] is the
    // constant d-th difference. r[0] is then the value at the next point.
    evals.reserve(new_len - cur);
    for _ in cur..new_len {
        for j in (0..d).rev() {
            r[j] = r[j] + r[j + 1];
        }
        evals.push(r[0]);
    }
}

#[cfg(all(test, feature = "pallas", feature = "vesta"))]
mod tests {
    use super::*;
    use crate::new_divisor;
    use ark_std::borrow::Borrow;
    use ark_std::UniformRand;
    use rand::prelude::StdRng;
    use rand_core::SeedableRng;
    use std::time::Instant;

    fn random_zero_sum_set<C: DivisorCurve>(n: usize, rng: &mut StdRng) -> Vec<Projective<C>> {
        let mut pts: Vec<Projective<C>> = (0..n - 1).map(|_| Projective::<C>::rand(rng)).collect();
        let sum = pts.iter().copied().reduce(|a, b| a + b).unwrap();
        pts.push(-sum);
        pts
    }

    fn assert_eq_poly<F: PrimeField>(got: &DivisorPoly<F>, expected: &DivisorPoly<F>) {
        assert_eq!(got.y_coefficient, expected.y_coefficient);
        assert_eq!(got.zero_coefficient, expected.zero_coefficient);
        assert_eq!(got.x_coefficients, expected.x_coefficients);
        assert_eq!(got.yx_coefficients, expected.yx_coefficients);
    }

    #[test]
    fn test_narrow() {
        fn check<C: DivisorCurve>() {
            let mut rng = StdRng::seed_from_u64(0);
            let interp = C::interpolator_for_scalar_mul();
            let interp = interp.borrow();
            for n in [2usize, 3, 4, 5, 8, 17, 64, 129, 256] {
                let points = random_zero_sum_set::<C>(n, &mut rng);
                let expected = new_divisor::<C>(&points, interp).unwrap();
                let got = new_divisor_narrow::<C>(&points, interp).unwrap();
                assert_eq_poly(&got, &expected);
            }
        }

        check::<ark_pallas::PallasConfig>();
        check::<ark_vesta::VestaConfig>();
    }

    #[test]
    fn test_narrow_multi() {
        fn check<C: DivisorCurve>() {
            let mut rng = StdRng::seed_from_u64(0);
            let interp = C::interpolator_for_scalar_mul();
            let interp = interp.borrow();
            let sets: Vec<Vec<Projective<C>>> = [2usize, 3, 5, 8, 17, 64, 256]
                .iter()
                .map(|&n| random_zero_sum_set::<C>(n, &mut rng))
                .collect();
            let refs: Vec<&[Projective<C>]> = sets.iter().map(|v| v.as_slice()).collect();

            let batched = new_divisors_narrow_multi::<C>(&refs, interp).unwrap();
            assert_eq!(batched.len(), sets.len());
            for (set, got) in sets.iter().zip(&batched) {
                assert_eq_poly(got, &new_divisor::<C>(set, interp).unwrap());
            }
        }

        check::<ark_pallas::PallasConfig>();
        check::<ark_vesta::VestaConfig>();
    }

    #[test]
    fn timing_narrow_vs_fixed() {
        fn check<C: DivisorCurve>() {
            let mut rng = StdRng::seed_from_u64(0);
            let interp = C::interpolator_for_scalar_mul();
            let interp = interp.borrow();
            let points = random_zero_sum_set::<C>(256, &mut rng);
            let iters = 200;

            let t = Instant::now();
            for _ in 0..iters {
                let _ = new_divisor::<C>(&points, interp).unwrap();
            }
            let fixed = t.elapsed();

            let t = Instant::now();
            for _ in 0..iters {
                let _ = new_divisor_narrow::<C>(&points, interp).unwrap();
            }
            let narrow = t.elapsed();

            println!(
                "N=256 x{iters}: fixed-width {fixed:?}, narrow {narrow:?} ({:.2}x)",
                fixed.as_secs_f64() / narrow.as_secs_f64()
            );
        }

        check::<ark_pallas::PallasConfig>();
    }

    #[test]
    fn timing_interp_fraction() {
        // What fraction of `new_divisor_narrow` is the final interpolation

        fn check<C: DivisorCurve>() {
            use std::time::Instant;

            let mut rng = StdRng::seed_from_u64(0);
            let interp = C::interpolator_for_scalar_mul();
            let interp = interp.borrow();
            let m = interp.required_evaluations() as usize;
            let points = random_zero_sum_set::<C>(256, &mut rng);
            let evals: Vec<C::BaseField> = (0..m).map(|_| UniformRand::rand(&mut rng)).collect();
            let iters = 200;

            let _ = new_divisor_narrow::<C>(&points, interp).unwrap();

            let t = Instant::now();
            for _ in 0..iters {
                let _ = new_divisor_narrow::<C>(&points, interp).unwrap();
            }
            let total = t.elapsed();

            let t = Instant::now();
            for _ in 0..iters {
                // The two interpolations new_divisor_narrow performs (A and B).
                let _ = interp.interpolate(&evals).unwrap();
                let _ = interp.interpolate(&evals).unwrap();
            }
            let interp_only = t.elapsed();

            println!(
                "N=256 x{iters}: narrow total {total:?} | interpolate {interp_only:?} ({:.0}% of total)",
                100.0 * interp_only.as_secs_f64() / total.as_secs_f64()
            );
        }

        check::<ark_pallas::PallasConfig>();
    }

    #[test]
    fn timing_b1() {
        // Isolates inversion-sharing: both sides are degree-aware, so the only difference is
        // per-divisor vs one-shared `batch_inversion` (normalize + slope + denom)

        fn check<C: DivisorCurve>() {
            let mut rng = StdRng::seed_from_u64(0);
            let interp = C::interpolator_for_scalar_mul();
            let interp = interp.borrow();
            let (k, n, reps) = (16usize, 256usize, 20usize);
            let sets: Vec<Vec<Projective<C>>> = (0..k)
                .map(|_| random_zero_sum_set::<C>(n, &mut rng))
                .collect();
            let refs: Vec<&[Projective<C>]> = sets.iter().map(|v| v.as_slice()).collect();

            let t = Instant::now();
            for _ in 0..reps {
                for s in &sets {
                    let _ = new_divisor_narrow::<C>(s, interp).unwrap();
                }
            }
            let narrow = t.elapsed();

            let t = Instant::now();
            for _ in 0..reps {
                let _ = new_divisors_narrow_multi::<C>(&refs, interp).unwrap();
            }
            let b1 = t.elapsed();

            println!(
                "K={k} N={n} x{reps}: serial-narrow {narrow:?} | B1 (shared inv) {b1:?} ({:.3}x)",
                narrow.as_secs_f64() / b1.as_secs_f64()
            );
        }

        check::<ark_pallas::PallasConfig>();
    }
}
