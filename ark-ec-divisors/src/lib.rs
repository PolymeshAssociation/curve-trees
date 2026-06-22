#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

// This code is ported from [Monero's codebase](https://github.com/monero-oxide/monero-oxide/tree/fcmp%2B%2B/crypto/divisors)
// Read the audit. Consider SlverBullet paper

use ark_ec::short_weierstrass::Projective;
use ark_ec::{AdditiveGroup, CurveConfig, CurveGroup};
use ark_ff::{batch_inversion, PrimeField, Zero};
use ark_std::borrow::Borrow;
use ark_std::{vec, vec::Vec};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

mod barycentric;
pub use barycentric::Interpolator;

mod divisor;
use divisor::{DivisorEvals, SmallDivisor};

mod poly;
pub use poly::DivisorPoly;
pub mod curves;
pub mod scalar_decomposition;
pub mod util;

pub mod error;
use error::Error;

pub use curves::DivisorCurve;
pub use scalar_decomposition::ScalarDecomposition;

type Xy<C> = (<C as CurveConfig>::BaseField, <C as CurveConfig>::BaseField);
type Denom<F> = (CtOption<F>, CtOption<F>);

/// Per-pair output of `line_args`: the sanitized points whose line we compute, plus degeneracy flags.
struct LineArgs<C: DivisorCurve> {
    /// Final first point
    a: Projective<C>,
    /// Final second point, chosen so the pair has distinct x (the batched slope never divides by zero).
    b: Projective<C>,
    /// Whether the original first or second point were identity
    a_is_identity: bool,
    b_is_identity: bool,
    /// Both original points were the identity.
    both_are_identity: Choice,
    /// One point was the identity, or the two were additive inverses.
    one_is_identity_or_additive_inverses: Choice,
    /// `line_args` changed `b` (a degenerate pair). When set, the original `b` shared `a`'s
    /// x-coordinate, so `a_x` is the original b's x for the denominator / constant term.
    modified: bool,
}

/// Batch-convert projective points to affine (x, y) pairs.
fn batch_to_xy<C: DivisorCurve>(pts: &[Projective<C>]) -> Vec<(C::BaseField, C::BaseField)> {
    Projective::<C>::normalize_batch(pts)
        .into_iter()
        .map(|a| (a.x, a.y))
        .collect()
}

/// Sanitize a pair so the batched slope computation is "well-defined", and record its degeneracy.
/// "well-defined" means x-coordinates of both points are different
fn line_args<C: DivisorCurve>(
    a: Projective<C>,
    b: Projective<C>,
    dummy_point: &Projective<C>,
) -> LineArgs<C> {
    let a_is_identity = a.is_zero();
    let b_is_identity = b.is_zero();

    // TODO: Projective<C> does not implement subtle::ConditionallySelectable or ConstantTimeEq;
    // ideally these would be Choice values and we'd use conditional_select throughout.
    let both_are_identity = Choice::from(u8::from(a_is_identity && b_is_identity));
    let additive_inverses = a == -b;
    let one_is_identity_or_additive_inverses = Choice::from(u8::from(
        a_is_identity || b_is_identity || additive_inverses,
    ));

    let orig_b = b;
    // If identity set to dummy point, if additive inverses, b = 2*a (vertical line).
    // If a == b, b = -2*a. See `finish_line` for how the slope is used or discarded.
    let a = if a_is_identity { *dummy_point } else { a };
    let b = if b_is_identity { *dummy_point } else { b };
    let b = if additive_inverses { a.double() } else { b }; // // discarded in `finish_line`
    let b = if a == b { -a.double() } else { b };

    LineArgs {
        a,
        b,
        a_is_identity,
        b_is_identity,
        both_are_identity,
        one_is_identity_or_additive_inverses,
        modified: b != orig_b,
    }
}

/// Computes all (slope, intercept) pairs between points `a[i]` and `b[i]`.
fn slopes_and_intercepts<C: DivisorCurve>(
    a: Vec<Xy<C>>,
    b: Vec<Xy<C>>,
) -> Result<Vec<(C::BaseField, C::BaseField)>, Error> {
    debug_assert_eq!(a.len(), b.len());
    // Compute \prod{1/(b_i.x - a_i.x)}
    let mut inv_diffs = a
        .iter()
        .zip(b.iter())
        .map(|(a, b)| {
            let (ax, bx) = (a.0, b.0);
            bx - ax
        })
        .collect::<Vec<C::BaseField>>();
    if inv_diffs.iter().any(|d| d.is_zero()) {
        return Err(Error::InvertingZero);
    }
    batch_inversion(&mut inv_diffs);

    // Compute slope = (b_i.y - a_i.y)/(b_i.x - a_i.x) and intercept = b_i.y - (slope * b_i.x) for each
    Ok(a.into_iter()
        .zip(b)
        .zip(inv_diffs)
        .map(|((a, b), inv_diff)| {
            let (ax, ay) = a;
            let (bx, by) = b;

            let slope = (by - ay) * inv_diff;
            let intercept = by - (slope * bx);
            debug_assert!((ay - (slope * ax) - intercept).is_zero());
            debug_assert!((by - (slope * bx) - intercept).is_zero());
            (slope, intercept)
        })
        .collect())
}

/// Constructs a `SmallDivisor` representing the line `y - slope * x - intercept`,
/// handling special cases where points are at infinity or are additive inverses.
fn finish_line<F: PrimeField>(
    slope: F,
    intercept: F,
    both_are_identity: Choice,
    one_is_identity_or_additive_inverses: (Choice, F),
) -> SmallDivisor<F> {
    // Following logic is the constant time equivalent of:
    //   if both_are_identity return SmallDivisor::new(F::ZERO, F::ONE, F::ZERO)
    //   if one_is_identity_or_additive_inverses return SmallDivisor::new(F::ONE, -constant_term, F::ZERO)
    //   else the usual line

    // ordinary line: y - slope x - intercept
    let mut res = SmallDivisor::new(-slope, -intercept, F::ONE);
    let (one_is_identity_or_additive_inverses, constant_term) =
        one_is_identity_or_additive_inverses;
    // vertical line `x - c`, c = constant_term (the pair's finite x-coordinate): used when one point is
    // at infinity, or the two points are additive inverses
    res = <_>::conditional_select(
        &res,
        &SmallDivisor::new(F::ONE, -constant_term, F::ZERO),
        one_is_identity_or_additive_inverses,
    );
    // the constant 1 - both points at infinity
    <_>::conditional_select(
        &res,
        &SmallDivisor::new(F::ZERO, F::ONE, F::ZERO),
        both_are_identity,
    )
}

/// Computes all lines required to construct a divisor, batching expensive operations.
///
/// Returns `(leaf_lines, merge_nodes)`: the `ceil(n/2)` leaf lines (leaves are not divided, so they
/// carry no denominator) and the merge nodes as `(line, denom)`, where `denom = (x1, x2)` is divided out
/// as `(x - x1)(x - x2)` during that merge.
fn lines_and_denoms<C: DivisorCurve>(
    points: &[Projective<C>],
) -> Result<
    (
        Vec<SmallDivisor<C::BaseField>>,
        Vec<(SmallDivisor<C::BaseField>, Denom<C::BaseField>)>,
    ),
    Error,
> {
    let num_leaves = points.len().div_ceil(2);
    // All the pairs of points from which lines will be created.
    // Builds a binary tree where `pairs` will contain leaves, followed by nodes above that leaf level,
    // followed by nodes of next upper level and so on. If number of nodes at any level is odd, the last node
    // is processed at next (upper) level
    // Each leaf is a pair of points and each parent is the sum of its 2 children.
    let pairs = {
        let mut pairs = Vec::<[Projective<C>; 2]>::with_capacity(points.len());
        let mut divs = Vec::<Projective<C>>::with_capacity(points.len().div_ceil(2));

        // Take 2 consecutive points from `points` and add them to `pairs`. If length of `points` is odd,
        // its last point is paired with point at infinity. `divs` will contain the sums of each pair from `pairs`
        let mut iter = points.iter().copied();
        while let Some(a) = iter.next() {
            let b = iter.next();
            pairs.push([a, b.unwrap_or_else(Projective::<C>::zero)]);
            let div = match b {
                Some(b) => a + b,
                None => a,
            };
            divs.push(div);
        }

        // `divs` now corresponds to parent level of leaves

        // process `divs` until it contains just the root
        while divs.len() > 1 {
            let mut next_divs = Vec::with_capacity((divs.len() / 2) + 1);
            // If there's an odd number of divisors, carry the odd one out to the next iteration
            if (divs.len() % 2) == 1 {
                next_divs.push(divs.pop().unwrap());
            }

            while let Some(a) = divs.pop() {
                let b = divs.pop().unwrap();
                pairs.push([a, b]);
                next_divs.push(a + b);
            }
            divs = next_divs;
        }
        pairs
    };

    // `g` is a dummy point substituted for points at infinity and gets discarded later.
    let g: Projective<C> = C::GENERATOR.into();

    // Sanitize each pair into the points whose line we compute, plus degeneracy flags.
    let args: Vec<LineArgs<C>> = pairs
        .iter()
        .map(|[a, b]| line_args::<C>(*a, *b, &g))
        .collect();
    // `a_xy` and `b_xy` are the affine coordinates of the first and second point from `pairs` but
    // taking into account `args`
    let (a_xy, b_xy) = {
        // First half of `pts` is each pair's (final) first point, the second half its second point.
        let mut pts = vec![Projective::zero(); 2 * args.len()];
        for (i, la) in args.iter().enumerate() {
            pts[i] = la.a;
            pts[args.len() + i] = la.b;
        }
        let mut xy = batch_to_xy::<C>(&pts);
        let b_xy = xy.split_off(args.len());
        (xy, b_xy)
    };

    // The denominator and the vertical-line constant term need the original b's x-coordinate. Whenever
    // `line_args` changed `b`, the original `b` had same x-coord as `a`
    let denom_xs: Vec<(C::BaseField, C::BaseField)> = args
        .iter()
        .zip(&a_xy)
        .zip(&b_xy)
        .map(|((l, &(a_x, _)), &(b_x, _))| (a_x, if l.modified { a_x } else { b_x }))
        .collect();

    let slopes = slopes_and_intercepts::<C>(a_xy, b_xy)?;

    // Assemble each line; leaves drop the denominator, merge nodes keep it.
    let mut leaf_lines = Vec::with_capacity(num_leaves);
    let mut merges = Vec::with_capacity(args.len() - num_leaves);
    for (i, ((l, (a_x, orig_b_x)), (slope, intercept))) in
        args.iter().zip(denom_xs).zip(slopes).enumerate()
    {
        let constant_term = if l.a_is_identity { orig_b_x } else { a_x };
        let line = finish_line(
            slope,
            intercept,
            l.both_are_identity,
            (l.one_is_identity_or_additive_inverses, constant_term),
        );
        if i < num_leaves {
            leaf_lines.push(line);
        } else {
            // dividing by the divisor function is only done for non-leaf nodes
            let denom = (
                CtOption::new(a_x, !Choice::from(u8::from(l.a_is_identity))),
                CtOption::new(orig_b_x, !Choice::from(u8::from(l.b_is_identity))),
            );
            merges.push((line, denom));
        }
    }
    Ok((leaf_lines, merges))
}

/// Create a divisor interpolating the following points.
///
/// This is the **checked** version of [`new_divisor`] that validates:
///   - At least two points must be passed in
///   - The points must sum to the point at infinity
///   - No point may be the point at infinity
pub fn new_divisor_checked<C: DivisorCurve>(
    points: &[Projective<C>],
    interpolator: &Interpolator<C::BaseField>,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    // No points were passed in, this is the point at infinity, or the single point isn't infinity
    // and accordingly doesn't sum to infinity. All three cause us to return None
    // Checks a bit other than the first bit is set, meaning this is >= 2
    let mut invalid_args = (points.len() & (!1usize)).ct_eq(&0);

    // The points don't sum to the point at infinity
    let sum = points
        .iter()
        .copied()
        .reduce(|a, b| a + b)
        .unwrap_or_else(Projective::<C>::zero);
    // TODO: Projective<C> does not implement ConstantTimeEq; ideally this would be CT
    invalid_args |= Choice::from(u8::from(!sum.is_zero()));
    // A point was the point at identity
    for point in points {
        // TODO: Projective<C> does not implement ConstantTimeEq; ideally this would be CT
        invalid_args |= Choice::from(u8::from(point.is_zero()));
    }
    if invalid_args.into() {
        return Err(Error::InvalidArguments);
    }

    new_divisor(points, interpolator)
}

/// Create a divisor interpolating the following points.
///
/// # Safety invariants (caller must guarantee)
///
/// The following preconditions are **not** validated at runtime (only as `debug_assert!`s):
///   - At least two points must be passed in
///   - The points **must** sum to the point at infinity
///   - No point may be the point at infinity
///
/// Use [`new_divisor_checked`] when the caller cannot guarantee these invariants.
///
/// Returns an error if the interpolator is too small.
///
/// Output: DivisorPoly representing `D(x,y) = a(x) - b(x)*y` such that:
///   - `D(P_i) = 0` for each input point `P_i`
///   - D has poles only at the point at infinity
pub fn new_divisor<C: DivisorCurve>(
    points: &[Projective<C>],
    interpolator: &Interpolator<C::BaseField>,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    // Creates divisor incrementally by first creating line divisors for pairs of consecutive points
    // in `points`. Then "merge" each such divisor pair to form a divisor for those points in a
    // binary tree fashion. Thus each line divisor forms a leaf and corresponds to 2 points. Then line
    // divisor of 2 leaves are "merged" to form divisor which corresponds to 4 points and this process
    // is continued till we have a divisor of all points. The idea used to "merge" 2 divisors is
    // based on the fact that multiplying 2 divisors adds their zeroes and dividing them removes the
    // zeroes (zeroes are roots of the divisor polynomial). Also the divisor for vertical line `x − c`
    // has 2 zeroes, points P and -P both of which have x-coordinate `c`.
    //
    // Merge of subtree `A` with sum `S_A`, divisor `D_A` that vanishes at {A-leaves, −S_A}) and `B`
    // with sum `S_B`, divisor `D_B` that vanishes at {B-leaves, −S_B}):
    //
    // We want the merged divisor to vanish at `{A-leaves, B-leaves, −(S_A+S_B)}`
    //
    // 1. Product divisor `D_A · D_B` vanishes at `{A-leaves, −S_A, B-leaves, −S_B}`. Compared to the target,
    // this has two extra zeros (`−S_A`, `−S_B`) and is missing `−(S_A+S_B)`
    // 2. Multiplying by the line `l_{S_A, S_B}` through `S_A` and `S_B` adds the zeros `{S_A, S_B, −(S_A+S_B)}`,
    // supplying the missing `−(S_A+S_B)`, but also adding unwanted `S_A` and `S_B`. The zero set is
    // now `{A-leaves, B-leaves, −S_A, −S_B, S_A, S_B, −(S_A+S_B)}`.
    // 3. Dividing by `(x − S_{A,x})` removes a zero at `S_A` and at `−S_A` at once (both share the
    // x-coordinate `S_{A,x}`). Similarly, dividing by `(x − S_{B,x})` removes `S_B` and `−S_B`.
    // We now have the zero set as `{A-leaves, B-leaves, −(S_A+S_B)}`.

    let points_len = points.len();

    let required_evals = interpolator.required_evaluations();
    let curve_poly_evals = C::evaluation_of_curve_poly();
    let curve_poly_evals = curve_poly_evals.borrow();
    assert_eq!(curve_poly_evals.len() as u16, required_evals);

    // Each leaf is a line divisor over a pair of input points. Merge nodes carry the
    // denominators the merges below divide out. `merges` is for the non-leaves.
    let (leaf_lines, merges) = lines_and_denoms::<C>(points)?;
    let mut divs: Vec<DivisorEvals<C::BaseField>> = leaf_lines
        .into_iter()
        .map(|line| DivisorEvals::from_small(line, required_evals))
        .collect();

    // Our Poly algorithm is leaky and will create an excessive number of y x**j and x**j
    // coefficients which are zero, yet as our implementation is constant time, still come with
    // an immense performance cost. This code truncates the coefficients we know are zero.
    let trim = |divisor: &mut DivisorPoly<_>, points_len: usize| {
        let truncate_yx = points_len.div_ceil(2).saturating_sub(2);
        let truncate_x = points_len / 2;
        if cfg!(debug_assertions) {
            for p in truncate_yx..divisor.yx_coefficients.len() {
                let c: <C as CurveConfig>::BaseField = divisor.yx_coefficients[p];
                debug_assert!(c.is_zero());
            }
            for p in truncate_x..divisor.x_coefficients.len() {
                debug_assert!(divisor.x_coefficients[p].is_zero());
            }
        }
        divisor.yx_coefficients.truncate(truncate_yx);
        divisor.x_coefficients.truncate(truncate_x);
    };

    // Every merge's `(x−x1)(x−x2)` denominator is known up front — `x1`/`x2` are subtree sums computed
    // in `lines_and_denoms` before any Evals arithmetic. So invert them all in one go.
    let required_evals = required_evals as usize;
    let mut all_denoms = Vec::with_capacity(merges.len() * required_evals);
    for (_, (x1, x2)) in &merges {
        all_denoms.extend(DivisorEvals::removal_denominator_evals(
            *x1,
            *x2,
            required_evals as u16,
        ));
    }
    batch_inversion(&mut all_denoms);

    // Pair them off until only one remains
    let mut i = 0;
    while divs.len() > 1 {
        let mut next_divs = vec![];
        // If there's an odd number of divisors, carry the odd one out to the next iteration
        if (divs.len() % 2) == 1 {
            next_divs.push(divs.pop().unwrap());
        }
        while let Some(a_div) = divs.pop() {
            let b_div = divs.pop().unwrap();
            let line = merges[i].0;
            let mut merged = DivisorEvals::merge_numerator([a_div, b_div], line, curve_poly_evals);
            merged.apply_inverted_denominator(
                &all_denoms[i * required_evals..(i + 1) * required_evals],
            );
            next_divs.push(merged);
            i += 1;
        }
        divs = next_divs;
    }

    let divisor = divs.remove(0);
    let mut divisor = divisor.to_poly(interpolator)?;
    trim(&mut divisor, points_len);
    Ok(divisor)
}
