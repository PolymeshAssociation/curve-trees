#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

// This code is ported from [Monero's codebase](https://github.com/monero-oxide/monero-oxide/tree/fcmp%2B%2B/crypto/divisors)

use ark_std::{vec, vec::Vec};
use core::ops::Add;

use subtle::{Choice, ConstantTimeEq, CtOption};

use ark_ff::{PrimeField, Zero, batch_inversion};
use subtle::ConditionallySelectable;

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

pub use curves::{DivisorCurve, XyPoint};
pub use scalar_decomposition::ScalarDecomposition;

type Xy<C> = (
    <C as DivisorCurve>::BaseField,
    <C as DivisorCurve>::BaseField,
);
type Denom<C> = (
    CtOption<<C as DivisorCurve>::BaseField>,
    CtOption<<C as DivisorCurve>::BaseField>,
);

struct LineArgs<C: DivisorCurve> {
    /// The `b` to use when calculating the line.
    ///
    /// This will be distinct if the points would otherwise share an `x` coordinate.
    b: C::XyPoint,
    /// If both points were the identity point.
    both_are_identity: Choice,
    /// If one point was the identity, or the points were additive inverses, and the single `x`
    /// coordinate between the two if so.
    one_is_identity_or_additive_inverses: (Choice, C::BaseField),
}

/// Prepare points to calculate their lines.
fn line_args<C: DivisorCurve>(
    a: C::XyPoint,
    b: C::XyPoint,
    a_x: C::BaseField,
    b_x: C::BaseField,
    g: &C::XyPoint,
) -> LineArgs<C> {
    let a_is_identity = a.is_identity();
    let b_is_identity = b.is_identity();

    let both_are_identity = a_is_identity & b_is_identity;

    let one_is_identity = a_is_identity | b_is_identity;
    let additive_inverses = a.ct_eq(&-b);
    let one_is_identity_or_additive_inverses = one_is_identity | additive_inverses;
    // F does not implement ConditionallySelectable
    // let one_is_identity_or_additive_inverses = (
    //     one_is_identity_or_additive_inverses,
    //     <_>::conditional_select(&a_x, &b_x, a.is_identity()),
    // );
    let x_coordinate = if a_is_identity.into() { b_x } else { a_x };
    let one_is_identity_or_additive_inverses = (one_is_identity_or_additive_inverses, x_coordinate);

    let a = <_>::conditional_select(&a, g, a_is_identity);
    let b = <_>::conditional_select(&b, g, b_is_identity);
    let b = <_>::conditional_select(&b, &a.double(), additive_inverses);
    let b = <_>::conditional_select(&b, &-a.double(), a.ct_eq(&b));

    LineArgs {
        b,
        both_are_identity,
        one_is_identity_or_additive_inverses,
    }
}

/// Computes all (slope, intercept) pairs between points `a[i]` and `b[i]`.
fn slopes_and_intercepts<C: DivisorCurve>(
    a: Vec<Xy<C>>,
    b: &[C::XyPoint],
) -> Result<Vec<(C::BaseField, C::BaseField)>, Error> {
    debug_assert_eq!(a.len(), b.len());
    let b: Vec<Xy<C>> = C::XyPoint::batch_to_xy(b);
    // Compute \prod{1/(a_i.x - b_i.x)}
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

    Ok(a.into_iter()
        .zip(b)
        .zip(inv_diffs)
        .map(|((a, b), inv_diff)| {
            let (ax, ay) = a;
            let (bx, by) = b;

            let slope = (by - ay) * inv_diff;
            let intercept = by - (slope * bx);
            debug_assert!(bool::from((ay - (slope * ax) - intercept).is_zero()));
            debug_assert!(bool::from((by - (slope * bx) - intercept).is_zero()));
            (slope, intercept)
        })
        .collect())
}

/// Complete calculation of a line from its arguments and the (potentially stubbed)
/// slope/intercept.
///
/// Constructs a `SmallDivisor` representing the line `y - slope * x - intercept`,
/// handling special cases where points are at infinity or are additive inverses.
fn finish_line<F: PrimeField>(
    slope: F,
    intercept: F,
    both_are_identity: Choice,
    one_is_identity_or_additive_inverses: (Choice, F),
) -> SmallDivisor<F> {
    // y - slope x - intercept
    let mut res = SmallDivisor::new(-slope, -intercept, F::ONE);
    // `x - x`, where the first `x` is the coefficient and the second `x` is a constant of the `x`
    // coordinate present within this pair of points
    let (one_is_identity_or_additive_inverses, constant_term) =
        one_is_identity_or_additive_inverses;
    res = <_>::conditional_select(
        &res,
        &SmallDivisor::new(F::ONE, -constant_term, F::ZERO),
        one_is_identity_or_additive_inverses,
    );
    // 1
    <_>::conditional_select(
        &res,
        &SmallDivisor::new(F::ZERO, F::ONE, F::ZERO),
        both_are_identity,
    )
}

/// Computes all lines required to construct a divisor, batching expensive operations.
fn lines_and_denoms<C: DivisorCurve>(
    points: &[C::XyPoint],
) -> Result<Vec<(SmallDivisor<C::BaseField>, Denom<C>)>, Error> {
    // All the pairs of points from which lines will be created
    let pairs = {
        let mut pairs = Vec::<[C::XyPoint; 2]>::with_capacity(points.len());
        let mut divs = Vec::<C::XyPoint>::with_capacity(points.len().div_ceil(2));

        let mut iter = points.iter().copied();
        while let Some(a) = iter.next() {
            let b = iter.next();
            pairs.push([a, b.unwrap_or(C::XyPoint::IDENTITY)]);
            let div = match b {
                Some(b) => a + b,
                None => a,
            };
            divs.push(div);
        }

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

    let g = C::XyPoint::from(C::generator());
    let (a_xy, b_xy) = {
        let mut points = pairs
            .iter()
            .map(|[a, _]| {
                let is_identity = a.is_identity();
                // F does not implement ConditionallySelectable
                // <_>::conditional_select(a, &g, is_identity)
                if is_identity.into() { g } else { *a }
            })
            .collect::<Vec<_>>();
        let a = points.len();
        points.extend(pairs.iter().map(|[_, b]| {
            let is_identity = b.is_identity();
            // F does not implement ConditionallySelectable
            // <_>::conditional_select(b, &g, is_identity)
            if is_identity.into() { g } else { *b }
        }));
        let mut xy = C::XyPoint::batch_to_xy(&points);
        let b_xy = xy.split_off(a);
        let a_xy = xy;
        (a_xy, b_xy)
    };

    let (line_args_and_denom, b): (Vec<_>, Vec<_>) = pairs
        .into_iter()
        .zip(a_xy.iter().zip(b_xy))
        .map(|(pair, (a_xy, b_xy))| {
            let (a_x, _) = a_xy;
            let ax = CtOption::new(*a_x, !pair[0].is_identity());
            let (b_x, _) = b_xy;
            let bx = CtOption::new(b_x, !pair[1].is_identity());
            let denom = (ax, bx);
            let [a, b] = pair;
            let args = line_args::<C>(a, b, *a_x, b_x, &g);
            let LineArgs {
                b,
                both_are_identity,
                one_is_identity_or_additive_inverses,
            } = args;
            (
                (
                    (both_are_identity, one_is_identity_or_additive_inverses),
                    denom,
                ),
                b,
            )
        })
        .unzip();

    let slopes_and_intercepts = slopes_and_intercepts::<C>(a_xy, &b)?;

    Ok(line_args_and_denom
        .into_iter()
        .zip(slopes_and_intercepts)
        .map(
            |(
                ((both_are_identity, one_is_identity_or_additive_inverses), denom),
                (slope, intercept),
            )| {
                let line = finish_line(
                    slope,
                    intercept,
                    both_are_identity,
                    one_is_identity_or_additive_inverses,
                );
                (line, denom)
            },
        )
        .collect())
}

/// Convert divisor from univariate to bivariate representation.
fn divisor_to_poly<C: DivisorCurve>(
    divisor: &DivisorEvals<C::BaseField>,
    interpolator: &Interpolator<C::BaseField>,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    let [a, b] = divisor.interpolate(interpolator)?;
    let zero_coefficient = a[0];
    let x_coefficients = a[1..].to_vec();
    let yx_coefficients = vec![b[1..].to_vec()];
    let y_coefficients = vec![b[0]];
    Ok(DivisorPoly {
        zero_coefficient,
        x_coefficients,
        yx_coefficients,
        y_coefficients,
    })
}

/// Create a divisor interpolating the following points.
///
/// Returns an error if:
///   - No points were passed in
///   - The points don't sum to the point at infinity
///   - A passed in point was the point at infinity
///   - If too small of an interpolator was passed in
///
/// If the arguments were valid, this function executes in an amount of time constant to the amount
/// of points.
#[allow(clippy::new_ret_no_self)]
pub fn new_divisor<C: DivisorCurve>(
    points: &[C::XyPoint],
    interpolator: &Interpolator<C::BaseField>,
) -> Result<DivisorPoly<C::BaseField>, Error> {
    // No points were passed in, this is the point at infinity, or the single point isn't infinity
    // and accordingly doesn't sum to infinity. All three cause us to return None
    // Checks a bit other than the first bit is set, meaning this is >= 2
    let mut invalid_args = (points.len() & (!1)).ct_eq(&0);

    // The points don't sum to the point at infinity
    let sum = points
        .iter()
        .copied()
        .reduce(C::XyPoint::add)
        .unwrap_or(C::XyPoint::IDENTITY);
    invalid_args |= !sum.is_identity();
    // A point was the point at identity
    for point in points {
        invalid_args |= point.is_identity();
    }
    if invalid_args.into() {
        return Err(Error::InvalidArguments);
    }

    let points_len = points.len();

    let modulus =
        DivisorEvals::compute_modulus(C::a(), C::b(), interpolator.required_evaluations());
    // Create the initial set of divisors
    let mut divs = vec![];
    let mut all_lines = lines_and_denoms::<C>(points)?.into_iter();
    for _ in 0..((points_len / 2) + (points_len % 2)) {
        let (line, _) = all_lines.next().unwrap();
        divs.push(DivisorEvals::<C::BaseField>::from_small(line, &modulus));
    }

    // Our Poly algorithm is leaky and will create an excessive number of y x**j and x**j
    // coefficients which are zero, yet as our implementation is constant time, still come with
    // an immense performance cost. This code truncates the coefficients we know are zero.
    let trim = |divisor: &mut DivisorPoly<_>, points_len: usize| {
        // We should only be trimming divisors reduced by the modulus
        debug_assert!(divisor.yx_coefficients.len() <= 1);
        if divisor.yx_coefficients.len() == 1 {
            let truncate_to = points_len.div_ceil(2).saturating_sub(2);
            for p in truncate_to..divisor.yx_coefficients[0].len() {
                let c: <C as DivisorCurve>::BaseField = divisor.yx_coefficients[0][p];
                debug_assert!(c.is_zero());
            }
            divisor.yx_coefficients[0].truncate(truncate_to);
        }
        {
            let truncate_to = points_len / 2;
            for p in truncate_to..divisor.x_coefficients.len() {
                debug_assert!(divisor.x_coefficients[p].is_zero());
            }
            divisor.x_coefficients.truncate(truncate_to);
        }
    };

    // Pair them off until only one remains
    while divs.len() > 1 {
        let mut next_divs = vec![];
        // If there's an odd number of divisors, carry the odd one out to the next iteration
        if (divs.len() % 2) == 1 {
            next_divs.push(divs.pop().unwrap());
        }

        while let Some(a_div) = divs.pop() {
            let b_div = divs.pop().unwrap();

            // Merge the two divisors
            let (line, denom) = all_lines.next().unwrap();
            let merged = DivisorEvals::merge([a_div, b_div], line, denom, &modulus);
            next_divs.push(merged);
        }

        divs = next_divs;
    }

    // Return the unified divisor
    let divisor = divs.remove(0);
    let mut divisor = divisor_to_poly::<C>(&divisor, interpolator)?;
    trim(&mut divisor, points_len);
    Ok(divisor)
}
