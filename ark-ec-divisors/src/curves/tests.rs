use core::borrow::Borrow;
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use ark_std::UniformRand;
use rand_core::{CryptoRngCore, SeedableRng};
use rand::rngs::StdRng;
use crate::{new_divisor, DivisorCurve, DivisorPoly, ScalarDecomposition};
use std::time::Instant;
use crate::util::DirectGenerator;

// Helper function to convert points to XyPoint format
fn points_xy<C: DivisorCurve>(points: &[C]) -> Vec<C::XyPoint> {
    points.iter().copied().map(C::XyPoint::from).collect()
}

/// y^2 - x^3 - A x - B
///
/// Section 2 of Eagen's security proofs define this modulus.
fn divisor_modulus<C: DivisorCurve>() -> DivisorPoly<C::BaseField> {
    DivisorPoly {
        // 0 y**1, 1 y*2
        y_coefficients: vec![C::BaseField::zero(), C::BaseField::ONE],
        yx_coefficients: vec![],
        x_coefficients: vec![
            // - A x
            -C::a(),
            // 0 x^2
            C::BaseField::zero(),
            // - x^3
            -C::BaseField::ONE,
        ],
        // - B
        zero_coefficient: -C::b(),
    }
}

/// Calculate the slope and intercept between two points.
///
/// This function panics when `a @ infinity`, `b @ infinity`, `a == b`, or when `a == -b`.
pub(crate) fn slope_intercept<C: DivisorCurve>(a: C, b: C) -> (C::BaseField, C::BaseField) {
    // slope = (by - ay) / (bx - ax)
    let (ax, ay) = C::to_xy(a).unwrap();
    debug_assert_eq!(divisor_modulus::<C>().eval(ax, ay), C::BaseField::zero());
    let (bx, by) = C::to_xy(b).unwrap();
    debug_assert_eq!(divisor_modulus::<C>().eval(bx, by), C::BaseField::zero());
    let slope = (by - ay) *
        Option::<C::BaseField>::from((bx - ax).inverse())
            .unwrap();

    // y = slope.x + intercept => intercept = y - slope.x
    let intercept = by - (slope * bx);

    // intercept calculated from a's coords is same
    debug_assert!((ay - (slope * ax) - intercept).is_zero());
    (slope, intercept)
}

// Equation 4 in the security proofs
fn check_divisor<C: DivisorCurve, R: CryptoRngCore>(rng: &mut R, points: Vec<C>) {
    let precomputation = C::interpolator_for_scalar_mul();

    let points_xy = points_xy(&points);

    // Create the divisor
    let divisor = new_divisor::<C>(&points_xy, precomputation.borrow()).unwrap();
    let eval = |c| {
        let (x, y) = C::to_xy(c).unwrap();
        divisor.eval(x, y)
    };

    // Decide challenges
    let c0 = C::random(rng);
    let mut c1 = C::random(rng); // Different point
    while c1 == c0 {
        c1 = C::random(rng);
    }
    let c2 = C::neg(C::add(c0, c1));
    let (slope, intercept) = slope_intercept::<C>(c0, c1);

    let mut rhs = <C as DivisorCurve>::BaseField::ONE;
    for point in points {
        let (x, y) = C::to_xy(point).unwrap();
        rhs *= intercept - (y - (slope * x));
    }
    assert_eq!(eval(c0) * eval(c1) * eval(c2), rhs);
}

fn test_divisor<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let precomputation = C::interpolator_for_scalar_mul();
    let num_bits = u64::from(C::ScalarField::MODULUS_BIT_SIZE);
    
    let mut new_divisor_times = Vec::new();
    let mut check_divisor_times = Vec::new();
    let mut total_times = Vec::new();

    for i in 1..=(num_bits as usize + 1) {
        let start_total = Instant::now();
        
        // Select points
        let mut points = vec![];
        for _ in 0..i {
            points.push(C::random(&mut rng));
        }
        // Make sure points sum to identity
        let sum = points.iter().copied().reduce(C::add).unwrap();
        points.push(C::neg(sum));

        let start_new_divisor = Instant::now();
        let points_xy = points_xy(&points);
        // Create the divisor
        let divisor = new_divisor::<C>(&points_xy, precomputation.borrow()).unwrap();
        new_divisor_times.push(start_new_divisor.elapsed());

        // Perform the original check
        let start_check = Instant::now();
        check_divisor(&mut rng, points.clone());
        check_divisor_times.push(start_check.elapsed());
        
        total_times.push(start_total.elapsed());

        // For a divisor interpolating 256 points, as one does when interpreting a 255-bit discrete log
        // with the result of its scalar multiplication against a fixed generator, the lengths of the
        // yx/x coefficients shouldn't supersede the following bounds
        assert!(C::ScalarField::MODULUS_BIT_SIZE < 256);
        let yx_len = divisor.yx_coefficients.first().unwrap_or(&vec![]).len();
        let x_len = divisor.x_coefficients.len().saturating_sub(1);
        // TODO: Uncomment.
        // assert!(yx_len <= 126, "yx-len={yx_len}");
        assert!(x_len <= 127, "x-len={x_len}");
        // TODO: Uncomment.
        // assert!(
        //     (1 + yx_len +
        //         x_len +
        //         1) <= 255
        // );

        // Decide challenges
        let c0 = C::random(&mut rng);
        let mut c1 = C::random(&mut rng); // Different point
        while c1 == c0 {
            c1 = C::random(&mut rng);
        }
        // c2 = -(c0 + c1)
        let c2 = C::neg(C::add(c0, c1));
        let (slope, intercept) = slope_intercept::<C>(c0, c1);

        // Logarithmic derivative check
        {
            let dx_over_dz = {
                let dx = DivisorPoly {
                    y_coefficients: vec![],
                    yx_coefficients: vec![],
                    x_coefficients: vec![C::BaseField::zero(), C::BaseField::from(3u64)],
                    zero_coefficient: C::a(),
                };

                let dy = DivisorPoly {
                    y_coefficients: vec![C::BaseField::from(2u64)],
                    yx_coefficients: vec![],
                    x_coefficients: vec![],
                    zero_coefficient: C::BaseField::zero(),
                };

                let dz = (dy.clone() * -slope) + &dx;

                // We want dx/dz, and dz/dx is equal to dy/dx - slope
                // Sagemath claims this, dy / dz, is the proper inverse
                (dy, dz)
            };

            {
                let sanity_eval = |c| {
                    let (x, y) = C::to_xy(c).unwrap();
                    dx_over_dz.0.eval(x, y) * dx_over_dz.1.eval(x, y).inverse().unwrap()
                };
                let sanity = sanity_eval(c0) + sanity_eval(c1) + sanity_eval(c2);
                // This verifies the dx/dz polynomial is correct
                assert_eq!(sanity, C::BaseField::zero());
            }

            // Logarithmic derivative check
            let test = |divisor: DivisorPoly<_>| {
                let (dx, dy) = divisor.differentiate();

                let lhs = |c| {
                    let (x, y) = C::to_xy(c).unwrap();

                    let n_0 = (C::BaseField::from(3u64) * (x * x)) + C::a();
                    let d_0 = (C::BaseField::from(2u64) * y).inverse().unwrap();
                    let p_0_n_0 = n_0 * d_0;

                    let n_1 = dy.eval(x, y);
                    let first = p_0_n_0 * n_1;

                    let second = dx.eval(x, y);

                    let d_1 = divisor.eval(x, y);

                    let fraction_1_n = first + second;
                    let fraction_1_d = d_1;

                    let fraction_2_n = dx_over_dz.0.eval(x, y);
                    let fraction_2_d = dx_over_dz.1.eval(x, y);

                    fraction_1_n * fraction_2_n * (fraction_1_d * fraction_2_d).inverse().unwrap()
                };
                let lhs = lhs(c0) + lhs(c1) + lhs(c2);

                let mut rhs = C::BaseField::zero();
                for point in &points {
                    let (x, y) = <C as DivisorCurve>::to_xy(*point).unwrap();
                    rhs += (intercept - (y - (slope * x))).inverse().unwrap();
                }

                assert_eq!(lhs, rhs);
            };
            // Test the divisor
            test(divisor.clone());
        }
    }
    
    // Calculate medians
    new_divisor_times.sort();
    check_divisor_times.sort();
    total_times.sort();
    
    let new_divisor_median = new_divisor_times[new_divisor_times.len() / 2];
    let check_divisor_median = check_divisor_times[check_divisor_times.len() / 2];
    let total_median = total_times[total_times.len() / 2];

    println!("test_divisor: new_divisor median {:?} ({} iterations), check_divisor median {:?} ({} iterations), total median {:?} ({} iterations)",
             new_divisor_median, new_divisor_times.len(), check_divisor_median, check_divisor_times.len(), total_median, total_times.len());
}

fn test_same_point<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let mut points = vec![C::random(&mut rng)];
    points.push(points[0]);
    let sum = points.iter().copied().reduce(C::add).unwrap_or(C::generator());
    points.push(C::neg(sum));
    check_divisor(&mut rng, points);
}

fn test_subset_sum_to_infinity<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let mut check_divisor_times = Vec::new();
    
    // Internally, a binary tree algorithm is used
    // This executes the first pass to end up with [0, 0] for further reductions
    {
        let mut points = vec![C::random(&mut rng)];
        points.push(C::neg(points[0]));

        let next = C::random(&mut rng);
        points.push(next);
        points.push(C::neg(next));
        
        let start = Instant::now();
        check_divisor(&mut rng, points);
        check_divisor_times.push(start.elapsed());
    }

    // This executes the first pass to end up with [0, X, -X, 0]
    {
        let mut points = vec![C::random(&mut rng)];
        points.push(C::neg(points[0]));

        let x_1 = C::random(&mut rng);
        let x_2 = C::random(&mut rng);
        points.push(x_1);
        points.push(x_2);

        points.push(C::neg(x_1));
        points.push(C::neg(x_2));

        let next = C::random(&mut rng);
        points.push(next);
        points.push(C::neg(next));
        
        let start = Instant::now();
        check_divisor(&mut rng, points);
        check_divisor_times.push(start.elapsed());
    }
    
    // Calculate median
    check_divisor_times.sort();
    let median = check_divisor_times[check_divisor_times.len() / 2];

    println!("test_subset_sum_to_infinity: median time {:?} ({} iterations)", median, check_divisor_times.len());
}

fn decomposition_correctness<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let count = 100;
    
    let mut decomposition_times = Vec::new();
    
    // Test random scalars and specific edge cases like ONE
    let mut scalars = Vec::new();
    for _ in 0..count {
        scalars.push(C::ScalarField::rand(&mut rng));
    }
    // Add ONE (the multiplicative identity)
    scalars.push(C::ScalarField::ONE);

    assert!(ScalarDecomposition::<C::ScalarField>::new(C::ScalarField::ZERO).is_err());

    for scalar in scalars {
        if scalar == C::ScalarField::ZERO {
            continue;
        }

        let start = Instant::now();
        let decomposition = ScalarDecomposition::<C::ScalarField>::new(scalar).unwrap();
        decomposition_times.push(start.elapsed());

        // 1. Verify sum of coefficients is NUM_BITS
        let sum: u64 = decomposition.decomposition().iter().sum();
        assert_eq!(sum, u64::from(C::ScalarField::MODULUS_BIT_SIZE));

        // 2. Verify reconstruction
        let mut reconstructed = C::ScalarField::ZERO;
        let mut base = C::ScalarField::ONE;
        for &coeff in decomposition.decomposition() {
            reconstructed += base * C::ScalarField::from(coeff);
            base = base.double();
        }
        assert_eq!(reconstructed, scalar);
    }
    
    // Calculate median
    decomposition_times.sort();
    let median = decomposition_times[decomposition_times.len() / 2];
    
    println!("decomposition_correctness: ScalarDecomposition::new median time {:?} ({} iterations)", median, decomposition_times.len());
}

fn scalar_mul_divisor_correctness<C: DivisorCurve>() {
    let mut rng = StdRng::seed_from_u64(0);
    let count = 20;

    let mut decomposition_times = Vec::new();
    let mut scalar_mul_times = Vec::new();

    for _ in 0..count {
        let scalar = C::ScalarField::rand(&mut rng);
        if scalar == C::ScalarField::ZERO {
            return;
        }

        let decomposition_start = Instant::now();
        let decomposition = ScalarDecomposition::<C::ScalarField>::new(scalar).unwrap();
        decomposition_times.push(decomposition_start.elapsed());
        
        let generator = C::random(&mut rng);

        let mul_start = Instant::now();
        let poly = decomposition.scalar_mul_divisor(DirectGenerator::from(generator)).unwrap();
        scalar_mul_times.push(mul_start.elapsed());

        // 1. Verify it vanishes at -(s * G)
        let neg_s_g = C::neg(C::mul(generator, scalar));
        let (x, y) = C::to_xy(neg_s_g).unwrap();
        assert!(poly.eval(x, y).is_zero());

        // 2. Verify it vanishes at 2^i * G for each coefficient count
        let mut p = generator;
        for &coeff in decomposition.decomposition() {
            if coeff > 0 {
                let (x, y) = C::to_xy(p).unwrap();
                assert!(poly.eval(x, y).is_zero());
            }
            p = C::add(p, p);
        }
    }
    
    // Calculate medians
    decomposition_times.sort();
    scalar_mul_times.sort();
    
    let decomposition_median = decomposition_times[decomposition_times.len() / 2];
    let scalar_mul_median = scalar_mul_times[scalar_mul_times.len() / 2];

    println!("scalar_mul_divisor_correctness: ScalarDecomposition::new median {:?} ({} iterations), scalar_mul_divisor median {:?} ({} iterations)",
             decomposition_median, decomposition_times.len(), scalar_mul_median, scalar_mul_times.len());
}

#[cfg(feature = "ed25519")]
#[test]
fn test_divisor_ed25519() {
    use ark_ed25519::EdwardsProjective;
    use ark_std::UniformRand;
    use rand_core::OsRng;

    // Since we're implementing Wei25519 ourselves, check the isomorphism works as expected
    {
        let incomplete_add = |p1: EdwardsProjective, p2: EdwardsProjective| {
            let (x1, y1) = EdwardsProjective::to_xy(p1).unwrap();
            let (x2, y2) = EdwardsProjective::to_xy(p2).unwrap();

            // mmadd-1998-cmo
            let u = y2 - y1;
            let uu = u * u;
            let v = x2 - x1;
            let vv = v * v;
            let vvv = v * vv;
            let R = vv * x1;
            let A = uu - vvv - R.double();
            let x3 = v * A;
            let y3 = (u * (R - A)) - (vvv * y1);
            let z3 = vvv;

            // Normalize from XYZ to XY
            let z3_inv = z3.inverse().unwrap();
            let x3 = x3 * z3_inv;
            let y3 = y3 * z3_inv;

            // Edwards addition -> Wei25519 coordinates should be equivalent to Wei25519 addition
            assert_eq!(EdwardsProjective::to_xy(p1 + p2).unwrap(), (x3, y3));
        };

        for _ in 0..256 {
            incomplete_add(
                EdwardsProjective::rand(&mut OsRng),
                EdwardsProjective::rand(&mut OsRng),
            );
        }
    }

    test_same_point::<EdwardsProjective>();
    test_subset_sum_to_infinity::<EdwardsProjective>();
    test_divisor::<EdwardsProjective>();
}

#[cfg(feature = "pallas")]
#[test]
fn test_divisor_pallas() {
    use crate::curves::pallas::Point;

    test_same_point::<Point>();
    test_subset_sum_to_infinity::<Point>();
    test_divisor::<Point>();
    decomposition_correctness::<Point>();
    scalar_mul_divisor_correctness::<Point>();
}

#[cfg(feature = "vesta")]
#[test]
fn test_divisor_vesta() {
    use crate::curves::vesta::Point;

    test_same_point::<Point>();
    test_subset_sum_to_infinity::<Point>();
    test_divisor::<Point>();
    decomposition_correctness::<Point>();
    scalar_mul_divisor_correctness::<Point>();
}
