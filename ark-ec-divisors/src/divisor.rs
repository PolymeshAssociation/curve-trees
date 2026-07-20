use crate::barycentric::Interpolator;
use crate::error::Error;
use crate::DivisorPoly;
use ark_ff::{batch_inversion, PrimeField};
use ark_std::{vec, vec::Vec};
use core::ops::Div;
use subtle::{Choice, ConditionallySelectable, CtOption};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Evaluations of a polynomial at consecutive points.
///
/// This represents a polynomial by storing its evaluations at points 0, 1, 2, ..., n-1
/// rather than storing coefficients. This enables efficient pointwise operations.
#[derive(Debug, Clone, Zeroize, ZeroizeOnDrop)]
pub struct Evals<F: PrimeField> {
    pub(crate) evals: Vec<F>,
    #[zeroize(skip)]
    degree: u16,
}

impl<F: PrimeField> Evals<F> {
    fn new(evals: Vec<F>, degree: u16) -> Self {
        Self { evals, degree }
    }

    /// Compute evaluations of the curve modulus polynomial `x^3 + ax + b`.
    ///
    /// This computes the evaluations of the curve equation at `x = 0, 1, 2, ..., n-1`.
    pub(super) fn compute_modulus(a: F, b: F, amount_of_evals: u16) -> Evals<F> {
        let mut evals = Vec::with_capacity(amount_of_evals as usize);
        for i in 0..amount_of_evals {
            let x = F::from(u64::from(i));
            let x_cube = x.square() * x;
            let ax = x * a;
            evals.push(x_cube + ax + b);
        }
        Self::new(evals, 3)
    }

    pub(crate) fn len(&self) -> usize {
        self.evals.len()
    }

    pub(crate) fn as_slice(&self) -> &[F] {
        &self.evals
    }
}

/// A small divisor representing a line through two points.
/// This represents a divisor of the form `a * y - slope * x - intercept`, a line through two points on
/// the curve. `a` is only ever 1 (an ordinary, non-vertical line) or 0 (a vertical line `x - c`, or
/// the constant 1 for the both-at-infinity case)
#[derive(Debug, Clone, Copy)]
pub(super) struct SmallDivisor<F: PrimeField> {
    /// slope
    x_coefficient: F,
    /// intercept
    zero_coefficient: F,
    /// a: 1 or 0
    y_coefficient: F,
}

impl<F: PrimeField> SmallDivisor<F> {
    pub(super) fn new(x_coefficient: F, zero_coefficient: F, y_coefficient: F) -> Self {
        Self {
            x_coefficient,
            zero_coefficient,
            y_coefficient,
        }
    }

    /// `(x_coefficient, zero_coefficient, y_coefficient)` = (slope, intercept, a).
    /// `pub(crate)` accessor so the experimental `narrow` module can build a leaf from a
    /// line. Remove with the prototype.
    pub(crate) fn coeffs(&self) -> (F, F, F) {
        (
            self.x_coefficient,
            self.zero_coefficient,
            self.y_coefficient,
        )
    }
}

/// A divisor function `f(x, y) = A(x) + yB(x)`.
///
/// `A` and `B` are represented as a sufficient number of evaluations from them to perform
/// interpolation and recover them.
#[derive(Debug, Clone, Zeroize, ZeroizeOnDrop)]
pub(super) struct DivisorEvals<F: PrimeField> {
    a: Evals<F>,
    b: Evals<F>,
}

impl<F: PrimeField> Div<Evals<F>> for DivisorEvals<F> {
    type Output = Self;

    fn div(mut self, mut rhs: Evals<F>) -> Self::Output {
        debug_assert_eq!(self.a.len(), self.b.len());
        debug_assert_eq!(self.a.len(), rhs.len());

        batch_inversion(&mut rhs.evals);
        for ((a, b), denom) in self
            .a
            .evals
            .iter_mut()
            .zip(self.b.evals.iter_mut())
            .zip(rhs.evals.iter())
        {
            *a *= denom;
            *b *= denom;
        }
        self.a.degree -= rhs.degree;
        self.b.degree -= rhs.degree;
        self
    }
}

impl<F: PrimeField> DivisorEvals<F> {
    /// Create divisor `A(x) - yB(x)` in the evaluation form given a line divisor
    pub(super) fn from_small(small: SmallDivisor<F>, num_evals: u16) -> Self {
        let SmallDivisor {
            mut x_coefficient,
            mut zero_coefficient,
            mut y_coefficient,
        } = small;

        // Divisor of a line f = ax - by + c where a = x_coefficient, b = y_coefficient and c = zero_coefficient
        // Since divisor is always in form A(x) - yB(x), A(x) = ax + c = x_coefficient*x + c and B(x) = b

        // Evals of A(x). Since evaluation domain (fixed in the protocol) is 0,1,2 ..num_evals-1,
        // evals are c, a+c, 2a+c, ...
        let mut a_evals = Vec::with_capacity(num_evals as usize);
        let mut last = zero_coefficient;
        for _ in 0..num_evals {
            a_evals.push(last);
            last += x_coefficient;
        }
        let a = Evals::new(a_evals, 1);

        // Evals of B(x). B(x) is constant polynomial
        let b = Evals::new(vec![y_coefficient; num_evals as usize], 0);

        x_coefficient.zeroize();
        zero_coefficient.zeroize();
        y_coefficient.zeroize();
        Self { a, b }
    }

    /// The degrees of the A, B polynomials after the multiplication of these divisors.
    fn degree_after_multiplication(&self, other_a_degree: u16, other_b_degree: u16) -> (u16, u16) {
        let (a1, b1) = (self.a.degree, self.b.degree);
        let (a2, b2) = (other_a_degree, other_b_degree);
        deg_after_mul((a1, b1), (a2, b2))
    }

    /// Multiply two divisors modulo the curve equation.
    fn mul_mod(mut self, rhs: &Self, modulus: &Evals<F>) -> Self {
        debug_assert_eq!(self.a.len(), rhs.a.len());
        debug_assert_eq!(self.b.len(), rhs.b.len());
        debug_assert_eq!(self.a.len(), self.b.len());

        let degree_after_multiplication =
            self.degree_after_multiplication(rhs.a.degree, rhs.b.degree);

        mul_mod_slices(
            &mut self.a.evals,
            &mut self.b.evals,
            &rhs.a.evals,
            &rhs.b.evals,
            &modulus.evals,
        );

        self.a.degree = degree_after_multiplication.0;
        self.b.degree = degree_after_multiplication.1;
        self
    }

    /// Multiply any divisor and a line divisor modulo the curve equation.
    fn mul_mod_small(mut self, rhs: SmallDivisor<F>, modulus: &Evals<F>) -> Self {
        debug_assert_eq!(self.a.len(), self.b.len());

        let degree_after_multiplication = self.degree_after_multiplication(1, 0);

        mul_mod_small_slices(
            &mut self.a.evals,
            &mut self.b.evals,
            &modulus.evals,
            rhs.x_coefficient,
            rhs.zero_coefficient,
            rhs.y_coefficient,
        );

        self.a.degree = degree_after_multiplication.0;
        self.b.degree = degree_after_multiplication.1;
        self
    }

    /// Remove 2 points by dividing by `(x - x1) * (x - x2)`.
    ///
    /// This divides the divisor by the product `(x - x1)(x - x2)`, effectively
    /// removing zeros at x-coordinates x1 and x2. This is used when merging divisors
    /// to remove unwanted zeros at intermediate sum points.
    #[allow(dead_code)]
    fn remove_diff(self, x1: CtOption<F>, x2: CtOption<F>) -> Self {
        debug_assert_eq!(self.a.len(), self.b.len());

        let denominator = Self::removal_denominator_evals(x1, x2, self.a.len() as u16);
        let denominator = Evals {
            evals: denominator,
            degree: 2,
        };
        self / denominator
    }

    /// Convert divisor from univariate to bivariate representation.
    pub fn to_poly(&self, interpolator: &Interpolator<F>) -> Result<DivisorPoly<F>, Error> {
        let [a, b] = self.interpolate(interpolator)?;
        // The interpolated polynomial is in the form A(x) + yB(x) where `a` are the coefficients
        // of A(x) and `b` are the coefficients of B(x).
        // Thus the interpolated polynomial is (a[0] + a[1]*x + a[2]*x^2 + ..) + y(b[0] + b[1]*x + b[2]*x^2 + ..)
        // Thus constant = a[0], y coefficient = b[0], x coefficients = a[1..], yx coefficients = b[1..]
        let zero_coefficient = a[0];
        let x_coefficients = a[1..].to_vec();
        let yx_coefficients = b[1..].to_vec();
        let y_coefficient = b[0];
        Ok(DivisorPoly {
            zero_coefficient,
            x_coefficients,
            yx_coefficients,
            y_coefficient,
        })
    }

    #[allow(dead_code)]
    pub(super) fn merge(
        divisors: [Self; 2],
        small: SmallDivisor<F>,
        denom: (CtOption<F>, CtOption<F>),
        modulus: &Evals<F>,
    ) -> Self {
        let [d0, d1] = divisors;
        let numerator = d0.mul_mod(&d1, modulus).mul_mod_small(small, modulus);
        let (x1, x2) = denom;
        numerator.remove_diff(x1, x2)
    }

    /// Numerator of a merge: `D_A · D_B · line` mod the curve poly, no division.
    pub(super) fn merge_numerator(
        divisors: [Self; 2],
        small: SmallDivisor<F>,
        modulus: &Evals<F>,
    ) -> Self {
        let [d0, d1] = divisors;
        d0.mul_mod(&d1, modulus).mul_mod_small(small, modulus)
    }

    /// Divide each eval by a pre-inverted degree-2 denominator slice.
    pub(super) fn apply_inverted_denominator(&mut self, inv_denom: &[F]) {
        debug_assert_eq!(self.a.len(), inv_denom.len());
        for ((a, b), d) in self
            .a
            .evals
            .iter_mut()
            .zip(self.b.evals.iter_mut())
            .zip(inv_denom.iter())
        {
            *a *= d;
            *b *= d;
        }
        self.a.degree -= 2;
        self.b.degree -= 2;
    }

    /// Per-level batched merge (one inversion per round).
    #[allow(dead_code)]
    pub(super) fn merge_round(
        pairs: Vec<([Self; 2], SmallDivisor<F>, (CtOption<F>, CtOption<F>))>,
        modulus: &Evals<F>,
    ) -> Vec<Self> {
        let len = modulus.len();
        let mut numerators = Vec::with_capacity(pairs.len());
        let mut denominators = Vec::with_capacity(pairs.len() * len);
        for ([d0, d1], small, (x1, x2)) in pairs {
            let numerator = d0.mul_mod(&d1, modulus).mul_mod_small(small, modulus);
            denominators.extend(Self::removal_denominator_evals(x1, x2, len as u16));
            numerators.push(numerator);
        }

        batch_inversion(&mut denominators);

        for (i, numerator) in numerators.iter_mut().enumerate() {
            let denom = &denominators[i * len..(i + 1) * len];
            for ((a, b), d) in numerator
                .a
                .evals
                .iter_mut()
                .zip(numerator.b.evals.iter_mut())
                .zip(denom.iter())
            {
                *a *= d;
                *b *= d;
            }
            numerator.a.degree -= 2;
            numerator.b.degree -= 2;
        }
        numerators
    }

    pub(super) fn interpolate(&self, interpolator: &Interpolator<F>) -> Result<[Vec<F>; 2], Error> {
        let max_degree = self.a.degree.max(self.b.degree);
        if max_degree > interpolator.degree() {
            return Err(Error::DegreeExceedsInterpolator(
                max_degree,
                interpolator.degree(),
            ));
        }
        let a = interpolator.interpolate(&self.a.evals)?;
        let b = interpolator.interpolate(&self.b.evals)?;
        Ok([a, b])
    }

    /// Evals of `(x - x1)(x - x2)`. A `None` (infinity) contributes a constant 1.
    pub(crate) fn removal_denominator_evals(
        x1: CtOption<F>,
        x2: CtOption<F>,
        num_evals: u16,
    ) -> Vec<F> {
        // [(-x1).(-x2), (1-x1).(1-x2), (2-x1).(2-x2), ..]
        let mut denominator = Vec::with_capacity(num_evals as usize);
        let (mut x_l, mut x_r) = (F::zero(), F::zero());

        let inc_l = F::from(u64::from(x1.is_some().unwrap_u8()));
        let inc_r = F::from(u64::from(x2.is_some().unwrap_u8()));

        let neg1 = -F::ONE;

        // F does not implement ConditionallySelectable
        // let (x1, x2) = (x1.unwrap_or(neg1), x2.unwrap_or(neg1));
        let x1 = if x1.is_some().into() {
            x1.unwrap()
        } else {
            neg1
        };
        let x2 = if x2.is_some().into() {
            x2.unwrap()
        } else {
            neg1
        };

        for _ in 0..num_evals {
            denominator.push((x_l - x1) * (x_r - x2));
            x_l += inc_l;
            x_r += inc_r;
        }
        denominator
    }
}

impl<F> ConditionallySelectable for SmallDivisor<F>
where
    // F: PrimeField + ConditionallySelectable,
    F: PrimeField,
{
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        // F does not implement ConditionallySelectable
        // let x_coefficient = <_>::conditional_select(&a.x_coefficient, &b.x_coefficient, choice);
        // let zero_coefficient =
        //     <_>::conditional_select(&a.zero_coefficient, &b.zero_coefficient, choice);
        // let y_coefficient = <_>::conditional_select(&a.y_coefficient, &b.y_coefficient, choice);
        let c = bool::from(choice);
        let x_coefficient = if !c { a.x_coefficient } else { b.x_coefficient };
        let zero_coefficient = if !c {
            a.zero_coefficient
        } else {
            b.zero_coefficient
        };
        let y_coefficient = if !c { a.y_coefficient } else { b.y_coefficient };
        SmallDivisor {
            x_coefficient,
            zero_coefficient,
            y_coefficient,
        }
    }
}

/// (A, B) degrees of `f1 * f2` reduced mod `y^2 = x^3 + a x + b`.
pub(crate) fn deg_after_mul((a1, b1): (u16, u16), (a2, b2): (u16, u16)) -> (u16, u16) {
    // f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
    // A = A1A2 + (x^3 + ax + b) B1B2
    // B = A1B2 + A2B1
    // deg(A) = max(A1 + A2, 3 + B1 + B2)
    // deg(B) = max(A1 + B2, A2 + B1)
    let a = (a1 + a2).max(3 + b1 + b2);
    let b = (a1 + b2).max(a2 + b1);
    (a, b)
}

/// Multiply two divisors modulo the curve equation, in evaluation domain.
///
/// Computes `f1 * f2` where `f1 = A1(x) - y.B1(x)` and `f2 = A2(x) - y.B2(x)` and multiplication
/// is done modulo `y^2 = x^3 + ax + b`.
///
/// The formula used is:
/// - `f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2`
/// - `A = A1A2 + (x^3 + ax + b) B1B2`
/// - `B = A1B2 + A2B1`
///
/// This is computed efficiently in the evaluation domain using pointwise operations.
pub(crate) fn mul_mod_slices<F: PrimeField>(
    a1: &mut [F],
    b1: &mut [F],
    a2: &[F],
    b2: &[F],
    modulus: &[F],
) {
    debug_assert_eq!(a1.len(), b1.len());
    debug_assert_eq!(a1.len(), a2.len());
    debug_assert_eq!(a1.len(), b2.len());
    debug_assert_eq!(a1.len(), modulus.len());

    // f1 * f2 = A1A2 - y(A1B2 + A2B1) + y^2 B1B2
    // f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
    // For product poly: A = A1A2 + (x^3 + ax + b) B1B2, B = A1B2 + A2B1
    for i in 0..a1.len() {
        let m = modulus[i];
        let a2_i = a2[i];
        let b2_i = b2[i];
        let a1a2 = a1[i] * a2_i;
        let b1b2 = b1[i] * b2_i;
        // (A1+B1)(A2+B2) = A1A2 + A1B2 + B1A2 + B1B2
        let cross = (a1[i] + b1[i]) * (a2_i + b2_i);
        let b = cross - (a1a2 + b1b2);
        let a = a1a2 + (b1b2 * m);
        a1[i] = a;
        b1[i] = b;
    }
}

/// Multiply any divisor and a line divisor modulo the curve equation, in evaluation domain.
pub(crate) fn mul_mod_small_slices<F: PrimeField>(
    a1: &mut [F],
    b1: &mut [F],
    modulus: &[F],
    line_x: F,
    line_zero: F,
    line_y: F,
) {
    debug_assert_eq!(a1.len(), b1.len());
    debug_assert_eq!(a1.len(), modulus.len());

    // Evals of line divisor poly f = ax - by + c at evaluation domain 0,1,2,..len-1 (fixed in the protocol):
    // for A(x) = [c, a+c, 2a+c, ... ]
    // for B(x) = [b, b, b, ....]
    // A(x) is calculated in the loop as A(i) = A(i-i) + a

    // a2 = A(0)
    let mut a2 = line_zero;
    let b2 = line_y;
    for i in 0..a1.len() {
        let m = modulus[i];
        let a1a2 = a1[i] * a2;
        let b1b2 = b1[i] * b2;
        // (A1+B1)(A2+B2) = A1A2 + A1B2 + B1A2 + B1B2
        let cross = (a1[i] + b1[i]) * (a2 + b2);
        let b = cross - (a1a2 + b1b2);
        let a = a1a2 + b1b2 * m;
        a2 += line_x;
        a1[i] = a;
        b1[i] = b;
    }
}
