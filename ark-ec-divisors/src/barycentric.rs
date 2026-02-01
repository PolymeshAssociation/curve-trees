//! Barycentric Lagrange interpolation for efficient polynomial reconstruction.
//!
//! This module provides efficient Lagrange interpolation using the barycentric form,
//! which allows for O(n) interpolation given precomputed weights, where n is the degree.

use ark_ff::{Field, PrimeField};
use ark_std::{vec, vec::Vec};
use core::{
    ops::{AddAssign, Mul},
    iter::successors,
};
use crate::error::Error;

/// The coefficients for a univariate polynomial with the leading coefficient _first_.
// TODO: This is opposite to how Poly stores coefficients, make these consistent
#[cfg_attr(test, derive(Debug, PartialEq))]
#[derive(Clone)]
pub struct UnivariatePoly<F>(Vec<F>);

impl<F: Field> AddAssign<&Self> for UnivariatePoly<F> {
    /// Panics if the polynomials are of different lengths.
    fn add_assign(&mut self, rhs: &Self) {
        assert_eq!(self.0.len(), rhs.0.len());
        for i in 0..self.0.len() {
            self.0[i] += rhs.0[i];
        }
    }
}

impl<F: Field> Mul<F> for UnivariatePoly<F> {
    type Output = Self;
    fn mul(mut self, scalar: F) -> Self {
        for coeff in &mut self.0 {
            *coeff *= scalar;
        }
        self
    }
}

impl<F: Field> UnivariatePoly<F> {
    #[cfg(test)]
    /// Evaluation with Horner's rule
    fn eval(&self, x: F) -> F {
        self.0.iter().fold(F::zero(), |acc, coeff| (acc * x) + coeff)
    }

    /// Multiply by `(x + c)`.
    fn mul_x_c(&mut self, c: F) {
        let coeffs = &mut self.0;
        // multiply by x
        coeffs.push(F::zero());

        // multiply by c and add
        let mut prior_coeff = coeffs[0];
        for coeff in &mut coeffs[1..] {
            let this_coeff = *coeff;
            *coeff += prior_coeff * c;
            prior_coeff = this_coeff;
        }
    }

    /// Divide the polynomial by `(x + c)` and returns quotient and remainder
    ///
    /// Executes in time variable to the length of the polynomial.
    fn div_x_c(mut self, c: F) -> (Self, F) {
        let coeffs = &mut self.0;
        if coeffs.is_empty() {
            return (Self(vec![]), F::zero());
        }
        let mut new_coeff = coeffs.remove(0);
        for coeff in coeffs {
            let this_coeff = *coeff;
            *coeff = new_coeff;
            new_coeff = this_coeff - (new_coeff * c);
        }
        let remainder = new_coeff;
        (self, remainder)
    }
}

/// Precomputed weights for barycentric interpolation
struct Weights<F: Field> {
    inverted_weights: Vec<F>,
    l: UnivariatePoly<F>,
}

impl<F: PrimeField> Weights<F> {
    /// `l(x) = (x-0)(x-1)(x-2)...(x-domain_size - 1)`
    fn l(domain_size: u16) -> UnivariatePoly<F> {
        assert_ne!(domain_size, 0);

        let mut poly = UnivariatePoly(vec![F::ONE]);
        for i in 0..domain_size {
            let i: F = F::from(u64::from(i));
            poly.mul_x_c(-i);
        }
        poly
    }

    /// Create new weights for barycentric interpolation over the domain `{0, 1, ..., n-1}`
    fn new(domain_size: u16) -> Self {
        assert_ne!(domain_size, 0);

        // Calculate barycentric weights:
        // w_i = 1 / ∏_{j≠i} (i - j)
        
        let start = Some(-F::ONE);
        let diffs = successors(start, |prev| Some(*prev - F::ONE));
        let diff_products = diffs.scan(F::ONE, |product, diff| {
            *product *= diff;
            Some(*product)
        });
        let mut diff_products: Vec<F> = diff_products.take(domain_size as usize - 1).collect();
        diff_products.reverse();
        diff_products.push(F::ONE);
        let diff_products_right = diff_products.into_iter();

        let diffs = successors(Some(F::ONE), |prev| Some(*prev + F::ONE));
        let diff_products_left = diffs.scan(F::ONE, |product, diff| {
            *product *= diff;
            Some(*product)
        });
        let diff_products_left = [F::ONE].into_iter().chain(diff_products_left);

        let weights: Vec<F> =
            diff_products_left.zip(diff_products_right).map(|(left, right)| left * right).collect();

        let mut inverted_weights = weights.clone();
        // Batch invert the weights
        ark_ff::batch_inversion(&mut inverted_weights);
        Weights { inverted_weights, l: Self::l(domain_size) }
    }

    /// Get the i-th Lagrange basis polynomial `L_i(x) = w_i * l(x)/(x - i)`
    fn li(&self, i: u16) -> UnivariatePoly<F> {
        ({
            let i = -F::from(u64::from(i));
            let (li, rem) = self.l.clone().div_x_c(i);
            // The `l` polynomial is the product of `x - i`, ensuring we can divide out `x - i`
            debug_assert_eq!(rem, F::zero());
            li
        }) * self.inverted_weights[i as usize]
    }
}

/// A precomputed interpolator which can perform fast Lagrange interpolation.
///
/// This interpolator is able to reconstruct polynomials from evaluations at points
/// 0, 1, 2, ..., n-1 using the barycentric form, which provides O(n) interpolation
/// after O(n²) preprocessing.
#[derive(Clone)]
pub struct Interpolator<F: Field> {
    lagrange_polys: Vec<UnivariatePoly<F>>,
}

impl<F: PrimeField> Interpolator<F> {
    /// Create a new interpolator for polynomials of the given degree.
    ///
    /// The interpolator will work for polynomials with degree up to `degree`,
    /// requiring `degree + 1` evaluation points.
    ///
    pub fn new(degree: u16) -> Self {
        let domain_size = degree + 1;
        let weights = Weights::new(domain_size);
        let mut lagrange_polys = Vec::with_capacity(domain_size as usize);
        for i in 0..domain_size {
            let li = weights.li(i);
            lagrange_polys.push(li);
        }
        Self { lagrange_polys }
    }

    /// The maximum degree this interpolator can handle
    pub fn degree(&self) -> u16 {
        self.lagrange_polys.len() as u16 - 1
    }

    /// The number of evaluation points required
    pub fn required_evaluations(&self) -> u16 {
        self.lagrange_polys.len() as u16
    }

    /// Attempt to reconstruct the original polynomial via interpolation.
    ///
    /// The returned polynomial will have its coefficients in little-endian order
    /// (constant term first, highest degree term last).
    ///
    /// Returns an error if not enough evaluations were provided to attempt interpolation.
    /// Returns garbage if the polynomial's degree exceeds this interpolator's degree.
    pub fn interpolate(&self, evals: &[F]) -> Result<Vec<F>, Error> {
        if evals.len() < self.lagrange_polys.len() {
            return Err(Error::InsufficientEvaluations(evals.len(), self.lagrange_polys.len()));
        }

        let mut poly = vec![F::zero(); evals.len()];
        for (eval, li) in evals.iter().zip(&self.lagrange_polys) {
            for (res, li) in poly.iter_mut().zip(li.0.iter().rev()) {
                *res += *li * *eval;
            }
        }
        Ok(poly)
    }

    /// Evaluate the interpolator at a specific point using the barycentric formula
    ///
    /// This is more efficient than full interpolation when you only need a single point evaluation
    #[cfg(test)]
    pub fn evaluate_at(&self, x: F, evals: &[F]) -> Result<F, Error> {
        if evals.len() < self.lagrange_polys.len() {
            return Err(Error::InsufficientEvaluations(evals.len(), self.lagrange_polys.len()));
        }

        let mut numerator = F::zero();
        let mut denominator = F::zero();

        let weights = self.inverted_weights();
        for (i, (eval, weight)) in evals.iter().zip(weights.iter()).enumerate() {
            let x_minus_i = x - F::from(u64::from(i as u16));
            let term = *weight / x_minus_i;
            numerator += *eval * term;
            denominator += term;
        }

        Ok(numerator / denominator)
    }

    #[cfg(test)]
    /// Get the inverted weights for manual barycentric evaluation
    fn inverted_weights(&self) -> Vec<F> {
        // Extract weights from the first Lagrange polynomial if available
        if let Some(_first_li) = self.lagrange_polys.first() {
            // Weights are embedded in the leading coefficients of the Lagrange polynomials
            // For now, return a simple pattern
            let mut weights = vec![F::zero(); self.lagrange_polys.len()];
            for (i, li) in self.lagrange_polys.iter().enumerate() {
                if let Some(&leading_coeff) = li.0.first() {
                    weights[i] = leading_coeff;
                }
            }
            weights
        } else {
            vec![F::zero(); self.lagrange_polys.len()]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_core::OsRng;

    fn test_div_x_c_generic<F: PrimeField>() {
        {
            assert_eq!(
                UnivariatePoly(vec![]).div_x_c(F::rand(&mut OsRng)),
                (UnivariatePoly(vec![]), F::zero())
            );
        }
        {
            let c0 = F::rand(&mut OsRng);
            assert_eq!(
                UnivariatePoly(vec![c0]).div_x_c(F::rand(&mut OsRng)),
                (UnivariatePoly(vec![]), c0)
            );
        }
        for i in 2..20 {
            let mut coeffs = UnivariatePoly(vec![F::zero(); i]);
            for coeff in &mut coeffs.0 {
                *coeff = F::rand(&mut OsRng);
            }
            let denom = F::rand(&mut OsRng);
            let (coeffs_div, coeffs_rem) = coeffs.clone().div_x_c(denom);
            
            // Test that dividing by (x + denom) and multiplying back gives original
            let mut reconstructed = coeffs_div.clone();
            reconstructed.mul_x_c(denom);
            // Add remainder to the constant term (last coefficient)
            *reconstructed.0.last_mut().unwrap() += coeffs_rem;
            
            assert_eq!(coeffs.0, reconstructed.0);
        }
    }

    #[test]
    fn test_div_x_c() {
        test_div_x_c_generic::<ark_pallas::Fq>();
        test_div_x_c_generic::<ark_vesta::Fq>();
    }

    fn interpolation_generic<F: PrimeField>() {
        for i in 2..50 {
            let mut evals = vec![F::zero(); i];
            for eval in &mut evals {
                *eval = F::rand(&mut OsRng);
            }

            let coeffs = UnivariatePoly(
                Interpolator::new((i - 1) as u16).interpolate(&evals).unwrap().into_iter().rev().collect(),
            );
            for (i, eval) in evals.into_iter().enumerate() {
                assert_eq!(coeffs.eval(F::from(u64::try_from(i).unwrap())), eval);
            }
        }
    }

    #[test]
    fn test_interpolation() {
        interpolation_generic::<ark_pallas::Fq>();
        interpolation_generic::<ark_vesta::Fq>();
    }

    fn test_weights_generic<F: PrimeField>() {
        // Test with small domain sizes
        for size in 2..10 {
            let weights = Weights::<F>::new(size as u16);
            
            // Test that the weights are correctly inverted
            for (i, weight) in weights.inverted_weights.iter().enumerate() {
                let mut product = F::ONE;
                for j in 0..size {
                    if i != j {
                        product *= F::from(u64::from(i as u16)) - F::from(u64::from(j as u16));
                    }
                }
                assert_eq!(*weight * product, F::ONE);
            }
        }
    }

    #[test]
    fn test_weights() {
        test_weights_generic::<ark_pallas::Fq>();
        test_weights_generic::<ark_vesta::Fq>();
    }

    fn test_barycentric_evaluation_generic<F: PrimeField>() {
        // Test that barycentric evaluation gives same result as interpolation
        for degree in 2..20 {
            let interpolator = Interpolator::new(degree as u16);
            let mut evals = vec![F::zero(); degree + 1];
            for eval in &mut evals {
                *eval = F::rand(&mut OsRng);
            }

            // Interpolate to get coefficients
            let coeffs = interpolator.interpolate(&evals).unwrap();
            let poly = UnivariatePoly(coeffs.into_iter().rev().collect());

            // Test evaluation at random points
            for _ in 0..10 {
                let x = F::rand(&mut OsRng);
                let interpolated_eval = poly.eval(x);
                let barycentric_eval = interpolator.evaluate_at(x, &evals).unwrap();
                assert_eq!(interpolated_eval, barycentric_eval);
            }
        }
    }

    #[test]
    fn test_barycentric_evaluation() {
        test_barycentric_evaluation_generic::<ark_pallas::Fq>();
        test_barycentric_evaluation_generic::<ark_vesta::Fq>();
    }
}