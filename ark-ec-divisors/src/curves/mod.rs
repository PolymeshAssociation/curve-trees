use crate::divisor::Evals;
use crate::Interpolator;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_std::borrow::Borrow;

#[cfg(any(test, feature = "pallas"))]
pub mod pallas;

#[cfg(any(test, feature = "vesta"))]
pub mod vesta;

#[cfg(any(test, feature = "helios"))]
pub mod helios;

#[cfg(any(test, feature = "selene"))]
pub mod selene;

#[cfg(any(test, feature = "wei25519"))]
pub mod wei25519;

#[cfg(test)]
mod tests;

/// A short Weierstrass curve whose scalar multiplications can be proved via divisors.
///
/// Implementing this trait for a curve config `C: SWCurveConfig` makes `Projective<C>` usable
/// as the point type throughout the divisor machinery. All arithmetic (add, negate, scalar mul,
/// doubling, random sampling, affine conversion) is inherited from the underlying `SWCurveConfig`
/// / `CurveGroup` implementations.
pub trait DivisorCurve: SWCurveConfig<BaseField: PrimeField> + Sized {
    /// The type representing a borrowed interpolator.
    type BorrowedInterpolator: Borrow<Interpolator<Self::BaseField>>;

    /// The type representing a borrowed scalar-mul modulus.
    type BorrowedEvaluationsOfCurvePoly: Borrow<Evals<Self::BaseField>>;

    /// Precomputed interpolator required for interpolating a divisor representing a
    /// scalar multiplication.
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator;

    /// Precomputed evaluations of the curve modulus polynomial `x^3 + ax + b` at
    /// `x = 0, 1, ..., n-1`, where `n` matches the scalar-mul interpolator's required number of
    /// evaluations. This depends only on the curve, so it is cached once per curve and reused
    /// across all divisor constructions.
    fn evaluation_of_curve_poly() -> Self::BorrowedEvaluationsOfCurvePoly;
}
