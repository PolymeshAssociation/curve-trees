use crate::Interpolator;
use ark_ec::CurveConfig;
use ark_ff::{Field, PrimeField};
use ark_std::borrow::Borrow;
use ark_std::ops::{Add, Neg};
use ark_std::vec::Vec;
use rand_core::CryptoRngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use zeroize::Zeroize;

#[cfg(any(
    feature = "pallas",
    feature = "vesta",
    feature = "helios",
    feature = "selene",
    feature = "wei25519"
))]
pub mod sw;

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

/// This trait is for short Weierstrass curves and needed especially when dealing with Ed25119 curve
pub trait DivisorCurve: Sized + Clone + Copy + Zeroize + PartialEq + Eq {
    /// The configuration for the short Weierstrass curve. But using CurveConfig as i need to make it for Ed25519 (Wei25519)
    type Config: CurveConfig<BaseField = Self::BaseField, ScalarField = Self::ScalarField>;

    /// An element of the field this curve is defined over (the base field).
    type BaseField: PrimeField;

    /// The scalar field of the curve (the field of scalars for scalar multiplication).
    type ScalarField: PrimeField;

    /// A point for which it's sufficiently efficient to retrieve the affine coordinates.
    type XyPoint: XyPoint<Self::BaseField> + From<Self>;

    /// The A in the curve equation `y^2 = x^3 + A x + B`.
    fn a() -> Self::BaseField;

    /// The B in the curve equation `y^2 = x^3 + A x + B`.
    fn b() -> Self::BaseField;

    /// The type representing an interpolator which has been borrowed.
    type BorrowedInterpolator: Borrow<Interpolator<Self::BaseField>>;

    /// Precomputed interpolator required for interpolating a divisor representing a scalar
    /// multiplication.
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator;

    /// Get the generator point for this curve.
    fn generator() -> Self;

    /// Add two curve points.
    fn add(self, other: Self) -> Self;

    /// Negate a curve point.
    fn neg(self) -> Self;

    /// Multiply a curve point by a scalar.
    fn mul(self, scalar: Self::ScalarField) -> Self;

    fn double(&self) -> Self;

    fn random<R: CryptoRngCore>(rng: &mut R) -> Self;

    /// Convert a point to its affine coordinates.
    ///
    /// Returns `None` if passed the point at infinity.
    ///
    /// This function may run in time variable to if the point is the identity.
    fn to_xy(point: Self) -> Option<(Self::BaseField, Self::BaseField)>;

    /// Convert a list of points to their affine coordinates.
    ///
    /// This method MAY panic if any present points are the identity or return an undefined value.
    fn batch_to_xy(points: &[Self]) -> Vec<(Self::BaseField, Self::BaseField)>;

    fn from_xy_unchecked(x: Self::BaseField, y: Self::BaseField) -> Self;
}

/// A trait representing a point with `(X, Y, _)` coordinates.
///
/// This makes no assumptions about how the point is represented yet expects the points to offer
/// cheap conversions to affine coordinates.
pub trait XyPoint<F: Field>:
    Sized
    + Clone
    + Copy
    + Neg<Output = Self>
    + Add<Output = Self>
    + Zeroize
    + ConstantTimeEq
    + ConditionallySelectable
{
    /// The additive identity.
    const IDENTITY: Self;
    /// If this point is the identity.
    fn is_identity(&self) -> Choice;
    /// Double the point.
    fn double(self) -> Self;
    /// Convert a list of points to their affine coordinates.
    ///
    /// This method MAY panic if any present points are the identity or return an undefined value.
    fn batch_to_xy(points: &[Self]) -> Vec<(F, F)>;
}
