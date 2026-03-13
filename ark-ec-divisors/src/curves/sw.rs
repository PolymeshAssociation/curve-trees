use ark_ec::CurveGroup;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use ark_std::UniformRand;
use ark_std::vec::Vec;
use rand_core::CryptoRngCore;
use zeroize::Zeroize;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use core::ops::{Add, Mul, Neg};

use crate::{Interpolator, DivisorCurve, XyPoint};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Zeroize)]
pub struct SwCurvePoint<C: SWCurveConfig>(pub Projective<C>);

impl<C: SWCurveConfig> Neg for SwCurvePoint<C> {
    type Output = Self;
    fn neg(self) -> Self::Output { Self(-self.0) }
}

impl<C: SWCurveConfig> Add for SwCurvePoint<C> {
    type Output = Self;
    fn add(self, other: Self) -> Self::Output { Self(self.0 + other.0) }
}

impl<C: SWCurveConfig> ConstantTimeEq for SwCurvePoint<C> {
    fn ct_eq(&self, other: &Self) -> Choice {
        Choice::from(u8::from(self.0 == other.0))
    }
}

impl<C: SWCurveConfig + Copy> ConditionallySelectable for SwCurvePoint<C> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        if bool::from(choice) { *b } else { *a }
    }
}

impl<C: SWCurveConfig> From<Affine<C>> for SwCurvePoint<C> {
    fn from(affine: Affine<C>) -> Self { Self(affine.into()) }
}

impl<C: SWCurveConfig> From<Projective<C>> for SwCurvePoint<C> {
    fn from(projective: Projective<C>) -> Self { Self(projective) }
}

impl<C: SWCurveConfig> Mul<C::ScalarField> for SwCurvePoint<C> {
    type Output = Self;
    fn mul(self, scalar: C::ScalarField) -> Self::Output { Self(self.0 * scalar) }
}

impl<C: SWCurveConfig + Copy> XyPoint<C::BaseField> for SwCurvePoint<C> {
    const IDENTITY: Self = SwCurvePoint(Projective::<C> {
        x: C::BaseField::ONE, y: C::BaseField::ONE, z: C::BaseField::ZERO,
    });

    fn is_identity(&self) -> Choice {
        Choice::from(u8::from(self.0 == Projective::<C>::zero()))
    }

    fn double(self) -> Self {
        Self(Projective::<C>::double(&self.0)) 
    }

    fn batch_to_xy(points: &[Self]) -> Vec<(C::BaseField, C::BaseField)> {
        let aff = Projective::<C>::normalize_batch(&points.iter().map(|p| p.0).collect::<Vec<_>>());
        aff.into_iter().map(|p| (p.x, p.y)).collect()
    }
}

pub trait HasInterpolator {
    fn get_interpolator() -> &'static Interpolator<Self::BaseField>
    where
        Self: SWCurveConfig;
}

impl<C: SWCurveConfig<BaseField: PrimeField> + Copy + PartialEq + Eq + HasInterpolator> DivisorCurve for SwCurvePoint<C> {
    type Config = C;
    type BaseField = C::BaseField;

    type ScalarField = C::ScalarField;
    type XyPoint = Self;

    fn a() -> Self::BaseField { C::COEFF_A }
    fn b() -> Self::BaseField { C::COEFF_B }

    type BorrowedInterpolator = &'static Interpolator<Self::BaseField>;

    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        C::get_interpolator()
    }
    fn generator() -> Self { C::GENERATOR.into() }

    fn add(self, other: Self) -> Self { self + other }
    fn neg(self) -> Self { -self }
    fn mul(self, scalar: Self::ScalarField) -> Self { self * scalar }
    fn double(&self) -> Self { 
        Self(Projective::<C>::double(&self.0)) 
    }

    fn random<R: CryptoRngCore>(rng: &mut R) -> Self {
        Self(Projective::<C>::rand(rng))
    }

    fn to_xy(point: Self) -> Option<(Self::BaseField, Self::BaseField)> {
        let aff = point.0.into_affine();
        Some((aff.x, aff.y))
    }

    fn batch_to_xy(points: &[Self]) -> Vec<(Self::BaseField, Self::BaseField)> {
        // TODO: This is inefficient. Fix
        let aff = Projective::<C>::normalize_batch(&points.iter().map(|p| p.0).collect::<Vec<_>>());
        aff.into_iter().map(|p| (p.x, p.y)).collect()
    }

    fn from_xy_unchecked(x: Self::BaseField, y: Self::BaseField) -> Self {
        let point = Affine::<C>::new_unchecked(x, y);
        Self(point.into())
    }
}
