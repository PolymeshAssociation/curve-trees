use crate::curves::DivisorCurve;
use crate::divisor::Evals;
use crate::util::DiscreteLogParameter;
use crate::Interpolator;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::{Field, MontFp, PrimeField};
use ark_wei25519::{Affine, Fq, Fr, Wei25519Config};
use generic_array::typenum::U;
use spin::Once;

use ark_curve25519::{
    Curve25519Config, EdwardsAffine as Curve25519Affine, EdwardsProjective as Curve25519Projective,
};
use ark_ec::twisted_edwards::MontgomeryAffine;
use ark_ec::AffineRepr;
use ark_ed25519::{EdwardsAffine as Ed25519Affine, EdwardsProjective as Ed25519Projective};

static WEI25519_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();
static WEI25519_MODULUS: Once<Evals<Fq>> = Once::new();

impl DivisorCurve for Wei25519Config {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    type BorrowedEvaluationsOfCurvePoly = &'static Evals<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        WEI25519_INTERPOLATOR.call_once(|| Interpolator::new(128))
    }
    fn evaluation_of_curve_poly() -> Self::BorrowedEvaluationsOfCurvePoly {
        WEI25519_MODULUS.call_once(|| {
            let n = Self::interpolator_for_scalar_mul().required_evaluations();
            Evals::compute_modulus(Self::COEFF_A, Self::COEFF_B, n)
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Wei25519Params;
impl DiscreteLogParameter for Wei25519Params {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}

// Conversion Constants from Sage script / IETF draft

/// A/3 mod p, the shift constant for Curve25519 <-> Wei25519
/// Computed in GF(2^255-19): A/3 = 486662/3 mod (2^255-19)
const MONTGOMERY_TO_WEI_SHIFT: Fq =
    MontFp!("19298681539552699237261830834781317975544997444273427339909597334652188435537");

/// Conversion constant for Ed25519 (twisted Edwards) to Wei25519
/// Ed25519 uses TWISTED Edwards form: -x^2 + y^2 = 1 + d·x^2·y^2  (note the negative on x^2)
/// The twist changes the sign of the conversion constant.
///
/// For twisted Edwards: c = -sqrt(-(A+2)) mod p
/// Computed: c = -sqrt(-486664) mod p = 51042569399160536130206135233146329284152202253034631822681833788666877215207
///
/// For comparison, untwisted Edwards (like Curve25519) would use: +sqrt(-(A+2))
const EDWARDS_TO_WEI_C: Fq =
    MontFp!("51042569399160536130206135233146329284152202253034631822681833788666877215207");

// Curve25519 (Montgomery) <-> Wei25519 Conversions
// Curve25519 is a Montgomery curve. In arkworks, it's represented in twisted Edwards form ([`Curve25519Affine`])
// but converts to Montgomery form ([`MontgomeryAffine`]).

/// Convert a Montgomery point (u, v) from Curve25519 to Wei25519 (X, Y)
/// - X = u + A/3
/// - Y = v (unchanged)
/// This is an isomorphism - defined at every affine point.
pub fn montgomery_to_wei25519(montgomery: &MontgomeryAffine<Curve25519Config>) -> Option<Affine> {
    // Montgomery curve point (u, v)
    let u = montgomery.x;
    let v = montgomery.y;

    // Wei25519 coordinates
    let x_w = u + MONTGOMERY_TO_WEI_SHIFT;
    let y_w = v;

    Some(Affine::new_unchecked(x_w, y_w))
}

/// Convert a Wei25519 point (X, Y) to Montgomery point (u, v) on Curve25519
/// - u = X - A/3
/// - v = Y (unchanged)
pub fn wei25519_to_montgomery(wei: &Affine) -> MontgomeryAffine<Curve25519Config> {
    let x_w = wei.x;
    let y_w = wei.y;

    // Montgomery coordinates
    let u = x_w - MONTGOMERY_TO_WEI_SHIFT;
    let v = y_w;

    MontgomeryAffine::<Curve25519Config>::new(u, v)
}

/// Convert a Curve25519 point (in Edwards form) to Wei25519
/// Curve25519 Edwards -> Curve25519 Montgomery -> Wei25519
/// Curve25519 Edwards: x^2 + y^2 = 1 + (121665/121666)·x^2·y^2
/// Curve25519 Montgomery: v^2 = u^3 + 486662·u^2 + u
///
/// Edwards to Montgomery mapping for Curve25519:
/// u = (1+y)/(1-y), v = u/x
pub fn curve25519_to_wei25519(edwards: &Curve25519Affine) -> Option<Affine> {
    if edwards.is_zero() {
        return None;
    }

    let one_plus_y = Fq::ONE + edwards.y;
    let one_minus_y = Fq::ONE - edwards.y;
    let u = one_plus_y * one_minus_y.inverse()?;
    let v = u * edwards.x.inverse()?;

    let montgomery = MontgomeryAffine::<Curve25519Config>::new(u, v);

    montgomery_to_wei25519(&montgomery)
}

/// Convert a Wei25519 point to Curve25519 Edwards point
/// Path: Wei25519 -> Curve25519 Montgomery -> Curve25519 Edwards
///
/// Montgomery to Edwards mapping for Curve25519:
/// x = u/v, y = (u-1)/(u+1)
pub fn wei25519_to_curve25519(wei: &Affine) -> Option<Curve25519Affine> {
    let montgomery = wei25519_to_montgomery(wei);

    let u = montgomery.x;
    let v = montgomery.y;

    let x = u * v.inverse()?;
    let u_minus_1 = u - Fq::ONE;
    let u_plus_1 = u + Fq::ONE;
    let y = u_minus_1 * u_plus_1.inverse()?;

    Some(Curve25519Affine::new_unchecked(x, y))
}

// Ed25519 <-> Wei25519 Conversions
// Ed25519 is an Edwards curve. The conversion is: Ed25519 Edwards -> Montgomery -> Wei25519

/// Convert an Ed25519 Edwards point to Wei25519
///
/// Ed25519 uses TWISTED Edwards form: -x^2 + y^2 = 1 + d·x^2·y^2
/// The negative coefficient on x^2 requires a sign adjustment in the conversion constant.
///
/// Formula (from IETF draft Appendix E.2 for twisted Edwards):
/// For twisted Edwards point (x_e, y_e):
/// - X_W = (1 + y_e) / (1 - y_e) + A/3
/// - Y_W = c * (1 + y_e) / ((1 - y_e) * x_e)
///
/// where c = -sqrt(-(A+2)) for twisted Edwards curves
pub fn ed25519_to_wei25519(edwards: &Ed25519Affine) -> Option<Affine> {
    if edwards.is_zero() {
        return None;
    }

    let x_e = edwards.x;
    let y_e = edwards.y;

    let one_plus_y = Fq::ONE + y_e;
    let one_minus_y = Fq::ONE - y_e;

    // X_W = (1 + y_e) / (1 - y_e) + A/3
    let x_w = one_plus_y * one_minus_y.inverse()? + MONTGOMERY_TO_WEI_SHIFT;

    // Y_W = c * (1 + y_e) / ((1 - y_e) * x_e)
    let denominator = one_minus_y * x_e;
    let y_w = EDWARDS_TO_WEI_C * one_plus_y * denominator.inverse()?;

    Some(Affine::new_unchecked(x_w, y_w))
}

/// Convert a Wei25519 point to Ed25519 Edwards point
/// For Wei25519 point (X_W, Y_W):
/// - u = X_W - A/3  (convert to Montgomery first)
/// - x_e = c * u / Y_W
/// - y_e = (u - 1) / (u + 1)
pub fn wei25519_to_ed25519(wei: &Affine) -> Option<Ed25519Affine> {
    let x_w = wei.x;
    let y_w = wei.y;

    // Convert to Montgomery u-coordinate
    let u = x_w - MONTGOMERY_TO_WEI_SHIFT;

    // x_e = c * u / Y_W
    let x_e = EDWARDS_TO_WEI_C * u * y_w.inverse()?;

    // y_e = (u - 1) / (u + 1)
    let y_e = (u - Fq::ONE) * (u + Fq::ONE).inverse()?;

    Some(Ed25519Affine::new_unchecked(x_e, y_e))
}

pub fn curve25519_projective_to_wei25519(edwards: &Curve25519Projective) -> Option<Affine> {
    use ark_ec::CurveGroup;
    let affine = edwards.into_affine();
    curve25519_to_wei25519(&affine)
}

pub fn ed25519_projective_to_wei25519(edwards: &Ed25519Projective) -> Option<Affine> {
    use ark_ec::CurveGroup;
    let affine = edwards.into_affine();
    ed25519_to_wei25519(&affine)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_std::UniformRand;
    use rand::prelude::StdRng;
    use rand_core::SeedableRng;

    #[test]
    fn test_curve25519_wei25519() {
        let mut rng = StdRng::seed_from_u64(0);

        for _ in 0..10 {
            let p1 = Curve25519Projective::rand(&mut rng).into_affine();
            let p2 = Curve25519Projective::rand(&mut rng).into_affine();
            let scalar = Fr::rand(&mut rng);

            // add in Curve25519, convert to Wei25519, verify
            let sum_curve25519 = (p1 + p2).into_affine();
            let w1 = curve25519_to_wei25519(&p1).unwrap();
            let w2 = curve25519_to_wei25519(&p2).unwrap();

            assert_eq!(wei25519_to_curve25519(&w1).unwrap(), p1);
            assert_eq!(wei25519_to_curve25519(&w2).unwrap(), p2);

            let sum_wei = (w1 + w2).into_affine();
            assert_eq!(curve25519_to_wei25519(&sum_curve25519).unwrap(), sum_wei);
            assert_eq!(wei25519_to_curve25519(&sum_wei).unwrap(), sum_curve25519);

            // multiply in Curve25519, convert to Wei25519
            let p1_mul_curve = (p1 * scalar).into_affine();
            let p1_mul_wei = (w1 * scalar).into_affine();

            assert_eq!(curve25519_to_wei25519(&p1_mul_curve).unwrap(), p1_mul_wei);
            assert_eq!(wei25519_to_curve25519(&p1_mul_wei).unwrap(), p1_mul_curve);

            // subtract in Curve25519, convert to Wei25519, verify
            let diff_curve25519 = (p1 - p2).into_affine();
            let diff_wei = (w1 - w2).into_affine();
            assert_eq!(curve25519_to_wei25519(&diff_curve25519).unwrap(), diff_wei);
            assert_eq!(wei25519_to_curve25519(&diff_wei).unwrap(), diff_curve25519);

            // negate in Curve25519, convert to Wei25519, verify
            let neg_p1_curve = -p1;
            let neg_w1_wei = -w1;
            assert_eq!(curve25519_to_wei25519(&neg_p1_curve).unwrap(), neg_w1_wei);
            assert_eq!(wei25519_to_curve25519(&neg_w1_wei).unwrap(), neg_p1_curve);
        }
    }

    #[test]
    fn test_ed25519_wei25519() {
        let mut rng = StdRng::seed_from_u64(0);

        for _ in 0..10 {
            let p1 = Ed25519Projective::rand(&mut rng).into_affine();
            let p2 = Ed25519Projective::rand(&mut rng).into_affine();
            let scalar = Fr::rand(&mut rng);

            // add in Ed25519, convert to Wei25519
            let sum_ed25519 = (p1 + p2).into_affine();
            let w1 = ed25519_to_wei25519(&p1).unwrap();
            let w2 = ed25519_to_wei25519(&p2).unwrap();

            assert_eq!(wei25519_to_ed25519(&w1).unwrap(), p1);
            assert_eq!(wei25519_to_ed25519(&w2).unwrap(), p2);

            let sum_wei = (w1 + w2).into_affine();
            assert_eq!(ed25519_to_wei25519(&sum_ed25519).unwrap(), sum_wei);
            assert_eq!(wei25519_to_ed25519(&sum_wei).unwrap(), sum_ed25519);

            // multiply in Ed25519, convert to Wei25519
            let p1_mul_ed = (p1 * scalar).into_affine();
            let p1_mul_wei = (w1 * scalar).into_affine();

            assert_eq!(ed25519_to_wei25519(&p1_mul_ed).unwrap(), p1_mul_wei);
            assert_eq!(wei25519_to_ed25519(&p1_mul_wei).unwrap(), p1_mul_ed);

            // subtract in Ed25519, convert to Wei25519, verify
            let diff_ed25519 = (p1 - p2).into_affine();
            let diff_wei = (w1 - w2).into_affine();
            assert_eq!(ed25519_to_wei25519(&diff_ed25519).unwrap(), diff_wei);
            assert_eq!(wei25519_to_ed25519(&diff_wei).unwrap(), diff_ed25519);

            // negate in Ed25519, convert to Wei25519, verify
            let neg_p1_ed = -p1;
            let neg_w1_wei = -w1;
            assert_eq!(ed25519_to_wei25519(&neg_p1_ed).unwrap(), neg_w1_wei);
            assert_eq!(wei25519_to_ed25519(&neg_w1_wei).unwrap(), neg_p1_ed);
        }
    }
}
