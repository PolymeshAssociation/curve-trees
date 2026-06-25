use crate::curves::DivisorCurve;
use crate::divisor::Evals;
use crate::util::DiscreteLogParameter;
use crate::Interpolator;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_secp256k1::{Config, Fq, Fr};
use generic_array::typenum::U;
use spin::Once;

static SECP256K1_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();
static SECP256K1_MODULUS: Once<Evals<Fq>> = Once::new();

impl DivisorCurve for Config {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    type BorrowedEvaluationsOfCurvePoly = &'static Evals<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        // Same as the 255-bit curves: the divisor interpolates num_bits+1 points, and
        // (256+1)/2 = (255+1)/2 = 128 x-coefficients
        SECP256K1_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
    fn evaluation_of_curve_poly() -> Self::BorrowedEvaluationsOfCurvePoly {
        SECP256K1_MODULUS.call_once(|| {
            let n = Self::interpolator_for_scalar_mul().required_evaluations();
            Evals::compute_modulus(Self::COEFF_A, Self::COEFF_B, n)
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Secp256k1Params;
impl DiscreteLogParameter for Secp256k1Params {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
