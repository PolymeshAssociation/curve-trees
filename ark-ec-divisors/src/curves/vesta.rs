use crate::curves::DivisorCurve;
use crate::divisor::Evals;
use crate::util::DiscreteLogParameter;
use crate::Interpolator;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_vesta::{Fq, Fr, VestaConfig};
use generic_array::typenum::U;
use spin::Once;

static VESTA_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();
static VESTA_MODULUS: Once<Evals<Fq>> = Once::new();

impl DivisorCurve for VestaConfig {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    type BorrowedEvaluationsOfCurvePoly = &'static Evals<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        VESTA_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
    fn evaluation_of_curve_poly() -> Self::BorrowedEvaluationsOfCurvePoly {
        VESTA_MODULUS.call_once(|| {
            let n = Self::interpolator_for_scalar_mul().required_evaluations();
            Evals::compute_modulus(Self::COEFF_A, Self::COEFF_B, n)
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct VestaParams;
impl DiscreteLogParameter for VestaParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
