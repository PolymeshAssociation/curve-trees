use crate::Interpolator;
use crate::curves::DivisorCurve;
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_vesta::{Fq, Fr, VestaConfig};
use generic_array::typenum::U;
use spin::Once;

static VESTA_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl DivisorCurve for VestaConfig {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        VESTA_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct VestaParams;
impl DiscreteLogParameter for VestaParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
