use crate::Interpolator;
use crate::curves::DivisorCurve;
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_pallas::{Fq, Fr, PallasConfig};
use generic_array::typenum::U;
use spin::Once;

static PALLAS_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl DivisorCurve for PallasConfig {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        PALLAS_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct PallasParams;
impl DiscreteLogParameter for PallasParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
