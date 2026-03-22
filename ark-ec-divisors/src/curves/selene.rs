use crate::Interpolator;
use crate::curves::DivisorCurve;
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_selene::{Fq, Fr, SeleneConfig};
use generic_array::typenum::U;
use spin::Once;

static SELENE_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl DivisorCurve for SeleneConfig {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        SELENE_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct SeleneParams;
impl DiscreteLogParameter for SeleneParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
