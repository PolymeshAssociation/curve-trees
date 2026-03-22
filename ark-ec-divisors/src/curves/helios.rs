use crate::Interpolator;
use crate::curves::DivisorCurve;
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_helios::{Fq, Fr, HeliosConfig};
use generic_array::typenum::U;
use spin::Once;

static HELIOS_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl DivisorCurve for HeliosConfig {
    type BorrowedInterpolator = &'static Interpolator<Fq>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        HELIOS_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct HeliosParams;
impl DiscreteLogParameter for HeliosParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
