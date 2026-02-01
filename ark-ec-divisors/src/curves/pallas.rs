use ark_pallas::{Fq, Fr, PallasConfig};
use ark_ff::PrimeField;
use generic_array::typenum::U;
use crate::{Interpolator};
use spin::Once;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;

static PALLAS_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl HasInterpolator for PallasConfig {
    fn get_interpolator() -> &'static Interpolator<Fq> {
        PALLAS_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

pub type Point = SwCurvePoint<PallasConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct PallasParams;
impl DiscreteLogParameter for PallasParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}