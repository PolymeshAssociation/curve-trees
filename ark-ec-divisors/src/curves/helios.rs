use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_helios::{Fq, Fr, HeliosConfig};
use generic_array::typenum::U;
use spin::Once;

static HELIOS_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl HasInterpolator for HeliosConfig {
    fn get_interpolator() -> &'static Interpolator<Fq> {
        HELIOS_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

pub type Point = SwCurvePoint<HeliosConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct HeliosParams;
impl DiscreteLogParameter for HeliosParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
