use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_selene::{Fq, Fr, SeleneConfig};
use generic_array::typenum::U;
use spin::Once;

static SELENE_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl HasInterpolator for SeleneConfig {
    fn get_interpolator() -> &'static Interpolator<Fq>
    where
        Self: SWCurveConfig,
    {
        SELENE_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

pub type Point = SwCurvePoint<SeleneConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct SeleneParams;
impl DiscreteLogParameter for SeleneParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
