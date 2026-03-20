use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_vesta::{Fq, Fr, VestaConfig};
use generic_array::typenum::U;
use spin::Once;

static VESTA_INTERPOLATOR: Once<Interpolator<Fq>> = Once::new();

impl HasInterpolator for VestaConfig {
    fn get_interpolator() -> &'static Interpolator<Fq>
    where
        Self: SWCurveConfig,
    {
        VESTA_INTERPOLATOR.call_once(|| Interpolator::new(130))
    }
}

pub type Point = SwCurvePoint<VestaConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct VestaParams;
impl DiscreteLogParameter for VestaParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
