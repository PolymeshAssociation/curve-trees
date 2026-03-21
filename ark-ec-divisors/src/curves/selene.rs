use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_selene::{Fq, Fr, SeleneConfig};
use generic_array::typenum::U;

#[cfg(feature = "std")]
static SELENE_INTERPOLATOR: spin::Once<Interpolator<Fq>> = spin::Once::new();

#[cfg(not(feature = "std"))]
static mut SELENE_INTERPOLATOR: Option<Interpolator<Fq>> = None;

impl HasInterpolator for SeleneConfig {
    fn get_interpolator() -> &'static Interpolator<Fq>
    where
        Self: SWCurveConfig,
    {
        #[cfg(feature = "std")]
        {
            SELENE_INTERPOLATOR.call_once(|| Interpolator::new(130))
        }
        #[cfg(not(feature = "std"))]
        {
            #[allow(static_mut_refs)]
            unsafe {
                if SELENE_INTERPOLATOR.is_none() {
                    SELENE_INTERPOLATOR = Some(Interpolator::new(130));
                }
                SELENE_INTERPOLATOR.as_ref().unwrap()
            }
        }
    }
}

pub type Point = SwCurvePoint<SeleneConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct SeleneParams;
impl DiscreteLogParameter for SeleneParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
