use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_helios::{Fq, Fr, HeliosConfig};
use generic_array::typenum::U;

#[cfg(feature = "std")]
static HELIOS_INTERPOLATOR: spin::Once<Interpolator<Fq>> = spin::Once::new();

#[cfg(not(feature = "std"))]
static mut HELIOS_INTERPOLATOR: Option<Interpolator<Fq>> = None;

impl HasInterpolator for HeliosConfig {
    fn get_interpolator() -> &'static Interpolator<Fq> {
        #[cfg(feature = "std")]
        {
            HELIOS_INTERPOLATOR.call_once(|| Interpolator::new(130))
        }
        #[cfg(not(feature = "std"))]
        {
            #[allow(static_mut_refs)]
            unsafe {
                if HELIOS_INTERPOLATOR.is_none() {
                    HELIOS_INTERPOLATOR = Some(Interpolator::new(130));
                }
                HELIOS_INTERPOLATOR.as_ref().unwrap()
            }
        }
    }
}

pub type Point = SwCurvePoint<HeliosConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct HeliosParams;
impl DiscreteLogParameter for HeliosParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
