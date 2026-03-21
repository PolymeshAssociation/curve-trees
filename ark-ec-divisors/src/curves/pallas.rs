use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ff::PrimeField;
use ark_pallas::{Fq, Fr, PallasConfig};
use generic_array::typenum::U;

#[cfg(feature = "std")]
static PALLAS_INTERPOLATOR: spin::Once<Interpolator<Fq>> = spin::Once::new();

#[cfg(not(feature = "std"))]
static mut PALLAS_INTERPOLATOR: Option<Interpolator<Fq>> = None;

impl HasInterpolator for PallasConfig {
    fn get_interpolator() -> &'static Interpolator<Fq> {
        #[cfg(feature = "std")]
        {
            PALLAS_INTERPOLATOR.call_once(|| Interpolator::new(130))
        }
        #[cfg(not(feature = "std"))]
        {
            #[allow(static_mut_refs)]
            unsafe {
                if PALLAS_INTERPOLATOR.is_none() {
                    PALLAS_INTERPOLATOR = Some(Interpolator::new(130));
                }
                PALLAS_INTERPOLATOR.as_ref().unwrap()
            }
        }
    }
}

pub type Point = SwCurvePoint<PallasConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct PallasParams;
impl DiscreteLogParameter for PallasParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
