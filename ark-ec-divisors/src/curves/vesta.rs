use crate::Interpolator;
use crate::curves::sw::{HasInterpolator, SwCurvePoint};
use crate::util::DiscreteLogParameter;
use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use ark_vesta::{Fq, Fr, VestaConfig};
use generic_array::typenum::U;

#[cfg(feature = "std")]
static VESTA_INTERPOLATOR: spin::Once<Interpolator<Fq>> = spin::Once::new();

#[cfg(not(feature = "std"))]
static mut VESTA_INTERPOLATOR: Option<Interpolator<Fq>> = None;

impl HasInterpolator for VestaConfig {
    fn get_interpolator() -> &'static Interpolator<Fq>
    where
        Self: SWCurveConfig,
    {
        #[cfg(feature = "std")]
        {
            VESTA_INTERPOLATOR.call_once(|| Interpolator::new(130))
        }
        #[cfg(not(feature = "std"))]
        {
            #[allow(static_mut_refs)]
            unsafe {
                if VESTA_INTERPOLATOR.is_none() {
                    VESTA_INTERPOLATOR = Some(Interpolator::new(130));
                }
                VESTA_INTERPOLATOR.as_ref().unwrap()
            }
        }
    }
}

pub type Point = SwCurvePoint<VestaConfig>;

#[derive(Debug, PartialEq, Clone)]
pub struct VestaParams;
impl DiscreteLogParameter for VestaParams {
    type ScalarBits = U<{ Fr::MODULUS_BIT_SIZE as usize }>;
}
