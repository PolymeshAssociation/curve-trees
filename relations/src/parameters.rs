use crate::error::Error;
use crate::lookup::Lookup3Bit;
use crate::rerandomize::build_tables;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_ec_divisors::util::GeneratorTable;
use ark_ec_divisors::DivisorCurve;
use ark_ff::{PrimeField, Zero};
use ark_pallas::{Affine as PallasAffine, PallasConfig};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use ark_vesta::{Affine as VestaAffine, VestaConfig};
use bulletproofs::hash_to_curve_pasta::{hash_to_pallas, hash_to_vesta};
use bulletproofs::{affine_from_bytes_tai, BulletproofGens, PedersenGens};
use core::iter;

pub trait SelRerandParametersRef<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    fn even_parameters(&self) -> &SingleLayerParameters<P0>;
    fn odd_parameters(&self) -> &SingleLayerParameters<P1>;
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy, T: SelRerandParametersRef<P0, P1>>
    SelRerandParametersRef<P0, P1> for &T
{
    fn even_parameters(&self) -> &SingleLayerParameters<P0> {
        (*self).even_parameters()
    }

    fn odd_parameters(&self) -> &SingleLayerParameters<P1> {
        (*self).odd_parameters()
    }
}

pub trait SelRerandProofParametersRef<
    P0: SWCurveConfig<BaseField: PrimeField> + Copy,
    P1: SWCurveConfig<BaseField: PrimeField> + Copy,
    DLogParams0: DiscreteLogParameters,
    DLogParams1: DiscreteLogParameters,
>
{
    fn even_parameters(&self) -> &SingleLayerProofParametersNew<P0, DLogParams1>;
    fn odd_parameters(&self) -> &SingleLayerProofParametersNew<P1, DLogParams0>;
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleLayerParameters<P: SWCurveConfig + Copy> {
    pub bp_gens: BulletproofGens<Affine<P>>,
    pub pc_gens: PedersenGens<Affine<P>>,
    pub delta: Affine<P>,
}

impl<P: SWCurveConfig + Copy> SingleLayerParameters<P> {
    pub fn new(generators_length: u32) -> Result<Self, Error> {
        let pc_gens = PedersenGens::<Affine<P>>::new().ok_or_else(|| {
            Error::GenerationError("Failed to generate Pedersen generators".into())
        })?;

        Ok(SingleLayerParameters {
            bp_gens: BulletproofGens::<Affine<P>>::new(generators_length, 1),
            pc_gens,
            delta: affine_from_bytes_tai(b"curve_trees_delta")
                .ok_or_else(|| Error::GenerationError("Failed to generate delta".into()))?,
        })
    }

    pub fn commit(
        &self,
        v: &[P::ScalarField],
        v_blinding: P::ScalarField,
        generator_set_index: u32,
    ) -> Affine<P> {
        let gens = self
            .bp_gens
            .share(0)
            .G((v.len() * (generator_set_index as usize + 1)) as u32)
            .skip(v.len() * generator_set_index as usize);

        let (generators, scalars) = if v_blinding.is_zero() {
            (
                gens.copied().collect::<Vec<_>>(),
                v.iter()
                    .map(|s| {
                        let s: P::ScalarField = *s;
                        s
                    })
                    .collect::<Vec<_>>(),
            )
        } else {
            (
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens)
                    .copied()
                    .collect::<Vec<_>>(),
                iter::once(&v_blinding)
                    .chain(v.iter())
                    .map(|s| {
                        let s: P::ScalarField = *s;
                        s
                    })
                    .collect::<Vec<_>>(),
            )
        };

        let comm = <Affine<P> as AffineRepr>::Group::msm(generators.as_slice(), scalars.as_slice());
        comm.unwrap().into_affine()
    }

    pub fn commit_for_default_node(
        &self,
        x: P::ScalarField,
        count: u32,
        generator_set_index: u32,
    ) -> Affine<P> {
        let gens = self
            .bp_gens
            .share(0)
            .G(count * (generator_set_index + 1))
            .skip((count * generator_set_index) as usize);
        let g = gens.copied().sum::<<Affine<P> as AffineRepr>::Group>();

        (g * x).into_affine()
    }

    pub fn bp_gens(&self) -> &BulletproofGens<Affine<P>> {
        &self.bp_gens
    }

    pub fn pc_gens(&self) -> &PedersenGens<Affine<P>> {
        &self.pc_gens
    }

    pub fn delta(&self) -> Affine<P> {
        self.delta
    }
}

macro_rules! impl_single_layer_parameters_new_using_label {
    ($config:ty, $affine:ty, $hash_fn:ident, $curve_name:literal) => {
        impl SingleLayerParameters<$config> {
            pub fn new_using_label(label: &[u8], generators_length: u32) -> Result<Self, Error> {
                let pc_gens = PedersenGens::<$affine>::new_using_label(label);
                let bp_gens =
                    BulletproofGens::<$affine>::new_using_label(label, generators_length, 1);
                let delta = $hash_fn($curve_name.as_bytes(), b"curve_trees_delta").into_affine();

                Ok(SingleLayerParameters {
                    bp_gens,
                    pc_gens,
                    delta,
                })
            }
        }
    };
}

impl_single_layer_parameters_new_using_label!(PallasConfig, PallasAffine, hash_to_pallas, "pallas");
impl_single_layer_parameters_new_using_label!(VestaConfig, VestaAffine, hash_to_vesta, "vesta");

/// Parameters for multi level select and rerandomize over a 2-cycle of curves
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SelRerandParameters<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    pub even_parameters: SingleLayerParameters<P0>,
    pub odd_parameters: SingleLayerParameters<P1>,
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> SelRerandParameters<P0, P1> {
    pub fn new(even_generators_length: u32, odd_generators_length: u32) -> Result<Self, Error> {
        Ok(SelRerandParameters {
            even_parameters: SingleLayerParameters::<P0>::new(even_generators_length)?,
            odd_parameters: SingleLayerParameters::<P1>::new(odd_generators_length)?,
        })
    }

    pub fn bp_gens(&self) -> (&BulletproofGens<Affine<P0>>, &BulletproofGens<Affine<P1>>) {
        (&self.even_parameters.bp_gens, &self.odd_parameters.bp_gens)
    }

    pub fn pc_gens(&self) -> (&PedersenGens<Affine<P0>>, &PedersenGens<Affine<P1>>) {
        (&self.even_parameters.pc_gens, &self.odd_parameters.pc_gens)
    }
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> SelRerandParametersRef<P0, P1>
    for SelRerandParameters<P0, P1>
{
    fn even_parameters(&self) -> &SingleLayerParameters<P0> {
        &self.even_parameters
    }

    fn odd_parameters(&self) -> &SingleLayerParameters<P1> {
        &self.odd_parameters
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleLayerProofParameters<P: SWCurveConfig + Copy> {
    pub sl_params: SingleLayerParameters<P>,
    pub tables: Vec<Lookup3Bit<2, P::BaseField>>,
}

impl<P: SWCurveConfig + Copy> SingleLayerProofParameters<P> {
    pub fn new(generators_length: u32) -> Result<Self, Error> {
        let sl_params = SingleLayerParameters::<P>::new(generators_length)?;
        let tables = build_tables(sl_params.pc_gens.B_blinding)?;
        Ok(Self { sl_params, tables })
    }

    pub fn bp_gens(&self) -> &BulletproofGens<Affine<P>> {
        self.sl_params.bp_gens()
    }

    pub fn pc_gens(&self) -> &PedersenGens<Affine<P>> {
        self.sl_params.pc_gens()
    }
}

impl<P: SWCurveConfig + Copy> From<SingleLayerParameters<P>> for SingleLayerProofParameters<P> {
    fn from(sl_params: SingleLayerParameters<P>) -> Self {
        let tables = build_tables(sl_params.pc_gens.B_blinding).expect("Failed to build tables");
        Self { sl_params, tables }
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SelRerandProofParameters<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> {
    pub even_parameters: SingleLayerProofParameters<P0>,
    pub odd_parameters: SingleLayerProofParameters<P1>,
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> SelRerandProofParameters<P0, P1> {
    pub fn new(even_generators_length: u32, odd_generators_length: u32) -> Result<Self, Error> {
        Ok(Self {
            even_parameters: SingleLayerProofParameters::new(even_generators_length)?,
            odd_parameters: SingleLayerProofParameters::new(odd_generators_length)?,
        })
    }

    pub fn bp_gens(&self) -> (&BulletproofGens<Affine<P0>>, &BulletproofGens<Affine<P1>>) {
        (
            self.even_parameters.bp_gens(),
            self.odd_parameters.bp_gens(),
        )
    }

    pub fn pc_gens(&self) -> (&PedersenGens<Affine<P0>>, &PedersenGens<Affine<P1>>) {
        (
            self.even_parameters.pc_gens(),
            self.odd_parameters.pc_gens(),
        )
    }
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> TryFrom<SelRerandParameters<P0, P1>>
    for SelRerandProofParameters<P0, P1>
{
    type Error = Error;

    fn try_from(sr_params: SelRerandParameters<P0, P1>) -> Result<Self, Self::Error> {
        let SelRerandParameters {
            even_parameters,
            odd_parameters,
        } = sr_params;
        Ok(Self {
            even_parameters: SingleLayerProofParameters::from(even_parameters),
            odd_parameters: SingleLayerProofParameters::from(odd_parameters),
        })
    }
}

impl<P0: SWCurveConfig + Copy, P1: SWCurveConfig + Copy> SelRerandParametersRef<P0, P1>
    for SelRerandProofParameters<P0, P1>
{
    fn even_parameters(&self) -> &SingleLayerParameters<P0> {
        &self.even_parameters.sl_params
    }

    fn odd_parameters(&self) -> &SingleLayerParameters<P1> {
        &self.odd_parameters.sl_params
    }
}

// A better way would be to make arkworks have BaseField as PrimeField
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SingleLayerProofParametersNew<
    P: SWCurveConfig<BaseField: PrimeField> + Copy,
    DLogParams: DiscreteLogParameters,
> {
    pub sl_params: SingleLayerParameters<P>,
    pub table_b_blinding: GeneratorTable<P::BaseField, DLogParams>,
    pub table_b: GeneratorTable<P::BaseField, DLogParams>,
}

impl<P: SWCurveConfig<BaseField: PrimeField> + Copy, DLogParams: DiscreteLogParameters>
    SingleLayerProofParametersNew<P, DLogParams>
{
    pub fn new(generators_length: u32) -> Result<Self, Error> {
        let sl_params = SingleLayerParameters::<P>::new(generators_length)?;
        Ok(Self::from_single_layer_params(sl_params))
    }

    pub fn from_single_layer_params(sl_params: SingleLayerParameters<P>) -> Self {
        let blinding_generator = sl_params.pc_gens.B_blinding.into_group();
        let table = GeneratorTable::<P::BaseField, DLogParams>::new(blinding_generator);
        let b_generator = sl_params.pc_gens.B.into_group();
        let table_b = GeneratorTable::<P::BaseField, DLogParams>::new(b_generator);
        Self {
            sl_params,
            table_b_blinding: table,
            table_b,
        }
    }

    pub fn bp_gens(&self) -> &BulletproofGens<Affine<P>> {
        self.sl_params.bp_gens()
    }

    pub fn pc_gens(&self) -> &PedersenGens<Affine<P>> {
        self.sl_params.pc_gens()
    }

    pub fn delta(&self) -> Affine<P> {
        self.sl_params.delta()
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SelRerandProofParametersNew<
    P0: SWCurveConfig<BaseField: PrimeField> + Copy,
    P1: SWCurveConfig<BaseField: PrimeField> + Copy,
    DLogParams0: DiscreteLogParameters,
    DLogParams1: DiscreteLogParameters,
> {
    pub even_parameters: SingleLayerProofParametersNew<P0, DLogParams1>,
    pub odd_parameters: SingleLayerProofParametersNew<P1, DLogParams0>,
}

pub struct SelRerandProofParametersRefNew<
    'a,
    P0: SWCurveConfig<BaseField: PrimeField> + Copy,
    P1: SWCurveConfig<BaseField: PrimeField> + Copy,
    DLogParams0: DiscreteLogParameters,
    DLogParams1: DiscreteLogParameters,
> {
    pub even_parameters: &'a SingleLayerProofParametersNew<P0, DLogParams1>,
    pub odd_parameters: &'a SingleLayerProofParametersNew<P1, DLogParams0>,
}

impl<
        'a,
        P0: SWCurveConfig<BaseField: PrimeField> + Copy,
        P1: SWCurveConfig<BaseField: PrimeField> + Copy,
        DLogParams0: DiscreteLogParameters,
        DLogParams1: DiscreteLogParameters,
    > SelRerandProofParametersRefNew<'a, P0, P1, DLogParams0, DLogParams1>
{
    pub fn new(
        even_parameters: &'a SingleLayerProofParametersNew<P0, DLogParams1>,
        odd_parameters: &'a SingleLayerProofParametersNew<P1, DLogParams0>,
    ) -> Self {
        Self {
            even_parameters,
            odd_parameters,
        }
    }
}

impl<
        P0: DivisorCurve + Copy,
        P1: DivisorCurve + Copy,
        DLog0: DiscreteLogParameters,
        DLog1: DiscreteLogParameters,
    > SelRerandProofParametersNew<P0, P1, DLog0, DLog1>
{
    pub fn new(even_generators_length: u32, odd_generators_length: u32) -> Result<Self, Error> {
        Ok(Self {
            even_parameters: SingleLayerProofParametersNew::<P0, DLog1>::new(
                even_generators_length,
            )?,
            odd_parameters: SingleLayerProofParametersNew::<P1, DLog0>::new(odd_generators_length)?,
        })
    }

    pub fn from_sr_params(sr_params: SelRerandParameters<P0, P1>) -> Self {
        let SelRerandParameters {
            even_parameters,
            odd_parameters,
        } = sr_params;
        Self {
            even_parameters: SingleLayerProofParametersNew::<P0, DLog1>::from_single_layer_params(
                even_parameters,
            ),
            odd_parameters: SingleLayerProofParametersNew::<P1, DLog0>::from_single_layer_params(
                odd_parameters,
            ),
        }
    }

    pub fn bp_gens(&self) -> (&BulletproofGens<Affine<P0>>, &BulletproofGens<Affine<P1>>) {
        (
            self.even_parameters.bp_gens(),
            self.odd_parameters.bp_gens(),
        )
    }

    pub fn pc_gens(&self) -> (&PedersenGens<Affine<P0>>, &PedersenGens<Affine<P1>>) {
        (
            self.even_parameters.pc_gens(),
            self.odd_parameters.pc_gens(),
        )
    }
}

impl<
        P0: SWCurveConfig<BaseField: PrimeField> + Copy,
        P1: SWCurveConfig<BaseField: PrimeField> + Copy,
        DLog0: DiscreteLogParameters,
        DLog1: DiscreteLogParameters,
    > SelRerandProofParametersRef<P0, P1, DLog0, DLog1>
    for SelRerandProofParametersNew<P0, P1, DLog0, DLog1>
{
    fn even_parameters(&self) -> &SingleLayerProofParametersNew<P0, DLog1> {
        &self.even_parameters
    }

    fn odd_parameters(&self) -> &SingleLayerProofParametersNew<P1, DLog0> {
        &self.odd_parameters
    }
}

impl<
        'a,
        P0: SWCurveConfig<BaseField: PrimeField> + Copy,
        P1: SWCurveConfig<BaseField: PrimeField> + Copy,
        DLog0: DiscreteLogParameters,
        DLog1: DiscreteLogParameters,
    > SelRerandProofParametersRef<P0, P1, DLog0, DLog1>
    for SelRerandProofParametersRefNew<'a, P0, P1, DLog0, DLog1>
{
    fn even_parameters(&self) -> &SingleLayerProofParametersNew<P0, DLog1> {
        self.even_parameters
    }

    fn odd_parameters(&self) -> &SingleLayerProofParametersNew<P1, DLog0> {
        self.odd_parameters
    }
}

impl<
        P0: SWCurveConfig<BaseField: PrimeField> + Copy,
        P1: SWCurveConfig<BaseField: PrimeField> + Copy,
        DLog0: DiscreteLogParameters,
        DLog1: DiscreteLogParameters,
        T: SelRerandProofParametersRef<P0, P1, DLog0, DLog1>,
    > SelRerandProofParametersRef<P0, P1, DLog0, DLog1> for &T
{
    fn even_parameters(&self) -> &SingleLayerProofParametersNew<P0, DLog1> {
        (*self).even_parameters()
    }

    fn odd_parameters(&self) -> &SingleLayerProofParametersNew<P1, DLog0> {
        (*self).odd_parameters()
    }
}

impl<
        'a,
        P0: SWCurveConfig<BaseField: PrimeField> + Copy,
        P1: SWCurveConfig<BaseField: PrimeField> + Copy,
        DLog0: DiscreteLogParameters,
        DLog1: DiscreteLogParameters,
    > SelRerandParametersRef<P0, P1> for SelRerandProofParametersNew<P0, P1, DLog0, DLog1>
{
    fn even_parameters(&self) -> &SingleLayerParameters<P0> {
        &self.even_parameters.sl_params
    }

    fn odd_parameters(&self) -> &SingleLayerParameters<P1> {
        &self.odd_parameters.sl_params
    }
}

impl<
        'a,
        P0: SWCurveConfig<BaseField: PrimeField> + Copy,
        P1: SWCurveConfig<BaseField: PrimeField> + Copy,
        DLog0: DiscreteLogParameters,
        DLog1: DiscreteLogParameters,
    > SelRerandParametersRef<P0, P1> for SelRerandProofParametersRefNew<'a, P0, P1, DLog0, DLog1>
{
    fn even_parameters(&self) -> &SingleLayerParameters<P0> {
        &self.even_parameters.sl_params
    }

    fn odd_parameters(&self) -> &SingleLayerParameters<P1> {
        &self.odd_parameters.sl_params
    }
}

macro_rules! impl_sel_rerand_new_using_label {
    (SelRerandParameters, $even_config:ty, $odd_config:ty) => {
        impl SelRerandParameters<$even_config, $odd_config> {
            pub fn new_using_label(
                label: &[u8],
                even_generators_length: u32,
                odd_generators_length: u32,
            ) -> Result<Self, Error> {
                Ok(Self {
                    even_parameters: SingleLayerParameters::<$even_config>::new_using_label(
                        label,
                        even_generators_length,
                    )?,
                    odd_parameters: SingleLayerParameters::<$odd_config>::new_using_label(
                        label,
                        odd_generators_length,
                    )?,
                })
            }
        }
    };
    (SelRerandProofParameters, $even_config:ty, $odd_config:ty) => {
        impl SelRerandProofParameters<$even_config, $odd_config> {
            pub fn new_using_label(
                label: &[u8],
                even_generators_length: u32,
                odd_generators_length: u32,
            ) -> Result<Self, Error> {
                Ok(Self {
                    even_parameters: SingleLayerProofParameters::from(
                        SingleLayerParameters::<$even_config>::new_using_label(label, even_generators_length)?
                    ),
                    odd_parameters: SingleLayerProofParameters::from(
                        SingleLayerParameters::<$odd_config>::new_using_label(label, odd_generators_length)?
                    ),
                })
            }
        }
    };
    (SelRerandProofParametersNew, $even_config:ty, $odd_config:ty, $dlog_params_0:ty, $dlog_params_1:ty) => {
        impl SelRerandProofParametersNew<$even_config, $odd_config, $dlog_params_0, $dlog_params_1> {
            pub fn new_using_label(
                label: &[u8],
                even_generators_length: u32,
                odd_generators_length: u32,
            ) -> Result<Self, Error> {
                Ok(Self {
                    even_parameters: SingleLayerProofParametersNew::<$even_config, $dlog_params_1>::from_single_layer_params(
                        SingleLayerParameters::<$even_config>::new_using_label(label, even_generators_length)?
                    ),
                    odd_parameters: SingleLayerProofParametersNew::<$odd_config, $dlog_params_0>::from_single_layer_params(
                        SingleLayerParameters::<$odd_config>::new_using_label(label, odd_generators_length)?
                    ),
                })
            }
        }
    };
}

impl_sel_rerand_new_using_label!(SelRerandParameters, PallasConfig, VestaConfig);
impl_sel_rerand_new_using_label!(SelRerandParameters, VestaConfig, PallasConfig);

impl_sel_rerand_new_using_label!(SelRerandProofParameters, PallasConfig, VestaConfig);
impl_sel_rerand_new_using_label!(SelRerandProofParameters, VestaConfig, PallasConfig);

impl_sel_rerand_new_using_label!(
    SelRerandProofParametersNew,
    PallasConfig,
    VestaConfig,
    PallasParams,
    VestaParams
);
impl_sel_rerand_new_using_label!(
    SelRerandProofParametersNew,
    VestaConfig,
    PallasConfig,
    VestaParams,
    PallasParams
);
