use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::{boxed::Box, fmt::Debug, marker::PhantomData, vec::Vec};
use core::ops::Add;
use generic_array::typenum::{Unsigned, U1};
use generic_array::{ArrayLength, GenericArray};

/// Trait for providing generator multiples (powers of 2).
pub trait GeneratorMultiplesSource<C: SWCurveConfig> {
    type Iter: Iterator<Item = Affine<C>>;

    /// Get an iterator over generator multiples: G, 2G, 4G, 8G, ...
    fn iter(&self) -> Self::Iter;
}

/// Iterator that doubles a point on each iteration.
pub struct DoublingIterator<C: SWCurveConfig> {
    current: Projective<C>,
}

impl<C: SWCurveConfig> Iterator for DoublingIterator<C> {
    type Item = Affine<C>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current;
        self.current = self.current.double();
        Some(result.into_affine())
    }
}

/// Implementation for direct computation from a generator point.
pub struct DirectGenerator<C: SWCurveConfig> {
    generator: Affine<C>,
}

impl<C: SWCurveConfig> DirectGenerator<C> {
    pub fn new(generator: Affine<C>) -> Self {
        Self { generator }
    }
}

impl<C: SWCurveConfig> GeneratorMultiplesSource<C> for DirectGenerator<C> {
    type Iter = DoublingIterator<C>;

    fn iter(&self) -> Self::Iter {
        DoublingIterator {
            current: self.generator.into_group(),
        }
    }
}

impl<'a, F: PrimeField, Parameters: DiscreteLogParameter, C: SWCurveConfig<BaseField = F>>
    GeneratorMultiplesSource<C> for &'a GeneratorTable<F, Parameters>
where
    Parameters: 'a,
{
    type Iter = GeneratorTableIter<'a, F, Parameters, C>;

    fn iter(&self) -> Self::Iter {
        GeneratorTableIter {
            table: self,
            index: 0,
            _phantom: PhantomData,
        }
    }
}

pub struct GeneratorTableIter<'a, F: PrimeField, Parameters: DiscreteLogParameter, C: SWCurveConfig>
{
    table: &'a GeneratorTable<F, Parameters>,
    index: usize,
    _phantom: PhantomData<C>,
}

impl<'a, F: PrimeField, Parameters: DiscreteLogParameter, C: SWCurveConfig<BaseField = F>> Iterator
    for GeneratorTableIter<'a, F, Parameters, C>
{
    type Item = Affine<C>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.table.0.len() {
            return None;
        }
        let (x, y) = self.table.0[self.index];
        self.index += 1;
        let point = Affine::<C>::new_unchecked(x, y);
        debug_assert!(
            point.is_on_curve(),
            "GeneratorTable entry is not on the curve"
        );
        Some(point)
    }
}

impl<C: SWCurveConfig> From<Affine<C>> for DirectGenerator<C> {
    fn from(generator: Affine<C>) -> Self {
        DirectGenerator::new(generator)
    }
}

/// Parameters for a discrete logarithm proof.
pub trait DiscreteLogParameter: Debug + Clone {
    /// The amount of bits used to represent a scalar.
    type ScalarBits: ArrayLength + Add<U1, Output: ArrayLength>;
}

/// A tabled generator for proving/verifying discrete logarithm claims.
#[derive(Debug, Clone)]
pub struct GeneratorTable<F: PrimeField, Parameters: DiscreteLogParameter>(
    /// Contains (x, y) coordinates of the generator multiplied by powers of two as `[G, 2G, 4G, ..., 2^s.G]` where `s` is `ScalarBits`.
    pub Box<GenericArray<(F, F), Parameters::ScalarBits>>,
);

impl<F: PrimeField, Parameters: DiscreteLogParameter> CanonicalSerialize
    for GeneratorTable<F, Parameters>
{
    fn serialize_with_mode<W: Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        for (x, y) in self.0.iter() {
            x.serialize_with_mode(&mut writer, compress)?;
            y.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        let size_per_element = F::default().serialized_size(compress) * 2;
        size_per_element * Parameters::ScalarBits::USIZE
    }
}

impl<F: PrimeField, Parameters: DiscreteLogParameter> Valid for GeneratorTable<F, Parameters> {
    fn check(&self) -> Result<(), SerializationError> {
        for (x, y) in self.0.iter() {
            x.check()?;
            y.check()?;
        }
        Ok(())
    }
}

impl<F: PrimeField, Parameters: DiscreteLogParameter> CanonicalDeserialize
    for GeneratorTable<F, Parameters>
{
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut array = Box::new(GenericArray::default());
        for i in 0..Parameters::ScalarBits::USIZE {
            let x = F::deserialize_with_mode(&mut reader, compress, validate)?;
            let y = F::deserialize_with_mode(&mut reader, compress, validate)?;
            array[i] = (x, y);
        }
        Ok(Self(array))
    }
}

impl<F: PrimeField, Parameters: DiscreteLogParameter> GeneratorTable<F, Parameters> {
    /// Create a new table for this generator.
    pub fn new<C: SWCurveConfig<BaseField = F>>(generator: Projective<C>) -> Self {
        let mut points = Vec::with_capacity(Parameters::ScalarBits::USIZE);
        points.push(generator);
        for i in 1..Parameters::ScalarBits::USIZE {
            points.push(points[i - 1].double());
        }

        let mut res = Self(Box::new(GenericArray::default()));
        let affines = Projective::<C>::normalize_batch(&points);
        for (i, aff) in affines.into_iter().enumerate() {
            res.0[i] = (aff.x, aff.y);
        }
        res
    }

    pub fn generator<C: SWCurveConfig<BaseField = F>>(&self) -> Projective<C> {
        let point = Affine::<C>::new_unchecked(self.0[0].0, self.0[0].1);
        debug_assert!(
            point.is_on_curve(),
            "GeneratorTable first entry is not on the curve"
        );
        point.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{DiscreteLogParameter, GeneratorTable};
    use ark_ec::short_weierstrass::Projective;
    use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use rand::prelude::StdRng;
    use rand_core::SeedableRng;

    use crate::curves::pallas::PallasParams;
    use ark_pallas::{Fq, Fr, PallasConfig};
    type PallasBase = Fq;

    use crate::curves::vesta::VestaParams;
    use ark_vesta::VestaConfig;
    type VestaBase = Fr;

    use crate::curves::helios::HeliosParams;
    use ark_helios::HeliosConfig;
    type HeliosBase = ark_helios::Fq;

    use crate::curves::selene::SeleneParams;
    use ark_selene::SeleneConfig;
    type SeleneBase = ark_selene::Fq;

    use crate::curves::wei25519::Wei25519Params;
    use ark_wei25519::Wei25519Config;
    type Wei25519Base = ark_wei25519::Fq;

    fn to_xy_helper<C: SWCurveConfig>(p: Projective<C>) -> Option<(C::BaseField, C::BaseField)> {
        let a = p.into_affine();
        if a.is_zero() {
            None
        } else {
            Some((a.x, a.y))
        }
    }

    #[test]
    fn generator_table_creation() {
        fn check<C: SWCurveConfig<BaseField = B>, Params: DiscreteLogParameter, B: PrimeField>() {
            let mut rng = StdRng::seed_from_u64(0);
            let generator = Projective::<C>::rand(&mut rng);
            let (gx, gy) = to_xy_helper::<C>(generator).unwrap();

            // Create generator table
            let table = GeneratorTable::<B, Params>::new::<C>(generator);

            // Verify the table has the right size
            let expected_size = Params::ScalarBits::USIZE;
            assert_eq!(table.0.len(), expected_size);

            // Verify first entry is the generator
            assert_eq!(table.0[0], (gx, gy));
            for i in 1..expected_size {
                let g_i = generator * <C as CurveConfig>::ScalarField::from(2u64).pow(&[i as u64]);
                let (gx_i, gy_i) = to_xy_helper::<C>(g_i).unwrap();
                assert_eq!(table.0[i], (gx_i, gy_i));
            }
        }

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase>();

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase>();

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase>();

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase>();

        println!("Testing Wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base>();
    }

    #[test]
    fn generator_table_serialization() {
        fn check<C: SWCurveConfig<BaseField = B>, Params: DiscreteLogParameter, B: PrimeField>() {
            let mut rng = StdRng::seed_from_u64(42);

            for _ in 0..10 {
                let generator = Projective::<C>::rand(&mut rng);
                let table = GeneratorTable::<B, Params>::new::<C>(generator);

                let mut serialized = Vec::new();
                table.serialize_compressed(&mut serialized).unwrap();

                let deserialized =
                    GeneratorTable::<B, Params>::deserialize_compressed(&serialized[..]).unwrap();

                let gen1 = table.generator::<C>();
                let gen2 = deserialized.generator::<C>();
                let (gen1_x, gen1_y) = to_xy_helper::<C>(gen1).unwrap();
                let (gen2_x, gen2_y) = to_xy_helper::<C>(gen2).unwrap();
                assert_eq!(gen1_x, gen2_x);
                assert_eq!(gen1_y, gen2_y);

                for (i, ((x1, y1), (x2, y2))) in
                    table.0.iter().zip(deserialized.0.iter()).enumerate()
                {
                    assert_eq!(x1, x2, "Mismatch at index {} for x coordinate", i);
                    assert_eq!(y1, y2, "Mismatch at index {} for y coordinate", i);
                }
            }
        }

        println!("Testing Pallas");
        check::<PallasConfig, PallasParams, PallasBase>();

        println!("Testing Vesta");
        check::<VestaConfig, VestaParams, VestaBase>();

        println!("Testing Helios");
        check::<HeliosConfig, HeliosParams, HeliosBase>();

        println!("Testing Selene");
        check::<SeleneConfig, SeleneParams, SeleneBase>();

        println!("Testing Wei25519");
        check::<Wei25519Config, Wei25519Params, Wei25519Base>();
    }
}
