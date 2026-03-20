use crate::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, Read, SerializationError, Valid, Validate,
    Write,
};
use ark_std::{fmt::Debug, marker::PhantomData, vec::Vec};
use core::ops::Add;
use generic_array::typenum::{U1, Unsigned};
use generic_array::{ArrayLength, GenericArray};

/// Trait for providing generator multiples (powers of 2).
pub trait GeneratorMultiplesSource<C: DivisorCurve> {
    type Iter: Iterator<Item = C>;

    /// Get an iterator over generator multiples: G, 2G, 4G, 8G, ...
    fn iter(&self) -> Self::Iter;
}

/// Iterator that doubles a point on each iteration.
pub struct DoublingIterator<C: DivisorCurve> {
    current: C,
}

impl<C: DivisorCurve> Iterator for DoublingIterator<C> {
    type Item = C;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current;
        self.current = self.current.double();
        Some(result)
    }
}

/// Implementation for direct computation from a generator point.
pub struct DirectGenerator<C: DivisorCurve> {
    generator: C,
}

impl<C: DivisorCurve> DirectGenerator<C> {
    pub fn new(generator: C) -> Self {
        Self { generator }
    }
}

impl<C: DivisorCurve> GeneratorMultiplesSource<C> for DirectGenerator<C> {
    type Iter = DoublingIterator<C>;

    fn iter(&self) -> Self::Iter {
        DoublingIterator {
            current: C::from(self.generator),
        }
    }
}

impl<'a, F: PrimeField, Parameters: DiscreteLogParameter, C: DivisorCurve<BaseField = F>>
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

pub struct GeneratorTableIter<'a, F: PrimeField, Parameters: DiscreteLogParameter, C: DivisorCurve>
{
    table: &'a GeneratorTable<F, Parameters>,
    index: usize,
    _phantom: PhantomData<C>,
}

impl<'a, F: PrimeField, Parameters: DiscreteLogParameter, C: DivisorCurve<BaseField = F>> Iterator
    for GeneratorTableIter<'a, F, Parameters, C>
{
    type Item = C;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.table.0.len() {
            return None;
        }
        let (x, y) = self.table.0[self.index];
        self.index += 1;
        Some(C::from_xy_unchecked(x, y))
    }
}

impl<C: DivisorCurve> From<C> for DirectGenerator<C> {
    fn from(generator: C) -> Self {
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
    pub GenericArray<(F, F), Parameters::ScalarBits>,
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
        let mut array = GenericArray::default();
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
    pub fn new<C: DivisorCurve<BaseField = F>>(generator: C) -> Self {
        let mut points = Vec::with_capacity(Parameters::ScalarBits::USIZE);
        points.push(generator);
        for i in 1..Parameters::ScalarBits::USIZE {
            points.push(points[i - 1].double());
        }

        let mut res = Self(GenericArray::default());
        for (i, (x, y)) in C::batch_to_xy(&points).into_iter().enumerate() {
            res.0[i] = (x, y);
        }
        res
    }

    pub fn generator<C: DivisorCurve<BaseField = F>>(&self) -> C {
        C::from_xy_unchecked(self.0[0].0, self.0[0].1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{DiscreteLogParameter, GeneratorTable};
    use ark_ff::Field;
    use rand::prelude::StdRng;
    use rand_core::SeedableRng;

    use crate::curves::pallas::{PallasParams, Point as PallasPoint};
    use ark_pallas::{Fq, Fr};

    use crate::curves::vesta::{Point as VestaPoint, VestaParams};

    type PallasBase = Fq;

    type VestaBase = Fr;

    use crate::curves::helios::{HeliosParams, Point as HeliosPoint};
    type HeliosBase = ark_helios::Fq;

    use crate::curves::selene::{Point as SelenePoint, SeleneParams};
    type SeleneBase = ark_selene::Fq;

    use crate::curves::wei25519::{Point as Wei25519Point, Wei25519Params};
    type Wei25519Base = ark_wei25519::Fq;

    #[test]
    fn generator_table_creation() {
        fn check<C: DivisorCurve<BaseField = B>, Params: DiscreteLogParameter, B: PrimeField>() {
            let mut rng = StdRng::seed_from_u64(0);
            let generator = C::random(&mut rng);
            let (gx, gy) = C::to_xy(generator).unwrap();

            // Create generator table
            let table = GeneratorTable::<B, Params>::new(generator);

            // Verify the table has the right size
            let expected_size = Params::ScalarBits::USIZE;
            assert_eq!(table.0.len(), expected_size);

            // Verify first entry is the generator
            assert_eq!(table.0[0], (gx, gy));
            for i in 1..expected_size {
                let g_i = C::mul(generator, C::ScalarField::from(2).pow(&[i as u64]));
                let (gx_i, gy_i) = C::to_xy(g_i).unwrap();
                assert_eq!(table.0[i], (gx_i, gy_i));
            }
        }

        println!("Testing Pallas");
        check::<PallasPoint, PallasParams, PallasBase>();

        println!("Testing Vesta");
        check::<VestaPoint, VestaParams, VestaBase>();

        println!("Testing Helios");
        check::<HeliosPoint, HeliosParams, HeliosBase>();

        println!("Testing Selene");
        check::<SelenePoint, SeleneParams, SeleneBase>();

        println!("Testing Wei25519");
        check::<Wei25519Point, Wei25519Params, Wei25519Base>();
    }

    #[test]
    fn generator_table_serialization() {
        fn check<C: DivisorCurve<BaseField = B>, Params: DiscreteLogParameter, B: PrimeField>() {
            let mut rng = StdRng::seed_from_u64(42);

            for _ in 0..10 {
                let generator = C::random(&mut rng);
                let table = GeneratorTable::<B, Params>::new(generator);

                let mut serialized = Vec::new();
                table.serialize_compressed(&mut serialized).unwrap();

                let deserialized =
                    GeneratorTable::<B, Params>::deserialize_compressed(&serialized[..]).unwrap();

                let gen1 = table.generator::<C>();
                let gen2 = deserialized.generator::<C>();
                let (gen1_x, gen1_y) = C::to_xy(gen1).unwrap();
                let (gen2_x, gen2_y) = C::to_xy(gen2).unwrap();
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
        check::<PallasPoint, PallasParams, PallasBase>();

        println!("Testing Vesta");
        check::<VestaPoint, VestaParams, VestaBase>();

        println!("Testing Helios");
        check::<HeliosPoint, HeliosParams, HeliosBase>();

        println!("Testing Selene");
        check::<SelenePoint, SeleneParams, SeleneBase>();

        println!("Testing Wei25519");
        check::<Wei25519Point, Wei25519Params, Wei25519Base>();
    }
}
