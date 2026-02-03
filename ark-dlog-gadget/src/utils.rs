use ark_std::marker::PhantomData;
use ark_std::ops::Neg;
use ark_ff::{Field, PrimeField};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable};
use zeroize::{Zeroize, ZeroizeOnDrop};
use ark_ec_divisors::{DivisorCurve, DivisorPoly, ScalarDecomposition};
use ark_ec_divisors::util::GeneratorMultiplesSource;
use crate::error::Error;


/// Result of scalar multiplication with its divisor for zero-knowledge proofs.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct ScalarMulAndDivisor<C: DivisorCurve> {
  /// The point resulting from this scalar multiplication.
  pub point: C,
  /// The `x` coordinate of the result of this scalar multiplication.
  pub x: C::BaseField,
  /// The `y` coordinate of the result of this scalar multiplication.
  pub y: C::BaseField,
  /// The divisor interpolating the inverse of this result with instances of `2**i G`, where `G` is
  /// some generator.
  pub divisor: DivisorPoly<C::BaseField>,
}

impl<C: DivisorCurve> ScalarMulAndDivisor<C> {
  /// Create a new ScalarMulAndDivisor from a scalar and generator source.
  pub fn new<G: GeneratorMultiplesSource<C>>(
    scalar: &ScalarDecomposition<C::ScalarField>,
    generator_source: G,
  ) -> Result<Self, Error>
  where
      G: Clone,
  {
    // Get the first generator to compute the result point
    let generator = {
      let mut iter = generator_source.clone().iter();
      iter.next().ok_or(Error::NoGenerators)?
    };

    let point = generator.mul(*scalar.scalar());
    let (x, y) = C::to_xy(point).ok_or(Error::PointAtInfinity)?;
    let divisor = scalar.scalar_mul_divisor(generator_source)?.normalize_x_coefficient();
    Ok(ScalarMulAndDivisor { point, x, y, divisor })
  }
}

/// The specification of a short Weierstrass curve over the field `F`.
///
/// The short Weierstrass curve is defined via the formula `y**2 = x**3 + a*x + b`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CurveSpec<F> {
  /// The `a` constant in the curve formula.
  pub a: F,
  /// The `b` constant in the curve formula.
  pub b: F,
}

/// A struct for a point on a towered curve which has been confirmed to be on-curve.
#[derive(Clone, Debug)]
pub struct OnCurve<F: PrimeField> {
  pub x: LinearCombination<F>,
  pub y: LinearCombination<F>,
}

/// Enforce (x, y) form a valid curve point
pub fn on_curve<F: PrimeField, Cs: ConstraintSystem<F>>(
  cs: &mut Cs,
  point: OnCurve<F>,
  curve: &CurveSpec<F>,
) {
  let x_lc = point.x;
  let y_lc = point.y;

  let (_, _, x_squared) = cs.multiply(x_lc.clone(), x_lc.clone());
  let (_, _, x_cubed) = cs.multiply(x_lc, x_squared.into());
  let (_, _, y_squared) = cs.multiply(y_lc.clone(), y_lc);

  // x^3 + A*x^2 + B - y^2 = 0
  cs.constrain(
    LinearCombination::<F>::from(x_cubed)
      + LinearCombination::<F>::from(x_squared).scalar_mul(curve.a)
      + curve.b
      - y_squared,
  )
}

/// Incomplete public addition of an elliptic curve point.
///
/// This constrains that `c = a + b` where:
/// - `a` is a fixed public point (given as coordinates)
/// - `b` is a variable point already verified to be on-curve
/// - `c` is the claimed sum, also verified to be on-curve
///
/// The function checks that `a.x != b.x` to ensure the addition is valid (non-infinite result).
///
/// The addition formula uses the slope λ = (b.y - a.y) / (b.x - a.x)
/// And constrains:
/// - λ * (b.x - a.x) = b.y - a.y
/// - λ * (c.x - a.x) = -c.y - a.y  
/// - λ * λ = a.x + b.x + c.x
/// TODO: "incomplete" is misleading, its not incomplete in the sense of elliptic curve formula
pub fn incomplete_add_pub<F: PrimeField, Cs: ConstraintSystem<F>>(
  cs: &mut Cs,
  a: (F, F),
  b: OnCurve<F>,
  c: OnCurve<F>,
) -> OnCurve<F> {
  let (a_x, a_y) = a;

  // Use the linear combinations directly
  let b_x_lc = b.x;
  let b_y_lc = b.y;
  let c_x_lc = c.x;
  let c_y_lc = c.y;

  // Calculate (b.x - a.x) and (b.y - a.y) as linear combinations
  let b_x_minus_a_x = b_x_lc.clone() - a_x;
  let b_y_minus_a_y = b_y_lc.clone() - a_y;
  let c_x_minus_a_x = c_x_lc.clone() - a_x;
  // let c_y_minus_a_y = c_y_lc.clone() - a_y;

  // Check b.x != a.0
  inequality(cs, b_x_lc.clone(), LinearCombination::<F>::from(a_x));

  // slope of line through (b_x, b_y) and (a_x, a_y)
  let slope = cs.evaluate(&b_y_lc).map(|b_y| {
    let b_x = cs.evaluate(&b_x_lc).unwrap();
    let b_x_minus_a_x_inv = (b_x - a_x).inverse().unwrap();
    (b_y - a_y) * b_x_minus_a_x_inv
  });

  let slope_lc = LinearCombination::<F>::from(cs.allocate(slope).unwrap());
  // slope * (b_x - a_x) = b_y - a_y
  // let b_x_minus_a_x_val = cs.evaluate(&b_x_minus_a_x);
  let (_, _, o) = cs.multiply(slope_lc.clone(), b_x_minus_a_x);
  cs.constrain(LinearCombination::<F>::from(o) - b_y_minus_a_y);

  // Since the line through (x1, y1) and (x0, y0) also intersects (-x2, y2) as as (x1, y1) + (x0, y0) = (x2, y2)
  // `slope` also slope of line through (x0, y0) and (x2, -y2), slope = -y2 - y0 / (x2 - x0)
  // slope * (c_x - a_x) = -c_y - a_y
  let (_, _, o) = cs.multiply(slope_lc.clone(), c_x_minus_a_x);
  let minus_cy_minus_ay = c_y_lc.clone().neg() - a_y;
  cs.constrain(LinearCombination::<F>::from(o) - minus_cy_minus_ay);

  // slope * slope = a_x + b_x + c_x
  let (_, _, o) = cs.multiply(slope_lc.clone(), slope_lc);
  cs.constrain(LinearCombination::<F>::from(o) - (b_x_lc + c_x_lc.clone() + a_x));

  OnCurve { x: c_x_lc, y: c_y_lc }
}

pub fn inverse<F: Field, Cs: ConstraintSystem<F>>(
  cs: &mut Cs,
  x_lc: LinearCombination<F>,
) -> LinearCombination<F> {
  // one = 1
  let one = LinearCombination::<F>::from(Variable::One(PhantomData::<F>));
  #[cfg(debug_assertions)]
  {
    let o = cs.evaluate(&one);
    if o.is_some() {
      assert_eq!(F::ONE, o.unwrap());
    }
  }
  let x_inv = cs.evaluate(&x_lc).map(|x| x.inverse().unwrap());
  let x_inv_lc: LinearCombination<F> = cs.allocate(x_inv).unwrap().into();
  let (_, _, o) = cs.multiply(x_lc, x_inv_lc.clone());
  cs.constrain(LinearCombination::<F>::from(o) - one);
  x_inv_lc
}

pub fn inequality<F: Field, Cs: ConstraintSystem<F>>(
  cs: &mut Cs,
  x_lc: LinearCombination<F>,
  y_lc: LinearCombination<F>,
) {
  inverse(cs, x_lc - y_lc);
}

#[cfg(test)]
mod tests {
  use std::time::{Instant};
  use ark_ec::{AffineRepr, CurveGroup};
  use super::*;
  use ark_pallas::{Affine as PallasAffine, Fq, Fr};
  use ark_vesta::Affine as VestaAffine;
  use bulletproofs::{BulletproofGens, PedersenGens};
  use bulletproofs::r1cs::{Prover, Verifier};
  use rand::prelude::StdRng;
  use rand_core::SeedableRng;
  use rand;
  use dock_crypto_utils::transcript::MerlinTranscript;

  type PallasBase = Fq;
  type PallasScalar = Fr;
  type VestaBase = Fr;
  type VestaScalar = Fq;

  #[test]
  fn test_on_curve() {
    fn check<
      C: AffineRepr<BaseField = B, ScalarField = S>,
      B: PrimeField,
      S: PrimeField,
      BP: AffineRepr<ScalarField = B, BaseField = S>,
    >() {
      let mut rng = StdRng::seed_from_u64(0);

      // Create curve spec: y^2 = x^3 + 5
      let curve = CurveSpec::<B> { a: B::ZERO, b: B::from(5u64) };

      // Create Pedersen generators
      let pc_gens = PedersenGens::<BP>::default();
      let bp_gens = BulletproofGens::<BP>::new(32, 1);

      let count = 50;
      let mut proving_times = Vec::with_capacity(count);
      let mut verifying_times = Vec::with_capacity(count);

      for _ in 0..count {
        let scalar = S::rand(&mut rng);
        let point = C::generator().mul(scalar).into_affine();
        let (x, y) = point.xy().unwrap();

        // Test with prover - just verify constraints can be created
        let transcript = MerlinTranscript::new(b"test-on-curve");
        let mut prover = Prover::new(&pc_gens, transcript);

        let blinding_x = B::rand(&mut rng);
        let blinding_y = B::rand(&mut rng);
        let (x_comm, x_var) = prover.commit(x, blinding_x);
        let (y_comm, y_var) = prover.commit(y, blinding_y);

        let point =
          OnCurve { x: LinearCombination::from(x_var), y: LinearCombination::from(y_var) };
        on_curve(&mut prover, point, &curve);

        // Prove and measure time
        let prove_start = Instant::now();
        let proof = prover.prove(&bp_gens).unwrap();
        proving_times.push(prove_start.elapsed());

        // Verify and measure time
        let transcript = MerlinTranscript::new(b"test-on-curve");
        let mut verifier = Verifier::new(transcript);
        let x_var = verifier.commit(x_comm);
        let y_var = verifier.commit(y_comm);

        let point =
          OnCurve { x: LinearCombination::from(x_var), y: LinearCombination::from(y_var) };
        on_curve(&mut verifier, point, &curve);

        let verify_start = Instant::now();
        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        verifying_times.push(verify_start.elapsed());
      }

      proving_times.sort();
      verifying_times.sort();
      let median_prove = proving_times[count / 2];
      let median_verify = verifying_times[count / 2];

      println!(
        "For {count} iterations, median proving time: {:?}, median verification time: {:?}",
        median_prove, median_verify
      );
    }

    println!("Testing Pallas");
    check::<PallasAffine, PallasBase, PallasScalar, VestaAffine>();
    println!("Testing Vesta");
    check::<VestaAffine, VestaBase, VestaScalar, PallasAffine>();
  }

  #[test]
  fn test_incomplete_add_pub() {
    fn check<
      C: AffineRepr<BaseField = B, ScalarField = S>,
      B: PrimeField,
      S: PrimeField,
      BP: AffineRepr<ScalarField = B, BaseField = S>,
    >() {
      let mut rng = StdRng::seed_from_u64(0);

      let generator = C::generator();
      let pc_gens = PedersenGens::<BP>::default();
      let bp_gens = BulletproofGens::<BP>::new(128, 1);

      let scalar1 = S::rand(&mut rng);
      let point1 = generator.mul(scalar1).into_affine();

      let count = 50;
      let mut proving_times = Vec::with_capacity(count);
      let mut verifying_times = Vec::with_capacity(count);

      let mut num_constraints = 0;

      for _ in 0..count {
        let scalar2 = S::rand(&mut rng);
        let point2 = generator.mul(scalar2).into_affine();

        assert_ne!(point1, point2);

        let (x1, y1) = point1.xy().unwrap();
        let (x2, y2) = point2.xy().unwrap();

        // Compute the sum using projective arithmetic
        let sum = (point1 + point2).into_affine();
        let (sum_x, sum_y) = sum.xy().unwrap();

        // Test with prover
        let transcript = MerlinTranscript::new(b"test-incomplete-add");
        let mut prover = Prover::new(&pc_gens, transcript);

        let blinding1 = B::rand(&mut rng);
        let blinding2 = B::rand(&mut rng);
        let blinding3 = B::rand(&mut rng);
        let blinding4 = B::rand(&mut rng);

        let (x2_comm, x2_var) = prover.commit(x2, blinding1);
        let (y2_comm, y2_var) = prover.commit(y2, blinding2);
        let (sum_x_comm, sum_x_var) = prover.commit(sum_x, blinding3);
        let (sum_y_comm, sum_y_var) = prover.commit(sum_y, blinding4);

        let point2_on_curve =
          OnCurve { x: LinearCombination::from(x2_var), y: LinearCombination::from(y2_var) };
        let sum_on_curve =
          OnCurve { x: LinearCombination::from(sum_x_var), y: LinearCombination::from(sum_y_var) };

        let OnCurve { x: c_x, y: c_y } =
          incomplete_add_pub(&mut prover, (x1, y1), point2_on_curve, sum_on_curve);

        assert_eq!(sum_x, prover.eval(&c_x.into()));
        assert_eq!(sum_y, prover.eval(&c_y.into()));

        num_constraints = prover.constraints.len();

        // Prove and measure time
        let prove_start = Instant::now();
        let proof = prover.prove(&bp_gens).unwrap();
        proving_times.push(prove_start.elapsed());

        // Verify and measure time
        let transcript = MerlinTranscript::new(b"test-incomplete-add");
        let mut verifier = Verifier::new(transcript);
        let x2_var = verifier.commit(x2_comm);
        let y2_var = verifier.commit(y2_comm);
        let sum_x_var = verifier.commit(sum_x_comm);
        let sum_y_var = verifier.commit(sum_y_comm);

        let point2_on_curve =
          OnCurve { x: LinearCombination::from(x2_var), y: LinearCombination::from(y2_var) };
        let sum_on_curve =
          OnCurve { x: LinearCombination::from(sum_x_var), y: LinearCombination::from(sum_y_var) };

        incomplete_add_pub(&mut verifier, (x1, y1), point2_on_curve, sum_on_curve);

        let verify_start = Instant::now();
        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        verifying_times.push(verify_start.elapsed());
      }

      proving_times.sort();
      verifying_times.sort();
      let median_prove = proving_times[count / 2];
      let median_verify = verifying_times[count / 2];

      println!(
        "For {count} iterations, {num_constraints} constraints, median proving time: {:?}, median verification time: {:?}",
        median_prove, median_verify
      );
    }

    println!("Testing Pallas");
    check::<PallasAffine, PallasBase, PallasScalar, VestaAffine>();
    println!("Testing Vesta");
    check::<VestaAffine, VestaBase, VestaScalar, PallasAffine>();
  }
}

