use core::ops::{Add, Div, Sub};
use ark_std::{fmt::Debug, vec, vec::Vec};
use ark_ec::AffineRepr;
use ark_ff::{batch_inversion, BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use bulletproofs::BulletproofGens;
use generic_array::{ArrayLength, GenericArray};
use generic_array::typenum::{Diff, Quot, Sum, Unsigned, U1, U2};
use bulletproofs::r1cs::{constant, ConstraintSystem, LinearCombination, Prover, Variable, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use ark_ec_divisors::{DivisorCurve, ScalarDecomposition};
use ark_ec_divisors::util::{DiscreteLogParameter, GeneratorMultiplesSource, GeneratorTable};
use crate::utils::{incomplete_add_pub, inverse, on_curve, CurveSpec, OnCurve, ScalarMulAndDivisor};
use crate::error::Error;

pub const DECOMPOSITION_SIZE: usize = 256;

/// Derived parameters for a discrete logarithm proof.
///
/// This should not be directly implemented. `DiscreteLogParameter` should be implemented for which
/// this will then be automatically derived.
pub trait DiscreteLogParameters: DiscreteLogParameter {
  /// The number of `x**i` coefficients in a divisor.
  ///
  /// This is the number of points in a divisor (the number of bits in a scalar, plus one) divided
  /// by two.
  type XCoefficients: ArrayLength;

  /// The number of `x**i` coefficients in a divisor, minus one.
  type XCoefficientsMinusOne: ArrayLength;

  /// The number of `y x**i` coefficients in a divisor.
  ///
  /// This is the number of points in a divisor (the number of bits in a scalar, plus one),
  /// ceiling division by two, minus two.
  type YxCoefficients: ArrayLength;
}

/// XCoefficients = (ScalarBits + 1) / 2
type XCoefficients<ScalarBits> = <<ScalarBits as Add<U1>>::Output as Div<U2>>::Output;

impl<P: DiscreteLogParameter> DiscreteLogParameters for P
where
  // XCoefficients
  P::ScalarBits: Add<U1>,
  <P::ScalarBits as Add<U1>>::Output: Add<U1> + Div<U2>,
  <<P::ScalarBits as Add<U1>>::Output as Div<U2>>::Output: ArrayLength + Sub<U1>,
  // XCoefficientsMinusOne
  XCoefficients<Self::ScalarBits>: Sub<U1>,
  <XCoefficients<Self::ScalarBits> as Sub<U1>>::Output: ArrayLength,
  // YxCoefficients
  <<P::ScalarBits as Add<U1>>::Output as Add<U1>>::Output: Div<U2>,
  <<<P::ScalarBits as Add<U1>>::Output as Add<U1>>::Output as Div<U2>>::Output: Sub<U2>,
  <<<<P::ScalarBits as Add<U1>>::Output as Add<U1>>::Output as Div<U2>>::Output as Sub<U2>>::Output:
    ArrayLength,
{
  type XCoefficients = XCoefficients<Self::ScalarBits>;
  // XCoefficients - 1
  type XCoefficientsMinusOne = Diff<XCoefficients<Self::ScalarBits>, U1>;
  // (ScalarBits + 1 + 1)/2 - 2 = (ScalarBits + 2)/2 - 2
  type YxCoefficients = Diff<Quot<Sum<Sum<Self::ScalarBits, U1>, U1>, U2>, U2>;
}

/// A representation of the divisor.
///
/// The coefficient for x**1 is explicitly excluded as it's expected to be normalized to 1.
#[derive(Clone)]
pub struct Divisor<F: PrimeField, Parameters: DiscreteLogParameters> {
  /// The coefficient for the `y` term of the divisor.
  ///
  /// There is never more than one `y**i x**0` coefficient as the leading term of the modulus is
  /// `y**2`. It's assumed the coefficient is non-zero (and present) as it will be for any divisor
  /// exceeding trivial complexity.
  pub y: Variable<F>,
  /// The coefficients for the `y**1 x**i` terms of the polynomial.
  pub yx: GenericArray<Variable<F>, Parameters::YxCoefficients>,
  /// The coefficients for the `x**i` terms of the polynomial, skipping x**1.
  ///
  /// x**1 is skipped as it's expected to be normalized to 1, and therefore constant, in order to
  /// ensure the divisor is non-zero (as necessary for the proof to be complete).
  // Subtract 1 from the length due to skipping the coefficient for x**1
  pub x_from_power_of_2: GenericArray<Variable<F>, Parameters::XCoefficientsMinusOne>,
  /// The constant term in the polynomial (alternatively, the coefficient for y**0 x**0).
  pub zero: Variable<F>,
}

// TODO: Try with having the scalar multiplied by different generator points. This can minimize the cost as the
// scalar decomposition has to be committed and proven once once

/// A point, its discrete logarithm, and the divisor to prove it.
#[derive(Clone)]
pub struct PointWithDlog<F: PrimeField, Parameters: DiscreteLogParameters> {
  /// The point which is supposedly the result of scaling the generator by the discrete logarithm.
  pub point: (Variable<F>, Variable<F>),
  /// The discrete logarithm, represented as coefficients of a polynomial of 2**i.
  pub dlog: GenericArray<Variable<F>, Parameters::ScalarBits>,
  /// The divisor interpolating the relevant doublings of generator with the inverse of the point.
  pub divisor: Divisor<F, Parameters>,
}

/// Commitments for the dlog and divisor witnesses combined.
#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct DivisorComms<C: AffineRepr> (pub Vec<C>);

/// Blindings for the combined dlog and divisor witnesses commitments.
pub struct DivisorCommsBlindings<F: PrimeField> (pub Vec<F>);

/// A struct containing a point used for the evaluation of a divisor.
///
/// Preprocesses and caches as much of the calculation as possible to minimize work upon reuse of
/// challenge points.
#[derive(Debug)]
struct ChallengePoint<F: PrimeField, Parameters: DiscreteLogParameters> {
  y: F,
  yx: GenericArray<F, Parameters::YxCoefficients>,
  x: GenericArray<F, Parameters::XCoefficients>,
  p_0_n_0: F,
  x_p_0_n_0: GenericArray<F, Parameters::YxCoefficients>,
  p_1_n: F,
  p_1_d: F,
}

impl<F: PrimeField, Parameters: DiscreteLogParameters> ChallengePoint<F, Parameters> {
  fn new(
    curve: &CurveSpec<F>,
    // The slope between all of the challenge points
    slope: F,
    // The x and y coordinates
    x: F,
    y: F,
    // The inversion of twice the y coordinate
    // We accept this as an argument so that the caller can calculate these with a batch inversion
    inv_two_y: F,
  ) -> Self {
    // Powers of x, skipping x**0
    let divisor_x_len = Parameters::XCoefficients::USIZE;
    let mut x_pows = GenericArray::default();
    x_pows[0] = x;
    for i in 1..divisor_x_len {
      let last = x_pows[i - 1];
      x_pows[i] = last * x;
    }

    // Powers of x multiplied by y
    let divisor_yx_len = Parameters::YxCoefficients::USIZE;
    let mut yx = GenericArray::default();
    // Skips x**0
    yx[0] = y * x;
    for i in 1..divisor_yx_len {
      let last = yx[i - 1];
      yx[i] = last * x;
    }

    let x_sq = x.square();
    let three_x_sq = x_sq.double() + x_sq;
    let three_x_sq_plus_a = three_x_sq + curve.a;
    let two_y = y.double();

    // p_0_n_0 from `DivisorChallenge`
    let p_0_n_0 = three_x_sq_plus_a * inv_two_y;
    let mut x_p_0_n_0 = GenericArray::default();
    // Since this iterates over x, which skips x**0, this also skips p_0_n_0 x**0
    for (i, x) in x_pows.iter().take(divisor_yx_len).enumerate() {
      x_p_0_n_0[i] = p_0_n_0 * x;
    }

    // p_1_n from `DivisorChallenge`
    let p_1_n = two_y;
    // p_1_d from `DivisorChallenge`
    let p_1_d = (-slope * p_1_n) + three_x_sq_plus_a;

    ChallengePoint { x: x_pows, y, yx, p_0_n_0, x_p_0_n_0, p_1_n, p_1_d }
  }
}

/// A challenge to evaluate divisors with.
///
/// This challenge must be sampled after writing the commitments to the transcript. This challenge
/// is reusable across various divisors.
// #[derive(Debug)]
pub struct DiscreteLogChallenge<F: PrimeField, Parameters: DiscreteLogParameters> {
  c0: ChallengePoint<F, Parameters>,
  c1: ChallengePoint<F, Parameters>,
  c2: ChallengePoint<F, Parameters>,
  slope: F,
  intercept: F,
}

/// A generator which has been challenged and is ready for use in evaluating discrete logarithm
/// claims.
#[derive(Debug)]
pub struct ChallengedGenerator<F: PrimeField, Parameters: DiscreteLogParameters>(
  GenericArray<F, Parameters::ScalarBits>,
);

impl<F: PrimeField, Parameters: DiscreteLogParameters> PointWithDlog<F, Parameters> {
  pub fn from_vars(mut decomposition: Vec<Variable<F>>, mut divisor: Vec<Variable<F>>) -> Self {
    let blind_x_var = decomposition.pop().unwrap();
    let blind_y_var = divisor.pop().unwrap();
    let dlog = GenericArray::<_, Parameters::ScalarBits>::from_slice(&decomposition).clone();

    let mut cursor_start = 1;
    let mut cursor_end = cursor_start + Parameters::YxCoefficients::USIZE;
    let yx =
      GenericArray::<_, Parameters::YxCoefficients>::from_slice(&divisor[cursor_start..cursor_end])
        .clone();
    cursor_start = cursor_end;
    cursor_end += Parameters::XCoefficientsMinusOne::USIZE;
    let x_from_power_of_2 = GenericArray::<_, Parameters::XCoefficientsMinusOne>::from_slice(
      &divisor[cursor_start..cursor_end],
    )
    .clone();
    let divisor = Divisor { y: divisor[0], yx, x_from_power_of_2, zero: divisor[cursor_end] };
    PointWithDlog { divisor, dlog, point: (blind_x_var, blind_y_var) }
  }
}

fn divisor_challenge_eval<
  F: PrimeField,
  CS: ConstraintSystem<F>,
  Parameters: DiscreteLogParameters,
>(
  cs: &mut CS,
  divisor: &Divisor<F, Parameters>,
  challenge: &ChallengePoint<F, Parameters>,
) -> LinearCombination<F> {
  // The evaluation of the divisor differentiated by y, further multiplied by p_0_n_0
  // Differentiation drops everything without a y coefficient, and drops what remains by a power
  // of y
  // (y**1 -> y**0, yx**i -> x**i)
  // This aligns with p_0_n_1  from `DivisorChallenge`
  let mut p_0_n_1 = LinearCombination::from_iter([(divisor.y, challenge.p_0_n_0)]);
  for (j, var) in divisor.yx.iter().enumerate() {
    // This does not index by `j + 1` as x_p_0_n_0 omits x**0
    p_0_n_1 = p_0_n_1 + LinearCombination::from_iter([(*var, challenge.x_p_0_n_0[j])]);
  }

  // The evaluation of the divisor differentiated by x
  // This aligns with p_0_n_2  from `DivisorChallenge`
  // The coefficient for x**1 is 1, so 1 becomes the new zero coefficient
  let mut p_0_n_2 = constant(F::ONE);

  // Handle the new y coefficient
  p_0_n_2 = p_0_n_2 + LinearCombination::from_iter([(divisor.yx[0], challenge.y)]);

  // Handle the new yx coefficients
  for (j, yx) in divisor.yx.iter().enumerate().skip(1) {
    // For the power which was shifted down, we multiply this coefficient
    // 3 x**2 -> 2 * 3 x**1
    let original_power_of_x = F::from((j + 1) as u64);
    // `j - 1` so `j = 1` indexes yx[0] as yx[0] is the y x**1
    // (yx omits y x**0)
    let weight = original_power_of_x * challenge.yx[j - 1];
    p_0_n_2 = p_0_n_2 + LinearCombination::from_iter([(*yx, weight)]);
  }

  // Handle the x coefficients
  // We don't skip the first one as `x_from_power_of_2` already omits x**1
  for (i, x) in divisor.x_from_power_of_2.iter().enumerate() {
    // i + 2 as the paper expects i to start from 1 and be + 1, yet we start from 0
    let original_power_of_x = F::from((i + 2) as u64);
    // Still x[i] as x[0] is x**1
    let weight = original_power_of_x * challenge.x[i];
    p_0_n_2 = p_0_n_2 + LinearCombination::from_iter([(*x, weight)]);
  }

  // p_0_n from `DivisorChallenge`
  let p_0_n = p_0_n_1 + p_0_n_2;

  // Evaluation of the divisor
  // p_0_d from `DivisorChallenge`
  let mut p_0_d = LinearCombination::from_iter([(divisor.y, challenge.y)]);
  for (var, c_yx) in divisor.yx.iter().zip(&challenge.yx) {
    p_0_d = p_0_d + LinearCombination::from_iter([(*var, *c_yx)]);
  }

  for (i, var) in divisor.x_from_power_of_2.iter().enumerate() {
    // This `i+1` is preserved, despite most not being as x omits x**0, as this assumes we
    // start with `i=1`
    p_0_d = p_0_d + LinearCombination::from_iter([(*var, challenge.x[i + 1])]);
  }

  // Adding x effectively adds a `1 x` term, ensuring the divisor isn't 0
  p_0_d = p_0_d + LinearCombination::from_iter([(divisor.zero, F::ONE)]);
  p_0_d = p_0_d + challenge.x[0];

  // Calculate the joint numerator
  // p_n from `DivisorChallenge`
  let p_n = p_0_n * challenge.p_1_n;
  // Calculate the joint denominator
  // p_d from `DivisorChallenge`
  let p_d = p_0_d * challenge.p_1_d;

  // We want `n / d = o`
  // `n / d = o` == `n = d * o`
  // These are safe unwraps as they're solely done by the prover and should always be non-zero
  let p_d_inv = inverse(cs, p_d.clone());
  let (_, _, o) = cs.multiply(p_n, p_d_inv);
  o.into()
}

/// Sample a challenge for a series of discrete logarithm claims.
///
/// This must be called after writing the commitments to the transcript.
///
/// The generators are assumed to be non-empty. They are not transcripted. If your generators are
/// dynamic, they must be properly transcripted into the context.
///
/// May panic/have undefined behavior if an assumption is broken.
///
///
/// This is part of `DiscreteLog` from `Discrete Log Proof`, specifically, the challenges and
/// the calculations dependent solely on them
#[allow(clippy::type_complexity)]
pub fn discrete_log_challenge<
  F: PrimeField,
  CS: ConstraintSystem<F>,
  Parameters: DiscreteLogParameters,
>(
  cs: &mut CS,
  curve: &CurveSpec<F>,
  generators: &[&GeneratorTable<F, Parameters>],
) -> Result<(DiscreteLogChallenge<F, Parameters>, Vec<ChallengedGenerator<F, Parameters>>), Error> {
  let transcript = cs.transcript();
  let mut sign_of_points = [0; 64];
  // Get the challenge points
  transcript.challenge_bytes(b"sign", &mut sign_of_points);
  let sign_of_point_0 = (sign_of_points[0] & 1) == 1;
  let sign_of_point_1 = ((sign_of_points[0] >> 1) & 1) == 1;

  fn sample_embedded_curve_point<F: PrimeField>(
    transcript: &mut MerlinTranscript,
    curve: &CurveSpec<F>,
    odd_y_coordinate: bool,
  ) -> (F, F) {
    loop {
      let c_x = transcript.challenge_scalar::<F>(b"c_x");
      let c_x_cube = c_x.square() * c_x;
      let ax = curve.a * c_x;
      let Some(c_y) = (c_x_cube + ax + curve.b).sqrt() else {
        continue;
      };
      // Takes a specific y coordinate as to not be dependent on whatever root the above sqrt
      // happens to returns
      let c_y_is_odd = c_y.into_bigint().is_odd();
      return (c_x, if c_y_is_odd != odd_y_coordinate { -c_y } else { c_y });
    }
  }

  let (c0_x, c0_y) = sample_embedded_curve_point::<F>(transcript, curve, sign_of_point_0);

  let c1_x;
  let c1_y;

  loop {
    let (x, y) = sample_embedded_curve_point::<F>(transcript, curve, sign_of_point_1);
    if x == c0_x {
      // new point cant be same or negative of old point
      continue;
    } else {
      c1_x = x;
      c1_y = y;
      break;
    }
  }


  // mmadd-1998-cmo
  fn incomplete_add<F: PrimeField>(x1: F, y1: F, x2: F, y2: F) -> (F, F) {

    let u = y2 - y1;
    let uu = u * u;
    let v = x2 - x1;
    let vv = v * v;
    let vvv = v * vv;
    let r = vv * x1;
    let a = uu - vvv - r.double();
    let x3 = v * a;
    let y3 = (u * (r - a)) - (vvv * y1);
    let z3 = vvv;

    // Normalize from XYZ to XY
    let z3_inv = z3.inverse().unwrap();
    let x3 = x3 * z3_inv;
    let y3 = y3 * z3_inv;

    (x3, y3)
  }

  let (c2_x, c2_y) = incomplete_add::<F>(c0_x, c0_y, c1_x, c1_y);
  // We want C0, C1, C2 = -(C0 + C1)
  let c2_y = -c2_y;

  // Calculate the slope and intercept
  // Safe invert as these x coordinates must be distinct due to passing the above incomplete_add
  let slope = (c1_y - c0_y) * (c1_x - c0_x).inverse().unwrap();
  let intercept = c0_y - (slope * c0_x);

  // Calculate the inversions for 2 c_y (for each c) and all of the challenged generators
  let mut inversions = vec![F::ZERO; 3 + (generators.len() * Parameters::ScalarBits::USIZE)];

  // Needed for the left-hand side eval
  {
    inversions[0] = c0_y.double();
    inversions[1] = c1_y.double();
    inversions[2] = c2_y.double();
  }

  // Perform the inversions for the generators
  for (i, generator) in generators.iter().enumerate() {
    // Needed for the right-hand side eval
    for (j, generator) in generator.0.iter().enumerate() {
      // `DiscreteLog` has weights of `(mu - (G_i.y + (slope * G_i.x)))**-1` in its last line
      inversions[3 + (i * Parameters::ScalarBits::USIZE) + j] =
        intercept - (generator.1 - (slope * generator.0));
    }
  }
  for challenge_inversion in &inversions {
    // This should be unreachable barring negligible probability
    if challenge_inversion.is_zero().into() {
      return Err(Error::InvertingZero);
    }
  }

  batch_inversion(&mut inversions);

  let mut inversions = inversions.into_iter();
  let inv_c0_two_y = inversions.next().unwrap();
  let inv_c1_two_y = inversions.next().unwrap();
  let inv_c2_two_y = inversions.next().unwrap();

  let c0 = ChallengePoint::new(curve, slope, c0_x, c0_y, inv_c0_two_y);
  let c1 = ChallengePoint::new(curve, slope, c1_x, c1_y, inv_c1_two_y);
  let c2 = ChallengePoint::new(curve, slope, c2_x, c2_y, inv_c2_two_y);

  // Fill in the inverted values
  let mut challenged_generators = Vec::with_capacity(generators.len());
  for _ in 0..generators.len() {
    let mut challenged_generator = GenericArray::default();
    for i in 0..Parameters::ScalarBits::USIZE {
      challenged_generator[i] = inversions.next().unwrap();
    }
    challenged_generators.push(ChallengedGenerator(challenged_generator));
  }

  Ok((DiscreteLogChallenge { c0, c1, c2, slope, intercept }, challenged_generators))
}

/// Prove this point has the specified discrete logarithm over the specified generator.
///
/// The discrete logarithm is not validated to be in a canonical form. The only guarantee made on
/// it is that it's a consistent representation of _a_ discrete logarithm (reuse won't enable
/// re-interpretation as a distinct discrete logarithm).
///
/// This does ensure the point is on-curve.
///
/// This MUST only be called with `Variable`s present within commitments.
///
/// May panic/have undefined behavior if an assumption is broken, or if passed an invalid
/// witness.
///
/// `DiscreteLog` from `Discrete Log Proof`
pub fn discrete_log<F: PrimeField, CS: ConstraintSystem<F>, Parameters: DiscreteLogParameters>(
  cs: &mut CS,
  curve: &CurveSpec<F>,
  point: PointWithDlog<F, Parameters>,
  challenge: &DiscreteLogChallenge<F, Parameters>,
  challenged_generator: &ChallengedGenerator<F, Parameters>,
) -> OnCurve<F> {
  let PointWithDlog { divisor, dlog, point } = point;

  // Ensure this is being safely called
  let arg_iter = [point.0, point.1, divisor.y, divisor.zero];
  let arg_iter = arg_iter.iter().chain(divisor.yx.iter());
  let arg_iter = arg_iter.chain(divisor.x_from_power_of_2.iter());
  let arg_iter = arg_iter.chain(dlog.iter());
  for variable in arg_iter {
    debug_assert!(
      matches!(variable, Variable::VectorCommit(_, _) | Variable::Committed(_)),
      "discrete log proofs requires all arguments belong to commitments",
    );
  }

  // Check the point is on curve
  let point_on_curve =
    OnCurve { x: LinearCombination::from(point.0), y: LinearCombination::from(point.1) };
  on_curve(cs, point_on_curve, curve);

  // The challenge has already been sampled so those lines aren't necessary

  // lhs from the paper, evaluating the divisor
  let c0_eval = divisor_challenge_eval(cs, &divisor, &challenge.c0);
  let c1_eval = divisor_challenge_eval(cs, &divisor, &challenge.c1);
  let c2_eval = divisor_challenge_eval(cs, &divisor, &challenge.c2);
  let lhs_eval = LinearCombination::default() + c0_eval + c1_eval + c2_eval;

  // Interpolate the doublings of the generator
  let mut rhs_eval = LinearCombination::default();
  // We call this `bit` yet it's not constrained to being a bit
  // It's presumed to be yet may be malleated
  for (bit, weight) in dlog.into_iter().zip(&challenged_generator.0) {
    rhs_eval = rhs_eval + LinearCombination::from_iter([(bit, *weight)]);
  }

  // Interpolate the output point
  // intercept - (y - (slope * x))
  // intercept - y + (slope * x)
  // -y + (slope * x) + intercept
  // EXCEPT the output point we're proving the discrete log for isn't the one interpolated
  // Its negative is, so -y becomes y
  // y + (slope * x) + intercept
  let output_interpolation = LinearCombination::default()
    + challenge.intercept
    + point.1
    + LinearCombination::from_iter([(point.0, challenge.slope)]);

  let output_interpolation_eval_inv = inverse(cs, output_interpolation);
  rhs_eval = rhs_eval + output_interpolation_eval_inv;

  cs.constrain(lhs_eval - rhs_eval);
  OnCurve { x: LinearCombination::from(point.0), y: LinearCombination::from(point.1) }
}

/// For enforcing `original_point + blind.point = blinded_point`
pub fn discrete_log_blinding<
  F: PrimeField,
  CS: ConstraintSystem<F>,
  Parameters: DiscreteLogParameters,
>(
  cs: &mut CS,
  original_point: (impl Into<LinearCombination<F>>, impl Into<LinearCombination<F>>),
  blind: PointWithDlog<F, Parameters>,
  blinded_point: (F, F),
  curve: &CurveSpec<F>,
  table: &[&GeneratorTable<F, Parameters>],
) -> Result<(), Error> {
  let (challenge, challenged_generators) = discrete_log_challenge(cs, curve, table)?;
  let mut challenged_generators = challenged_generators.into_iter();
  let challenged_T = challenged_generators.next().unwrap();
  discrete_log_blinding_given_challenge(
    cs,
    original_point,
    blind,
    blinded_point,
    curve,
    &challenge,
    &challenged_T,
  );
  Ok(())
}

pub fn discrete_log_blinding_given_challenge<
  F: PrimeField,
  CS: ConstraintSystem<F>,
  Parameters: DiscreteLogParameters,
>(
  cs: &mut CS,
  original_point: (impl Into<LinearCombination<F>>, impl Into<LinearCombination<F>>),
  blind: PointWithDlog<F, Parameters>,
  blinded_point: (F, F),
  curve: &CurveSpec<F>,
  challenge: &DiscreteLogChallenge<F, Parameters>,
  challenged_T: &ChallengedGenerator<F, Parameters>,
) {
  let o_x_lc = original_point.0.into();
  let o_y_lc = original_point.1.into();
  let (o_tilde_x, o_tilde_y) = blinded_point;

  // Check O is on curve
  let O = OnCurve { x: o_x_lc, y: o_y_lc };
  on_curve(cs, O.clone(), &curve);

  // Discrete log for o_blind
  let o_blind = discrete_log(cs, &curve, blind, challenge, challenged_T);

  // Check O = O_tilde + o_blind
  incomplete_add_pub(cs, (o_tilde_x, o_tilde_y), o_blind, O);
}

#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct DivisorWitness<F: PrimeField> {
  /// Decomposition of the scalar
  pub decomposition: Vec<F>,
  /// Coefficients of the divisor polynomial
  pub divisor: Vec<F>,
}

pub fn create_divisor_and_decomposition<
  F: PrimeField,
  C: DivisorCurve<BaseField = F>,
  Parameters: DiscreteLogParameters,
>(
  generator_source: impl GeneratorMultiplesSource<C> + Clone,
  blinding: C::ScalarField,
) -> Result<DivisorWitness<F>, Error> {
  // TODO: This is not general and wont support fields over 255 bits

  let scalar = ScalarDecomposition::new(blinding)?;
  let scalar_mul_and_divisor = ScalarMulAndDivisor::<C>::new(&scalar, generator_source)?;
  let dlog_bits = Parameters::ScalarBits::USIZE;
  if dlog_bits != 255 {
    return Err(Error::UnsupportedScalarBits(dlog_bits));
  }
  let yx_expected_len = Parameters::YxCoefficients::USIZE;
  let x_expected_len = Parameters::XCoefficients::USIZE;

  let dlog = scalar.decomposition();
  if dlog.len() != dlog_bits {
    return Err(Error::DecompositionLengthMismatch(dlog.len(), dlog_bits));
  }
  let result_x = scalar_mul_and_divisor.x;
  let result_y = scalar_mul_and_divisor.y;
  let divisor = &scalar_mul_and_divisor.divisor;

  let mut decomposition = Vec::with_capacity(DECOMPOSITION_SIZE);
  for i in 0..dlog_bits {
    decomposition.push(C::BaseField::from(dlog[i]));
  }

  decomposition.push(result_x);

  let mut divisor_witness = Vec::with_capacity(DECOMPOSITION_SIZE);
  divisor_witness.push(*divisor.y_coefficients.first().unwrap_or(&C::BaseField::ZERO));

  if divisor.yx_coefficients.is_empty() || divisor.yx_coefficients[0].len() > yx_expected_len {
    let yx_len = if divisor.yx_coefficients.is_empty() { 0 } else { divisor.yx_coefficients[0].len() };
    return Err(Error::IncorrectDivisorWitness(yx_len, yx_expected_len));
  }

  let yx = &divisor.yx_coefficients[0];
  for i in 0..yx_expected_len {
    divisor_witness.push(*yx.get(i).unwrap_or(&C::BaseField::ZERO));
  }

  for i in 1..x_expected_len {
    divisor_witness.push(*divisor.x_coefficients.get(i).unwrap_or(&C::BaseField::ZERO));
  }

  divisor_witness.push(divisor.zero_coefficient);

  if divisor_witness.len() > 255 {
    return Err(Error::DivisorWitnessLengthExceeded(divisor_witness.len()));
  }
  while divisor_witness.len() < 255 {
    divisor_witness.push(C::BaseField::ZERO);
  }

  divisor_witness.push(result_y);
  Ok(DivisorWitness { decomposition, divisor: divisor_witness })
}

fn dlog_and_divisor_vars<F: PrimeField, Parameters: DiscreteLogParameters>(
  mut vars_dlog: Vec<Variable<F>>,
  mut vars_divisor: Vec<Variable<F>>,
) -> PointWithDlog<F, Parameters> {
  let blind_x_var = vars_dlog.pop().unwrap();
  let blind_y_var = vars_divisor.pop().unwrap();
  let dlog = GenericArray::<_, Parameters::ScalarBits>::from_slice(&vars_dlog).clone();

  let mut cursor_start = 1;
  let mut cursor_end = cursor_start + Parameters::YxCoefficients::USIZE;
  let yx = GenericArray::<_, Parameters::YxCoefficients>::from_slice(
    &vars_divisor[cursor_start..cursor_end],
  )
  .clone();
  cursor_start = cursor_end;
  cursor_end += Parameters::XCoefficientsMinusOne::USIZE;
  let x_from_power_of_2 = GenericArray::<_, Parameters::XCoefficientsMinusOne>::from_slice(
    &vars_divisor[cursor_start..cursor_end],
  )
  .clone();
  let divisor =
    Divisor { y: vars_divisor[0], yx, x_from_power_of_2, zero: vars_divisor[cursor_end] };
  PointWithDlog { divisor, dlog, point: (blind_x_var, blind_y_var) }
}

pub fn commit_witness_chunks_prover<
  F: PrimeField,
  C: AffineRepr<ScalarField = F>,
  R: CryptoRngCore,
  Parameters: DiscreteLogParameters,
>(
  rng: &mut R,
  cs: &mut Prover<MerlinTranscript, C>,
  divisor_witness: &DivisorWitness<F>,
  chunk_len: usize,
  bp_gens: &BulletproofGens<C>,
) -> Result<(DivisorComms<C>, DivisorCommsBlindings<F>, PointWithDlog<F, Parameters>), Error> {
  let combined_witness: Vec<F> = divisor_witness.decomposition.iter().chain(divisor_witness.divisor.iter()).cloned().collect();
  if combined_witness.len() % chunk_len != 0 {
    return Err(Error::WitnessChunkLengthMismatch(combined_witness.len(), chunk_len));
  }

  let chunk_count = combined_witness.len() / chunk_len;
  let mut commitments = Vec::with_capacity(chunk_count);
  let mut blindings_vec = Vec::with_capacity(chunk_count);
  let mut vars = Vec::with_capacity(combined_witness.len());

  // Don't want to commit large vectors as they negatively impact perf, trading off proof size for time
  for i in 0..chunk_count {
    let chunk = &combined_witness[i*chunk_len..(i+1)*chunk_len];
    let blinding = F::rand(rng);
    let (comm, vars_chunk) = cs.commit_vec(chunk, blinding, bp_gens);
    commitments.push(comm);
    blindings_vec.push(blinding);
    vars.extend(vars_chunk);
  }

  let comms = DivisorComms(commitments);
  let blindings = DivisorCommsBlindings(blindings_vec);

  // Split vars back into dlog and divisor parts
  let vars_dlog = vars[0..divisor_witness.decomposition.len()].to_vec();
  let vars_divisor = vars[divisor_witness.decomposition.len()..].to_vec();

  let point_with_dlog = dlog_and_divisor_vars(vars_dlog, vars_divisor);

  Ok((comms, blindings, point_with_dlog))
}

pub fn commit_witness_chunks_verifier<
  F: PrimeField,
  C: AffineRepr<ScalarField = F>,
  Parameters: DiscreteLogParameters,
>(
  cs: &mut Verifier<MerlinTranscript, C>,
  comms: &DivisorComms<C>,
  chunk_len: usize,
) -> PointWithDlog<F, Parameters> {
  let mut vars = Vec::with_capacity(DECOMPOSITION_SIZE * 2);

  for comm in &comms.0 {
    let chunk_vars = cs.commit_vec(chunk_len, *comm);
    vars.extend(chunk_vars);
  }

  let vars_dlog = vars[0..DECOMPOSITION_SIZE].to_vec();
  let vars_divisor = vars[DECOMPOSITION_SIZE..].to_vec();

  dlog_and_divisor_vars(vars_dlog, vars_divisor)
}

#[cfg(test)]
mod tests {
  use std::time::{Duration, Instant};
  use ark_ec::{AffineRepr};
  use super::*;
  use crate::utils::CurveSpec;
  use ark_pallas::{Affine as PallasAffine, Fq, Fr};
  use ark_serialize::CanonicalSerialize;
  use ark_vesta::Affine as VestaAffine;
  use bulletproofs::{BulletproofGens, PedersenGens};
  use bulletproofs::r1cs::{Prover, Verifier};
  use rand::prelude::StdRng;
  use rand_core::SeedableRng;
  use rand;
  use ark_ec_divisors::curves::pallas::{PallasParams, Point as PallasPoint};
  use ark_ec_divisors::curves::vesta::{Point as VestaPoint, VestaParams};

  type PallasBase = Fq;
  type PallasScalar = Fr;
  type VestaBase = Fr;
  type VestaScalar = Fq;

  #[test]
  fn test_blinding_with_discrete_log() {
    fn check<
      C: DivisorCurve<BaseField = B, ScalarField = S>,
      Params: DiscreteLogParameters,
      B: PrimeField,
      S: PrimeField,
      BP: AffineRepr<ScalarField = B>,
    >(
      count: usize,
      vc_len: usize,
    ) {
      let mut rng = StdRng::seed_from_u64(0);

      // Create curve spec: y^2 = x^3 + 5
      let curve = CurveSpec::<B> { a: B::ZERO, b: B::from(5u64) };

      let pc_gens = PedersenGens::<BP>::default();
      let bp_gens = BulletproofGens::<BP>::new(512, 1);

      let generator = C::random(&mut rng);
      let generator_table = GeneratorTable::<B, Params>::new(generator);

      let mut proving_times = Vec::with_capacity(count);
      let mut proving_times_0 = Vec::with_capacity(count);
      let mut proving_times_00 = Vec::with_capacity(count);
      let mut verifying_times = Vec::with_capacity(count);
      let mut verifying_times_0 = Vec::with_capacity(count);
      let mut verifying_times_00 = Vec::with_capacity(count);
      let mut proof_size = 0;
      for _ in 0..count {
        // Create scalar o and compute o_blind = o.generator
        let o = S::rand(&mut rng);
        let o_blind_point = generator.mul(o);

        // Create O (the original point)
        let O = C::generator().mul(S::rand(&mut rng));

        // Create O_tilde = O + o_blind
        let o_tilde_point = O.add(o_blind_point);
        let (o_tilde_x, o_tilde_y) = C::to_xy(o_tilde_point).unwrap();
        let (o_x, o_y) = C::to_xy(O).unwrap();

        let start = Instant::now();

        let transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let (comm_orig, mut vars_orig) =
          prover.commit_vec(&[o_x, o_y], B::rand(&mut rng), &bp_gens);
        let o_y_var = vars_orig.pop().unwrap();
        let o_x_var = vars_orig.pop().unwrap();

        let (comms, o_blind_claim) = {
          let witness =
            create_divisor_and_decomposition::<_, C, Params>(&generator_table, -o).unwrap();
          let (comms, _, o_blind_claim) = commit_witness_chunks_prover::<_, _, _, Params>(
            &mut rng,
            &mut prover,
            &witness,
            vc_len,
            &bp_gens,
          )
          .unwrap();

          (comms, o_blind_claim)
        };

        proving_times_00.push(start.elapsed());

        discrete_log_blinding(
          &mut prover,
          (o_x_var, o_y_var),
          o_blind_claim,
          (o_tilde_x, o_tilde_y),
          &curve,
          &[&generator_table],
        ).unwrap();

        proving_times_0.push(start.elapsed());

        let proof = prover.prove(&bp_gens).unwrap();
        proving_times.push(start.elapsed());

        if proof_size == 0 {
          proof_size =
            proof.compressed_size() + comms.compressed_size() + comm_orig.compressed_size();
        }

        let start = Instant::now();

        let transcript = MerlinTranscript::new(b"test");
        let mut verifier = Verifier::new(transcript);

        let mut vars_orig = verifier.commit_vec(2, comm_orig);
        let o_y_var = vars_orig.pop().unwrap();
        let o_x_var = vars_orig.pop().unwrap();

        let o_blind_claim =
          commit_witness_chunks_verifier::<_, _, Params>(&mut verifier, &comms, vc_len);

        verifying_times_00.push(start.elapsed());

        discrete_log_blinding(
          &mut verifier,
          (o_x_var, o_y_var),
          o_blind_claim,
          (o_tilde_x, o_tilde_y),
          &curve,
          &[&generator_table],
        ).unwrap();

        verifying_times_0.push(start.elapsed());
        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        verifying_times.push(start.elapsed());
      }

      proving_times_0.sort();
      proving_times.sort();
      verifying_times_0.sort();
      verifying_times.sort();

      let total_prove_00: Duration = proving_times_00.iter().sum();
      let total_prove_0: Duration = proving_times_0.iter().sum();
      let total_prove: Duration = proving_times.iter().sum();
      let total_verify_00: Duration = verifying_times_00.iter().sum();
      let total_verify_0: Duration = verifying_times_0.iter().sum();
      let total_verify: Duration = verifying_times.iter().sum();
      let median_prove_00 = proving_times_00[count / 2];
      let median_prove_0 = proving_times_0[count / 2];
      let median_prove = proving_times[count / 2];
      let median_verify_00 = verifying_times_00[count / 2];
      let median_verify_0 = verifying_times_0[count / 2];
      let median_verify = verifying_times[count / 2];

      println!(
        "For {count} iterations, and vec commitment size={vc_len}, proof size (single) = {proof_size}, \
        total proving time: {:?}, median proving time: {:?}, total verification time: {:?}, median verification time: {:?}. \
        For non BP proof generation/verification, total proving {:?}, median proving {:?}, total verification {:?}, median verification {:?}. \
        For commitments, total proving {:?}, median proving {:?}, total verification {:?}, median verification {:?}",
        total_prove, median_prove, total_verify, median_verify, total_prove_0, median_prove_0, total_verify_0, median_verify_0,
        total_prove_00, median_prove_00, total_verify_00, median_verify_00
      );
    }

    let count = 5;
    let vc_len = 32;
    println!("Testing Pallas");
    check::<PallasPoint, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);
    println!("Testing Vesta");
    check::<VestaPoint, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);
  }

  #[test]
  fn test_blinding_with_discrete_log_combined() {
    fn check<
      C: DivisorCurve<BaseField = B, ScalarField = S>,
      Params: DiscreteLogParameters,
      B: PrimeField,
      S: PrimeField,
      BP: AffineRepr<ScalarField = B>,
    >(
      count: usize,
      vc_len: usize,
    ) {
      let mut rng = StdRng::seed_from_u64(0);

      // Create curve spec: y^2 = x^3 + 5
      let curve = CurveSpec::<B> { a: B::ZERO, b: B::from(5u64) };

      let pc_gens = PedersenGens::<BP>::default();
      let bp_gens = BulletproofGens::<BP>::new(512, 1);

      let generator = C::random(&mut rng);

      let generator_table = GeneratorTable::<B, Params>::new(generator);

      // Collect all the data for all iterations
      let mut all_o_blind_claims = Vec::new();
      let mut all_o_tilde_points = Vec::new();
      let mut all_divisor_commitments = Vec::new();

      let mut all_o = Vec::new();
      let mut all_o_coords = Vec::new();
      for _ in 0..count {
        // Create O (the original point)
        let O = C::generator().mul(S::rand(&mut rng));
        all_o.push(O);
        let (O_x, O_y) = C::to_xy(O).unwrap();
        all_o_coords.push(O_x);
        all_o_coords.push(O_y);
      }

      let start = Instant::now();
      let transcript = MerlinTranscript::new(b"test");
      let mut prover = Prover::new(&pc_gens, transcript);

      // Commit to all at once
      let (comm_orig, all_O_vars) = prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

      for i in 0..count {
        // Create scalar o and compute o_blind = o.generator
        let o = S::rand(&mut rng);
        let o_blind_point = generator.mul(o);

        let O = &all_o[i];

        // Create O_tilde = O - o_blind
        let O_tilde_point = O.add(o_blind_point.neg());
        let (O_tilde_x, O_tilde_y) = C::to_xy(O_tilde_point).unwrap();

        all_o_tilde_points.push((O_tilde_x, O_tilde_y));

        let (comms, o_blind_claim) = {
          let witness =
            create_divisor_and_decomposition::<_, C, Params>(&generator_table, o).unwrap();
          let (comms, _, o_blind_claim) = commit_witness_chunks_prover::<_, _, _, Params>(
            &mut rng,
            &mut prover,
            &witness,
            vc_len,
            &bp_gens,
          )
          .unwrap();

          (comms, o_blind_claim)
        };

        all_divisor_commitments.push(comms);
        all_o_blind_claims.push(o_blind_claim);
      }

      let proving_time_00 = start.elapsed();

      for (i, o_blind_claim) in all_o_blind_claims.into_iter().enumerate() {
        let (O_x_var, O_y_var) = (all_O_vars[2 * i], all_O_vars[2 * i + 1]);
        let (O_tilde_x, O_tilde_y) = all_o_tilde_points[i];
        discrete_log_blinding(
          &mut prover,
          (O_x_var, O_y_var),
          o_blind_claim,
          (O_tilde_x, O_tilde_y),
          &curve,
          &[&generator_table],
        ).unwrap();
      }

      let proving_time_0 = start.elapsed();
      let proof = prover.prove(&bp_gens).unwrap();
      let proving_time = start.elapsed();

      let total_proof_size = proof.compressed_size()
        + comm_orig.compressed_size()
        + all_divisor_commitments.compressed_size();

      let start = Instant::now();
      let transcript = MerlinTranscript::new(b"test");
      let mut verifier = Verifier::new(transcript);

      let mut all_o_blind_claims = Vec::new();

      let vars_orig = verifier.commit_vec(2 * count, comm_orig);

      for i in 0..count {
        let O_x_var = vars_orig[2 * i];
        let O_y_var = vars_orig[2 * i + 1];

        let o_blind_claim = commit_witness_chunks_verifier::<_, _, Params>(
          &mut verifier,
          &all_divisor_commitments[i],
          vc_len,
        );
        all_o_blind_claims.push((o_blind_claim, O_x_var, O_y_var));
      }

      let verifying_time_00 = start.elapsed();

      for (i, (o_blind_claim, o_x_var, o_y_var)) in all_o_blind_claims.into_iter().enumerate() {
        let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
        discrete_log_blinding(
          &mut verifier,
          (o_x_var, o_y_var),
          o_blind_claim,
          (o_tilde_x, o_tilde_y),
          &curve,
          &[&generator_table],
        ).unwrap();
      }

      let verifying_time_0 = start.elapsed();
      verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
      let verifying_time = start.elapsed();

      println!(
        "For {count} discrete log proofs, vec commitment size={vc_len}, total proof size = {total_proof_size}, \
        proving time: {:?}, verification time: {:?}. For non BP proof generation/verification proving time {:?}, verification time {:?}. \
        For commitments, proving time {:?}, verification time {:?}",
        proving_time, verifying_time, proving_time_0, verifying_time_0, proving_time_00, verifying_time_00
      );
    }

    let count = 4;
    let vc_len = 64;
    println!("Testing Pallas");
    check::<PallasPoint, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);
    println!("Testing Vesta");
    check::<VestaPoint, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);
  }

  #[test]
  fn test_blinding_with_discrete_log_combined_reuse_challenge() {
    fn check<
      C: DivisorCurve<BaseField = B, ScalarField = S>,
      Params: DiscreteLogParameters,
      B: PrimeField,
      S: PrimeField,
      BP: AffineRepr<ScalarField = B>,
    >(
      count: usize,
      vc_len: usize,
    ) {
      let mut rng = StdRng::seed_from_u64(0);

      // Create curve spec: y^2 = x^3 + 5
      let curve = CurveSpec::<B> { a: B::ZERO, b: B::from(5u64) };

      let pc_gens = PedersenGens::<BP>::default();
      let bp_gens = BulletproofGens::<BP>::new(512, 1);

      let generator = C::random(&mut rng);
      let generator_table = GeneratorTable::<B, Params>::new(generator);

      // Collect all the data for all iterations
      let mut all_o_blind_claims = Vec::new();
      let mut all_o_tilde_points = Vec::new();
      let mut all_divisor_commitments = Vec::new();

      let mut all_o = Vec::new();
      let mut all_o_coords = Vec::new();
      for _ in 0..count {
        // Create O (the original point)
        let O = C::generator().mul(S::rand(&mut rng));
        all_o.push(O);
        let (O_x, O_y) = C::to_xy(O).unwrap();
        all_o_coords.push(O_x);
        all_o_coords.push(O_y);
      }

      let start = Instant::now();
      let transcript = MerlinTranscript::new(b"test");
      let mut prover = Prover::new(&pc_gens, transcript);

      // Commit to all at once
      let (comm_orig, all_O_vars) = prover.commit_vec(&all_o_coords, B::rand(&mut rng), &bp_gens);

      for i in 0..count {
        // Create scalar o and compute o_blind = o.generator
        let o = S::rand(&mut rng);
        let o_blind_point = generator.mul(o);

        let O = &all_o[i];

        // Create O_tilde = O - o_blind
        let O_tilde_point = O.add(o_blind_point.neg());
        let (O_tilde_x, O_tilde_y) = C::to_xy(O_tilde_point).unwrap();

        all_o_tilde_points.push((O_tilde_x, O_tilde_y));

        let (comms, o_blind_claim) = {
          let witness =
            create_divisor_and_decomposition::<_, C, Params>(&generator_table, o).unwrap();
          let (comms, _, o_blind_claim) = commit_witness_chunks_prover::<_, _, _, Params>(
            &mut rng,
            &mut prover,
            &witness,
            vc_len,
            &bp_gens,
          )
          .unwrap();

          (comms, o_blind_claim)
        };

        all_divisor_commitments.push(comms);
        all_o_blind_claims.push(o_blind_claim);
      }

      let proving_time_00 = start.elapsed();

      let (challenge, challenged_generators) =
        discrete_log_challenge(&mut prover, &curve, &[&generator_table]).unwrap();
      let mut challenged_generators = challenged_generators.into_iter();
      let challenged_T = challenged_generators.next().unwrap();

      for (i, o_blind_claim) in all_o_blind_claims.into_iter().enumerate() {
        let (O_x_var, O_y_var) = (all_O_vars[2 * i], all_O_vars[2 * i + 1]);
        let (O_tilde_x, O_tilde_y) = all_o_tilde_points[i];
        discrete_log_blinding_given_challenge(
          &mut prover,
          (O_x_var, O_y_var),
          o_blind_claim,
          (O_tilde_x, O_tilde_y),
          &curve,
          &challenge,
          &challenged_T,
        );
      }

      let proving_time_0 = start.elapsed();
      let proof = prover.prove(&bp_gens).unwrap();
      let proving_time = start.elapsed();

      let total_proof_size = proof.compressed_size()
        + comm_orig.compressed_size()
        + all_divisor_commitments.compressed_size();

      let start = Instant::now();
      let transcript = MerlinTranscript::new(b"test");
      let mut verifier = Verifier::new(transcript);

      let mut all_o_blind_claims = Vec::new();

      let vars_orig = verifier.commit_vec(2 * count, comm_orig);

      for i in 0..count {
        let O_x_var = vars_orig[2 * i];
        let O_y_var = vars_orig[2 * i + 1];

        let o_blind_claim = commit_witness_chunks_verifier::<_, _, Params>(
          &mut verifier,
          &all_divisor_commitments[i],
          vc_len,
        );
        all_o_blind_claims.push((o_blind_claim, O_x_var, O_y_var));
      }

      let verifying_time_00 = start.elapsed();

      let (challenge, challenged_generators) =
        discrete_log_challenge(&mut verifier, &curve, &[&generator_table]).unwrap();
      let mut challenged_generators = challenged_generators.into_iter();
      let challenged_T = challenged_generators.next().unwrap();

      for (i, (o_blind_claim, o_x_var, o_y_var)) in all_o_blind_claims.into_iter().enumerate() {
        let (o_tilde_x, o_tilde_y) = all_o_tilde_points[i];
        discrete_log_blinding_given_challenge(
          &mut verifier,
          (o_x_var, o_y_var),
          o_blind_claim,
          (o_tilde_x, o_tilde_y),
          &curve,
          &challenge,
          &challenged_T,
        );
      }

      let verifying_time_0 = start.elapsed();
      verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
      let verifying_time = start.elapsed();

      println!(
        "For {count} discrete log proofs, vec commitment size={vc_len}, total proof size = {total_proof_size}, \
        proving time: {:?}, verification time: {:?}. For non BP proof generation/verification proving time {:?}, verification time {:?}. \
        For commitments, proving time {:?}, verification time {:?}",
        proving_time, verifying_time, proving_time_0, verifying_time_0, proving_time_00, verifying_time_00
      );
    }

    let count = 10;
    let vc_len = 256;
    println!("Testing Pallas");
    check::<PallasPoint, PallasParams, PallasBase, PallasScalar, VestaAffine>(count, vc_len);
    println!("Testing Vesta");
    check::<VestaPoint, VestaParams, VestaBase, VestaScalar, PallasAffine>(count, vc_len);
  }
}
