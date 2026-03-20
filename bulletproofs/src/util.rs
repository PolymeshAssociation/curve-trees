#![deny(missing_docs)]
#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use zeroize::ZeroizeOnDrop;

use dock_crypto_utils::ff::inner_product;

/// Represents a degree-1 vector polynomial \\(\mathbf{a} + \mathbf{b} \cdot x\\).
#[derive(ZeroizeOnDrop)]
pub struct VecPoly1<F: PrimeField>(pub Vec<F>, pub Vec<F>);

/// Represents a degree-3 vector polynomial
/// \\(\mathbf{a} + \mathbf{b} \cdot x + \mathbf{c} \cdot x^2 + \mathbf{d} \cdot x^3 \\).
#[derive(ZeroizeOnDrop)]
pub struct VecPoly3<F: PrimeField>(pub Vec<F>, pub Vec<F>, pub Vec<F>, pub Vec<F>);

pub const T_LABELS: [&[u8]; 401] = [
    b"T_0", b"T_1", b"T_2", b"T_3", b"T_4", b"T_5", b"T_6", b"T_7", b"T_8", b"T_9", b"T_10",
    b"T_11", b"T_12", b"T_13", b"T_14", b"T_15", b"T_16", b"T_17", b"T_18", b"T_19", b"T_20",
    b"T_21", b"T_22", b"T_23", b"T_24", b"T_25", b"T_26", b"T_27", b"T_28", b"T_29", b"T_30",
    b"T_31", b"T_32", b"T_33", b"T_34", b"T_35", b"T_36", b"T_37", b"T_38", b"T_39", b"T_40",
    b"T_41", b"T_42", b"T_43", b"T_44", b"T_45", b"T_46", b"T_47", b"T_48", b"T_49", b"T_50",
    b"T_51", b"T_52", b"T_53", b"T_54", b"T_55", b"T_56", b"T_57", b"T_58", b"T_59", b"T_60",
    b"T_61", b"T_62", b"T_63", b"T_64", b"T_65", b"T_66", b"T_67", b"T_68", b"T_69", b"T_70",
    b"T_71", b"T_72", b"T_73", b"T_74", b"T_75", b"T_76", b"T_77", b"T_78", b"T_79", b"T_80",
    b"T_81", b"T_82", b"T_83", b"T_84", b"T_85", b"T_86", b"T_87", b"T_88", b"T_89", b"T_90",
    b"T_91", b"T_92", b"T_93", b"T_94", b"T_95", b"T_96", b"T_97", b"T_98", b"T_99", b"T_100",
    b"T_101", b"T_102", b"T_103", b"T_104", b"T_105", b"T_106", b"T_107", b"T_108", b"T_109",
    b"T_110", b"T_111", b"T_112", b"T_113", b"T_114", b"T_115", b"T_116", b"T_117", b"T_118",
    b"T_119", b"T_120", b"T_121", b"T_122", b"T_123", b"T_124", b"T_125", b"T_126", b"T_127",
    b"T_128", b"T_129", b"T_130", b"T_131", b"T_132", b"T_133", b"T_134", b"T_135", b"T_136",
    b"T_137", b"T_138", b"T_139", b"T_140", b"T_141", b"T_142", b"T_143", b"T_144", b"T_145",
    b"T_146", b"T_147", b"T_148", b"T_149", b"T_150", b"T_151", b"T_152", b"T_153", b"T_154",
    b"T_155", b"T_156", b"T_157", b"T_158", b"T_159", b"T_160", b"T_161", b"T_162", b"T_163",
    b"T_164", b"T_165", b"T_166", b"T_167", b"T_168", b"T_169", b"T_170", b"T_171", b"T_172",
    b"T_173", b"T_174", b"T_175", b"T_176", b"T_177", b"T_178", b"T_179", b"T_180", b"T_181",
    b"T_182", b"T_183", b"T_184", b"T_185", b"T_186", b"T_187", b"T_188", b"T_189", b"T_190",
    b"T_191", b"T_192", b"T_193", b"T_194", b"T_195", b"T_196", b"T_197", b"T_198", b"T_199",
    b"T_200", b"T_201", b"T_202", b"T_203", b"T_204", b"T_205", b"T_206", b"T_207", b"T_208",
    b"T_209", b"T_210", b"T_211", b"T_212", b"T_213", b"T_214", b"T_215", b"T_216", b"T_217",
    b"T_218", b"T_219", b"T_220", b"T_221", b"T_222", b"T_223", b"T_224", b"T_225", b"T_226",
    b"T_227", b"T_228", b"T_229", b"T_230", b"T_231", b"T_232", b"T_233", b"T_234", b"T_235",
    b"T_236", b"T_237", b"T_238", b"T_239", b"T_240", b"T_241", b"T_242", b"T_243", b"T_244",
    b"T_245", b"T_246", b"T_247", b"T_248", b"T_249", b"T_250", b"T_251", b"T_252", b"T_253",
    b"T_254", b"T_255", b"T_256", b"T_257", b"T_258", b"T_259", b"T_260", b"T_261", b"T_262",
    b"T_263", b"T_264", b"T_265", b"T_266", b"T_267", b"T_268", b"T_269", b"T_270", b"T_271",
    b"T_272", b"T_273", b"T_274", b"T_275", b"T_276", b"T_277", b"T_278", b"T_279", b"T_280",
    b"T_281", b"T_282", b"T_283", b"T_284", b"T_285", b"T_286", b"T_287", b"T_288", b"T_289",
    b"T_290", b"T_291", b"T_292", b"T_293", b"T_294", b"T_295", b"T_296", b"T_297", b"T_298",
    b"T_299", b"T_300", b"T_301", b"T_302", b"T_303", b"T_304", b"T_305", b"T_306", b"T_307",
    b"T_308", b"T_309", b"T_310", b"T_311", b"T_312", b"T_313", b"T_314", b"T_315", b"T_316",
    b"T_317", b"T_318", b"T_319", b"T_320", b"T_321", b"T_322", b"T_323", b"T_324", b"T_325",
    b"T_326", b"T_327", b"T_328", b"T_329", b"T_330", b"T_331", b"T_332", b"T_333", b"T_334",
    b"T_335", b"T_336", b"T_337", b"T_338", b"T_339", b"T_340", b"T_341", b"T_342", b"T_343",
    b"T_344", b"T_345", b"T_346", b"T_347", b"T_348", b"T_349", b"T_350", b"T_351", b"T_352",
    b"T_353", b"T_354", b"T_355", b"T_356", b"T_357", b"T_358", b"T_359", b"T_360", b"T_361",
    b"T_362", b"T_363", b"T_364", b"T_365", b"T_366", b"T_367", b"T_368", b"T_369", b"T_370",
    b"T_371", b"T_372", b"T_373", b"T_374", b"T_375", b"T_376", b"T_377", b"T_378", b"T_379",
    b"T_380", b"T_381", b"T_382", b"T_383", b"T_384", b"T_385", b"T_386", b"T_387", b"T_388",
    b"T_389", b"T_390", b"T_391", b"T_392", b"T_393", b"T_394", b"T_395", b"T_396", b"T_397",
    b"T_398", b"T_399", b"T_400",
];

/// The general case for Vector CP.
pub struct VecPoly<F: PrimeField>(Vec<Vec<F>>);

pub struct Poly<F: PrimeField>(Vec<F>);

impl<F: PrimeField> Poly<F> {
    pub fn zero(deg: usize) -> Self {
        Poly(vec![F::zero(); deg + 1])
    }

    #[inline]
    pub fn coeff(&mut self) -> &mut [F] {
        &mut self.0
    }

    #[inline]
    pub fn deg(&self) -> usize {
        self.0.len() - 1
    }

    pub fn eval(&self, x: F) -> F {
        let mut out = F::zero();
        // Horner's rule
        for v in self.0.iter().rev() {
            out *= x;
            out += v;
        }
        out
    }
}

impl<F: PrimeField> From<Vec<F>> for Poly<F> {
    fn from(v: Vec<F>) -> Self {
        Self(v)
    }
}

impl<F: PrimeField> VecPoly<F> {
    #[inline]
    pub fn coeff_mut(&mut self, deg: usize) -> &mut [F] {
        &mut self.0[deg]
    }

    #[inline]
    pub fn deg(&self) -> usize {
        self.0.len() - 1
    }

    #[inline]
    pub fn coeff(&self, deg: usize) -> &[F] {
        &self.0[deg]
    }

    pub fn zero(n: usize, deg: usize) -> Self {
        VecPoly(vec![vec![F::zero(); n]; deg + 1])
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0[0].len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            for v in self.0.iter().rev() {
                out[i] *= x;
                out[i] += v[i];
            }
        }
        out
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    ///
    /// This is the case in the constraint system proof.
    pub fn inner_product(lhs: &Self, rhs: &Self) -> Poly<F> {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let deg = lhs.deg() + rhs.deg();

        // log::debug!("combined degree: {}", deg);

        let mut res = Poly::zero(deg);

        for d in 0..deg + 1 {
            for l in 0..(d + 1) {
                let r = d - l;
                if lhs.deg() >= l && rhs.deg() >= r {
                    res.coeff()[d] += inner_product(lhs.coeff(l), rhs.coeff(r));
                }
            }
        }

        res
    }
}

/// Represents a degree-2 scalar polynomial \\(a + b \cdot x + c \cdot x^2\\)
#[derive(ZeroizeOnDrop)]
pub struct Poly2<F: PrimeField>(pub F, pub F, pub F);

/// Represents a degree-6 scalar polynomial, without the zeroth degree
/// \\(a \cdot x + b \cdot x^2 + c \cdot x^3 + d \cdot x^4 + e \cdot x^5 + f \cdot x^6\\)
#[derive(ZeroizeOnDrop)]
pub struct Poly6<F: PrimeField> {
    pub t1: F,
    pub t2: F,
    pub t3: F,
    pub t4: F,
    pub t5: F,
    pub t6: F,
}

/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
pub struct ScalarExp<F: PrimeField> {
    x: F,
    next_exp_x: F,
}

impl<F: PrimeField> Iterator for ScalarExp<F> {
    type Item = F;

    fn next(&mut self) -> Option<F> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

/// Return an iterator of the powers of `x`.
pub fn exp_iter<F: PrimeField>(x: F) -> ScalarExp<F> {
    let next_exp_x = F::one();
    ScalarExp { x, next_exp_x }
}

pub fn add_vec<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    if a.len() != b.len() {
        // throw some error
        //log::debug!("lengths of vectors don't match for vector addition");
    }
    let mut out = vec![F::zero(); b.len()];
    for i in 0..a.len() {
        out[i] = a[i] + b[i];
    }
    out
}

impl<F: PrimeField> VecPoly1<F> {
    pub fn zero(n: usize) -> Self {
        VecPoly1(vec![F::zero(); n], vec![F::zero(); n])
    }

    pub fn inner_product(&self, rhs: &VecPoly1<F>) -> Poly2<F> {
        // Uses Karatsuba's method
        let l = self;
        let r = rhs;

        let t0 = inner_product(&l.0, &r.0);
        let t2 = inner_product(&l.1, &r.1);

        let l0_plus_l1 = add_vec(&l.0, &l.1);
        let r0_plus_r1 = add_vec(&r.0, &r.1);

        let t1 = inner_product(&l0_plus_l1, &r0_plus_r1) - t0 - t2;

        Poly2(t0, t1, t2)
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0.len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + self.1[i] * x;
        }
        out
    }
}

impl<F: PrimeField> VecPoly3<F> {
    pub fn zero(n: usize) -> Self {
        VecPoly3(
            vec![F::zero(); n],
            vec![F::zero(); n],
            vec![F::zero(); n],
            vec![F::zero(); n],
        )
    }

    /// Compute an inner product of `lhs`, `rhs` which have the property that:
    /// - `lhs.0` is zero;
    /// - `rhs.2` is zero;
    ///
    /// This is the case in the constraint system proof.
    pub fn special_inner_product(lhs: &Self, rhs: &Self) -> Poly6<F> {
        // TODO: make checks that l_poly.0 and r_poly.2 are zero.

        let t1 = inner_product(&lhs.1, &rhs.0);
        let t2 = inner_product(&lhs.1, &rhs.1) + inner_product(&lhs.2, &rhs.0);
        let t3 = inner_product(&lhs.2, &rhs.1) + inner_product(&lhs.3, &rhs.0);
        let t4 = inner_product(&lhs.1, &rhs.3) + inner_product(&lhs.3, &rhs.1);
        let t5 = inner_product(&lhs.2, &rhs.3);
        let t6 = inner_product(&lhs.3, &rhs.3);

        Poly6 {
            t1,
            t2,
            t3,
            t4,
            t5,
            t6,
        }
    }

    pub fn eval(&self, x: F) -> Vec<F> {
        let n = self.0.len();
        let mut out = vec![F::zero(); n];
        for i in 0..n {
            out[i] = self.0[i] + x * (self.1[i] + x * (self.2[i] + x * self.3[i]));
        }
        out
    }
}

impl<F: PrimeField> Poly2<F> {
    pub fn eval(&self, x: F) -> F {
        self.0 + x * (self.1 + x * self.2)
    }
}

impl<F: PrimeField> Poly6<F> {
    pub fn eval(&self, x: F) -> F {
        x * (self.t1 + x * (self.t2 + x * (self.t3 + x * (self.t4 + x * (self.t5 + x * self.t6)))))
    }
}

// /// Takes the sum of all the powers of `x`, up to `n`
// /// If `n` is a power of 2, it uses the efficient algorithm with `2*lg n` multiplications and additions.
// /// If `n` is not a power of 2, it uses the slow algorithm with `n` multiplications and additions.
// /// In the Bulletproofs case, all calls to `sum_of_powers` should have `n` as a power of 2.
pub fn sum_of_powers<F: PrimeField>(x: &F, n: usize) -> F {
    if !n.is_power_of_two() {
        return sum_of_powers_slow(x, n);
    }
    if n == 0 || n == 1 {
        return F::from(n as u64);
    }
    let mut m = n;
    let mut result = F::one() + x;
    let mut factor = *x;
    while m > 2 {
        factor = factor * factor;
        result = result + factor * result;
        m /= 2;
    }
    result
}

// takes the sum of all of the powers of x, up to n
fn sum_of_powers_slow<F: PrimeField>(x: &F, n: usize) -> F {
    exp_iter(*x).take(n).sum()
}

/// Given `data` with `len >= 32`, return the first 32 bytes.
pub fn read32(data: &[u8]) -> [u8; 32] {
    let mut buf32 = [0u8; 32];
    buf32[..].copy_from_slice(&data[..32]);
    buf32
}

/// Hash a byte string to a curve point using try and increment
pub fn affine_from_bytes_tai<C: AffineRepr>(bytes: &[u8]) -> Option<C> {
    use sha3::{Digest, Sha3_256};

    for i in 0..=u8::MAX {
        let mut sha = Sha3_256::new();
        sha.update(bytes);
        sha.update([i]);
        let result = sha.finalize();
        let res = C::from_random_bytes(result.as_slice());
        if let Some(point) = res {
            return Some(point.clear_cofactor());
        }
    }
    None
}

pub fn field_as_bytes<F: PrimeField>(field: &F) -> Vec<u8> {
    let mut bytes = Vec::new();
    if let Err(e) = field.serialize_compressed(&mut bytes) {
        panic!("{}", e)
    }
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_log::test;

    use ark_pallas::*;

    type Scalar = <Affine as AffineRepr>::ScalarField;
    use ark_ff::{One, Zero};

    #[test]
    fn exp_2_is_powers_of_2() {
        let exp_2: Vec<_> = exp_iter(Scalar::from(2u64)).take(4).collect();

        assert_eq!(exp_2[0], Scalar::from(1u64));
        assert_eq!(exp_2[1], Scalar::from(2u64));
        assert_eq!(exp_2[2], Scalar::from(4u64));
        assert_eq!(exp_2[3], Scalar::from(8u64));
    }

    #[test]
    fn test_inner_product() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), inner_product(&a, &b));
    }

    #[test]
    fn test_sum_of_powers() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), sum_of_powers(&x, 0));
        assert_eq!(sum_of_powers_slow(&x, 1), sum_of_powers(&x, 1));
        assert_eq!(sum_of_powers_slow(&x, 2), sum_of_powers(&x, 2));
        assert_eq!(sum_of_powers_slow(&x, 4), sum_of_powers(&x, 4));
        assert_eq!(sum_of_powers_slow(&x, 8), sum_of_powers(&x, 8));
        assert_eq!(sum_of_powers_slow(&x, 16), sum_of_powers(&x, 16));
        assert_eq!(sum_of_powers_slow(&x, 32), sum_of_powers(&x, 32));
        assert_eq!(sum_of_powers_slow(&x, 64), sum_of_powers(&x, 64));
    }

    #[test]
    fn test_sum_of_powers_slow() {
        let x = Scalar::from(10u64);
        assert_eq!(sum_of_powers_slow(&x, 0), Scalar::zero());
        assert_eq!(sum_of_powers_slow(&x, 1), Scalar::one());
        assert_eq!(sum_of_powers_slow(&x, 2), Scalar::from(11u64));
        assert_eq!(sum_of_powers_slow(&x, 3), Scalar::from(111u64));
        assert_eq!(sum_of_powers_slow(&x, 4), Scalar::from(1111u64));
        assert_eq!(sum_of_powers_slow(&x, 5), Scalar::from(11111u64));
        assert_eq!(sum_of_powers_slow(&x, 6), Scalar::from(111111u64));
    }
}
