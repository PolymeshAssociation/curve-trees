#![deny(missing_docs)]
#![allow(non_snake_case)]
#![allow(dead_code)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;

use zeroize::{Zeroize, ZeroizeOnDrop};

/// The general case for Vector CP. This is a polynomial of degree `d` where each coefficient is a vector of length `n`.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct VecPoly<F: PrimeField>(
    /// Outer vector has size `d + 1`, inner vector has size `n` where `n` is the size of the vector and `d` is the degree of the polynomial.
    Vec<Vec<F>>,
);

#[derive(Zeroize, ZeroizeOnDrop)]
pub struct Poly<F: PrimeField>(Vec<F>);

impl<F: PrimeField> Poly<F> {
    pub fn zero(deg: usize) -> Self {
        Poly(vec![F::zero(); deg + 1])
    }

    #[inline]
    pub fn coeff_mut(&mut self) -> &mut [F] {
        &mut self.0
    }

    #[inline]
    pub fn coeff(&self) -> &[F] {
        &self.0
    }

    #[inline]
    pub fn deg(&self) -> usize {
        self.0.len() - 1
    }

    pub fn eval(&self, x: F) -> F {
        let mut out = F::zero();
        // Horner's rule, `a_0 + a_1 * x + a_2 * x^2 + ... + a_n * x^n = a_0 + x(a_1 + x(a_2 + x(... + x(a_{n-1} + x(a_n + 0))))`
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

    /// Evaluate at `x`, reserving `extra_capacity` trailing slots so a caller that pads the result
    /// does not reallocate and keep the secret evaluation in a freed buffer.
    pub fn eval(&self, x: F, extra_capacity: usize) -> Vec<F> {
        let n = self.0[0].len();
        let mut out = Vec::with_capacity(n + extra_capacity);
        out.resize(n, F::zero());
        for i in 0..n {
            for v in self.0.iter().rev() {
                out[i] *= x;
                out[i] += v[i];
            }
        }
        out
    }

    /// Product of polynomials when some coefficients of `lhs` are known to be 0
    pub fn special_product(lhs: &Self, rhs: &Self, mid_degree: usize) -> Poly<F> {
        let l_deg = lhs.deg();
        let r_deg = rhs.deg();
        debug_assert_eq!(l_deg, r_deg);
        // degree of product polynomial
        let prod_deg = l_deg + r_deg;

        let mut res = Poly::zero(prod_deg);

        for d in 0..(prod_deg + 1) {
            // for each degree `d` of product polynomial, find all valid pairs of degrees (l, r) of
            // input polynomials such that `l + r = d`
            for l in mid_degree..(d + 1) {
                let r = d - l;
                // lhs has 0 coefficients for degrees < mid_degree but not for degrees >= mid_degree
                if l_deg >= l && r_deg >= r && (r <= mid_degree || r == r_deg) {
                    res.coeff_mut()[d] += F::inner_product(lhs.coeff(l), rhs.coeff(r));
                }
            }
        }
        res
    }
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
        let res = C::from_random_bytes(result.as_ref());
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
