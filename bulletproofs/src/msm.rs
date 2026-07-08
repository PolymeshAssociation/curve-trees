//! Variable-time double-scalar multiplication: `b1 * k1 + b2 * k2`.
//!
//! Implements Shamir's trick (shared doublings over the plain bits) and the Joint Sparse Form
//! (shared doublings + minimal-weight signed recoding), which for random scalars needs ~0.5·L
//! additions instead of Shamir's ~0.75·L, where `L` is the scalar bit length.
//!
//! **These algorithms are variable-time**
//!
//! This module is staged here and is intended to move to `dock_crypto_utils` later.

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BitIteratorBE, PrimeField};
use ark_std::vec::Vec;
use core::ops::{AddAssign, SubAssign};

/// Computes the joint sparse form (JSF) of two non-negative integers, given as
/// little-endian `u64` limbs.
/// The result is a sequence of signed digit pairs `(u1, u2)`, each in `{-1, 0, 1}`, ordered from
/// most significant to least significant, such that `k1 = \sum_i{u1_i * 2^i}` and `k2 = \sum_i{u2_i * 2^i}`.
/// The JSF is the joint signed-binary representation of minimal weight: of any three consecutive
/// positions at least one is `(0, 0)`, so on average only about half the positions are nonzero
/// The returned sequence never starts with `(0, 0)` and is at most one digit longer than the bit length
/// of `max(k1, k2)`.
/// Reference: Taken from Algorithm 3.50 of the book [Guide to Elliptic Curve Cryptography](http://tomlr.free.fr/Math%E9matiques/Math%20Complete/Cryptography/Guide%20to%20Elliptic%20Curve%20Cryptography%20-%20D.%20Hankerson,%20A.%20Menezes,%20S.%20Vanstone.pdf)
pub fn joint_sparse_form(k1: &[u64], k2: &[u64]) -> Vec<(i8, i8)> {
    let len = k1.len().max(k2.len());
    let mut a = k1.to_vec();
    let mut b = k2.to_vec();
    // One extra zero limb of headroom: a `-1` digit increments the value by 1 before halving,
    // which can carry out of a full-width top limb (top bit set). The spare limb absorbs that
    // carry, so the recoding is correct for any input — not only values with a clear top bit.
    a.resize(len + 1, 0);
    b.resize(len + 1, 0);

    // The JSF of an L-bit pair has at most L + 1 digits
    let mut digits = Vec::with_capacity(len * 64 + 1);
    while !limbs_is_zero(&a) || !limbs_is_zero(&b) {
        let a_low = a[0];
        let b_low = b[0];

        let mut u1 = 0i8;
        if a_low & 1 == 1 {
            // a mod 4 is 1 or 3, mapping to +1 or -1.
            u1 = 2 - (a_low & 3) as i8;
            // Flip the sign so that the next position can become a joint zero.
            if matches!(a_low & 7, 3 | 5) && (b_low & 3) == 2 {
                u1 = -u1;
            }
        }

        let mut u2 = 0i8;
        if b_low & 1 == 1 {
            u2 = 2 - (b_low & 3) as i8;
            if matches!(b_low & 7, 3 | 5) && (a_low & 3) == 2 {
                u2 = -u2;
            }
        }

        digits.push((u1, u2));
        // a = (a - u1) / 2, b = (b - u2) / 2. `a - u1` is even (a is odd whenever u1 != 0), so the
        // halving is exact.
        limbs_sub_signed_then_halve(&mut a, u1);
        limbs_sub_signed_then_halve(&mut b, u2);
    }

    digits.reverse();
    digits
}

/// Computes `b1 * k1 + b2 * k2` using the joint sparse form of `(k1, k2)`.
///
/// Compared to [`binary_scalar_mul_shamir`] (Shamir's trick over the plain bits) this
/// does the same number of doublings but fewer additions, because the JSF has
/// about half as many nonzero positions. It precomputes `b1 + b2` and `b1 - b2`;
/// the four other table entries (the negations) are free for these groups.
///
/// When the bases are available in affine form, prefer [`binary_scalar_mul_jsf_affine`],
/// which uses cheaper mixed additions for the single-base digits.
pub fn binary_scalar_mul_jsf<G: CurveGroup>(
    b1: G,
    k1: G::ScalarField,
    b2: G,
    k2: G::ScalarField,
) -> G {
    let sum = b1 + b2;
    let diff = b1 - b2;
    let digits = joint_sparse_form(k1.into_bigint().as_ref(), k2.into_bigint().as_ref());
    jsf_fold(b1, b2, sum, diff, digits)
}

/// Computes `b1 * k1 + b2 * k2`. Identical to [`binary_scalar_mul_jsf`] but for affine points
pub fn binary_scalar_mul_jsf_affine<C: AffineRepr>(
    b1: &C,
    k1: C::ScalarField,
    b2: &C,
    k2: C::ScalarField,
) -> C::Group {
    let sum = (*b1).into_group() + *b2;
    let diff = (*b1).into_group() - *b2;
    let digits = joint_sparse_form(k1.into_bigint().as_ref(), k2.into_bigint().as_ref());
    // Affine bases: the single-base digits use mixed (projective += affine) additions.
    jsf_fold::<C::Group, C>(*b1, *b2, sum, diff, digits)
}

/// Shared double-and-add core for the JSF double-scalar multiplication, driven by the precomputed
/// MSB-first `digits` and the `sum = b1 + b2` / `diff = b1 - b2` table entries.
fn jsf_fold<G, B>(b1: B, b2: B, sum: G, diff: G, digits: Vec<(i8, i8)>) -> G
where
    G: CurveGroup + AddAssign<B> + SubAssign<B>,
    B: Copy,
{
    // Apply one JSF digit to the accumulator.
    let apply = |res: &mut G, (u1, u2): (i8, i8)| match (u1, u2) {
        (1, 0) => *res += b1,
        (-1, 0) => *res -= b1,
        (0, 1) => *res += b2,
        (0, -1) => *res -= b2,
        (1, 1) => *res += sum,
        (-1, -1) => *res -= sum,
        (1, -1) => *res += diff,
        (-1, 1) => *res -= diff,
        // (0, 0) contributes nothing; it never leads the sequence (see `joint_sparse_form`).
        _ => {}
    };

    let mut digits = digits.into_iter();
    let mut res = match digits.next() {
        // The digit sequence never starts with (0, 0)
        Some(first) => {
            let mut res = G::ZERO;
            apply(&mut res, first);
            res
        }
        // Both scalars are zero.
        None => return G::ZERO,
    };
    for digit in digits {
        res.double_in_place();
        apply(&mut res, digit);
    }
    res
}

/// Computes `b1 * k1 + b2 * k2` using Shamir's trick (a joint double-and-add
/// over the plain bits of `k1` and `k2`). Kept alongside [`binary_scalar_mul_jsf`] for
/// comparison.
pub fn binary_scalar_mul_shamir<G: CurveGroup>(
    b1: G,
    k1: G::ScalarField,
    b2: G,
    k2: G::ScalarField,
) -> G {
    let b1b2 = b1 + b2;
    let iter_k1 = BitIteratorBE::new(k1.into_bigint());
    let iter_k2 = BitIteratorBE::new(k2.into_bigint());

    let mut res = G::ZERO;
    let mut skip_leading_zeros = true;
    for pair in iter_k1.zip(iter_k2) {
        if skip_leading_zeros {
            if pair == (false, false) {
                continue;
            }
            skip_leading_zeros = false;
        }
        res.double_in_place();
        match pair {
            (true, false) => res += b1,
            (false, true) => res += b2,
            (true, true) => res += b1b2,
            (false, false) => {}
        }
    }
    res
}

/// Returns `true` if every limb is zero.
fn limbs_is_zero(x: &[u64]) -> bool {
    x.iter().all(|&l| l == 0)
}

/// Sets `x = (x - d) / 2` for `d` in `{-1, 0, 1}`, treating `x` as a
/// little-endian unsigned integer. `x` is odd whenever `d != 0`, so the result
/// is exact.
fn limbs_sub_signed_then_halve(x: &mut [u64], d: i8) {
    match d {
        1 => {
            // x -= 1
            let mut borrow = 1u64;
            for limb in x.iter_mut() {
                let (v, b) = limb.overflowing_sub(borrow);
                *limb = v;
                borrow = b as u64;
            }
            // x was odd (>= 1), so subtracting 1 cannot underflow.
            debug_assert_eq!(borrow, 0, "subtracting 1 from a zero value");
        }
        -1 => {
            // x += 1
            let mut carry = 1u64;
            for limb in x.iter_mut() {
                let (v, c) = limb.overflowing_add(carry);
                *limb = v;
                carry = c as u64;
            }
            // `joint_sparse_form` pads with a spare top limb, so the increment cannot carry out.
            debug_assert_eq!(carry, 0, "increment carried out of the limb array");
        }
        _ => {}
    }

    // x >>= 1
    let mut carry = 0u64;
    for limb in x.iter_mut().rev() {
        let new_carry = *limb << 63;
        *limb = (*limb >> 1) | carry;
        carry = new_carry;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::short_weierstrass::{Affine, Projective};
    use ark_ec::AdditiveGroup;
    use ark_ec::CurveConfig;
    use ark_pallas::PallasConfig;
    use ark_std::rand::{prelude::StdRng, SeedableRng};
    use ark_std::{One, UniformRand, Zero};

    type G = PallasConfig;
    type Fr = <PallasConfig as CurveConfig>::ScalarField;

    fn naive(b1: Projective<G>, k1: Fr, b2: Projective<G>, k2: Fr) -> Projective<G> {
        b1 * k1 + b2 * k2
    }

    /// Rebuild the pair of scalars encoded by JSF digits (MSB first) and check the
    /// non-adjacency property: of any 3 consecutive positions, at least one is (0, 0).
    #[test]
    fn jsf_digits_reconstruct_scalars() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..50 {
            let k1 = Fr::rand(&mut rng);
            let k2 = Fr::rand(&mut rng);
            let digits = joint_sparse_form(k1.into_bigint().as_ref(), k2.into_bigint().as_ref());

            // No leading joint zero.
            assert_ne!(digits.first(), Some(&(0, 0)));

            let (mut r1, mut r2) = (Fr::ZERO, Fr::ZERO);
            for &(u1, u2) in &digits {
                r1.double_in_place();
                r2.double_in_place();
                match u1 {
                    1 => r1 += Fr::one(),
                    -1 => r1 -= Fr::one(),
                    _ => {}
                }
                match u2 {
                    1 => r2 += Fr::one(),
                    -1 => r2 -= Fr::one(),
                    _ => {}
                }
            }
            assert_eq!(r1, k1);
            assert_eq!(r2, k2);

            // JSF property: at least one joint zero in any window of 3.
            for w in digits.windows(3) {
                assert!(
                    w.iter().any(|&d| d == (0, 0)),
                    "three consecutive nonzero JSF columns"
                );
            }
        }
    }

    /// Exercises the overflow path that the field-element test never hits: a limb with the top
    /// bit set, where a `-1` digit's `+1` carries out of the top limb and must be absorbed by the
    /// headroom limb. Reconstructs the recoded integers directly (values < 2^65, so i128 is exact)
    /// rather than in the field, which would reduce mod p.
    #[test]
    fn jsf_handles_full_width_limbs() {
        // All-ones single limb (= 2^64 - 1): first step picks -1 (MAX ≡ 3 mod 4), so `+1` carries.
        let digits = joint_sparse_form(&[u64::MAX], &[u64::MAX]);
        let (mut r1, mut r2) = (0i128, 0i128);
        for &(u1, u2) in &digits {
            r1 = r1 * 2 + u1 as i128;
            r2 = r2 * 2 + u2 as i128;
        }
        assert_eq!(r1, u64::MAX as i128);
        assert_eq!(r2, u64::MAX as i128);

        // Mixed widths: full-width first limb plus a second limb.
        let digits = joint_sparse_form(&[u64::MAX, 0x1234], &[u64::MAX, 0]);
        let (mut r1, mut r2) = (0i128, 0i128);
        for &(u1, u2) in &digits {
            r1 = r1 * 2 + u1 as i128;
            r2 = r2 * 2 + u2 as i128;
        }
        assert_eq!(r1, ((0x1234i128) << 64) + u64::MAX as i128);
        assert_eq!(r2, u64::MAX as i128);
    }

    #[test]
    fn double_scalar_mul_variants_agree() {
        let mut rng = StdRng::seed_from_u64(1);
        for _ in 0..25 {
            let b1 = Projective::<G>::rand(&mut rng);
            let b2 = Projective::<G>::rand(&mut rng);
            let k1 = Fr::rand(&mut rng);
            let k2 = Fr::rand(&mut rng);

            let expected = naive(b1, k1, b2, k2);
            assert_eq!(binary_scalar_mul_shamir(b1, k1, b2, k2), expected);
            assert_eq!(binary_scalar_mul_jsf(b1, k1, b2, k2), expected);

            let (a1, a2) = (b1.into_affine(), b2.into_affine());
            assert_eq!(binary_scalar_mul_jsf_affine(&a1, k1, &a2, k2), expected);
        }
    }

    #[test]
    fn double_scalar_mul_edge_cases() {
        let mut rng = StdRng::seed_from_u64(2);
        let b1 = Projective::<G>::rand(&mut rng);
        let b2 = Projective::<G>::rand(&mut rng);
        let k = Fr::rand(&mut rng);
        let (a1, a2) = (b1.into_affine(), b2.into_affine());

        let cases: [(Projective<G>, Fr, Projective<G>, Fr); 7] = [
            // One scalar zero (either side), both zero.
            (b1, Fr::ZERO, b2, k),
            (b1, k, b2, Fr::ZERO),
            (b1, Fr::ZERO, b2, Fr::ZERO),
            // Scalars one.
            (b1, Fr::one(), b2, Fr::one()),
            // Equal bases, opposite bases (sum is the identity), same base/scalar.
            (b1, k, b1, k),
            (b1, k, -b1, k),
            (b1, Fr::one(), -b1, Fr::one()),
        ];

        for (p1, s1, p2, s2) in cases {
            let expected = naive(p1, s1, p2, s2);
            assert_eq!(binary_scalar_mul_shamir(p1, s1, p2, s2), expected);
            assert_eq!(binary_scalar_mul_jsf(p1, s1, p2, s2), expected);
            assert_eq!(
                binary_scalar_mul_jsf_affine(&p1.into_affine(), s1, &p2.into_affine(), s2),
                expected
            );
        }

        // Affine variant with the original affine points.
        assert_eq!(
            binary_scalar_mul_jsf_affine(&a1, k, &a2, k),
            naive(b1, k, b2, k)
        );
    }

    #[test]
    fn timing_double_scalar_mul() {
        use ark_ec::VariableBaseMSM;
        use std::time::Instant;

        macro_rules! run_timing {
            ($cfg:ty, $label:expr) => {{
                type C = $cfg;
                type S = <C as CurveConfig>::ScalarField;
                type In = (Projective<C>, Projective<C>, Affine<C>, Affine<C>, S, S);

                let mut rng = StdRng::seed_from_u64(7);
                let n = 2000usize;
                let inputs: Vec<In> = (0..n)
                    .map(|_| {
                        let b1 = Projective::<C>::rand(&mut rng);
                        let b2 = Projective::<C>::rand(&mut rng);
                        let k1 = S::rand(&mut rng);
                        let k2 = S::rand(&mut rng);
                        (b1, b2, b1.into_affine(), b2.into_affine(), k1, k2)
                    })
                    .collect();

                // All variants must agree before we trust the timings.
                {
                    let (b1, b2, a1, a2, k1, k2) = inputs[0];
                    let expected = b1 * k1 + b2 * k2;
                    assert_eq!(
                        Projective::<C>::msm_unchecked(&[a1, a2], &[k1, k2]),
                        expected
                    );
                    assert_eq!(binary_scalar_mul_shamir(b1, k1, b2, k2), expected);
                    assert_eq!(binary_scalar_mul_jsf(b1, k1, b2, k2), expected);
                    assert_eq!(binary_scalar_mul_jsf_affine(&a1, k1, &a2, k2), expected);
                }

                macro_rules! time_one {
                    ($name:expr, $f:expr) => {{
                        let f = $f;
                        let start = Instant::now();
                        let mut acc = Projective::<C>::zero();
                        for x in &inputs {
                            acc += core::hint::black_box(f(x));
                        }
                        let _ = core::hint::black_box(acc);
                        let el = start.elapsed();
                        println!(
                            "  {:24} {:>13?} total  {:>11?}/op",
                            $name,
                            el,
                            el / n as u32
                        );
                    }};
                }

                println!("== {} ({} double-scalar muls) ==", $label, n);
                time_one!("msm_unchecked(2)", |x: &In| {
                    Projective::<C>::msm_unchecked(&[x.2, x.3], &[x.4, x.5])
                });
                time_one!("Shamir", |x: &In| binary_scalar_mul_shamir(
                    x.0, x.4, x.1, x.5
                ));
                time_one!("JSF projective", |x: &In| binary_scalar_mul_jsf(
                    x.0, x.4, x.1, x.5
                ));
                time_one!("JSF affine", |x: &In| {
                    binary_scalar_mul_jsf_affine(&x.2, x.4, &x.3, x.5)
                });
            }};
        }

        run_timing!(PallasConfig, "Pallas");
        run_timing!(ark_vesta::VestaConfig, "Vesta");
    }
}
