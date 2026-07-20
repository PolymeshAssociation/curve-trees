#![allow(non_snake_case)]

//! Experimental: Variant of the original inner product proof to use polynomial folding rather than
//! Laurent folding; avoiding inverses for both prover and verifier. Described [here](https://reports.zksecurity.xyz/reports/generalized-bulletproofs/)

extern crate alloc;

use alloc::borrow::Borrow;
use alloc::{vec, vec::Vec};

use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress};
use ark_std::{cfg_into_iter, cfg_iter, cfg_iter_mut, One, Zero};
use core::iter;
use dock_crypto_utils::transcript::MerlinTranscript;
use zeroize::Zeroize;

use crate::errors::ProofError;
use crate::inner_product_proof::inner_product;
use crate::msm::binary_scalar_mul_jsf_affine;
use crate::transcript::TranscriptProtocol;

/// Inner-product proof using polynomial folding: `G' = G_L + u*G_R`, `a' = u*a_L + a_R`,
/// `H' = u*H_L + H_R`, `b' = b_L + u*b_R`. Round relation: `P' = u^2*L + u*P + R`.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct InnerProductProofAlt<C: AffineRepr> {
    pub(crate) L_vec: Vec<C>,
    pub(crate) R_vec: Vec<C>,
    pub(crate) a: C::ScalarField,
    pub(crate) b: C::ScalarField,
}

impl<C: AffineRepr> InnerProductProofAlt<C> {
    pub fn create(
        transcript: &mut MerlinTranscript,
        Q: &C,
        G_factors: &[C::ScalarField],
        H_factors: &[C::ScalarField],
        mut G_vec: Vec<C>,
        mut H_vec: Vec<C>,
        mut a_vec: Vec<C::ScalarField>,
        mut b_vec: Vec<C::ScalarField>,
    ) -> Result<InnerProductProofAlt<C>, ProofError> {
        #[cfg(feature = "parallel")]
        use rayon::prelude::*;

        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);
        assert_eq!(G_factors.len(), n);
        assert_eq!(H_factors.len(), n);
        assert!(n.is_power_of_two());

        transcript.innerproduct_domain_sep(n as u64);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        let mut first_round = true;

        while n != 1 {
            n /= 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(a_L, b_R);
            let c_R = inner_product(a_R, b_L);

            // L/R scalars and points
            let (mut l_scalars, mut r_scalars): (Vec<C::ScalarField>, Vec<C::ScalarField>) =
                if first_round {
                    (
                        a_L.iter()
                            .zip(G_factors[n..].iter())
                            .map(|(a_val, g)| *a_val * *g)
                            .chain(
                                b_R.iter()
                                    .zip(H_factors[..n].iter())
                                    .map(|(b_val, h)| *b_val * *h),
                            )
                            .chain(iter::once(c_L))
                            .collect(),
                        a_R.iter()
                            .zip(G_factors[..n].iter())
                            .map(|(a_val, g)| *a_val * *g)
                            .chain(
                                b_L.iter()
                                    .zip(H_factors[n..].iter())
                                    .map(|(b_val, h)| *b_val * *h),
                            )
                            .chain(iter::once(c_R))
                            .collect(),
                    )
                } else {
                    (
                        a_L.iter()
                            .chain(b_R.iter())
                            .chain(iter::once(&c_L))
                            .copied()
                            .collect(),
                        a_R.iter()
                            .chain(b_L.iter())
                            .chain(iter::once(&c_R))
                            .copied()
                            .collect(),
                    )
                };

            let l_points: Vec<C> = G_R
                .iter()
                .chain(H_L.iter())
                .chain(iter::once(Q))
                .copied()
                .collect();
            let r_points: Vec<C> = G_L
                .iter()
                .chain(H_R.iter())
                .chain(iter::once(Q))
                .copied()
                .collect();

            #[cfg(feature = "parallel")]
            let (L, R): (C, C) = rayon::join(
                || C::Group::msm_unchecked(l_points.as_slice(), l_scalars.as_slice()).into(),
                || C::Group::msm_unchecked(r_points.as_slice(), r_scalars.as_slice()).into(),
            );
            #[cfg(not(feature = "parallel"))]
            let (L, R): (C, C) = (
                C::Group::msm_unchecked(l_points.as_slice(), l_scalars.as_slice()).into(),
                C::Group::msm_unchecked(r_points.as_slice(), r_scalars.as_slice()).into(),
            );

            l_scalars.zeroize();
            r_scalars.zeroize();

            L_vec.push(L);
            R_vec.push(R);

            transcript.append_point(b"L", &L);
            transcript.append_point(b"R", &R);

            let u = TranscriptProtocol::challenge_scalar::<C>(transcript, b"u");

            // Scalar folds: a' = u*a_L + a_R, b' = b_L + u*b_R.
            cfg_iter_mut!(a_L)
                .zip(cfg_iter!(a_R))
                .for_each(|(a_l, a_r)| *a_l = *a_l * u + *a_r);
            cfg_iter_mut!(b_L)
                .zip(cfg_iter!(b_R))
                .for_each(|(b_l, b_r)| *b_l = *b_l + u * *b_r);

            let (g_l, g_r): (&[C], &[C]) = (G_L, G_R);
            let (h_l, h_r): (&[C], &[C]) = (H_L, H_R);

            // First round absorbs G_factors/H_factors
            // Later rounds: G'[i] = G_L[i] + u*G_R[i], H'[i] = u*H_L[i] + H_R[i]
            let folded_G: Vec<C::Group> = cfg_into_iter!(0..n)
                .map(|i| {
                    if first_round {
                        // G'[i] = G_factors[i]*G_L[i] + (u*G_factors[n+i])*G_R[i]
                        binary_scalar_mul_jsf_affine(
                            &g_l[i],
                            G_factors[i],
                            &g_r[i],
                            u * G_factors[n + i],
                        )
                    } else {
                        // G'[i] = G_L[i] + u*G_R[i]
                        let mut acc = g_r[i].into_group() * u;
                        acc += g_l[i];
                        acc
                    }
                })
                .collect();
            let folded_H: Vec<C::Group> = cfg_into_iter!(0..n)
                .map(|i| {
                    if first_round {
                        // H'[i] = (u*H_factors[i])*H_L[i] + H_factors[n+i]*H_R[i]
                        binary_scalar_mul_jsf_affine(
                            &h_l[i],
                            u * H_factors[i],
                            &h_r[i],
                            H_factors[n + i],
                        )
                    } else {
                        // H'[i] = u*H_L[i] + H_R[i]
                        let mut acc = h_l[i].into_group() * u;
                        acc += h_r[i];
                        acc
                    }
                })
                .collect();

            G_L.copy_from_slice(&C::Group::normalize_batch(&folded_G));
            H_L.copy_from_slice(&C::Group::normalize_batch(&folded_H));

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;

            first_round = false;
        }

        let proof = InnerProductProofAlt {
            L_vec,
            R_vec,
            a: a[0],
            b: b[0],
        };

        a_vec.zeroize();
        b_vec.zeroize();

        Ok(proof)
    }

    /// Returns `(l_coeffs, r_coeffs, s, xi_prod)` for use in a combined MSM.
    /// Unrolling `P_k = u_k^2*L_k + u_k*P_{k-1} + R_k` gives
    /// `P_m = xi_prod*P + Σ_k [r_coeffs[k]*(u_k^2*L_k + R_k)]` where:
    /// - `l_coeffs[k] = u_k^2 * \prod_{j>k} u_j`
    /// - `r_coeffs[k] = \prod_{j>k} u_j`
    /// - `xi_prod = \prod_k u_k`
    /// - `s[i] = \prod_{k where bit k of i is set} u_k`, base `s[0] = 1`.
    /// H-side coefficient for H[i] is `s[n-1-i]`.
    pub(crate) fn verification_scalars(
        &self,
        n: usize,
        transcript: &mut MerlinTranscript,
    ) -> Result<
        (
            Vec<C::ScalarField>,
            Vec<C::ScalarField>,
            Vec<C::ScalarField>,
            C::ScalarField,
        ),
        ProofError,
    > {
        if self.L_vec.len() != self.R_vec.len() {
            return Err(ProofError::VerificationError);
        }
        let lg_n = self.L_vec.len();
        if lg_n >= 32 {
            return Err(ProofError::VerificationError);
        }
        if n != (1 << lg_n) {
            return Err(ProofError::VerificationError);
        }

        transcript.innerproduct_domain_sep(n as u64);

        // Recompute challenges in creation order [u_1, .., u_{lg_n}].
        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.validate_and_append_point(b"L", L)?;
            transcript.validate_and_append_point(b"R", R)?;
            challenges.push(TranscriptProtocol::challenge_scalar::<C>(transcript, b"u"));
        }

        // Backward suffix scan: suffix = \prod_{j>k} u_j, after full scan = xi_prod = \prod u_k.
        let mut l_coeffs = vec![C::ScalarField::zero(); lg_n];
        let mut r_coeffs = vec![C::ScalarField::zero(); lg_n];
        let mut suffix = C::ScalarField::one();
        for k in (0..lg_n).rev() {
            r_coeffs[k] = suffix;
            let u = challenges[k];
            l_coeffs[k] = u * u * suffix;
            suffix *= u;
        }
        let xi_prod = suffix;

        // s[i] = product of challenges at rounds where the corresponding bit of i is set. Same
        // induction as the classic s-vector but using the raw challenge and base s[0] = 1.
        let mut s = Vec::with_capacity(n);
        s.push(C::ScalarField::one());
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            let u_lg_i = challenges[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i);
        }

        Ok((l_coeffs, r_coeffs, s, xi_prod))
    }

    #[allow(dead_code)]
    pub fn verify<IG, IH>(
        &self,
        n: usize,
        transcript: &mut MerlinTranscript,
        G_factors: IG,
        H_factors: IH,
        P: &C,
        Q: &C,
        G: &[C],
        H: &[C],
    ) -> Result<(), ProofError>
    where
        IG: IntoIterator,
        IG::Item: Borrow<C::ScalarField>,
        IH: IntoIterator,
        IH::Item: Borrow<C::ScalarField>,
    {
        let (l_coeffs, r_coeffs, s, xi_prod) = self.verification_scalars(n, transcript)?;

        let g_times_a_times_s = G_factors
            .into_iter()
            .zip(s.iter())
            .map(|(g_i, s_i)| (self.a * s_i) * g_i.borrow())
            .take(G.len());

        let s_rev = s.iter().rev();
        let h_times_b_times_s = H_factors
            .into_iter()
            .zip(s_rev)
            .map(|(h_i, s_i_rev)| (self.b * s_i_rev) * h_i.borrow());

        let neg_l = l_coeffs.iter().map(|c| -*c);
        let neg_r = r_coeffs.iter().map(|c| -*c);

        // Checks: 0 = a*b*Q + \sum{a*s[i]*G_factors[i]}*G[i] + \sum{b*s[n-1-i]*H_factors[i]}*H[i]
        //               - \sum{l_coeffs[k]*L[k]} - \sum{r_coeffs[k]*R[k]} - xi_prod*P
        let result = C::Group::msm_unchecked(
            iter::once(Q)
                .chain(G.iter())
                .chain(H.iter())
                .chain(self.L_vec.iter())
                .chain(self.R_vec.iter())
                .chain(iter::once(P))
                .copied()
                .collect::<Vec<C>>()
                .as_slice(),
            iter::once(self.a * self.b)
                .chain(g_times_a_times_s)
                .chain(h_times_b_times_s)
                .chain(neg_l)
                .chain(neg_r)
                .chain(iter::once(-xi_prod))
                .collect::<Vec<C::ScalarField>>()
                .as_slice(),
        );

        if result.is_zero() {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    #[allow(dead_code)]
    pub fn serialized_size(&self, compress: Compress) -> usize {
        let scalars_size = self.a.serialized_size(compress) * 2;
        let l_and_r_size = self.L_vec.serialized_size(compress) * 2;
        scalars_size + l_and_r_size
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inner_product_proof::{inner_product, InnerProductProof};
    use crate::{affine_from_bytes_tai, util, BulletproofGens};
    use ark_pallas::Affine;
    use ark_serialize::CanonicalSerialize;
    use ark_std::rand::{prelude::StdRng, Rng, SeedableRng};
    use ark_std::UniformRand;
    use std::time::{Duration, Instant};
    use test_log::test;

    type F = <Affine as AffineRepr>::ScalarField;

    fn test_helper_create(n: usize) -> Result<(), ProofError> {
        let seed = [
            1, 0, 0, 0, 23, 0, 0, 0, 200, 1, 0, 0, 210, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ];
        let mut rng = StdRng::from_seed(seed);

        let bp_gens = BulletproofGens::<Affine>::new(n as u32, 1);
        let G: Vec<_> = bp_gens.share(0).G(n as u32).copied().collect();
        let H: Vec<_> = bp_gens.share(0).H(n as u32).copied().collect();
        let Q = affine_from_bytes_tai::<Affine>(b"test point").unwrap();

        let a: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let b: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let c = inner_product(&a, &b);

        let G_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();
        let y_inv: F = rng.gen();
        let H_factors: Vec<F> = util::exp_iter(y_inv).take(n).collect();

        // P = <a,G> + <b*H_factors, H> + <a,b>*Q
        let b_prime: Vec<F> = b
            .iter()
            .zip(util::exp_iter(y_inv))
            .map(|(bi, yi)| *bi * yi)
            .collect();
        let P: Affine = <Affine as AffineRepr>::Group::msm_unchecked(
            G.iter()
                .chain(H.iter())
                .chain(core::iter::once(&Q))
                .copied()
                .collect::<Vec<_>>()
                .as_slice(),
            a.iter()
                .copied()
                .chain(b_prime.iter().copied())
                .chain(core::iter::once(c))
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .into();

        let mut t = MerlinTranscript::new(b"invfreeipptest");
        let proof = InnerProductProofAlt::create(
            &mut t,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        )?;

        let mut t = MerlinTranscript::new(b"invfreeipptest");
        proof.verify(
            n,
            &mut t,
            core::iter::repeat(F::one()).take(n),
            util::exp_iter(y_inv).take(n),
            &P,
            &Q,
            &G,
            &H,
        )?;

        let mut buf = Vec::with_capacity(proof.serialized_size(Compress::Yes));
        proof.serialize_compressed(&mut buf).unwrap();
        let proof2 = InnerProductProofAlt::<Affine>::deserialize_compressed(&buf[..]).unwrap();

        let mut t = MerlinTranscript::new(b"invfreeipptest");
        proof2.verify(
            n,
            &mut t,
            core::iter::repeat(F::one()).take(n),
            util::exp_iter(y_inv).take(n),
            &P,
            &Q,
            &G,
            &H,
        )?;

        Ok(())
    }

    #[test]
    fn make_ipp_1() -> Result<(), ProofError> {
        test_helper_create(1)
    }

    #[test]
    fn make_ipp_2() -> Result<(), ProofError> {
        test_helper_create(2)
    }

    #[test]
    fn make_ipp_4() -> Result<(), ProofError> {
        test_helper_create(4)
    }

    #[test]
    fn make_ipp_32() -> Result<(), ProofError> {
        test_helper_create(32)
    }

    #[test]
    fn make_ipp_64() -> Result<(), ProofError> {
        test_helper_create(64)
    }

    /// Tampered P must be rejected.
    #[test]
    fn tampered_P_rejected() {
        let mut rng = StdRng::from_seed([42u8; 32]);
        let n = 4;
        let bp_gens = BulletproofGens::<Affine>::new(n as u32, 1);
        let G: Vec<_> = bp_gens.share(0).G(n as u32).copied().collect();
        let H: Vec<_> = bp_gens.share(0).H(n as u32).copied().collect();
        let Q = affine_from_bytes_tai::<Affine>(b"test point").unwrap();
        let a: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let b: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let G_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();
        let H_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();

        let c = inner_product(&a, &b);
        let P: Affine = <Affine as AffineRepr>::Group::msm_unchecked(
            G.iter()
                .chain(H.iter())
                .chain(core::iter::once(&Q))
                .copied()
                .collect::<Vec<_>>()
                .as_slice(),
            a.iter()
                .copied()
                .chain(b.iter().copied())
                .chain(core::iter::once(c))
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .into();

        let mut t = MerlinTranscript::new(b"test");
        let proof = InnerProductProofAlt::create(
            &mut t,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a,
            b,
        )
        .unwrap();

        let bad_P: Affine = (P.into_group() + Q).into();

        let mut t = MerlinTranscript::new(b"test");
        assert!(proof
            .verify(
                n,
                &mut t,
                core::iter::repeat(F::one()).take(n),
                core::iter::repeat(F::one()).take(n),
                &bad_P,
                &Q,
                &G,
                &H,
            )
            .is_err());
    }

    fn valid_proof(n: usize) -> InnerProductProofAlt<Affine> {
        let mut rng = StdRng::from_seed([0u8; 32]);
        let bp_gens = BulletproofGens::<Affine>::new(n as u32, 1);
        let G: Vec<_> = bp_gens.share(0).G(n as u32).copied().collect();
        let H: Vec<_> = bp_gens.share(0).H(n as u32).copied().collect();
        let Q = affine_from_bytes_tai::<Affine>(b"test point").unwrap();
        let a: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let b: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let G_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();
        let H_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();
        let mut t = MerlinTranscript::new(b"test");
        InnerProductProofAlt::create(&mut t, &Q, &G_factors, &H_factors, G, H, a, b).unwrap()
    }

    #[test]
    fn input_validate_verifier() {
        // Unequal L_vec/R_vec lengths.
        let proof = valid_proof(4);
        let mut bad = proof.clone();
        bad.L_vec.push(bad.L_vec[0]);
        let mut t = MerlinTranscript::new(b"test");
        assert!(bad.verification_scalars(4, &mut t).is_err());

        // Consistent extension -> lg_n grows but caller-fixed n stays 4.
        let proof = valid_proof(4);
        let mut bad = proof.clone();
        bad.L_vec.push(bad.L_vec[0]);
        bad.R_vec.push(bad.R_vec[0]);
        let mut t = MerlinTranscript::new(b"test");
        assert!(bad.verification_scalars(4, &mut t).is_err());

        // Truncated.
        let proof = valid_proof(4);
        let mut short = proof.clone();
        short.L_vec.pop();
        short.R_vec.pop();
        let mut t = MerlinTranscript::new(b"test");
        assert!(short.verification_scalars(4, &mut t).is_err());

        // Empty vectors.
        let proof = valid_proof(4);
        let mut empty = proof;
        empty.L_vec.clear();
        empty.R_vec.clear();
        let mut t = MerlinTranscript::new(b"test");
        assert!(empty.verification_scalars(4, &mut t).is_err());

        // lg_n >= 32 overflow guard.
        let proof = valid_proof(4);
        let mut big = proof;
        for _ in 0..32 {
            big.L_vec.push(big.L_vec[0]);
            big.R_vec.push(big.R_vec[0]);
        }
        let mut t = MerlinTranscript::new(b"test");
        assert!(big.verification_scalars(1usize << 20, &mut t).is_err());
    }

    #[test]
    fn cross_check_same_P() {
        let mut rng = StdRng::from_seed([7u8; 32]);
        let n = 8;
        let bp_gens = BulletproofGens::<Affine>::new(n as u32, 1);
        let G: Vec<_> = bp_gens.share(0).G(n as u32).copied().collect();
        let H: Vec<_> = bp_gens.share(0).H(n as u32).copied().collect();
        let Q = affine_from_bytes_tai::<Affine>(b"test point").unwrap();
        let a: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let b: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
        let G_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();
        let H_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();

        let c = inner_product(&a, &b);
        let P: Affine = <Affine as AffineRepr>::Group::msm_unchecked(
            G.iter()
                .chain(H.iter())
                .chain(core::iter::once(&Q))
                .copied()
                .collect::<Vec<_>>()
                .as_slice(),
            a.iter()
                .copied()
                .chain(b.iter().copied())
                .chain(core::iter::once(c))
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .into();

        // Classic proof verifies.
        let mut t = MerlinTranscript::new(b"classic");
        let classic = InnerProductProof::create(
            &mut t,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        )
        .unwrap();
        let mut t = MerlinTranscript::new(b"classic");
        classic
            .verify(
                n,
                &mut t,
                core::iter::repeat(F::one()).take(n),
                core::iter::repeat(F::one()).take(n),
                &P,
                &Q,
                &G,
                &H,
            )
            .unwrap();

        // Inversion-free proof verifies the same P.
        let mut t = MerlinTranscript::new(b"invfree");
        let inv_free = InnerProductProofAlt::create(
            &mut t,
            &Q,
            &G_factors,
            &H_factors,
            G.clone(),
            H.clone(),
            a.clone(),
            b.clone(),
        )
        .unwrap();
        let mut t = MerlinTranscript::new(b"invfree");
        inv_free
            .verify(
                n,
                &mut t,
                core::iter::repeat(F::one()).take(n),
                core::iter::repeat(F::one()).take(n),
                &P,
                &Q,
                &G,
                &H,
            )
            .unwrap();

        // The two proofs encode different L/R values (different fold). Assert they differ.
        assert_ne!(classic.L_vec, inv_free.L_vec);

        // A classic proof must NOT verify under the inv-free verifier (different round relation).
        let classic_as_invfree = InnerProductProofAlt {
            L_vec: classic.L_vec.clone(),
            R_vec: classic.R_vec.clone(),
            a: classic.a,
            b: classic.b,
        };
        let mut t = MerlinTranscript::new(b"invfree");
        assert!(classic_as_invfree
            .verify(
                n,
                &mut t,
                core::iter::repeat(F::one()).take(n),
                core::iter::repeat(F::one()).take(n),
                &P,
                &Q,
                &G,
                &H,
            )
            .is_err());
    }

    #[test]
    fn compare_ipp() {
        const REPS: usize = 30;

        for &n in &[1024usize, 2048, 4096] {
            let mut rng = StdRng::from_seed([0u8; 32]);
            let bp_gens = BulletproofGens::<Affine>::new(n as u32, 1);
            let G: Vec<_> = bp_gens.share(0).G(n as u32).copied().collect();
            let H: Vec<_> = bp_gens.share(0).H(n as u32).copied().collect();
            let Q = affine_from_bytes_tai::<Affine>(b"bench").unwrap();
            let G_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();
            let H_factors: Vec<F> = core::iter::repeat(F::one()).take(n).collect();

            let inputs: Vec<(Vec<F>, Vec<F>, Affine)> = (0..REPS)
                .map(|_| {
                    let a: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
                    let b: Vec<F> = (0..n).map(|_| F::rand(&mut rng)).collect();
                    let c = inner_product(&a, &b);
                    let P: Affine = <Affine as AffineRepr>::Group::msm_unchecked(
                        G.iter()
                            .chain(H.iter())
                            .chain(core::iter::once(&Q))
                            .copied()
                            .collect::<Vec<_>>()
                            .as_slice(),
                        a.iter()
                            .copied()
                            .chain(b.iter().copied())
                            .chain(core::iter::once(c))
                            .collect::<Vec<_>>()
                            .as_slice(),
                    )
                    .into();
                    (a, b, P)
                })
                .collect();

            let classic_proofs: Vec<InnerProductProof<Affine>> = inputs
                .iter()
                .map(|(a, b, _)| {
                    let mut t = MerlinTranscript::new(b"bench");
                    InnerProductProof::create(
                        &mut t,
                        &Q,
                        &G_factors,
                        &H_factors,
                        G.clone(),
                        H.clone(),
                        a.clone(),
                        b.clone(),
                    )
                    .unwrap()
                })
                .collect();
            let invfree_proofs: Vec<InnerProductProofAlt<Affine>> = inputs
                .iter()
                .map(|(a, b, _)| {
                    let mut t = MerlinTranscript::new(b"bench");
                    InnerProductProofAlt::create(
                        &mut t,
                        &Q,
                        &G_factors,
                        &H_factors,
                        G.clone(),
                        H.clone(),
                        a.clone(),
                        b.clone(),
                    )
                    .unwrap()
                })
                .collect();

            let unit = || core::iter::repeat(F::one()).take(n);
            let classic_create = |a: &Vec<F>, b: &Vec<F>| {
                let mut t = MerlinTranscript::new(b"bench");
                core::hint::black_box(
                    InnerProductProof::create(
                        &mut t,
                        &Q,
                        &G_factors,
                        &H_factors,
                        core::hint::black_box(G.clone()),
                        core::hint::black_box(H.clone()),
                        core::hint::black_box(a.clone()),
                        core::hint::black_box(b.clone()),
                    )
                    .unwrap(),
                );
            };
            let invfree_create = |a: &Vec<F>, b: &Vec<F>| {
                let mut t = MerlinTranscript::new(b"bench");
                core::hint::black_box(
                    InnerProductProofAlt::create(
                        &mut t,
                        &Q,
                        &G_factors,
                        &H_factors,
                        core::hint::black_box(G.clone()),
                        core::hint::black_box(H.clone()),
                        core::hint::black_box(a.clone()),
                        core::hint::black_box(b.clone()),
                    )
                    .unwrap(),
                );
            };

            classic_create(&inputs[0].0, &inputs[0].1);
            invfree_create(&inputs[0].0, &inputs[0].1);

            let (mut cc_min, mut ic_min, mut cv_min, mut iv_min) =
                (Duration::MAX, Duration::MAX, Duration::MAX, Duration::MAX);
            let (mut cc_sum, mut ic_sum, mut cv_sum, mut iv_sum) = (
                Duration::ZERO,
                Duration::ZERO,
                Duration::ZERO,
                Duration::ZERO,
            );

            for rep in 0..REPS {
                let (a, b, P) = &inputs[rep];

                let t = Instant::now();
                classic_create(a, b);
                let d = t.elapsed();
                cc_min = cc_min.min(d);
                cc_sum += d;

                let t = Instant::now();
                invfree_create(a, b);
                let d = t.elapsed();
                ic_min = ic_min.min(d);
                ic_sum += d;

                let t = Instant::now();
                let _ = core::hint::black_box(classic_proofs[rep].verify(
                    n,
                    &mut MerlinTranscript::new(b"bench"),
                    unit(),
                    unit(),
                    P,
                    &Q,
                    &G,
                    &H,
                ));
                let d = t.elapsed();
                cv_min = cv_min.min(d);
                cv_sum += d;

                let t = Instant::now();
                let _ = core::hint::black_box(invfree_proofs[rep].verify(
                    n,
                    &mut MerlinTranscript::new(b"bench"),
                    unit(),
                    unit(),
                    P,
                    &Q,
                    &G,
                    &H,
                ));
                let d = t.elapsed();
                iv_min = iv_min.min(d);
                iv_sum += d;
            }

            let mean = |s: Duration| s / REPS as u32;
            println!(
                "n={n:5} | create classic min {:>9?} (mean {:>9?}) | invfree min {:>9?} (mean {:>9?}) | speedup {:.2}x",
                cc_min, mean(cc_sum), ic_min, mean(ic_sum),
                cc_min.as_secs_f64() / ic_min.as_secs_f64(),
            );
            println!(
                "n={n:5} | verify classic min {:>9?} (mean {:>9?}) | invfree min {:>9?} (mean {:>9?}) | speedup {:.2}x",
                cv_min, mean(cv_sum), iv_min, mean(iv_sum),
                cv_min.as_secs_f64() / iv_min.as_secs_f64(),
            );
        }
    }
}
