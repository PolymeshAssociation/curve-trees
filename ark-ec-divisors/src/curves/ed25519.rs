use ark_std::sync::LazyLock;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_ec::{AffineRepr, CurveGroup};

use ark_ed25519::{EdwardsAffine, EdwardsConfig, EdwardsProjective, Fq, Fr};
use crypto_bigint::{Encoding, U256};
use rand_core::CryptoRngCore;
use crate::{Projective, Interpolator, DivisorCurve};

impl DivisorCurve for EdwardsProjective {
    type Config = EdwardsConfig;
    type BaseField = Fq;
    type ScalarField = Fr;
    type XyPoint = Projective<Self>;

    // Wei25519 a/b
    // https://www.ietf.org/archive/id/draft-ietf-lwig-curve-representations-02.pdf E.3
    fn a() -> Self::BaseField {
        let a_val = U256::from_be_hex(
            "2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa984914a144",
        );
        // Convert U256 to Fq using BigInteger
        let bytes = a_val.to_be_bytes();
        Fq::from_be_bytes_mod_order(&bytes)
    }

    fn b() -> Self::BaseField {
        let b_val = U256::from_be_hex(
            "7b425ed097b425ed097b425ed097b425ed097b425ed097b4260b5e9c7710c864",
        );
        // Convert U256 to Fq using BigInteger
        let bytes = b_val.to_be_bytes();
        Fq::from_be_bytes_mod_order(&bytes)
    }

    type BorrowedInterpolator = &'static Interpolator<Self::BaseField>;
    fn interpolator_for_scalar_mul() -> Self::BorrowedInterpolator {
        static PRECOMPUTE: LazyLock<Interpolator<Fq>> =
            LazyLock::new(|| Interpolator::new(128));
        &*PRECOMPUTE
    }

    fn generator() -> Self {
        <EdwardsProjective as CurveGroup>::generator()
    }

    fn add(self, other: Self) -> Self {
        self + other
    }

    fn neg(self) -> Self {
        -self
    }

    fn mul(self, scalar: Self::ScalarField) -> Self {
        self * scalar
    }

    fn random<R: CryptoRngCore>(rng: &mut R) -> Self {
        todo!()
    }

    // https://www.ietf.org/archive/id/draft-ietf-lwig-curve-representations-02.pdf E.2
    fn to_xy(point: Self) -> Option<(Self::BaseField, Self::BaseField)> {
        let affine: EdwardsAffine = point.into();
        if affine.is_zero() {
            return None;
        }

        // Get Edwards coordinates
        let edwards_x = affine.x;
        let edwards_y = affine.y;

        use crypto_bigint::{
            modular::runtime_mod::{DynResidueParams, DynResidue},
        };
        // modulus = 2^255 - 19
        const MODULUS: DynResidueParams<{ U256::LIMBS }> =
            DynResidueParams::new(&U256::ONE.shl_vartime(255).wrapping_sub(&U256::from_u64(19)));

        // Calculate Wei25519 coordinates
        const Y_TO_X_MAP_CONST: Fq = {
            let map_val = DynResidue::new(&U256::from_u64(486662), MODULUS)
                .mul(&DynResidue::new(&U256::from_u64(3), MODULUS).invert().0)
                .retrieve();
            let bytes = map_val.to_be_bytes();
            Fq::from_be_bytes_mod_order(&bytes)
        };

        let edwards_y_plus_one = Fq::ONE + edwards_y;
        let one_minus_edwards_y = Fq::ONE - edwards_y;
        let wei_x = (edwards_y_plus_one *
            one_minus_edwards_y
                .inverse()
                .expect("couldn't map non-identity Ed25519 point's y coordinate to Wei25519 x")) +
            Y_TO_X_MAP_CONST;

        const C_SQUARE: DynResidue<{ U256::LIMBS }> =
            DynResidue::new(&U256::from_u64(486662 + 2), MODULUS).neg();
        const C_I: DynResidue<{ U256::LIMBS }> =
            C_SQUARE.pow(&MODULUS.modulus().wrapping_add(&U256::from_u64(3)).shr_vartime(3));
        const SQRT_M1: DynResidue<{ U256::LIMBS }> = DynResidue::new(
            &U256::from_be_hex("2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0"),
            MODULUS,
        );
        const C: Fq = {
            let c_val = C_I.mul(&SQRT_M1).retrieve();
            let bytes = c_val.to_be_bytes();
            Fq::from_be_bytes_mod_order(&bytes)
        };

        let wei_y = C *
            edwards_y_plus_one *
            (one_minus_edwards_y * edwards_x)
                .inverse()
                .expect("couldn't map non-identity Ed25519 point's x coordinate to Wei25519 y");
        Some((wei_x, wei_y))
    }
}