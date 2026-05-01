use crate::errors::ProofError as Error;
use crate::generators::HashToCurveExt;
use ark_ec::hashing::curve_maps::parity;
use ark_ec::short_weierstrass::{Affine as SWAffine, Projective as SWProjective, SWCurveConfig};
use ark_ec::CurveGroup;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use ark_ff::{Field, MontFp, One};
use ark_pallas::{Fq as PallasBase, PallasConfig, Projective as PallasProjective};
use ark_vesta::{Fq as VestaBase, Projective as VestaProjective, VestaConfig};
use sha2::Sha256;

macro_rules! hash_to_curve_naive {
    ($base_field:ty, $curve_config:ty, $projective:ty, $zeta:expr, $iso_a:expr, $iso_b:expr, $iso_consts:expr, $dst:expr, $message:expr) => {{
        let hasher = <DefaultFieldHasher<Sha256> as HashToField<$base_field>>::new($dst);
        let u = hasher.hash_to_field::<2>($message);

        // This is more expensive since the isogeny map is applied twice vs adding points in the isogeny curve first
        // and then applying the isogeny map. But it should be correct as isogeny is a homomorphism.

        let q0 = map_to_curve_simple_swu::<$base_field, $curve_config>(u[0], $zeta, $iso_a, $iso_b);
        let q0 = iso_map::<$base_field, $curve_config>(q0, $iso_consts);

        let q1 = map_to_curve_simple_swu::<$base_field, $curve_config>(u[1], $zeta, $iso_a, $iso_b);
        let q1 = iso_map::<$base_field, $curve_config>(q1, $iso_consts);

        q0 + q1
    }};
}

macro_rules! hash_to_curve {
    ($base_field:ty, $curve_config:ty, $projective:ty, $zeta:expr, $iso_a:expr, $iso_b:expr, $iso_consts:expr, $dst:expr, $message:expr) => {{
        let hasher = <DefaultFieldHasher<Sha256> as HashToField<$base_field>>::new($dst);
        let u = hasher.hash_to_field::<2>($message);

        let q0 = map_to_curve_simple_swu::<$base_field, $curve_config>(u[0], $zeta, $iso_a, $iso_b);
        let q1 = map_to_curve_simple_swu::<$base_field, $curve_config>(u[1], $zeta, $iso_a, $iso_b);

        // Since the base field of both the target and isogeny curves are same and curve constant A is
        // not used (B is same) in point addition unless point doubling. But doubling should rarely happen
        let q0 = <$projective>::new_unchecked(q0.0, q0.1, q0.2);
        let q1 = <$projective>::new_unchecked(q1.0, q1.1, q1.2);
        if q0 == q1 {
            return Err(Error::HashToCurveError);
        }
        let sum = q0 + q1;
        Ok(iso_map::<$base_field, $curve_config>((sum.x, sum.y, sum.z), $iso_consts))
    }};
}

pub fn hash_to_pallas_slow(dst: &[u8], message: &[u8]) -> PallasProjective {
    hash_to_curve_naive!(
        PallasBase,
        PallasConfig,
        PallasProjective,
        PALLAS_ZETA,
        ISO_PALLAS_A,
        ISO_PALLAS_B,
        &ISO_PALLAS_CONSTS,
        dst,
        message
    )
}

/// This can fail if both calls to `map_to_curve_simple_swu` generate the same point.
/// This would rarely happen in practice.
/// Faster than `hash_to_pallas_slow`
pub fn hash_to_pallas_fallible(dst: &[u8], message: &[u8]) -> Result<PallasProjective, Error> {
    hash_to_curve!(
        PallasBase,
        PallasConfig,
        PallasProjective,
        PALLAS_ZETA,
        ISO_PALLAS_A,
        ISO_PALLAS_B,
        &ISO_PALLAS_CONSTS,
        dst,
        message
    )
}

pub fn hash_to_vesta_slow(dst: &[u8], message: &[u8]) -> VestaProjective {
    hash_to_curve_naive!(
        VestaBase,
        VestaConfig,
        VestaProjective,
        VESTA_ZETA,
        ISO_VESTA_A,
        ISO_VESTA_B,
        &ISO_VESTA_CONSTS,
        dst,
        message
    )
}

/// This can fail if both calls to `map_to_curve_simple_swu` generate the same point.
/// This would rarely happen in practice.
/// Faster than `hash_to_vesta_slow`
pub fn hash_to_vesta_fallible(dst: &[u8], message: &[u8]) -> Result<VestaProjective, Error> {
    hash_to_curve!(
        VestaBase,
        VestaConfig,
        VestaProjective,
        VESTA_ZETA,
        ISO_VESTA_A,
        ISO_VESTA_B,
        &ISO_VESTA_CONSTS,
        dst,
        message
    )
}

/// Call the faster but fallible version but fallback to slower version if it fails.
/// This can be variable time but currently fine for our use-case
pub fn hash_to_pallas(dst: &[u8], message: &[u8]) -> PallasProjective {
    if let Ok(p) = hash_to_pallas_fallible(dst, message) {
        p
    } else {
        hash_to_pallas_slow(dst, message)
    }
}

/// Call the faster but fallible version but fallback to slower version if it fails.
/// This can be variable time but currently fine for our use-case
pub fn hash_to_vesta(dst: &[u8], message: &[u8]) -> VestaProjective {
    if let Ok(p) = hash_to_vesta_fallible(dst, message) {
        p
    } else {
        hash_to_vesta_slow(dst, message)
    }
}

impl HashToCurveExt for PallasConfig {
    fn hash_to_curve(dst: &[u8], message: &[u8]) -> SWAffine<Self> {
        hash_to_pallas(dst, message).into_affine()
    }
}

impl HashToCurveExt for VestaConfig {
    fn hash_to_curve(dst: &[u8], message: &[u8]) -> SWAffine<Self> {
        hash_to_vesta(dst, message).into_affine()
    }
}

// pub struct IsoPallas;

// impl SWCurveConfig for IsoPallas {
//     const COEFF_A: Self::BaseField = MontFp!("10949663248450308183708987909873589833737836120165333298109615750520499732811");
//     const COEFF_B: Self::BaseField = MontFp!("1265");
//     // These values are wrong but don't care as they are not used
//     const GENERATOR: SWAffine<Self> = SWAffine::new_unchecked(MontFp!("1265"), MontFp!("1265"));
// }
// Need to define CurveConfig for which i need cofactor of the Isogenous curve

/// Taken from arkworks ark-ec's MapToCurve::map_to_curve but returns point's projective coordinates jacobian
/// This is supposed to be constant time. For variable time like when done for public parameters, a more optimal algorithm can be created
// pub fn map_to_curve_simple_swu<F: Field, P: SWCurveConfig<BaseField = F>, I: SWCurveConfig<BaseField = F>>(element: F, zeta: F) -> SWAffine<I> {
pub fn map_to_curve_simple_swu<F: Field, P: SWCurveConfig<BaseField = F>>(
    element: F,
    zeta: F,
    iso_a: F,
    iso_b: F,
) -> (F, F, F) {
    // 1. tv1 = inv0(Z^2 * u^4 + Z * u^2)
    // 2. x1 = (-B / A) * (1 + tv1)
    // 3. If tv1 == 0, set x1 = B / (Z * A)
    // 4. gx1 = x1^3 + A * x1 + B
    //
    // We use the "Avoiding inversions" optimization in [WB2019, section 4.2]
    // (not to be confused with section 4.3):
    //
    //   here       [WB2019]
    //   -------    ---------------------------------
    //   Z          ξ
    //   u          t
    //   Z * u^2    ξ * t^2 (called u, confusingly)
    //   x1         X_0(t)
    //   x2         X_1(t)
    //   gx1        g(X_0(t))
    //   gx2        g(X_1(t))
    //
    // Using the "here" names:
    //    x1 = num_x1/div      = [B*(Z^2 * u^4 + Z * u^2 + 1)] / [-A*(Z^2 * u^4 + Z * u^2]
    //   gx1 = num_gx1/div_gx1 = [num_x1^3 + A * num_x1 * div^2 + B * div^3] / div^3
    // let a = I::COEFF_A;
    // let b = I::COEFF_B;
    let a = iso_a;
    let b = iso_b;

    // zeta * u^2
    let zeta_u2 = zeta * element.square();
    // zeta^2 * u^4 + zeta * u^2
    let ta = zeta_u2.square() + zeta_u2;
    let num_x1 = b * (ta + <P::BaseField as One>::one());
    // if zeta^2 * u^4 + zeta * u^2 == 0, then a * zeta else -a * (zeta^2 * u^4 + zeta * u^2)
    let div = a * if ta.is_zero() { zeta } else { -ta };

    let num2_x1 = num_x1.square();
    let div2 = div.square();
    let div3 = div2 * div;
    let num_gx1 = (num2_x1 + a * div2) * num_x1 + b * div3;

    // 5. x2 = Z * u^2 * x1
    let num_x2 = zeta_u2 * num_x1; // same div

    // 6. gx2 = x2^3 + A * x2 + B  [optimized out; see below]
    // 7. If is_square(gx1), set x = x1 and y = sqrt(gx1)
    // 8. Else set x = x2 and y = sqrt(gx2)
    let gx1_square;
    let gx1;

    debug_assert!(
        !div3.is_zero(),
        "we have checked that neither a or ZETA are zero. Q.E.D."
    );
    let y1: P::BaseField = {
        gx1 = num_gx1 / div3;
        if gx1.legendre().is_qr() {
            gx1_square = true;
            match gx1.sqrt() {
                Some(y) => y,
                _ => unreachable!("We have checked that gx1 is a quadratic residue. Q.E.D"),
            }
        } else {
            let zeta_gx1 = zeta * gx1;
            gx1_square = false;
            match zeta_gx1.sqrt() {
                Some(y) => y,
                _ => unreachable!("We have checked that ZETA * gx1 is a quadratic residue. Q.E.D"),
            }
        }
    };

    // This optimization also comes from a generalization of [WB2019, section 4.2].
    //
    // We use the specialization with h = Z = ZETA (a fixed quadratic non-residue).
    // Since gx2 = g(Z * u^2 * x1) = Z^3 * u^6 * gx1, when gx1 is not square we take
    // y1 such that y1^2 = Z * gx1 (i.e., y1 = sqrt(Z * gx1)), and then set
    // y2 = Z * u^3 * y1. This gives y2^2 = (Z * u^3)^2 * (Z * gx1) = Z^3 * u^6 * gx1 = gx2,
    // so we avoid computing gx2 explicitly.

    // Not including theta like done in zcash pasta curves as the square root algorithm is different.
    let y2 = zeta_u2 * element * y1;
    let num_x = if gx1_square { num_x1 } else { num_x2 };
    let y = if gx1_square { y1 } else { y2 };

    // let x_affine = num_x / div;
    let y_affine = if parity(&y) == parity(&element) {
        y
    } else {
        -y
    };

    (num_x * div, y_affine * div3, div)
}

/// Taken from pasta_curves crate hashtocurve module.
/// Implements a degree 3 isogeny map.
pub fn iso_map<F: Field, P: SWCurveConfig<BaseField = F>>(
    p: (F, F, F),
    iso: &[F; 13],
) -> SWProjective<P> {
    let (x, y, z) = p;

    let z2 = z.square();
    let z3 = z2 * z;
    let z4 = z2.square();
    let z6 = z3.square();

    let num_x = ((iso[0] * x + iso[1] * z2) * x + iso[2] * z4) * x + iso[3] * z6;
    let div_x = (z2 * x + iso[4] * z4) * x + iso[5] * z6;

    let num_y = (((iso[6] * x + iso[7] * z2) * x + iso[8] * z4) * x + iso[9] * z6) * y;
    let div_y = (((x + iso[10] * z2) * x + iso[11] * z4) * x + iso[12] * z6) * z3;

    let zo = div_x * div_y;
    let xo = num_x * div_y * zo;
    let yo = num_y * div_x * zo.square();
    SWProjective {
        x: xo,
        y: yo,
        z: zo,
    }
}

// These constants are taken from pasta_curves crate.
const ISO_PALLAS_A: PallasBase =
    MontFp!("10949663248450308183708987909873589833737836120165333298109615750520499732811");
const ISO_PALLAS_B: PallasBase = MontFp!("1265");
// Equivalent to 28948022309329048855892746252171976963363056481941560715954676764349967630324
const PALLAS_ZETA: PallasBase = MontFp!("-13");
const ISO_PALLAS_CONSTS: [PallasBase; 13] = [
    MontFp!("6432893846517566412420610278260439325191790329320346825767705947633326140075"),
    MontFp!("23989696149150192365340222745168215001509815558210986772351135915822265203574"),
    MontFp!("10492611921771203378452795982353351666191589197598957448093274638589204800759"),
    MontFp!("12865787693035132824841220556520878650383580658640693651535411895266652280192"),
    MontFp!("13271109177048389296812780941310096270046944650307955939477485891950613419807"),
    MontFp!("22768321103861051515190775253992702316905399997697804654926324362758820947460"),
    MontFp!("11793638718615538422771118843477472096184948937087302513907460903994431256804"),
    MontFp!("11994848074575096182670111372584107500754907779105493386175567957911132601787"),
    MontFp!("28823569610051396102362669851238297121581474897215657071023781420043761726004"),
    MontFp!("1072148974419594402070101713043406554198631721553391137627950991272221023311"),
    MontFp!("5432652610908059517272798285879155923388888734491153551238890455750936314542"),
    MontFp!("10408918692925056833786833257634153023990087029210292532869619559576527581706"),
    MontFp!("28948022309329048855892746252171976963363056481941560715954676764349967629797"),
];

const ISO_VESTA_A: VestaBase =
    MontFp!("17413348858408915339762682399132325137863850198379221683097628341577494210225");
const ISO_VESTA_B: VestaBase = MontFp!("1265");
// Equivalent to 28948022309329048855892746252171976963363056481941647379679742748393362948084
const VESTA_ZETA: VestaBase = MontFp!("-13");
const ISO_VESTA_CONSTS: [VestaBase; 13] = [
    MontFp!("25731575386070265649682441113041757300767161317281464337493104665238544842753"),
    MontFp!("13377367003779316331268047403600734872799183885837485433911493934102207511749"),
    MontFp!("11064082577423419940183149293632076317553812518550871517841037420579891210813"),
    MontFp!("22515128462811482443472135973911537638171266152621281295306466582083726737451"),
    MontFp!("4604213796697651557841441623718706001740429044770779386484474413346415813353"),
    MontFp!("9250006497141849826017568406346290940322373181457057184910582871723433210981"),
    MontFp!("8577191795356755216560813704347252433589053772427154779164368221746181614251"),
    MontFp!("21162694656554182593580396827886355918081120183889566406795618341247785229923"),
    MontFp!("11620280474556824258112134491145636201000922752744881519070727793732904824884"),
    MontFp!("13937936667454727226911322269564285204582212380194126516142098360337545123123"),
    MontFp!("21380331849711001764708535561664047484292171808126992769566582994216305194078"),
    MontFp!("27750019491425549478052705219038872820967119544371171554731748615170299632943"),
    MontFp!("28948022309329048855892746252171976963363056481941647379679742748393362947557"),
];

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use rand::Rng;
    use std::time::Duration;
    use std::time::Instant;

    #[test]
    fn h2c_pallas() {
        let dst = b"test-pallas-dst";
        let message = b"test-message";
        let h = hash_to_pallas_slow(dst, message);
        let h_affine = h.into_affine();
        assert!(h_affine.is_on_curve());
        assert!(h_affine.is_in_correct_subgroup_assuming_on_curve());
        assert!(!h_affine.is_zero());

        let h_1 = hash_to_pallas_fallible(dst, message).unwrap();
        let h_1_affine = h_1.into_affine();
        assert!(h_1_affine.is_on_curve());
        assert!(h_1_affine.is_in_correct_subgroup_assuming_on_curve());
        assert!(!h_1_affine.is_zero());

        // Both methods should produce same result
        assert_eq!(h_affine, h_1_affine);
    }

    #[test]
    fn h2c_vesta() {
        let dst = b"test-vesta-dst";
        let message = b"test-message";
        let h = hash_to_vesta_slow(dst, message);
        let h_affine = h.into_affine();
        assert!(h_affine.is_on_curve());
        assert!(h_affine.is_in_correct_subgroup_assuming_on_curve());
        assert!(!h_affine.is_zero());

        let h_1 = hash_to_vesta_fallible(dst, message).unwrap();
        let h_1_affine = h_1.into_affine();
        assert!(h_1_affine.is_on_curve());
        assert!(h_1_affine.is_in_correct_subgroup_assuming_on_curve());
        assert!(!h_1_affine.is_zero());

        // Both methods should produce same result
        assert_eq!(h_affine, h_1_affine);
    }

    #[test]
    fn h2c_both() {
        let mut rng = rand::thread_rng();
        let iterations = 100;

        let mut total_pallas_naive_duration = Duration::default();
        let mut total_pallas_optimized_duration = Duration::default();
        let mut total_vesta_naive_duration = Duration::default();
        let mut total_vesta_optimized_duration = Duration::default();

        for i in 0..iterations {
            // Generate random message and DST
            let message_len = 10 + (i % 50); // Variable length between 10-59 bytes
            let message: Vec<u8> = (0..message_len).map(|_| rng.gen::<u8>()).collect();

            let dst_len = 5 + (i % 10); // Variable length between 5-14 bytes
            let dst: Vec<u8> = (0..dst_len).map(|_| rng.gen::<u8>()).collect();

            // Test Pallas curve with timing
            let start = Instant::now();
            let h_pallas_naive = hash_to_pallas_slow(&dst, &message);
            total_pallas_naive_duration += start.elapsed();

            let h_pallas_naive_affine = h_pallas_naive.into_affine();
            assert!(h_pallas_naive_affine.is_on_curve());
            assert!(h_pallas_naive_affine.is_in_correct_subgroup_assuming_on_curve());
            assert!(!h_pallas_naive_affine.is_zero());

            let start = Instant::now();
            let h_pallas = hash_to_pallas_fallible(&dst, &message).unwrap();
            total_pallas_optimized_duration += start.elapsed();

            let h_pallas_affine = h_pallas.into_affine();
            assert!(h_pallas_affine.is_on_curve());
            assert!(h_pallas_affine.is_in_correct_subgroup_assuming_on_curve());
            assert!(!h_pallas_affine.is_zero());

            // Both methods should produce same result for Pallas
            assert_eq!(h_pallas_naive_affine, h_pallas_affine);

            // Test Vesta curve with timing
            let start = Instant::now();
            let h_vesta_naive = hash_to_vesta_slow(&dst, &message);
            total_vesta_naive_duration += start.elapsed();

            let h_vesta_naive_affine = h_vesta_naive.into_affine();
            assert!(h_vesta_naive_affine.is_on_curve());
            assert!(h_vesta_naive_affine.is_in_correct_subgroup_assuming_on_curve());
            assert!(!h_vesta_naive_affine.is_zero());

            let start = Instant::now();
            let h_vesta = hash_to_vesta_fallible(&dst, &message).unwrap();
            total_vesta_optimized_duration += start.elapsed();

            let h_vesta_affine = h_vesta.into_affine();
            assert!(h_vesta_affine.is_on_curve());
            assert!(h_vesta_affine.is_in_correct_subgroup_assuming_on_curve());
            assert!(!h_vesta_affine.is_zero());

            // Both methods should produce same result for Vesta
            assert_eq!(h_vesta_naive_affine, h_vesta_affine);
        }

        // Print timing results after loop
        println!(
            "Hash-to-curve timing comparison ({} iterations):",
            iterations
        );
        println!("Pallas:");
        println!("  Naive function:     {:?}", total_pallas_naive_duration);
        println!(
            "  Optimized function: {:?}",
            total_pallas_optimized_duration
        );
        println!("Vesta:");
        println!("  Naive function:     {:?}", total_vesta_naive_duration);
        println!("  Optimized function: {:?}", total_vesta_optimized_duration);
    }
}
