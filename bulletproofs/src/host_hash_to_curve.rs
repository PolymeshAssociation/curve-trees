#[cfg(feature = "impl_host_hash_to_curve")]
pub mod host_fn {
    use ark_host_msm::{CurveMSMId, CURVE_ID_LEN};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress};
    use ark_std::vec::Vec;

    use ark_pallas::PallasConfig;
    use ark_std::boxed::Box;
    use ark_std::collections::BTreeMap;
    use ark_vesta::VestaConfig;

    use crate::generators::HashToCurveExt;

    type HashToCurveFn = Box<dyn Fn(&mut [u8], u32) -> u32 + Send + Sync>;

    pub struct RegisteredCurves {
        curves: BTreeMap<CurveMSMId, HashToCurveFn>,
    }

    impl RegisteredCurves {
        pub fn new() -> Self {
            let mut curves = RegisteredCurves {
                curves: BTreeMap::new(),
            };
            curves.register_curve::<PallasConfig>();
            curves.register_curve::<VestaConfig>();
            curves
        }

        pub fn register_curve<C: HashToCurveExt + 'static>(&mut self) -> bool {
            let name = C::curve_name();
            let curve_id = CurveMSMId::from_curve_name(name);
            self.curves
                .insert(curve_id, Box::new(batch_hash_to_curve_impl::<C>));
            true
        }

        pub fn batch_hash_to_curve(&self, buffer: &mut [u8], buf_len: u32) -> u32 {
            if (buf_len as usize) < CURVE_ID_LEN {
                return 0; // Buffer too small to contain curve ID
            }
            if let Some(curve_id) = CurveMSMId::deserialize_uncompressed_unchecked(&buffer[..]).ok()
            {
                if let Some(msm_fn) = self.curves.get(&curve_id) {
                    if buf_len as usize > CURVE_ID_LEN {
                        return msm_fn(buffer, buf_len);
                    } else {
                        return 1; // Curve is supported, but no MSM data provided
                    }
                }
            }
            0
        }
    }

    #[cfg(feature = "std")]
    lazy_static::lazy_static! {
        pub static ref SUPPORTED_CURVES: RegisteredCurves = {
            RegisteredCurves::new()
        };
    }

    #[cfg(not(feature = "std"))]
    static mut SUPPORTED_CURVES: Option<RegisteredCurves> = None;

    #[cfg(not(feature = "std"))]
    #[allow(static_mut_refs)]
    fn get_supported_curves() -> &'static RegisteredCurves {
        unsafe {
            if SUPPORTED_CURVES.is_none() {
                SUPPORTED_CURVES = Some(RegisteredCurves::new());
            }
            SUPPORTED_CURVES.as_ref().unwrap()
        }
    }

    #[cfg(feature = "std")]
    pub fn batch_hash_to_curve(buffer: &mut [u8], buf_len: u32) -> u32 {
        SUPPORTED_CURVES.batch_hash_to_curve(buffer, buf_len)
    }

    #[cfg(not(feature = "std"))]
    pub fn batch_hash_to_curve(buffer: &mut [u8], buf_len: u32) -> u32 {
        get_supported_curves().batch_hash_to_curve(buffer, buf_len)
    }

    fn batch_hash_to_curve_impl<C: HashToCurveExt>(buffer: &mut [u8], buf_len: u32) -> u32 {
        if buf_len as usize == CURVE_ID_LEN {
            // The curve is supported.
            return 1;
        }
        let buf_len = buf_len as usize;
        let mut cursor = ark_std::io::Cursor::new(&buffer[CURVE_ID_LEN..buf_len]);

        // Deserialize the parameters for the host hash_to_curve operation.  The `curve_id` is already deserialized by the caller, so we only need to deserialize the other parameters.
        let dst = Vec::<u8>::deserialize_uncompressed(&mut cursor).unwrap();
        let msg_prefix = Vec::<u8>::deserialize_uncompressed(&mut cursor).unwrap();
        let gens_offset = u32::deserialize_uncompressed(&mut cursor).unwrap();
        let gens_count = u32::deserialize_uncompressed(&mut cursor).unwrap();

        // Check that the buffer has enough space for the results of the batched hash_to_curve operation.  Each point is serialized in uncompressed form, which takes `C::uncompressed_size()` bytes.
        let expected_res_len = C::batch_uncompressed_size(gens_count);
        if expected_res_len > buf_len {
            // Not enough space in the buffer for the results.
            return 0;
        }

        let res = C::batch_hash_to_curve(&dst, &msg_prefix, gens_offset, gens_count);
        // Ensure the result fits in the buffer before serializing.
        let res_len = res.serialized_size(Compress::No);
        if res_len > buf_len {
            // Not enough space in the buffer for the result.
            return 0;
        }
        // Serialize the result of the batched hash_to_curve operation back into the buffer, starting from the beginning of the buffer (overwriting the input parameters).
        res.serialize_uncompressed(&mut buffer[0..res_len]).unwrap();
        res_len as u32
    }
}

#[cfg(not(feature = "impl_host_hash_to_curve"))]
pub mod host_fn {
    use ark_ec::short_weierstrass::Affine as SWAffine;
    use ark_host_msm::{pack_fat_pointer, CurveMSMId};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::vec::Vec;

    use crate::generators::HashToCurveExt;

    #[cfg_attr(feature = "polkavm", polkavm_derive::polkavm_import)]
    extern "C" {
        /// let (buf_ptr, buf_len) = unpack_fat_pointer(fat_ptr);
        ///
        /// If `buf_len` is 32, then the call is to check if the host supports the specified curve, and the `buffer` contains only `CurveMSMId`.
        /// If `buf_len` is greater than 32, then the call is to perform batch hash to curve, and the `buffer` contains the serialized input parameters, with the first 32 bytes being the `CurveMSMId`.
        ///
        /// The caller should allocate enough space in the buffer for the results of the batch hash to curve operation, which is `C::batch_uncompressed_size(gens_count)` bytes, where `gens_count` is
        /// one of the input parameters.  The host function will write the serialized results back into the buffer, starting from the beginning of the buffer (overwriting the input parameters).
        ///
        /// A return value of 0 indicates that the host does not support the curve or that an error occurred during the host call,
        /// while a non-zero return value indicates the length of the serialized result of the batch hash to curve operation.
        fn host_batch_hash_to_curve(fat_ptr: u64) -> u32;
    }

    #[cfg(not(feature = "std"))]
    pub fn use_host_batch_hash_to_curve<C: HashToCurveExt>(
        dst: &[u8],
        msg_prefix: &[u8],
        gens_offset: u32,
        gens_count: u32,
    ) -> Option<Vec<SWAffine<C>>> {
        let mut buffer = Vec::new();
        let curve_name = C::curve_name();
        let curve_id = CurveMSMId::from_curve_name(curve_name);
        curve_id.serialize_uncompressed(&mut buffer).ok()?;

        // Call the host function with only the curve ID to check if the host supports MSM for this curve.
        let fat_ptr = pack_fat_pointer(buffer.as_ptr() as u32, buffer.len() as u32);
        let res_len = unsafe { host_batch_hash_to_curve(fat_ptr) as usize };
        if res_len == 0 {
            // Host does not support MSM for this curve or an error occurred.
            return None;
        }

        // Serialize parmeters for the host hash_to_curve operation.  The `curve_id` is already serialized in the buffer, so we only need to append the other parameters.
        dst.serialize_uncompressed(&mut buffer).ok()?;
        msg_prefix.serialize_uncompressed(&mut buffer).ok()?;
        gens_offset.serialize_uncompressed(&mut buffer).ok()?;
        gens_count.serialize_uncompressed(&mut buffer).ok()?;

        // Make sure there is enough space in the buffer for the results of the batched hash_to_curve operation.  Each point is serialized in uncompressed form, which takes `C::uncompressed_size()` bytes.
        let expected_res_len = C::batch_uncompressed_size(gens_count);
        if expected_res_len > buffer.len() {
            buffer.resize(expected_res_len, 0);
        }

        let fat_ptr = pack_fat_pointer(buffer.as_ptr() as u32, buffer.len() as u32);
        let res_len = unsafe { host_batch_hash_to_curve(fat_ptr) as usize };
        if res_len > 0 {
            Vec::<SWAffine<C>>::deserialize_uncompressed_unchecked(&buffer[..res_len]).ok()
        } else {
            // An error occurred during MSM.
            None
        }
    }
}
