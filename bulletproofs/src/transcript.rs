//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use crate::errors::ProofError;
use crate::util;
use ark_ec::AffineRepr;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use sha2::Sha256;

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-bit, `m`-party range proof.
    #[allow(dead_code)]
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64);

    /// Append a domain separator for a length-`n` inner product proof.
    fn innerproduct_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a constraint system.
    fn r1cs_domain_sep(&mut self);

    /// Commit a domain separator for a CS without randomized constraints.
    fn r1cs_1phase_domain_sep(&mut self);

    /// Commit a domain separator for a CS with randomized constraints.
    fn r1cs_2phase_domain_sep(&mut self);

    /// Append a `scalar` with the given `label`.
    fn append_scalar<C: AffineRepr>(&mut self, label: &'static [u8], scalar: &C::ScalarField);

    /// Append a `point` with the given `label`.
    fn append_point<C: AffineRepr>(&mut self, label: &'static [u8], point: &C);

    /// Check that a point is not the identity, then append it to the
    /// transcript.  Otherwise, return an error.
    fn validate_and_append_point<C: AffineRepr>(
        &mut self,
        label: &'static [u8],
        point: &C,
    ) -> Result<(), ProofError>;

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar<C: AffineRepr>(&mut self, label: &'static [u8]) -> C::ScalarField;

    /// Append a `u64` index with the given `label`.
    fn append_index(&mut self, label: &'static [u8], index: u64);
}

impl TranscriptProtocol for MerlinTranscript {
    fn rangeproof_domain_sep(&mut self, n: u64, m: u64) {
        self.append_message(b"dom-sep", b"rangeproof v1");
        self.merlin.append_u64(b"n", n);
        self.merlin.append_u64(b"m", m);
    }

    fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipp v1");
        self.merlin.append_u64(b"n", n);
    }

    fn r1cs_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs v1");
    }

    fn r1cs_1phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-1phase");
    }

    fn r1cs_2phase_domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"r1cs-2phase");
    }

    fn append_scalar<C: AffineRepr>(&mut self, label: &'static [u8], scalar: &C::ScalarField) {
        self.append_message(label, &util::field_as_bytes(scalar));
    }

    fn append_point<C: AffineRepr>(&mut self, label: &'static [u8], point: &C) {
        let mut bytes = Vec::new();
        if let Err(e) = point.serialize_compressed(&mut bytes) {
            panic!("{}", e)
        }
        self.append_message(label, &bytes);
    }

    fn validate_and_append_point<C: AffineRepr>(
        &mut self,
        label: &'static [u8],
        point: &C,
    ) -> Result<(), ProofError> {
        if point.is_zero() {
            Err(ProofError::VerificationError)
        } else {
            let mut bytes = Vec::new();
            point
                .serialize_compressed(&mut bytes)
                .map_err(|_| ProofError::VerificationError)?;
            self.append_message(label, &bytes);
            Ok(())
        }
    }

    fn challenge_scalar<C: AffineRepr>(&mut self, label: &'static [u8]) -> C::ScalarField {
        let mut bytes = [0u8; 64];
        self.challenge_bytes(label, &mut bytes);

        let hasher = <DefaultFieldHasher<Sha256> as HashToField<C::ScalarField>>::new(label);
        let [result] = hasher.hash_to_field::<1>(&bytes);
        result
    }

    fn append_index(&mut self, label: &'static [u8], index: u64) {
        self.merlin.append_u64(label, index);
    }
}
