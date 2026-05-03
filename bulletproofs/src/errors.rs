//! Errors related to proving and verifying proofs.

extern crate alloc;
use alloc::{string::String, vec::Vec};

use thiserror::Error;

/// Represents an error in proof creation, verification, or parsing.
#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum ProofError {
    /// This error occurs when a proof failed to verify.
    #[error("Proof verification failed.")]
    VerificationError,
    /// This error occurs when the proof encoding is malformed.
    #[error("Proof data could not be parsed.")]
    FormatError,
    /// This error occurs during proving if the number of blinding
    /// factors does not match the number of values.
    #[error("Wrong number of blinding factors supplied.")]
    WrongNumBlindingFactors,
    /// This error occurs when attempting to create a proof with
    /// bitsize other than \\(8\\), \\(16\\), \\(32\\), or \\(64\\).
    #[error("Invalid bitsize, must have n = 8,16,32,64.")]
    InvalidBitsize,
    /// This error occurs when attempting to create an aggregated
    /// proof with non-power-of-two aggregation size.
    #[error("Invalid aggregation size, m must be a power of 2.")]
    InvalidAggregation,
    /// This error occurs when there are insufficient generators for the proof.
    #[error("Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength(u32, u32),
    /// This error results from an internal error during proving.
    ///
    /// The single-party prover is implemented by performing
    /// multiparty computation with ourselves.  However, because the
    /// MPC protocol is not exposed by the single-party API, we
    /// consider its errors to be internal errors.
    #[error("Internal error during proof creation: {0}")]
    ProvingError(MPCError),

    /// Hash to curve error
    #[error("Hash to curve error")]
    HashToCurveError,
    /// Attempting to invert zero in challenge calculation.
    #[error("Attempting to invert zero in challenge calculation")]
    InvertingZero,
}

impl From<MPCError> for ProofError {
    fn from(e: MPCError) -> ProofError {
        match e {
            MPCError::InvalidBitsize => ProofError::InvalidBitsize,
            MPCError::InvalidAggregation => ProofError::InvalidAggregation,
            MPCError::InvalidGeneratorsLength(u1, u2) => {
                ProofError::InvalidGeneratorsLength(u1, u2)
            }
            _ => ProofError::ProvingError(e),
        }
    }
}

/// Represents an error during the multiparty computation protocol for
/// proof aggregation.
///
/// This is a separate type from the `ProofError` to allow a layered
/// API: although the MPC protocol is used internally for single-party
/// proving, its API should not expose the complexity of the MPC
/// protocol.
#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum MPCError {
    /// This error occurs when the dealer gives a zero challenge,
    /// which would annihilate the blinding factors.
    #[error("Dealer gave a malicious challenge value.")]
    MaliciousDealer,
    /// This error occurs when attempting to create a proof with
    /// bitsize other than \\(8\\), \\(16\\), \\(32\\), or \\(64\\).
    #[error("Invalid bitsize, must have n = 8,16,32,64")]
    InvalidBitsize,
    /// This error occurs when attempting to create an aggregated
    /// proof with non-power-of-two aggregation size.
    #[error("Invalid aggregation size, m must be a power of 2")]
    InvalidAggregation,
    /// This error occurs when there are insufficient generators for the proof.
    #[error("Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength(u32, u32),
    /// This error occurs when the dealer is given the wrong number of
    /// value commitments.
    #[error("Wrong number of value commitments")]
    WrongNumBitCommitments,
    /// This error occurs when the dealer is given the wrong number of
    /// polynomial commitments.
    #[error("Wrong number of value commitments")]
    WrongNumPolyCommitments,
    /// This error occurs when the dealer is given the wrong number of
    /// proof shares.
    #[error("Wrong number of proof shares")]
    WrongNumProofShares,
    /// This error occurs when one or more parties submit malformed
    /// proof shares.
    #[error("Malformed proof shares from parties {bad_shares:?}")]
    MalformedProofShares {
        /// A vector with the indexes of the parties whose shares were malformed.
        bad_shares: Vec<usize>,
    },
}

/// Represents an error during the proving or verifying of a constraint system.
///
/// XXX: should this be separate from a `ProofError`?
#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum R1CSError {
    /// Occurs when there are insufficient generators for the proof.
    #[error("Invalid generators size, too few generators for proof")]
    InvalidGeneratorsLength(u32, u32),
    /// This error occurs when the proof encoding is malformed.
    #[error("Proof data could not be parsed.")]
    FormatError,
    /// Occurs when verification of an
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[error("R1CSProof did not verify correctly.")]
    VerificationError,

    /// Occurs when batch verification of 1 or more
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[error("Batch of R1CSProof did not verify correctly.")]
    BatchVerificationError,

    /// Occurs when no `VerificationTuple` is provided during batch verification
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[error("Occurs when no `VerificationTuple` is provided")]
    NoVerificationTuple,

    /// Occurs when 2 or more incompatible `VerificationTuple`s are provided during batch verification
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[error("Occurs when no VerificationTuple is provided")]
    IncompatibleVerificationTuple(u32, u32),

    /// Occurs when trying to use a missing variable assignment.
    /// Used by gadgets that build the constraint system to signal that
    /// a variable assignment is not provided when the prover needs it.
    #[error("Variable does not have a value assignment.")]
    MissingAssignment,

    /// Occurs when a gadget receives an inconsistent input.
    #[error("Gadget error: {description:?}")]
    GadgetError {
        /// The description of the reasons for the error.
        description: String,
    },

    /// Occurs when generation of an
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[error("R1CSProof failed to generate with error: {0}")]
    ProofGenerationError(String),

    /// Occurs when verification of an
    /// [`R1CSProof`](::r1cs::R1CSProof) fails.
    #[error("R1CSProof failed to verify with error: {0}")]
    VerificationErrorWithReason(String),
}

impl From<ProofError> for R1CSError {
    fn from(e: ProofError) -> R1CSError {
        match e {
            ProofError::InvalidGeneratorsLength(u1, u2) => {
                R1CSError::InvalidGeneratorsLength(u1, u2)
            }
            ProofError::FormatError => R1CSError::FormatError,
            ProofError::VerificationError => R1CSError::VerificationError,
            _ => panic!("unexpected error type in conversion"),
        }
    }
}
