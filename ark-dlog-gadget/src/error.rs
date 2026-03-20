use ark_ec_divisors::error::Error as DivisorError;
use thiserror::Error;

/// Error type for dlog gadget operations.
#[derive(Debug, Clone, Error)]
pub enum Error {
    /// Error from the divisor crate.
    #[error("Divisor error: {0}")]
    Divisor(#[from] DivisorError),
    /// Generator source provided no generators.
    #[error("Generator source provided no generators")]
    NoGenerators,
    /// Point is at infinity when it should not be.
    #[error("Point is at infinity when it should not be")]
    PointAtInfinity,
    /// Attempting to invert zero in challenge calculation.
    #[error("Attempting to invert zero in challenge calculation")]
    InvertingZero,
    /// Unsupported scalar bits (only 255 bits supported).
    #[error("Unsupported scalar bits: got {0}, expected 255")]
    UnsupportedScalarBits(usize),
    /// Decomposition length mismatch.
    #[error("Decomposition length mismatch: got {0}, expected {1}")]
    DecompositionLengthMismatch(usize, usize),
    /// X coefficients length exceeds expected length.
    #[error("X coefficients length exceeds expected length: got {0}, expected at most {1}")]
    XCoefficientsLengthExceeded(usize, usize),
    /// X coefficient at position 0 is not 1.
    #[error("X coefficient at position 0 is not 1")]
    InvalidXCoefficientAtZero,
    /// Incorrect divisor witness structure.
    #[error(
        "Incorrect divisor witness structure: yx coefficients length is {0}, expected at most {1}"
    )]
    IncorrectDivisorWitness(usize, usize),
    /// Divisor witness length exceeded maximum (255).
    #[error("Divisor witness length exceeded maximum: got {0}, expected at most 255")]
    DivisorWitnessLengthExceeded(usize),
    /// Combined witness length is not evenly divisible by chunk length.
    #[error("Combined witness length is not evenly divisible by chunk length: {0} % {1}")]
    WitnessChunkLengthMismatch(usize, usize),
    /// Mismatched size error.
    #[error("Mismatched size: got {0}, expected {1}")]
    MismatchedSize(usize, usize),
}
