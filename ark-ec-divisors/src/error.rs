use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum Error {
    /// Insufficient evaluations provided for interpolation.
    #[error("Insufficient evaluations provided for interpolation: got {0}, expected at least {1}")]
    InsufficientEvaluations(usize, usize),
    /// Polynomial degree exceeds interpolator's capability.
    #[error("Polynomial degree exceeds interpolator's capability: got {0}, expected at most {1}")]
    DegreeExceedsInterpolator(u16, u16),
    /// Invalid arguments provided (e.g., no points, points don't sum to infinity, point at infinity).
    #[error("Invalid arguments provided")]
    InvalidArguments,
    /// Scalar is zero when it must be non-zero.
    #[error("Scalar is zero when it must be non-zero")]
    ZeroScalar,
    /// Attempting to invert zero in challenge calculation.
    #[error("Attempting to invert zero in challenge calculation")]
    InvertingZero,
}
