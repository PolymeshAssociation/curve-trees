use ark_serialize::SerializationError;
use ark_std::string::String;
use schnorr_pok::error::SchnorrError;
use thiserror::Error;

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    /// Curve Tree height cannot be 0
    #[error("Curve Tree height cannot be 0")]
    HeightCantBe0,

    /// Child doesn't exist at the given index
    #[error("Child doesn't exist at index {0}")]
    ChildDoesntExistAtIndex(u64),

    /// Leaf doesn't exist at the given index
    #[error("Leaf doesn't exist at index {0}")]
    LeafDoesntExistAtIndex(u64),

    /// Leaf already exists at the given index
    #[error("Leaf already exists at index {0}")]
    LeafAlreadyExistAtIndex(u64),

    /// Leaf index is not expected
    #[error("Leaf index {0} is not expected, expected {1}")]
    LeafIndexNotAsExpected(u64, u64),

    /// Leaf index is not in the expected range
    #[error("Leaf index {1} is not in the expected range [0, {0})")]
    TreeWontSupportRequiredInsertions(u64, u64),

    /// Serialization error
    #[error("Serialization error: {0}")]
    SerializationError(SerializationError),

    /// Schnorr proof error
    #[error("Schnorr proof error: {0:?}")]
    SchnorrError(SchnorrError),

    /// Failed to generate point or scalar.
    #[error("Failed to generate point or scalar: {0}")]
    GenerationError(String),

    /// Bulletprof R1CS error
    #[error("Bulletproof R1CS error: {0}")]
    BulletproofR1CSError(#[from] bulletproofs::r1cs::R1CSError),

    /// Mismatched size.
    #[error("Mismatched size: {0} {1}")]
    MismatchedSize(usize, usize),

    /// The curve point cannot be 0.
    #[error("The curve point cannot be 0")]
    PointCantBeZero,
}

impl From<ark_serialize::SerializationError> for Error {
    fn from(err: ark_serialize::SerializationError) -> Self {
        Error::SerializationError(err)
    }
}
