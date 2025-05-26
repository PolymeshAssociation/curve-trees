use ark_serialize::SerializationError;
use schnorr_pok::error::SchnorrError;

#[derive(Debug)]
pub enum Error {
    HeightCantBe0,
    LeafDoesntExistAtIndex(u64),
    LeafAlreadyExistAtIndex(u64),
    LeafIndexNotAsExpected(u64, u64),
    TreeWontSupportRequiredInsertions(u64, u64),
    SerializationError(SerializationError),
    SchnorrError(SchnorrError),
}