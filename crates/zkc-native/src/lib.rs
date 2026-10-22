//! Default native VM backend: concrete values, operation bindings and services.
//! Ark PCS is nonhiding; setup honesty and protocol soundness remain premises.
mod backend;
mod bindings;
mod codec;
mod diagonal;
pub mod hash;
pub mod matrix;
pub mod merkle;
mod numerical;
mod operations;
pub mod oracle;
pub mod relation;
mod resource;
pub mod ring;
mod sampling;
pub mod services;
mod setups;
mod transcript;
mod value;

/// Independently installed physical domains and their nominal associations.
pub mod domains;
pub use zkc_kernels::plonky3::binary::{Binary64, Binary64Ext3};
pub use zkc_kernels::plonky3::{
    KoalaBear, KoalaBearExt4, KoalaBearExt8, parse_decimal as parse_koala_bear_decimal,
};

pub use backend::{
    ComputationCheckpoint, EntryPolicy, NativeBackend, NativeCall, NativeOperation, PortConstraint,
};
pub use codec::{
    NativeInputSize, NativeWireError, has_native_wire, native_wire_size, readable_wire,
    requires_setup,
};
pub use resource::{Capability, CapabilityObservation, Domain, LogicalUnit};
pub use setups::SetupRegistry;
pub use value::{Policy, Value};
pub use zkc_kernels::{GroupPoint, Keys, Scalar, parse_decimal};
use zkc_runtime::vm::BackendError;

pub use zkc_kernels::SCALAR_MODULUS_DECIMAL;

pub(crate) type Result<T> = std::result::Result<T, BackendError>;
pub(crate) fn refused(reason: &str) -> BackendError {
    BackendError::new(format!("refused:{reason}"))
}
pub(crate) fn exhausted(reason: &str) -> BackendError {
    BackendError::new(format!("exhausted:{reason}"))
}
pub(crate) fn ark(error: zkc_kernels::Error) -> BackendError {
    use zkc_kernels::Error::*;
    match error {
        ArityLimit | ElementLimit | ByteLimit | SetupLimit | CapacityOverflow | Allocation
        | EntropyUnavailable => exhausted(error.code()),
        _ => refused(error.code()),
    }
}
/// Adapter observation classification. Runtime preserves the original error code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorClass {
    Rejected,
    Refused,
    Exhausted,
}
/// Unknown errors fail closed as Refused, never as successful verification.
pub fn classify_error(error: &BackendError) -> ErrorClass {
    if error.code == "rejected:require" {
        ErrorClass::Rejected
    } else if error.code.starts_with("exhausted:") {
        ErrorClass::Exhausted
    } else {
        ErrorClass::Refused
    }
}

pub use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar as RistrettoScalar};
pub use diagonal::Diagonal;
pub use zkc_kernels::edwards::EdwardsPrime;
pub fn parse_ristretto_decimal(s: &str) -> Result<RistrettoScalar> {
    zkc_kernels::fields::parse_ristretto_decimal(s).map_err(field_error)
}

pub use zkc_kernels::RISTRETTO_SCALAR_MODULUS_DECIMAL;

pub use zkc_kernels::bls12_381::{G2 as Bls12381G2, Gt as Bls12381Gt};
/// BN254 scalar field and checked subgroup points.
pub use zkc_kernels::bn254::Gt as Bn254Gt;
pub use zkc_kernels::bn254::{
    G1 as Bn254G1, G2 as Bn254G2, Scalar as Bn254Scalar, parse_decimal as parse_bn254_decimal,
};

mod variant;
pub use variant::Variant;
mod fixed_vector;
pub use fixed_vector::FixedVector;
mod sequence;
pub use sequence::Sequence;
mod field_array;
pub use field_array::FieldArray;

#[cfg(feature = "test-utils")]
mod test_tape;
#[cfg(feature = "test-utils")]
pub use test_tape::TestTape;

pub(crate) fn field_error(error: zkc_kernels::fields::Error) -> BackendError {
    refused(error.code())
}

mod host;
pub use host::native_encoding_bound;
