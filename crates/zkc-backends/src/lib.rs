//! Concrete mathematical adapters for the independent interactive role runtime.
//! Ark PCS is nonhiding; setup honesty and protocol soundness remain premises.
mod backend;
mod bindings;
mod codec;
mod diagonal;
pub mod external;
mod external_kernels;
mod kernels;
pub mod matrix;
pub mod oracle;
pub mod representations;
mod resource;
mod sampling;
mod setups;
mod transcript;
mod value;

pub mod choices;
/// Independently installed physical domains and their nominal associations.
pub mod domains;
pub mod plonky3;
pub use plonky3::{KoalaBear, KoalaBearExt8, parse_decimal as parse_koala_bear_decimal};

mod public_operands;
pub use public_operands::{PublicRolePolicy, requires_public_operands};

pub use backend::{EntryPolicy, NativeBackend, PortConstraint, PublicInputs};
pub use codec::{InputBindings, requires_setup};
pub use resource::{Capability, CapabilityObservation, Domain, LogicalUnit};
pub use setups::SetupRegistry;
pub use value::{Policy, Value};
pub use zkc_arkworks::{GroupPoint, Keys, Scalar, parse_decimal};
use zkc_runtime::interactive::BackendError;

/// Exact size of the BLS12-381 base/challenge field; no reduction or floating-point loss.
/// For an independently uniform challenge and a fixed nonzero degree-d
/// polynomial, the root probability is at most d / this value (capped at one).
/// This algebraic fact does not prove CSPRNG independence or PCS soundness.
pub const SCALAR_MODULUS_DECIMAL: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

pub(crate) type Result<T> = std::result::Result<T, BackendError>;
pub(crate) fn refused(reason: &str) -> BackendError {
    BackendError::new(format!("refused:{reason}"))
}
pub(crate) fn exhausted(reason: &str) -> BackendError {
    BackendError::new(format!("exhausted:{reason}"))
}
pub(crate) fn ark(error: zkc_arkworks::Error) -> BackendError {
    use zkc_arkworks::Error::*;
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
pub use kernels::arithmetic::parse_ristretto_decimal;

/// Exact order of the Ristretto255 scalar field. No sampler uniformity claim.
pub const RISTRETTO_SCALAR_MODULUS_DECIMAL: &str =
    "7237005577332262213973186563042994240857116359379907606001950938285454250989";

/// BN254 scalar field and checked subgroup points.
pub use zkc_arkworks::bn254::{
    G1 as Bn254G1, G2 as Bn254G2, Scalar as Bn254Scalar, parse_decimal as parse_bn254_decimal,
};

mod variant;
pub use variant::Variant;
