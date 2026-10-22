//! Host boundary for the admitted native message profile.
use zkc_backends::{NativeBackend, NativeWireError};
use zkc_runtime::vm::{Backend, BackendError, DecodeReason, PhysicalType};

/// Distinguish invalid received bytes from failures of the trusted Host adapter.
#[derive(Debug)]
pub enum WireError {
    /// The receiver accepts the completion and stops with this decoding reason.
    Invalid(DecodeReason),
    /// Host capacity was exhausted before accepting the receive completion.
    Limit,
    /// The trusted adapter failed before accepting the receive completion.
    Backend(BackendError),
}

/// The closed native wire profile selected by `zkc.run/0` bundle admission.
/// Implementations preserve its exact physical identities and canonical framing;
/// this trait is not a codec extension point. Host outcomes do not depend on a
/// concrete backend's value or error types.
pub trait WireBackend: Backend {
    /// Bound retained decoding storage before materializing a received value.
    /// Backends without a measurement implementation refuse closed.
    fn decoding_bound(&self, _ty: &PhysicalType, _bytes: &[u8]) -> Result<usize, WireError> {
        Err(WireError::Limit)
    }
    fn encode_native(&self, value: &Self::Value) -> Result<Vec<u8>, WireError>;
    fn decode_native(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Self::Value, WireError>;
}

impl From<NativeWireError> for WireError {
    fn from(error: NativeWireError) -> Self {
        match error {
            NativeWireError::Invalid(reason) => Self::Invalid(reason),
            NativeWireError::Limit => Self::Limit,
            NativeWireError::Backend(error) => Self::Backend(error),
        }
    }
}

impl WireBackend for NativeBackend {
    fn decoding_bound(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        self.measure_native_wire(ty, bytes)
            .map(|size| size.retained_bytes())
            .map_err(Into::into)
    }
    fn encode_native(&self, value: &Self::Value) -> Result<Vec<u8>, WireError> {
        self.encode_native_value(value).map_err(Into::into)
    }
    fn decode_native(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Self::Value, WireError> {
        self.decode_native_value(ty, bytes).map_err(Into::into)
    }
}
