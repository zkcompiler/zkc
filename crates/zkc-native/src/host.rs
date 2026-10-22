//! Concrete native adaptation of the runtime-owned Host transport contracts.
use crate::{NativeBackend, NativeWireError, Value, has_native_wire, native_wire_size};
use zkc_runtime::host::wire::{ProofBackend, WireBackend, WireError};
use zkc_runtime::vm::{PhysicalType, Value as RuntimeValue};

impl From<NativeWireError> for WireError {
    fn from(error: NativeWireError) -> Self {
        match error {
            NativeWireError::Invalid(reason) => Self::Invalid(reason),
            NativeWireError::Limit => Self::Limit,
            NativeWireError::Backend(error) => Self::Backend(error),
        }
    }
}

impl From<WireError> for NativeWireError {
    fn from(error: WireError) -> Self {
        match error {
            WireError::Invalid(reason) => Self::Invalid(reason),
            WireError::Limit => Self::Limit,
            WireError::Backend(error) => Self::Backend(error),
        }
    }
}

/// Native frames reserve their exact fixed width, or conservative retention and
/// descriptor/framing slack for structured payloads, without encoding to size.
pub fn native_encoding_bound(value: &Value) -> usize {
    native_wire_size(&value.physical_type()).unwrap_or_else(|| {
        value
            .retained_bytes()
            .saturating_mul(4)
            .saturating_add(4096)
    })
}
impl WireBackend for NativeBackend {
    fn supports_wire(&self, ty: &PhysicalType) -> bool {
        has_native_wire(ty)
    }
    fn fixed_wire_size(&self, ty: &PhysicalType) -> Option<usize> {
        native_wire_size(ty)
    }
    fn encoding_bound(&self, value: &Value) -> Result<usize, WireError> {
        Ok(native_encoding_bound(value))
    }
    fn decoding_bound(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        self.measure_native_wire(ty, bytes)
            .map(|size| size.retained_bytes())
            .map_err(Into::into)
    }
    fn encode_wire(&self, value: &Value) -> Result<Vec<u8>, WireError> {
        self.encode_native_value(value).map_err(Into::into)
    }
    fn decode_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Value, WireError> {
        self.decode_native_value(ty, bytes).map_err(Into::into)
    }
}
impl ProofBackend for NativeBackend {
    fn acceptance(&self, value: &Value) -> Option<bool> {
        if let Value::Bool(value) = value {
            Some(*value)
        } else {
            None
        }
    }
    fn raw_bytes<'a>(&self, value: &'a Value) -> Result<&'a [u8], WireError> {
        self.encode_raw_bytes(value).map_err(Into::into)
    }
    fn raw_decoding_bound(&self, _ty: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        Ok(bytes.len())
    }
    fn decode_raw(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Value, WireError> {
        self.decode_raw_bytes(ty, bytes).map_err(Into::into)
    }
}
