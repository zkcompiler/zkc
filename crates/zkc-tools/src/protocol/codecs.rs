use super::WireBackend;
use zkc_backends::{NativeBackend, Value};
use zkc_runtime::interactive::BackendError;

impl WireBackend for NativeBackend {
    fn encode(&self, value: &Value) -> Result<Vec<u8>, BackendError> {
        self.encode_value(value)
    }
    fn decode(
        &self,
        ty: zkc_runtime::interactive::PhysicalType,
        bytes: &[u8],
    ) -> Result<Value, BackendError> {
        self.decode_typed_value(ty, bytes)
    }
}
