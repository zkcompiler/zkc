//! Record actual native primitive requests and allocation steps for comparison
//! with the independent physical Lean reference. No protocol math is supplied.
use serde_json::{Value as Json, json};
use zkc_backends::{NativeBackend, Value};
use zkc_runtime::interactive::{
    Backend, BackendError, BoundSignature, Frame, FrameExit, Invocation, OperationBinding,
};

pub struct PhysicalObserved {
    pub inner: NativeBackend,
    pub steps: Vec<Json>,
    pub requests: Vec<Json>,
}
impl Backend for PhysicalObserved {
    type Value = Value;
    fn binding_signature(&self, b: &OperationBinding) -> Option<BoundSignature> {
        self.inner.binding_signature(b)
    }
    fn validate_value(&self, v: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, v: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(f, v)
    }
    fn leave_frame(&mut self, f: &Frame, e: FrameExit, v: &[Value]) -> Result<(), BackendError> {
        self.inner.leave_frame(f, e, v)
    }
    fn apply(&mut self, i: &Invocation<'_>, v: &[Value]) -> Result<Vec<Value>, BackendError> {
        let record = json!([
            i.site,
            i.binding.declaration().contract,
            i.max_output_bytes.to_string()
        ]);
        self.steps.push(json!([
            "attempt",
            record,
            self.inner.active_frames().to_string()
        ]));
        self.requests.push(json!([
            i.site,
            i.frame.origin().json()[4],
            i.binding.declaration().contract
        ]));
        let result = self.inner.apply(i, v);
        if result.is_ok() {
            self.steps.push(json!([
                "completed",
                record,
                self.inner.active_frames().to_string()
            ]));
        }
        result
    }
}
