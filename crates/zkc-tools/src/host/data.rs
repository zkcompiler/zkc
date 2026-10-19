//! Explicitly retained immutable data. Reuse grants no invocation authority.
use super::{capacity::Capacity, inputs::Result};
use std::sync::Arc;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, SetupRegistry, Value};
use zkc_runtime::vm::{PhysicalType, Value as RuntimeValue};

/// Decoded immutable data and its canonical bytes, owned by the application.
/// Every invocation checks its own type, policy, setup and loading budgets.
/// Capabilities and setup keys use their separate Host APIs.
/// The native wire profile fixes bytes by physical type and value; invocation
/// domains and capacity may restrict admission but cannot change the encoding.
#[derive(Clone)]
pub struct PreparedData(Arc<Data>);
struct Data {
    ty: PhysicalType,
    value: Value,
    wire: Vec<u8>,
}
impl std::fmt::Debug for PreparedData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedData")
            .field("type", &self.0.ty)
            .field("retained_bytes", &self.retained_bytes())
            .finish_non_exhaustive()
    }
}
impl PreparedData {
    /// Decode once under an explicit capacity. This API does not import or
    /// authorize setup material; setup-dependent values require the setup owner.
    pub fn from_wire(ty: PhysicalType, wire: Vec<u8>, capacity: Capacity) -> Result<Self> {
        let backend = codec(capacity)?;
        capacity.check_wire(wire.len())?;
        let mut admission = super::admission::Admission::new(capacity.loading())?;
        let id = admission.native_wire(&backend, ty.clone(), wire.as_slice(), None)?;
        admission.data(id, ty.kind())?;
        let value = admission.load(&backend, &capacity.backend())?.remove(0);
        Self::retain(value, wire, capacity)
    }
    /// Freeze a native value and its canonical encoding. Use Native inputs
    /// directly when a private value should remain unencoded.
    /// Elements must satisfy their upstream library invariants, as for Native.
    pub fn from_value(value: Value, capacity: Capacity) -> Result<Self> {
        let backend = codec(capacity)?;
        let mut admission = super::admission::Admission::new(capacity.loading())?;
        let ty = value.physical_type();
        let input = super::request::InputValue::from(value);
        let id = admission.native_data(&backend, ty.clone(), &input, None)?;
        admission.data(id, ty.kind())?;
        admission.charge_encoding(id)?;
        let value = admission.load(&backend, &capacity.backend())?.remove(0);
        let wire = backend
            .encode_native_value(&value)
            .map_err(|e| e.to_string())?;
        // The canonical pair must also fit the wire planner's estimate. This
        // checks the reuse invariant once at construction, before publication.
        let estimate = backend
            .native_input_retained_bytes(&ty, &wire)
            .map_err(|e| e.to_string())?;
        if value.retained_bytes() > estimate {
            return Err("artifact-input-size-estimate".into());
        }
        Self::retain(value, wire, capacity)
    }
    fn retain(value: Value, wire: Vec<u8>, capacity: Capacity) -> Result<Self> {
        // Charge both representations: retaining a cache is an explicit cost.
        let retained = value
            .retained_bytes()
            .checked_add(wire.len())
            .ok_or("native-data-bytes-limit")?;
        if retained > capacity.values.live_bytes.min(capacity.values.total_bytes) {
            return Err("native-data-bytes-limit".into());
        }
        Ok(Self(Arc::new(Data {
            ty: value.physical_type(),
            value,
            wire,
        })))
    }
    pub fn physical_type(&self) -> &PhysicalType {
        &self.0.ty
    }
    pub fn canonical_bytes(&self) -> &[u8] {
        &self.0.wire
    }
    /// Logical retained payload in both representations, excluding allocator
    /// overhead. Each clone shares this allocation; applications bound its lifetime.
    pub fn retained_bytes(&self) -> usize {
        self.0.value.retained_bytes() + self.0.wire.len()
    }
    pub(crate) fn value(&self) -> &Value {
        &self.0.value
    }
}
fn codec(capacity: Capacity) -> Result<NativeBackend> {
    capacity.validate()?;
    let policy = capacity.backend();
    NativeBackend::new(
        policy,
        EntryPolicy::new(Domain::new("input", "preparation", "data", None), None),
        SetupRegistry::new(Vec::new(), &policy).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn preparation_is_immutable_bounded_and_type_specific() {
        fn send_sync<T: Send + Sync>() {}
        send_sync::<PreparedData>();
        let capacity = Capacity::default();
        for value in [
            Value::Bool(false),
            Value::Index(17),
            Value::Bytes(vec![0, 1, 255].into()),
            Value::Vector(vec![zkc_backends::Scalar::from(7); 16].into()),
            Value::table(&[zkc_backends::Scalar::from(7); 16], &capacity.backend()).unwrap(),
        ] {
            let ty = value.physical_type();
            let material = PreparedData::from_value(value, capacity).unwrap();
            let wire = material.canonical_bytes().to_vec();
            let decoded = PreparedData::from_wire(ty.clone(), wire.clone(), capacity).unwrap();
            assert_eq!(decoded.canonical_bytes(), wire);
            assert_eq!(decoded.physical_type(), &ty);
            assert_eq!(decoded.retained_bytes(), material.retained_bytes());
            assert!(Arc::ptr_eq(&material.0, &material.clone().0));
            let mut truncated = wire.clone();
            truncated.pop();
            assert!(PreparedData::from_wire(ty.clone(), truncated, capacity).is_err());
            let mut trailing = wire.clone();
            trailing.push(0);
            assert!(PreparedData::from_wire(ty.clone(), trailing, capacity).is_err());
            let mut small = capacity;
            small.wire_bytes = wire.len() - 1;
            assert!(PreparedData::from_value(material.value().clone(), small).is_err());
            assert_eq!(
                PreparedData::from_wire(ty, wire, small).unwrap_err(),
                "native-capacity-wire"
            );
        }
        let mut backend = codec(capacity).unwrap();
        let value = Value::Bool(true);
        let ty = value.physical_type();
        let wire = backend.encode_native_value(&value).unwrap();
        let mut single = capacity;
        single.values.live_bytes = value.retained_bytes();
        assert_eq!(
            PreparedData::from_wire(ty, wire, single).unwrap_err(),
            "native-data-bytes-limit"
        );
        assert_eq!(
            PreparedData::from_value(value, single).unwrap_err(),
            "native-data-bytes-limit"
        );
        // An in-process value with no native wire profile cannot be prepared.
        let point =
            Value::point(vec![zkc_backends::Scalar::from(7); 4], &capacity.backend()).unwrap();
        assert_eq!(
            PreparedData::from_value(point, capacity).unwrap_err(),
            "native-input-private"
        );
        let capability = backend
            .issue_rng_for(
                zkc_runtime::vm::Identity::Bls12381Fr,
                Domain::new("input", "preparation", "data", None),
                1,
            )
            .unwrap();
        assert_eq!(
            PreparedData::from_value(capability, capacity).unwrap_err(),
            "native-input-private"
        );
    }
}
