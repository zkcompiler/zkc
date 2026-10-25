//! Compound data planning uses backend-owned physical measurements. Loading is
//! deferred until Admission has reserved every operand in the invocation.
use super::*;
use crate::host::request::InputValue;
use zkc_native::{NativeInputSize, Variant};

/// Check constructor shape and byte bounds before setup imports. The admitted
/// type bounds recursion; backend validation/loading remains a later phase.
pub(crate) fn check_native_data(
    ty: &PhysicalType,
    request: &InputValue,
    capacity: crate::host::capacity::Capacity,
) -> Result<()> {
    match request {
        InputValue::Wire(bytes) => capacity.check_wire(bytes.len()),
        InputValue::WireFile { .. } => Ok(()),
        InputValue::Native(value) => Input::native_value(ty.clone(), value, None, None).map(|_| ()),
        InputValue::Prepared(data) => {
            capacity.check_wire(data.canonical_bytes().len())?;
            Input::native_value(ty.clone(), data.value(), None, None).map(|_| ())
        }
        InputValue::Variant {
            alternative,
            payload,
        } => {
            let logical = ty.logical();
            let descriptor = logical.variant_descriptor().ok_or("native-input-type")?;
            let arm = descriptor
                .alternatives()
                .get(*alternative)
                .ok_or("native-input-alternative")?;
            if !ty.is_duplicable() {
                return Err("native-input-private".into());
            }
            if arm.payload().len() != payload.len() {
                return Err("native-input-payload".into());
            }
            for (physical, child) in ty
                .variant_payload(*alternative)
                .ok_or("native-input-type")?
                .iter()
                .zip(payload)
            {
                check_native_data(physical, child, capacity)?;
            }
            Ok(())
        }
        _ => Err("native-input-private".into()),
    }
}

/// Only private typed Host adapters enable this path. Public byte/native ingress
/// retains its codec requirement; no file or resource declaration is executable.
pub(crate) fn check_retained_data(
    ty: &PhysicalType,
    input: &InputValue,
    capacity: crate::execution::Capacity,
) -> Result<()> {
    if zkc_native::has_native_wire(ty) {
        return check_native_data(ty, input, capacity);
    }
    if !ty.is_duplicable() || matches!(ty.kind(), Type::ProverKey | Type::VerifierKey) {
        return Err("native-input-private".into());
    }
    match input {
        InputValue::Native(v) if v.physical_type() == *ty => Ok(()),
        InputValue::Variant {
            alternative,
            payload,
        } => {
            let logical = ty.logical();
            let descriptor = logical.variant_descriptor().ok_or("native-input-type")?;
            let arm = descriptor
                .alternatives()
                .get(*alternative)
                .ok_or("native-input-alternative")?;
            if arm.payload().len() != payload.len() {
                return Err("native-input-payload".into());
            }
            for (physical, input) in ty
                .variant_payload(*alternative)
                .ok_or("native-input-type")?
                .iter()
                .zip(payload)
            {
                check_retained_data(physical, input, capacity)?;
            }
            Ok(())
        }
        _ => Err("native-input-private".into()),
    }
}
impl<'a> Admission<'a> {
    /// Plan immutable native data using the same complete invocation budget.
    pub fn native_data(
        &mut self,
        backend: &NativeBackend,
        ty: PhysicalType,
        request: &'a InputValue,
        selected: Option<Arc<VerifierKey>>,
    ) -> Result<usize> {
        let input = if self.retained_inputs && !zkc_native::has_native_wire(&ty) {
            self.plan_retained(backend, ty, request, selected)?
        } else {
            self.plan(backend, ty, request, selected)?.0
        };
        self.add(input)
    }
    fn plan_retained(
        &mut self,
        backend: &NativeBackend,
        ty: PhysicalType,
        request: &'a InputValue,
        selected: Option<Arc<VerifierKey>>,
    ) -> Result<Input<'a>> {
        check_retained_data(&ty, request, crate::execution::Capacity::default())?;
        self.work(1)?;
        match request {
            InputValue::Native(value) => {
                self.work(value.retained_bytes())?;
                Ok(Input::Retained {
                    ty,
                    value,
                    selected,
                })
            }
            InputValue::Variant {
                alternative,
                payload,
            } => {
                let arm = ty
                    .variant_payload(*alternative)
                    .ok_or("native-input-type")?;
                let mut children = Vec::new();
                let mut bytes = ty.descriptor_bytes() + 256 + payload.len() * 512;
                for (physical, input) in arm.iter().zip(payload) {
                    let physical = physical.clone();
                    let child = if zkc_native::has_native_wire(&physical) {
                        self.plan(backend, physical, input, selected.clone())?.0
                    } else {
                        self.plan_retained(backend, physical, input, selected.clone())?
                    };
                    bytes = bytes
                        .checked_add(child.estimate()?)
                        .ok_or("artifact-input-bytes-limit")?;
                    children.push(child);
                }
                Ok(Input::Variant {
                    ty,
                    alternative: *alternative,
                    payload: children,
                    estimate: bytes,
                })
            }
            _ => Err("native-input-private".into()),
        }
    }
    /// Canonical public binding and shared-input comparison traverse a loaded
    /// value once more. Reserve that work before loading any invocation data.
    pub fn charge_encoding(&mut self, id: usize) -> Result<()> {
        self.work(self.inputs[id].1)
    }

    fn plan(
        &mut self,
        backend: &NativeBackend,
        ty: PhysicalType,
        request: &'a InputValue,
        selected: Option<Arc<VerifierKey>>,
    ) -> Result<(Input<'a>, NativeInputSize)> {
        self.work(1)?;
        match request {
            InputValue::Prepared(data) => self.plan_wire(
                backend,
                ty,
                Cow::Borrowed(data.canonical_bytes()),
                Some(data.value()),
                selected,
            ),
            InputValue::Native(value) => {
                let input = Input::native_value(ty, value, selected, None)?;
                self.work(value.retained_bytes())?;
                let size = backend
                    .measure_native_input(value)
                    .map_err(|e| e.to_string())?;
                Ok((input, size))
            }
            InputValue::Wire(bytes) => {
                self.plan_wire(backend, ty, Cow::Borrowed(bytes.as_slice()), None, selected)
            }
            InputValue::WireFile { file, sha256 } => {
                let bytes = self.file_wire(file, sha256, backend.policy().max_wire_bytes)?;
                self.plan_wire(backend, ty, Cow::Owned(bytes), None, selected)
            }
            InputValue::Variant {
                alternative,
                payload,
            } => {
                let logical = ty.logical();
                let descriptor = logical.variant_descriptor().ok_or("native-input-type")?;
                let arm = descriptor
                    .alternatives()
                    .get(*alternative)
                    .ok_or("native-input-alternative")?;
                if !ty.is_duplicable() || !zkc_native::has_native_wire(&ty) {
                    return Err("native-input-private".into());
                }
                if arm.payload().len() != payload.len() {
                    return Err("native-input-payload".into());
                }
                let mut inputs = Vec::new();
                let mut sizes = Vec::new();
                for (physical, value) in ty
                    .variant_payload(*alternative)
                    .ok_or("native-input-type")?
                    .iter()
                    .zip(payload)
                {
                    let (input, size) =
                        self.plan(backend, physical.clone(), value, selected.clone())?;
                    inputs.push(input);
                    sizes.push(size);
                }
                let size = backend
                    .measure_native_variant(&ty, *alternative, &sizes)
                    .map_err(|e| e.to_string())?;
                Ok((
                    Input::Variant {
                        ty,
                        alternative: *alternative,
                        payload: inputs,
                        estimate: size.retained_bytes(),
                    },
                    size,
                ))
            }
            _ => Err("native-input-private".into()),
        }
    }
    pub(super) fn plan_wire(
        &mut self,
        backend: &NativeBackend,
        ty: PhysicalType,
        bytes: Cow<'a, [u8]>,
        prepared: Option<&'a Value>,
        selected: Option<Arc<VerifierKey>>,
    ) -> Result<(Input<'a>, NativeInputSize)> {
        self.work(bytes.len())?;
        let size = backend
            .measure_native_wire(&ty, &bytes)
            .map_err(|e| e.to_string())?;
        let input = if let Some(value) = prepared {
            Input::native_value(ty, value, selected, Some(size.retained_bytes()))?
        } else {
            Input::NativeWire {
                ty,
                bytes,
                estimate: size.retained_bytes(),
                selected,
            }
        };
        Ok((input, size))
    }
}

pub(super) fn check(backend: &NativeBackend, input: &Input<'_>) -> Result<()> {
    match input {
        Input::Native {
            value, selected, ..
        } => check_native(backend, value, selected.as_deref()),
        Input::Retained {
            value, selected, ..
        } => {
            zkc_runtime::vm::Backend::validate_value(backend, value).map_err(|e| e.to_string())?;
            if let Some(key) = selected {
                super::super::setups::check_input(value, key)?;
            }
            Ok(())
        }
        Input::Variant { payload, .. } => {
            for child in payload {
                check(backend, child)?;
            }
            Ok(())
        }
        Input::NativeWire { .. } | Input::Key { .. } | Input::Ready(_) => Ok(()),
    }
}
pub(super) fn load(backend: &NativeBackend, input: Input<'_>) -> Result<Value> {
    match input {
        Input::Native { value, .. } => Ok(value.clone()),
        Input::NativeWire {
            ty,
            bytes,
            selected,
            ..
        } => {
            #[cfg(test)]
            DECODE_COUNT.with(|n| n.set(n.get() + 1));
            let value = backend
                .decode_native_value(&ty, &bytes)
                .map_err(|e| e.to_string())?;
            if value.physical_type() != ty {
                return Err("native-input-type".into());
            }
            check_native(backend, &value, selected.as_deref())?;
            Ok(value)
        }
        Input::Variant {
            ty,
            alternative,
            payload,
            estimate,
        } => {
            let values = payload
                .into_iter()
                .map(|child| load(backend, child))
                .collect::<Result<Vec<_>>>()?;
            let value = Value::Variant(
                Variant::new(ty.clone(), alternative, values).map_err(|e| e.to_string())?,
            );
            if value.retained_bytes() > estimate {
                return Err("artifact-input-size-estimate".into());
            }
            if zkc_native::has_native_wire(&ty) {
                backend
                    .validate_native_input(&value)
                    .map_err(|e| e.to_string())?;
            } else {
                zkc_runtime::vm::Backend::validate_value(backend, &value)
                    .map_err(|e| e.to_string())?;
            }
            Ok(value)
        }
        Input::Retained { value, .. } => Ok(value.clone()),
        Input::Key { .. } | Input::Ready(_) => {
            unreachable!("only immutable data is planned as variant payload")
        }
    }
}
