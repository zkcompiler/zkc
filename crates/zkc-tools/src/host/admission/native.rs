//! Compound data planning uses backend-owned physical measurements. Loading is
//! deferred until Admission has reserved every operand in the invocation.
use super::*;
use crate::host::request::InputValue;
use zkc_backends::{NativeInputSize, Variant};

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
            for (expected, child) in arm.payload().iter().zip(payload) {
                let physical =
                    PhysicalType::default_for(expected.clone()).map_err(|e| e.to_string())?;
                check_native_data(&physical, child, capacity)?;
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
        let (input, _) = self.plan(backend, ty, request, selected)?;
        self.add(input)
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
                if !ty.is_duplicable() || !zkc_backends::has_native_wire(&ty) {
                    return Err("native-input-private".into());
                }
                if arm.payload().len() != payload.len() {
                    return Err("native-input-payload".into());
                }
                let mut inputs = Vec::new();
                let mut sizes = Vec::new();
                for (logical, value) in arm.payload().iter().zip(payload) {
                    let physical =
                        PhysicalType::default_for(logical.clone()).map_err(|e| e.to_string())?;
                    let (input, size) = self.plan(backend, physical, value, selected.clone())?;
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
            let descriptor = ty
                .logical()
                .variant_descriptor()
                .expect("planned variant")
                .clone();
            let value = Value::Variant(
                Variant::new(descriptor, alternative, values).map_err(|e| e.to_string())?,
            );
            if value.retained_bytes() > estimate {
                return Err("artifact-input-size-estimate".into());
            }
            backend
                .validate_native_input(&value)
                .map_err(|e| e.to_string())?;
            Ok(value)
        }
        Input::Key { .. } | Input::Ready(_) => {
            unreachable!("only immutable data is planned as variant payload")
        }
    }
}
