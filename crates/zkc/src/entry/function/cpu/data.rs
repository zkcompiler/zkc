//! Executable data has no file paths, material import requests or capabilities.
use super::*;
use crate::execution::{Capacity, InputValue};
use std::sync::Arc;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Value as Native};
use zkc_runtime::vm::{
    ExecutionLedger, LiveReservation, PhysicalType, Value as RuntimeValue, WorkBudget,
};

type DataResult<T> = std::result::Result<T, String>;
// Measurement vectors can grow geometrically within the existing conservative
// 512-byte slot reservation, before any native payload is constructed.
const _: () = assert!(std::mem::size_of::<zkc_cpu::NativeInputSize>() <= 256);
#[derive(Clone)]
pub struct TypedValue {
    schema: Arc<Schema>,
    pub(super) payload: Arc<Payload>,
    // A whole result product can share a transferred native reservation.
    _live: Arc<LiveReservation>,
}
pub(super) enum Payload {
    Unit,
    Native(Native),
    Product(Vec<TypedValue>),
    Alternative {
        alternative: String,
        fields: Vec<TypedValue>,
        native: Native,
    },
}
impl std::fmt::Debug for TypedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypedValue")
            .field("type", &self.schema.display_type)
            .field("identity", &self.schema.identity)
            .finish_non_exhaustive()
    }
}
impl TypedValue {
    pub fn schema(&self) -> &Schema {
        &self.schema
    }
    pub fn into_value(self) -> crate::entry::Value {
        self.to_value()
    }
    pub(super) fn to_value(&self) -> crate::entry::Value {
        use crate::entry::Value;
        match self.payload.as_ref() {
            Payload::Unit => Value::Unit,
            Payload::Native(v) => v.clone().into(),
            Payload::Product(values) => match self.schema.kind {
                SchemaKind::Tuple => Value::Tuple(values.iter().map(Self::to_value).collect()),
                SchemaKind::Array => Value::Array(values.iter().map(Self::to_value).collect()),
                SchemaKind::Associated => Value::Associated(Box::new(values[0].to_value())),
                _ => Value::Record(
                    self.schema
                        .fields
                        .iter()
                        .zip(values)
                        .map(|(f, v)| (f.name.clone(), v.to_value()))
                        .collect(),
                ),
            },
            Payload::Alternative {
                alternative,
                fields,
                ..
            } => {
                let arm = self
                    .schema
                    .alternatives
                    .iter()
                    .find(|a| a.name == *alternative)
                    .expect("admitted arm");
                Value::Variant {
                    alternative: alternative.clone(),
                    fields: arm
                        .fields
                        .iter()
                        .zip(fields)
                        .map(|(f, v)| (f.name.clone(), v.to_value()))
                        .collect(),
                }
            }
        }
    }
    pub(super) fn boolean(&self) -> bool {
        let Payload::Native(Native::Bool(b)) = self.payload.as_ref() else {
            unreachable!("admitted boolean")
        };
        *b
    }
    pub(super) fn index(&self) -> u64 {
        let Payload::Native(Native::Index(i)) = self.payload.as_ref() else {
            unreachable!("admitted index")
        };
        *i
    }
    pub(super) fn fields(&self) -> &[TypedValue] {
        match self.payload.as_ref() {
            Payload::Product(v) => v,
            Payload::Unit => &[],
            _ => unreachable!("admitted product"),
        }
    }
    pub(super) fn native(&self) -> DataResult<&Native> {
        match self.payload.as_ref() {
            Payload::Native(v) => Ok(v),
            _ => Err("entry-host-data".into()),
        }
    }
    pub(super) fn flatten(&self, out: &mut Vec<Native>) -> DataResult<()> {
        match self.payload.as_ref() {
            Payload::Unit => {}
            Payload::Native(v) => out.push(v.clone()),
            Payload::Product(v) => {
                for v in v {
                    v.flatten(out)?;
                }
            }
            Payload::Alternative { native, .. } => out.push(native.clone()),
        }
        Ok(())
    }
    fn measure_leaves(
        &self,
        backend: &CpuBackend,
        ledger: &ExecutionLedger,
        out: &mut Vec<zkc_cpu::NativeInputSize>,
    ) -> DataResult<()> {
        match self.payload.as_ref() {
            Payload::Unit => {}
            Payload::Product(values) => {
                for value in values {
                    value.measure_leaves(backend, ledger, out)?;
                }
            }
            Payload::Native(value) | Payload::Alternative { native: value, .. } => {
                out.push(measure_native_value(backend, value, ledger)?);
            }
        }
        Ok(())
    }
}
pub(super) fn backend(
    capacity: Capacity,
    cpu: CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> DataResult<CpuBackend> {
    backend_for(capacity, "entry", cpu, installation)
}
pub(super) fn numerical_backend(
    host: &EntryHost,
    capacity: Capacity,
    function: &str,
) -> DataResult<CpuBackend> {
    backend_for(
        capacity,
        function,
        host.cpu.clone(),
        host.options.limits.installation.clone(),
    )
}
fn backend_for(
    capacity: Capacity,
    function: &str,
    cpu: CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> DataResult<CpuBackend> {
    CpuBackend::new_with_installation(
        capacity.backend(),
        EntryPolicy::new(Domain::new("", "entry-host", function, None), None),
        Default::default(),
        cpu,
        installation,
    )
    .map_err(|e| e.to_string())
}
fn charge(ledger: &ExecutionLedger, fresh: usize) -> DataResult<Arc<LiveReservation>> {
    ledger
        .charge(
            WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: 0,
            },
            fresh,
        )
        .map_err(|e| e.to_string())?;
    ledger
        .reserve_live(fresh)
        .map(Arc::new)
        .map_err(|e| e.to_string())
}
fn measure_native_value(
    backend: &CpuBackend,
    value: &Native,
    ledger: &ExecutionLedger,
) -> DataResult<zkc_cpu::NativeInputSize> {
    // Charge the retained bound before walking payloads, including repeated
    // uses of shared data. Recursive sequences and variants cache that bound.
    ledger
        .charge(
            WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: u64::try_from(value.retained_bytes())
                    .map_err(|_| "entry-host-output-limit")?,
            },
            0,
        )
        .map_err(|e| e.to_string())?;
    if !backend.installation().supports_type(&value.physical_type()) {
        return Err("native-input-type".into());
    }
    backend
        .measure_native_value(value)
        .map_err(|e| e.to_string())
}
pub(super) fn pack(
    host: &EntryHost,
    s: &Schema,
    alternative: &str,
    values: Vec<TypedValue>,
    ledger: &ExecutionLedger,
) -> DataResult<TypedValue> {
    let mut bytes = 512 + values.len() * std::mem::size_of::<TypedValue>();
    if s.kind == SchemaKind::Variant {
        let index = s
            .alternatives
            .iter()
            .position(|a| a.name == alternative)
            .expect("admitted arm");
        let ty = &host.types[&s.leaves[0]];
        let descriptor = ty.variant_descriptor().expect("admitted variant");
        // Reserve before building the native arm or its operand vector.
        bytes = bytes
            .saturating_add(descriptor.retained_bytes())
            .saturating_add(512)
            .saturating_add(
                values
                    .iter()
                    .map(|v| v.schema.leaves.len() * std::mem::size_of::<Native>().max(512))
                    .sum::<usize>(),
            );
        let live = charge(ledger, bytes)?;
        let backend = backend(
            host.options.limits.capacity,
            host.cpu.clone(),
            host.options.limits.installation.clone(),
        )?;
        let mut sizes = Vec::new();
        for value in &values {
            value.measure_leaves(&backend, ledger, &mut sizes)?;
        }
        let physical = PhysicalType::default_for(ty.clone()).map_err(|e| e.to_string())?;
        if !backend.installation().supports_type(&physical) {
            return Err("native-input-type".into());
        }
        backend
            .measure_native_variant(&physical, index, &sizes)
            .map_err(|e| e.to_string())?;
        drop(sizes);
        let mut payload = Vec::new();
        for v in &values {
            v.flatten(&mut payload)?;
        }
        let native = Native::Variant(
            zkc_cpu::Variant::new(physical, index, payload).map_err(|e| e.to_string())?,
        );
        return Ok(TypedValue {
            schema: host.schema(s),
            payload: Arc::new(Payload::Alternative {
                alternative: alternative.into(),
                fields: values,
                native,
            }),
            _live: live,
        });
    }
    let live = charge(ledger, bytes)?;
    let payload = if s.kind == SchemaKind::Unit {
        Payload::Unit
    } else {
        Payload::Product(values)
    };
    Ok(TypedValue {
        schema: host.schema(s),
        payload: Arc::new(payload),
        _live: live,
    })
}
pub(super) fn index(
    host: &EntryHost,
    s: &Schema,
    n: u64,
    ledger: &ExecutionLedger,
) -> DataResult<TypedValue> {
    let live = charge(ledger, 512)?;
    Ok(TypedValue {
        schema: host.schema(s),
        payload: Arc::new(Payload::Native(Native::Index(n))),
        _live: live,
    })
}
pub(super) fn collect(
    host: &EntryHost,
    s: &Schema,
    leaves: &mut impl Iterator<Item = Native>,
    live: Arc<LiveReservation>,
) -> DataResult<TypedValue> {
    let payload = match s.kind {
        SchemaKind::Unit => Payload::Unit,
        SchemaKind::Record | SchemaKind::Tuple | SchemaKind::Array | SchemaKind::Associated => {
            Payload::Product(
                s.fields
                    .iter()
                    .map(|f| collect(host, &f.schema, leaves, live.clone()))
                    .collect::<DataResult<_>>()?,
            )
        }
        SchemaKind::Variant => {
            let Native::Variant(value) = leaves.next().ok_or("entry-host-output")? else {
                return Err("entry-host-output".into());
            };
            let arm = s
                .alternatives
                .get(value.alternative())
                .ok_or("entry-host-output")?;
            let mut payload = value.payload().iter().cloned();
            let fields = arm
                .fields
                .iter()
                .map(|f| collect(host, &f.schema, &mut payload, live.clone()))
                .collect::<DataResult<_>>()?;
            if payload.next().is_some() {
                return Err("entry-host-output".into());
            }
            Payload::Alternative {
                alternative: arm.name.clone(),
                fields,
                native: Native::Variant(value),
            }
        }
        _ => {
            let v = leaves.next().ok_or("entry-host-output")?;
            if v.physical_type().logical().spelling() != s.leaves[0] {
                return Err("entry-host-output-type".into());
            }
            Payload::Native(v)
        }
    };
    Ok(TypedValue {
        schema: host.schema(s),
        payload: Arc::new(payload),
        _live: live,
    })
}
pub(super) fn import(
    host: &EntryHost,
    s: &Schema,
    v: crate::entry::Value,
    ledger: &ExecutionLedger,
) -> DataResult<TypedValue> {
    crate::entry::interface::schemas::check_import(s)?;
    host.cpu.enter(|| load_ingress(host, s, v, ledger))
}
fn load_ingress(
    host: &EntryHost,
    s: &Schema,
    v: crate::entry::Value,
    ledger: &ExecutionLedger,
) -> DataResult<TypedValue> {
    let _planning = charge(ledger, metadata(s))?;

    let mut inputs = Vec::new();
    crate::entry::value::flatten(s, v, &mut inputs)?;
    let backend = backend(
        host.options.limits.capacity,
        host.cpu.clone(),
        host.options.limits.installation.clone(),
    )?;
    let mut admission =
        crate::host::admission::Admission::new(host.options.limits.capacity.loading())?
            .with_shared_ledger(Some(ledger.clone()));
    for (input, spelling) in inputs.iter().zip(&s.leaves) {
        let ty =
            PhysicalType::default_for(host.types[spelling].clone()).map_err(|e| e.to_string())?;
        let id = admission.native_data(&backend, ty.clone(), input, None)?;
        admission.data(id, ty.kind())?;
    }
    let (values, live) = admission.load_shared(
        &backend,
        &host.options.limits.capacity.backend(),
        ledger,
        metadata(s),
    )?;
    let mut values = values.into_iter();
    let result = collect(host, s, &mut values, Arc::new(live))?;
    if values.next().is_some() {
        return Err("entry-host-input-shape".into());
    }
    Ok(result)
}
pub(super) fn duplicate(value: &crate::entry::Value) -> crate::entry::Value {
    use crate::entry::Value;
    match value {
        Value::Leaf(v) => Value::Leaf(duplicate_input(v)),
        Value::Unit => Value::Unit,
        Value::Tuple(v) => Value::Tuple(v.iter().map(duplicate).collect()),
        Value::Array(v) => Value::Array(v.iter().map(duplicate).collect()),
        Value::Record(v) => {
            Value::Record(v.iter().map(|(n, v)| (n.clone(), duplicate(v))).collect())
        }
        Value::Variant {
            alternative,
            fields,
        } => Value::Variant {
            alternative: alternative.clone(),
            fields: fields
                .iter()
                .map(|(n, v)| (n.clone(), duplicate(v)))
                .collect(),
        },
        Value::Associated(v) => Value::Associated(Box::new(duplicate(v))),
    }
}
fn duplicate_input(value: &InputValue) -> InputValue {
    match value {
        InputValue::Native(v) => InputValue::Native(v.clone()),
        InputValue::Wire(v) => InputValue::Wire(v.clone()),
        InputValue::Prepared(v) => InputValue::Prepared(v.clone()),
        InputValue::WireSource { file, sha256 } => InputValue::WireSource {
            file: file.clone(),
            sha256: *sha256,
        },
        InputValue::Resource { budget } => InputValue::Resource { budget: *budget },
        InputValue::VerifierKey => InputValue::VerifierKey,
        InputValue::ProverKey(v) => InputValue::ProverKey(v.clone()),
        InputValue::ProverKeyFile { path, fingerprint } => InputValue::ProverKeyFile {
            path: path.clone(),
            fingerprint: *fingerprint,
        },
        InputValue::ProverKeyInput { file, fingerprint } => InputValue::ProverKeyInput {
            file: file.clone(),
            fingerprint: *fingerprint,
        },
        InputValue::Variant {
            alternative,
            payload,
        } => InputValue::Variant {
            alternative: *alternative,
            payload: payload.iter().map(duplicate_input).collect(),
        },
    }
}

pub(super) fn metadata(s: &Schema) -> usize {
    let variant = if s.kind == SchemaKind::Variant {
        // The logical descriptor and active native slots are retained alongside
        // typed projections; count the largest possible arm conservatively.
        512 + s.leaves.first().map_or(0, |leaf| leaf.len() * 32)
            + s.alternatives.len() * 1024
            + s.alternatives
                .iter()
                .map(|a| {
                    a.fields
                        .iter()
                        .map(|f| f.schema.leaves.len())
                        .sum::<usize>()
                        * 512
                })
                .max()
                .unwrap_or(0)
    } else {
        0
    };
    512 + variant
        + s.fields.iter().map(|f| metadata(&f.schema)).sum::<usize>()
        + s.alternatives
            .iter()
            .flat_map(|a| &a.fields)
            .map(|f| metadata(&f.schema))
            .sum::<usize>()
}

// Child owners have already validated these immutable data. In particular,
// mathematical values need no public wire codec merely to remain in memory.
pub(super) fn from_output(
    host: &EntryHost,
    schema: &Schema,
    value: crate::entry::Value,
    ledger: &ExecutionLedger,
) -> DataResult<TypedValue> {
    fn bound(
        host: &EntryHost,
        backend: &CpuBackend,
        ledger: &ExecutionLedger,
        s: &Schema,
        v: &crate::entry::Value,
        mut leaves: Option<&mut Vec<zkc_cpu::NativeInputSize>>,
    ) -> DataResult<usize> {
        use crate::entry::Value;
        let add = |a: usize, b: usize| {
            a.checked_add(b)
                .ok_or_else(|| "entry-host-output-limit".to_owned())
        };
        match v {
            Value::Unit if s.kind == SchemaKind::Unit => Ok(0),
            Value::Leaf(InputValue::Native(v)) if s.leaves.len() == 1 => {
                if v.physical_type().logical().spelling() != s.leaves[0]
                    || !backend.installation().supports_type(&v.physical_type())
                {
                    return Err("entry-host-output-type".into());
                }
                if let Some(leaves) = leaves {
                    leaves.push(measure_native_value(backend, v, ledger)?);
                }
                Ok(v.retained_bytes())
            }
            Value::Tuple(v) if s.kind == SchemaKind::Tuple && v.len() == s.fields.len() => {
                s.fields.iter().zip(v).try_fold(0, |n, (f, v)| {
                    add(
                        n,
                        bound(host, backend, ledger, &f.schema, v, leaves.as_deref_mut())?,
                    )
                })
            }
            Value::Array(v) if s.kind == SchemaKind::Array && v.len() == s.fields.len() => {
                s.fields.iter().zip(v).try_fold(0, |n, (f, v)| {
                    add(
                        n,
                        bound(host, backend, ledger, &f.schema, v, leaves.as_deref_mut())?,
                    )
                })
            }
            Value::Record(v) if s.kind == SchemaKind::Record && v.len() == s.fields.len() => {
                s.fields.iter().try_fold(0, |n, f| {
                    add(
                        n,
                        bound(
                            host,
                            backend,
                            ledger,
                            &f.schema,
                            v.get(&f.name).ok_or("entry-host-output-shape")?,
                            leaves.as_deref_mut(),
                        )?,
                    )
                })
            }
            Value::Associated(v) if s.kind == SchemaKind::Associated => {
                bound(host, backend, ledger, &s.fields[0].schema, v, leaves)
            }
            Value::Variant {
                alternative,
                fields,
            } if s.kind == SchemaKind::Variant => {
                let (index, arm) = s
                    .alternatives
                    .iter()
                    .enumerate()
                    .find(|(_, a)| a.name == *alternative)
                    .ok_or("entry-host-output-shape")?;
                if arm.fields.len() != fields.len() {
                    return Err("entry-host-output-shape".into());
                }
                let mut payload = Vec::new();
                let bytes = arm.fields.iter().try_fold(0, |n, f| {
                    add(
                        n,
                        bound(
                            host,
                            backend,
                            ledger,
                            &f.schema,
                            fields.get(&f.name).ok_or("entry-host-output-shape")?,
                            Some(&mut payload),
                        )?,
                    )
                })?;
                let ty = PhysicalType::default_for(host.types[&s.leaves[0]].clone())
                    .map_err(|e| e.to_string())?;
                if !backend.installation().supports_type(&ty) {
                    return Err("native-input-type".into());
                }
                let size = backend
                    .measure_native_variant(&ty, index, &payload)
                    .map_err(|e| e.to_string())?;
                if let Some(leaves) = leaves {
                    leaves.push(size);
                }
                Ok(bytes)
            }
            _ => Err("entry-host-output-shape".into()),
        }
    }
    fn collect_owned(
        host: &EntryHost,
        s: &Schema,
        v: crate::entry::Value,
        live: Arc<LiveReservation>,
    ) -> DataResult<TypedValue> {
        use crate::entry::Value;
        let payload = match (s.kind, v) {
            (SchemaKind::Unit, Value::Unit) => Payload::Unit,
            (SchemaKind::Tuple, Value::Tuple(v)) | (SchemaKind::Array, Value::Array(v)) => {
                Payload::Product(
                    s.fields
                        .iter()
                        .zip(v)
                        .map(|(f, v)| collect_owned(host, &f.schema, v, live.clone()))
                        .collect::<DataResult<_>>()?,
                )
            }
            (SchemaKind::Record, Value::Record(mut v)) => Payload::Product(
                s.fields
                    .iter()
                    .map(|f| {
                        collect_owned(
                            host,
                            &f.schema,
                            v.remove(&f.name).expect("checked output shape"),
                            live.clone(),
                        )
                    })
                    .collect::<DataResult<_>>()?,
            ),
            (SchemaKind::Associated, Value::Associated(v)) => {
                Payload::Product(vec![collect_owned(
                    host,
                    &s.fields[0].schema,
                    *v,
                    live.clone(),
                )?])
            }
            (
                SchemaKind::Variant,
                Value::Variant {
                    alternative,
                    mut fields,
                },
            ) => {
                let index = s
                    .alternatives
                    .iter()
                    .position(|a| a.name == alternative)
                    .expect("checked output shape");
                let values = s.alternatives[index]
                    .fields
                    .iter()
                    .map(|f| {
                        collect_owned(
                            host,
                            &f.schema,
                            fields.remove(&f.name).expect("checked output shape"),
                            live.clone(),
                        )
                    })
                    .collect::<DataResult<Vec<_>>>()?;
                let mut payload = Vec::new();
                for value in &values {
                    value.flatten(&mut payload)?;
                }
                let physical = PhysicalType::default_for(host.types[&s.leaves[0]].clone())
                    .map_err(|e| e.to_string())?;
                let native = Native::Variant(
                    zkc_cpu::Variant::new(physical, index, payload).map_err(|e| e.to_string())?,
                );
                Payload::Alternative {
                    alternative,
                    fields: values,
                    native,
                }
            }
            (_, Value::Leaf(InputValue::Native(v))) => {
                if s.leaves.len() != 1
                    || v.physical_type().logical().spelling() != s.leaves[0]
                    || !v.physical_type().is_duplicable()
                {
                    return Err("entry-host-output-type".into());
                }
                Payload::Native(*v)
            }
            _ => return Err("entry-host-output-shape".into()),
        };
        Ok(TypedValue {
            schema: host.schema(s),
            payload: Arc::new(payload),
            _live: live,
        })
    }
    // Bound measurement scratch before walking the source shape. The complete
    // active variants are checked before collect_owned builds any native spine.
    let planning = charge(ledger, metadata(schema))?;
    let backend = backend(
        host.options.limits.capacity,
        host.cpu.clone(),
        host.options.limits.installation.clone(),
    )?;
    // Standalone native leaves retain their owner's validation and count units;
    // only a newly assembled active variant needs aggregate payload counts.
    let bytes = bound(host, &backend, ledger, schema, &value, None)?
        .checked_add(metadata(schema))
        .ok_or("entry-host-output-limit")?;
    drop(planning);
    let live = charge(ledger, bytes)?;
    collect_owned(host, schema, value, live)
}

/// Conservative ownership of descriptions retained by application contexts.
/// File descriptors retain no file contents until bounded native loading.
pub(super) fn description_bytes(value: &crate::entry::Value) -> usize {
    use crate::entry::Value;
    let children = match value {
        Value::Unit => 0,
        Value::Leaf(input) => match input {
            InputValue::Native(v) => v.retained_bytes(),
            InputValue::Wire(v) => v.len(),
            InputValue::Prepared(v) => v
                .value()
                .retained_bytes()
                .saturating_add(v.canonical_bytes().len()),
            InputValue::ProverKey(v) => v.value().retained_bytes(),
            InputValue::ProverKeyFile { path, .. } => path.len(),
            InputValue::Variant { payload, .. } => payload.len() * 512,
            _ => 0,
        },
        Value::Tuple(v) | Value::Array(v) => v.iter().map(description_bytes).sum(),
        Value::Record(v) => v.iter().map(|(n, v)| n.len() + description_bytes(v)).sum(),
        Value::Variant {
            alternative,
            fields,
        } => {
            alternative.len()
                + fields
                    .iter()
                    .map(|(n, v)| n.len() + description_bytes(v))
                    .sum::<usize>()
        }
        Value::Associated(v) => description_bytes(v),
    };
    children.saturating_add(512)
}
