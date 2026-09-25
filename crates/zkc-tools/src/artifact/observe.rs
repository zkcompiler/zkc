//! Source-normalized V observations around actual backend transitions.
//! The wrapper delegates every custody hook and kernel; it never fabricates a
//! response on a failing apply and never serializes P-only private operands.
use super::{
    construction::{CheckedBundle, type_spelling},
    io::*,
};
use crate::protocol::WireBackend;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use zkc_backends::Value;
use zkc_runtime::{
    interactive::{
        ArtifactFormat, Backend, BackendError, Frame, FrameExit, FrameKind, Identity, Invocation,
        LogicalType, PathElement, PhysicalType, Representation, Type, Value as RuntimeValue,
    },
    logical,
};

struct Event {
    value: Json,
    bytes: usize,
}
impl Event {
    fn new(value: Json) -> std::result::Result<Self, BackendError> {
        Ok(Self {
            bytes: json_size(&value)?,
            value,
        })
    }
}
// Count serialization without allocating a second copy of a potentially large
// public event. All inputs are bounded before they reach this writer.
fn json_size(value: &Json) -> std::result::Result<usize, BackendError> {
    struct Count(usize);
    impl std::io::Write for Count {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.0 = self
                .0
                .checked_add(bytes.len())
                .ok_or_else(|| std::io::Error::other("size"))?;
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut size = Count(0);
    serde_json::to_writer(&mut size, value).map_err(|_| BackendError::new("observer-json"))?;
    Ok(size.0)
}

// Upper bounds for installed native values, independent of the
// operation's algorithm. They use the host's same finite value policy. A new
// public kind must provide a bound before its transition can be observed.
fn response_bound(
    request: &Json,
    outputs: &[PhysicalType],
    format: ArtifactFormat,
) -> std::result::Result<usize, BackendError> {
    let policy = zkc_backends::Policy::default();
    let mut size = json_size(&json!(["response", request, []]))?;
    for (index, ty) in outputs.iter().enumerate() {
        if let Some((factors, backing, count)) = diagonal_shape(ty.clone(), &policy)? {
            let shell = json!([
                "zkc.diagonal-observation/1",
                ty.logical().spelling(),
                [factors.spelling(), ""],
                [backing.spelling(), ""]
            ]);
            // Both admitted diagonal shapes have 32-byte wire elements.
            size += usize::from(index > 0) + json_size(&shell)? + 4 * (10 + 32 * count);
            continue;
        }
        let wire = match ty.kind() {
            Type::Index => 14,
            Type::Indices => 10 + 8 * policy.max_table_elements,
            Type::Field => 38,
            Type::Bool => 7,
            Type::Group => 54,
            Type::Round => 102,
            Type::Point => 10 + 32 * policy.max_arity,
            Type::Table | Type::Vector | Type::Polynomial => 10 + 32 * policy.max_table_elements,
            Type::Matrix => policy.max_wire_bytes,
            Type::Groups => 10 + 48 * policy.max_groups,
            Type::Commitment if ty.logical().identity().is_row_commitment() => 38,
            Type::Proof if ty.logical().identity().is_row_commitment() => 10 + 32 * 24,
            Type::Commitments => 10 + 32 * policy.max_table_elements,
            Type::Commitment => 6 + 81 + 48,
            Type::Proof => 6 + 81 + 96 * policy.max_arity,
            Type::VerifierKey => 81 + 144 + 48 * policy.max_arity,
            _ => return Err(BackendError::new("observer-private-output")),
        };
        size += usize::from(index > 0) + type_spelling(ty.logical(), format).len() + 7 + 2 * wire;
    }
    Ok(size)
}

// Exactly the two installed depth-one diagnostic shapes. This is an audit
// representation, not a new serializable mathematical type or runtime codec.
fn diagonal_shape(
    ty: PhysicalType,
    policy: &zkc_backends::Policy,
) -> std::result::Result<Option<(LogicalType, LogicalType, usize)>, BackendError> {
    let (field, backing, count) = match ty.representation() {
        Representation::FrDiagonal => (
            Identity::Bls12381Fr,
            Type::Vector,
            policy.max_table_elements,
        ),
        Representation::RistrettoDiagonal => (
            Identity::Ristretto255Scalar,
            Type::Groups,
            policy.max_groups.min(policy.max_table_elements),
        ),
        _ => return Ok(None),
    };
    let factors = LogicalType::new(Type::Vector, field)
        .map_err(|_| BackendError::new("observer-diagonal-type"))?;
    let backing = LogicalType::new(
        backing,
        if backing == Type::Groups {
            Identity::Ristretto255Group
        } else {
            field
        },
    )
    .map_err(|_| BackendError::new("observer-diagonal-type"))?;
    if ty.logical() != backing {
        return Err(BackendError::new("observer-diagonal-type"));
    }
    Ok(Some((factors, backing, count)))
}

#[derive(Clone)]
struct SourceOp {
    origin: Vec<String>,
    kernel: String,
    attrs: Vec<String>,
    arguments: Vec<String>,
    classification: String,
}

/// Diagnostic recording policy. Disabling it preserves inner backend calls but
/// omits event allocation, observer limits and events; it is not trace equivalence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraceMode {
    Full,
    None,
}

pub struct Observed<B> {
    inner: B,
    validator: String,
    format: ArtifactFormat,
    origins: BTreeMap<(String, String), SourceOp>,
    source_map: Option<zkc_runtime::interactive::SourceMap>,
    events: Vec<Json>,
    event_bytes: usize,
    trace: TraceMode,
}
impl<B: WireBackend<Value = Value>> Observed<B> {
    pub(super) fn new(inner: B, bundle: &CheckedBundle, trace: TraceMode) -> Result<Self> {
        let mut origins = BTreeMap::new();
        if trace == TraceMode::Full {
            for function in list(&bundle.common[2])? {
                if list(function.get(4).ok_or("artifact-observer-function")?)?
                    .iter()
                    .any(|op| matches!(op.get(0).and_then(Json::as_str), Some("if" | "for")))
                {
                    return Err("artifact-observer-local-control-unsupported".into());
                }
            }
        }
        let rows = if trace == TraceMode::Full {
            list(&bundle.manifest[4])?
        } else {
            &[]
        };
        for row in rows {
            let r = array(row, 8)?;
            let origin = r[2..7]
                .iter()
                .map(|v| Ok(text(v)?.to_owned()))
                .collect::<Result<Vec<_>>>()?;
            let classification = text(&r[7])?.to_owned();
            let (kernel, arguments, attrs) = if classification == "construction" {
                (String::new(), Vec::new(), Vec::new())
            } else {
                let function = list(&bundle.common[2])?
                    .iter()
                    .find(|f| f.get(1) == Some(&r[4]))
                    .ok_or("artifact-observer-function")?;
                let body = function.get(4).ok_or("artifact-observer-function")?;
                let op = list(body)?
                    .iter()
                    .find(|op| {
                        op.get(0).and_then(Json::as_str) == Some("op") && op.get(1) == Some(&r[5])
                    })
                    .ok_or("artifact-observer-op")?;
                let op = array(op, 6)?;
                let (contract, arguments) = match bundle.admitted.format() {
                    ArtifactFormat::ExplicitBindings => {
                        let binding = list(&bundle.common[1])?
                            .iter()
                            .find(|b| b.get(0) == Some(&op[2]))
                            .ok_or("artifact-observer-binding")?;
                        let binding = array(binding, 4)?;
                        (
                            text(&binding[1])?.to_owned(),
                            list(&binding[2])?
                                .iter()
                                .map(|a| Ok(text(a)?.into()))
                                .collect::<Result<_>>()?,
                        )
                    }
                };
                (
                    contract,
                    arguments,
                    list(&op[3])?
                        .iter()
                        .map(|a| Ok(text(a)?.into()))
                        .collect::<Result<_>>()?,
                )
            };
            let key = (text(&r[0])?.into(), text(&r[1])?.into());
            if origins
                .insert(
                    key,
                    SourceOp {
                        origin,
                        kernel,
                        attrs,
                        arguments,
                        classification,
                    },
                )
                .is_some()
            {
                return Err("artifact-observer-duplicate".into());
            }
        }
        Ok(Self {
            inner,
            validator: bundle.validator.clone(),
            format: bundle.admitted.format(),
            origins,
            source_map: if trace == TraceMode::Full {
                bundle.admitted.source_map().cloned()
            } else {
                None
            },
            events: Vec::new(),
            event_bytes: 0,
            trace,
        })
    }
    pub fn inner(&self) -> &B {
        &self.inner
    }
    pub fn events(&self) -> &[Json] {
        &self.events
    }
    fn reserve(&mut self, bytes: usize, count: usize) -> std::result::Result<(), BackendError> {
        if self.event_bytes.saturating_add(bytes) > INPUT_LIMIT {
            return Err(BackendError::new("exhausted:observer-bytes"));
        }
        self.events
            .try_reserve(count)
            .map_err(|_| BackendError::new("exhausted:observer-allocation"))?;
        Ok(())
    }
    fn record(&mut self, event: Event) {
        self.event_bytes += event.bytes;
        self.events.push(event.value);
    }
    fn value(&self, value: &Value, ty: LogicalType) -> std::result::Result<Json, BackendError> {
        if value.physical_type().logical() != ty {
            return Err(BackendError::new("observer-value-type"));
        }
        if diagonal_shape(value.physical_type(), &zkc_backends::Policy::default())?.is_some() {
            // This diagnostic exposes the two explicit immutable backings. It is
            // never a canonical vector encoding or an accepted transcript value.
            let p = zkc_backends::Policy::default();
            let (factors, backing) = match value {
                Value::FrDiagonal(d) => (
                    Value::vector(d.factors(), &p)?,
                    Value::vector(d.backing(), &p)?,
                ),
                Value::RistrettoDiagonal(d) => (
                    Value::ristretto_vector(d.factors(), &p)?,
                    Value::ristretto_groups(d.backing(), &p)?,
                ),
                _ => return Err(BackendError::new("observer-diagonal-type")),
            };
            return Ok(json!([
                "zkc.diagonal-observation/1",
                ty.spelling(),
                self.value(&factors, factors.physical_type().logical())?,
                self.value(&backing, backing.physical_type().logical())?
            ]));
        }
        let bytes = match value {
            Value::VerifierKey(vk) => vk
                .to_bytes(&zkc_backends::Policy::default().ark_bounds())
                .map_err(|_| BackendError::new("observer-key"))?,
            _ => self.inner.encode(value)?,
        };
        Ok(json!([type_spelling(ty, self.format), hex(&bytes)]))
    }
    fn values(
        &self,
        values: &[Value],
        types: &[PhysicalType],
    ) -> std::result::Result<Vec<Json>, BackendError> {
        if values.len() != types.len() {
            return Err(BackendError::new("observer-value-arity"));
        }
        values
            .iter()
            .zip(types)
            .map(|(v, t)| self.value(v, t.logical()))
            .collect()
    }
}
fn request(
    i: &Invocation<'_>,
    origin: &[String],
    kernel: &str,
    arguments: &[String],
    attrs: &[String],
    _format: ArtifactFormat,
) -> Json {
    let runtime = i.frame.origin();
    let path = runtime
        .path
        .iter()
        .map(|p| match p {
            PathElement::Conditional { site, taken } => {
                json!(["if", site, if *taken { "then" } else { "else" }])
            }
            PathElement::Match { site, alternative } => json!(["match", site, alternative]),
            PathElement::For { site, index } => json!(["for", site, index.to_string()]),
            PathElement::Call { site, instance } => json!(["call", site, instance]),
            PathElement::Loop { site, iteration } => json!(["loop", site, iteration.to_string()]),
        })
        .collect::<Vec<_>>();
    let mut operation = vec![json!("operation")];
    operation.extend(origin.iter().map(|s| json!(s)));
    operation.push(json!(kernel));
    operation.push(json!(arguments));
    operation.push(json!(attrs));
    json!([
        "zkc.logical-origin/2",
        runtime.entry,
        runtime.instance,
        path,
        operation
    ])
}
impl<B: WireBackend<Value = Value>> Backend for Observed<B> {
    type Value = Value;
    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.inner.binding_signature(binding)
    }
    fn validate_value(&self, v: &Value) -> std::result::Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> std::result::Result<(), BackendError> {
        self.inner.enter_frame(f, args)
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        exit: FrameExit,
        outputs: &[Value],
    ) -> std::result::Result<(), BackendError> {
        self.inner.leave_frame(f, exit, outputs)
    }
    fn apply(
        &mut self,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> std::result::Result<Vec<Value>, BackendError> {
        if self.trace == TraceMode::None || i.frame.role() != self.validator {
            return self.inner.apply(i, args);
        }
        let FrameKind::Local { function, site } = i.frame.kind() else {
            return Err(BackendError::new("observer-frame"));
        };
        let binding = i.binding.declaration();
        let (kernel, arguments) = (binding.contract.as_str(), binding.arguments.as_slice());
        // Representation conversions have been checked against the constructed
        // source; they are not additional original protocol observations.
        if kernel == "table.relayout" {
            return self.inner.apply(i, args);
        }
        let source_function = match &self.source_map {
            Some(map) => {
                &map.call(&i.frame.origin().instance, i.frame.role(), site)
                    .filter(|call| call.function == *function)
                    .ok_or_else(|| BackendError::new("observer-source-call"))?
                    .source_function
            }
            None => return Err(BackendError::new("observer-source-map")),
        };
        let op = self
            .origins
            .get(&(source_function.clone(), i.site.to_owned()))
            .cloned()
            .ok_or_else(|| BackendError::new("observer-origin"))?;
        let signature = i.binding.signature();
        if kernel.starts_with("transcript.observe.") {
            let origin = logical::message_origin(i.frame.origin(), i.attributes)
                .map_err(|_| BackendError::new("observer-origin"))?;
            let value = args
                .get(1)
                .ok_or_else(|| BackendError::new("observer-input"))?;
            let event = Event::new(json!([
                "message",
                hex(&origin),
                type_spelling(signature.inputs[1].logical(), self.format),
                hex(&self.inner.encode(value)?)
            ]))?;
            self.reserve(event.bytes, 1)?;
            let output = self.inner.apply(i, args)?;
            self.record(event);
            return Ok(output);
        }
        if matches!(kernel, "transcript.challenge" | "transcript.draw_index") {
            let index = kernel == "transcript.draw_index";
            let field_arguments = {
                vec![
                    signature.inputs[0]
                        .logical()
                        .identity()
                        .scalar_field()
                        .ok_or_else(|| BackendError::new("observer-suite"))?
                        .name()
                        .to_owned(),
                ]
            };
            let req = request(
                i,
                i.attributes,
                if index { "random.index" } else { "random.draw" },
                &field_arguments,
                &[],
                self.format,
            );
            let origin = logical::challenge_origin(i.frame.origin(), i.attributes)
                .map_err(|_| BackendError::new("observer-origin"))?;
            let mut observed_inputs = vec![json!(["selected_rng"])];
            if index {
                observed_inputs.push(
                    self.value(
                        args.get(1)
                            .ok_or_else(|| BackendError::new("observer-input"))?,
                        signature.inputs[1].logical(),
                    )?,
                );
            }
            let before = Event::new(json!(["request", req, observed_inputs]))?;
            // Every Fr challenge has the same canonical wire width. Reserve
            // request, challenge and response together before the draw consumes
            // a transcript transition; failure inside apply keeps only request.
            let placeholder = json!([
                type_spelling(signature.outputs[0].logical(), self.format),
                "0".repeat(76)
            ]);
            let after_bound = json_size(&json!(["challenge", hex(&origin), placeholder]))?
                + json_size(&json!(["response", req, [placeholder, ["selected_rng"]]]))?;
            self.reserve(before.bytes + after_bound, 3)?;
            self.record(before);
            let output = self.inner.apply(i, args)?;
            let value = self.value(
                output
                    .first()
                    .ok_or_else(|| BackendError::new("observer-output"))?,
                signature.outputs[0].logical(),
            )?;
            let challenge = Event::new(json!(["challenge", hex(&origin), value]))?;
            let response = Event::new(json!(["response", req, [value, ["selected_rng"]]]))?;
            if challenge.bytes + response.bytes > after_bound {
                return Err(BackendError::new("observer-output-bound"));
            }
            self.record(challenge);
            self.record(response);
            return Ok(output);
        }
        if op.classification == "recipe" {
            return self.inner.apply(i, args);
        }
        if op.classification != "original"
            || kernel != op.kernel
            || arguments != op.arguments
            || i.attributes != op.attrs
        {
            return Err(BackendError::new("observer-operation"));
        }
        let req = request(
            i,
            &op.origin,
            &op.kernel,
            &op.arguments,
            &op.attrs,
            self.format,
        );
        let before = Event::new(json!([
            "request",
            req,
            self.values(args, &signature.inputs)?
        ]))?;
        let after_bound = response_bound(&req, &signature.outputs, self.format)?;
        self.reserve(before.bytes + after_bound, 2)?;
        self.record(before);
        let output = self.inner.apply(i, args)?;
        let after = Event::new(json!([
            "response",
            req,
            self.values(&output, &signature.outputs)?
        ]))?;
        if after.bytes > after_bound {
            return Err(BackendError::new("observer-output-bound"));
        }
        self.record(after);
        Ok(output)
    }
}
impl<B: WireBackend<Value = Value>> WireBackend for Observed<B> {
    fn encode(&self, v: &Value) -> std::result::Result<Vec<u8>, BackendError> {
        self.inner.encode(v)
    }
    fn decode(
        &self,
        ty: zkc_runtime::interactive::PhysicalType,
        bytes: &[u8],
    ) -> std::result::Result<Value, BackendError> {
        self.inner.decode(ty, bytes)
    }
}

#[cfg(test)]
mod tests;
