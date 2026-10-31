use super::{InputGroup, InputInterface, MAX_REQUEST_BYTES};
use crate::entry::{
    NamedValues, Value,
    interface::raw::{Field, Kind, Schema},
};
use crate::{
    execution::{Capacity, InputSource, InputValue},
    io::{bytes::digest, document},
};
use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_runtime::vm::PhysicalType;
impl InputInterface<'_> {
    fn check_native_input(self, schema: &Schema) -> Result<(), String> {
        self.check_input(schema)?;
        if schema.leaves.iter().all(|s| {
            zkc_runtime::vm::LogicalType::parse(s).is_ok_and(|t| t.is_native_message_data())
        }) {
            Ok(())
        } else {
            Err("entry-input-codec".into())
        }
    }
}

/// File resolution is opt-in. Implementations return opened regular descriptors;
/// reads and cryptographic import still occur in common Host preparation.
pub trait Resolver {
    fn resolve(&mut self, relative: &str) -> Result<InputSource, String>;
}
#[derive(Debug)]
pub struct InputError {
    pub code: String,
    pub path: String,
}
impl std::fmt::Display for InputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.code)
    }
}
impl std::error::Error for InputError {}
impl InputError {
    fn at(code: impl Into<String>, path: &str) -> Self {
        Self {
            code: code.into(),
            path: path.into(),
        }
    }
}
/// One decoder per invocation, so documents and references share aggregate limits.
pub struct Decoder {
    installation: zkc_cpu::CpuInstallation,
    document: document::Budget,
    capacity: Capacity,
    inline_bytes: usize,
    references: usize,
}
impl Decoder {
    pub fn new(capacity: Capacity) -> Result<Self, String> {
        Self::with_installation(capacity, Default::default())
    }
    pub fn with_installation(
        capacity: Capacity,
        installation: zkc_cpu::CpuInstallation,
    ) -> Result<Self, String> {
        capacity.validate()?;
        Ok(Self {
            installation,
            document: document::Budget::new(MAX_REQUEST_BYTES),
            capacity,
            inline_bytes: 0,
            references: 0,
        })
    }
    pub fn remaining_document_bytes(&self) -> usize {
        self.document.remaining_bytes()
    }
    #[cfg(feature = "files")]
    pub(crate) fn select_installation(&mut self, installation: zkc_cpu::CpuInstallation) {
        self.installation = installation;
    }
    pub fn decode_optional(
        &mut self,
        group: &InputGroup<'_>,
        bytes: Option<&[u8]>,
        resolver: Option<&mut dyn Resolver>,
    ) -> Result<NamedValues, InputError> {
        match bytes {
            Some(bytes) => self.decode(group, bytes, resolver),
            None if group.is_empty() => Ok(NamedValues::new()),
            None => Err(InputError::at("entry-input-missing", group.name())),
        }
    }
    pub fn decode(
        &mut self,
        group: &InputGroup<'_>,
        bytes: &[u8],
        mut resolver: Option<&mut dyn Resolver>,
    ) -> Result<NamedValues, InputError> {
        let value = self
            .document
            .read(bytes)
            .map_err(|e| InputError::at(e, group.name))?;
        let Json::Object(mut values) = value else {
            return Err(InputError::at("entry-input-shape", group.name));
        };
        let mut result = NamedValues::new();
        for port in &group.ports {
            let path = format!("{}.{}", group.name, port.name);
            let value = values
                .remove(port.name)
                .ok_or_else(|| InputError::at("entry-input-names", &path))?;
            let decoded = if port.key == Some("prover_key") {
                let (file, pin) =
                    reference(&value, "fingerprint").map_err(|e| InputError::at(e, &path))?;
                let file = self
                    .reference(&file, &mut resolver)
                    .map_err(|e| InputError::at(e, &path))?;
                InputValue::ProverKeyInput {
                    file,
                    fingerprint: pin,
                }
                .into()
            } else {
                group
                    .interface
                    .check_native_input(port.schema)
                    .map_err(|e| InputError::at(e, &path))?;
                self.value(group.interface, port.schema, value, &path, &mut resolver)?
            };
            result.insert(port.name.to_owned(), decoded);
        }
        if let Some(name) = values.keys().next() {
            return Err(InputError::at(
                "entry-input-names",
                &format!("{}.{name}", group.name),
            ));
        }
        Ok(result)
    }
    fn reference(
        &mut self,
        path: &str,
        resolver: &mut Option<&mut dyn Resolver>,
    ) -> Result<InputSource, String> {
        self.references += 1;
        if self.references > 1024 {
            return Err("entry-input-reference-limit".into());
        }
        resolver
            .as_deref_mut()
            .ok_or("entry-input-reference")?
            .resolve(path)
    }
    fn value(
        &mut self,
        interface: InputInterface<'_>,
        schema: &Schema,
        value: Json,
        path: &str,
        resolver: &mut Option<&mut dyn Resolver>,
    ) -> Result<Value, InputError> {
        let error = |code| InputError::at(code, path);
        Ok(match (schema.kind, value) {
            (Kind::Unit, Json::Null) => Value::Unit,
            (Kind::Tuple | Kind::Array, Json::Array(values)) => {
                if values.len() != schema.fields.len() {
                    return Err(error("entry-input-shape".into()));
                }
                let values = schema
                    .fields
                    .iter()
                    .zip(values)
                    .enumerate()
                    .map(|(i, (f, v))| {
                        self.value(interface, &f.schema, v, &format!("{path}[{i}]"), resolver)
                    })
                    .collect::<Result<_, _>>()?;
                if schema.kind == Kind::Tuple {
                    Value::Tuple(values)
                } else {
                    Value::Array(values)
                }
            }
            (Kind::Record, Json::Object(values)) => {
                Value::Record(self.fields(interface, &schema.fields, values, path, resolver)?)
            }
            (_, Json::Null) => return Err(error("entry-input-unfilled".into())),
            (Kind::Variant, Json::Object(mut v)) => {
                let alternative = v
                    .remove("case")
                    .and_then(|v| v.as_str().map(str::to_owned))
                    .ok_or_else(|| error("entry-input-alternative".into()))?;
                let Some(Json::Object(fields)) = v.remove("fields") else {
                    return Err(error("entry-input-fields".into()));
                };
                if !v.is_empty() {
                    return Err(error("entry-input-fields".into()));
                }
                let arm = schema
                    .alternatives
                    .iter()
                    .find(|a| a.name == alternative)
                    .ok_or_else(|| error("entry-input-alternative".into()))?;
                Value::Variant {
                    alternative,
                    fields: self.fields(interface, &arm.fields, fields, path, resolver)?,
                }
            }
            (Kind::Boolean | Kind::Index | Kind::Field | Kind::Group | Kind::Builtin, v) => {
                if v.get("file").is_some() {
                    let (file, pin) = reference(&v, "sha256").map_err(error)?;
                    InputValue::WireSource {
                        file: self.reference(&file, resolver).map_err(error)?,
                        sha256: pin,
                    }
                    .into()
                } else {
                    let logical = zkc_runtime::vm::LogicalType::parse(&schema.leaves[0])
                        .map_err(|_| error("entry-input-codec".into()))?;
                    let ty = PhysicalType::default_for(logical.clone())
                        .map_err(|_| error("entry-input-codec".into()))?;
                    if !self.installation.supports_wire(&ty) {
                        return Err(error("entry-input-codec".into()));
                    }
                    let remaining = self
                        .capacity
                        .values
                        .total_bytes
                        .saturating_sub(self.inline_bytes);
                    let bytes =
                        zkc_cpu::readable_wire(&ty, &v, remaining.min(self.capacity.wire_bytes))
                            .map_err(|e| error(e.into()))?;
                    self.inline_bytes += bytes.len();
                    InputValue::Wire(bytes.into()).into()
                }
            }
            _ => return Err(error("entry-input-shape".into())),
        })
    }
    fn fields(
        &mut self,
        interface: InputInterface<'_>,
        fields: &[Field],
        mut values: serde_json::Map<String, Json>,
        path: &str,
        resolver: &mut Option<&mut dyn Resolver>,
    ) -> Result<BTreeMap<String, Value>, InputError> {
        let mut result = BTreeMap::new();
        for field in fields {
            let path = format!("{path}.{}", field.name);
            let value = values
                .remove(&field.name)
                .ok_or_else(|| InputError::at("entry-input-fields", &path))?;
            result.insert(
                field.name.clone(),
                self.value(interface, &field.schema, value, &path, resolver)?,
            );
        }
        if let Some(name) = values.keys().next() {
            return Err(InputError::at(
                "entry-input-fields",
                &format!("{path}.{name}"),
            ));
        }
        Ok(result)
    }
}
fn reference(value: &Json, pin: &str) -> Result<(String, [u8; 32]), String> {
    if value.is_null()
        || value.get("file").is_some_and(Json::is_null)
        || value.get(pin).is_some_and(Json::is_null)
    {
        return Err("entry-input-unfilled".into());
    }
    let object = value.as_object().ok_or("entry-input-reference")?;
    if object.len() != 2 {
        return Err("entry-input-reference".into());
    }
    let file = object
        .get("file")
        .and_then(Json::as_str)
        .ok_or("entry-input-reference")?;
    let hash = object
        .get(pin)
        .and_then(Json::as_str)
        .ok_or("entry-input-reference")?;
    Ok((
        file.into(),
        digest(hash).map_err(|_| "entry-input-reference")?,
    ))
}
