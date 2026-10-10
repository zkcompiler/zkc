//! Borrowed input groups and schema-directed readable values. Schema authority
//! remains in Interface; decoders neither run protocols nor discover files.
use super::{
    Interface, NamedValues, Value,
    interface::{
        InputPort,
        raw::{Field, Kind, Schema},
    },
};
use crate::{
    execution::{Capacity, InputFile, InputValue},
    host::{document, inputs::digest},
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use zkc_runtime::interactive::{PhysicalType, Type};

pub struct InputGroup<'a> {
    pub(super) interface: &'a Interface,
    name: &'a str,
    pub(super) ports: Vec<InputPort<'a>>,
}
impl InputGroup<'_> {
    pub fn name(&self) -> &str {
        self.name
    }
    pub fn is_empty(&self) -> bool {
        self.ports.is_empty()
    }
    /// Null leaves are unfilled placeholders. Empty products retain their sole value.
    pub fn template(&self) -> Json {
        Json::Object(
            self.ports
                .iter()
                .map(|p| {
                    (
                        p.name.clone(),
                        if p.key == Some(Type::ProverKey) {
                            json!({"file":null,"fingerprint":null})
                        } else {
                            template(&p.schema)
                        },
                    )
                })
                .collect(),
        )
    }
    pub fn describe(&self) -> Json {
        let ports = self
            .ports
            .iter()
            .map(|port| {
                json!({
                    "name": port.name,
                    "schema": describe(&port.schema),
                    "initializer": (port.key == Some(Type::ProverKey)).then_some("prover_key"),
                    "constructible": port.key == Some(Type::ProverKey) ||
                        super::value::check_import(&port.schema).is_ok() &&
                        port.schema.leaves.iter().all(|name| {
                            self.interface.logical_type(name)
                                .and_then(|logical| PhysicalType::default_for(logical.clone()).ok())
                                .is_some_and(|ty| zkc_backends::has_native_wire(&ty))
                        }),
                })
            })
            .collect::<Vec<_>>();
        json!({"name": self.name, "required": !self.is_empty(), "ports": ports})
    }
}
impl Interface {
    /// Proofs expose public data once and the prover's remaining witness inputs.
    /// Run groups are role-local even when the source port names several roles.
    pub fn input_groups<'a>(&'a self) -> Vec<InputGroup<'a>> {
        let group = |name: &'a str, ports: Vec<InputPort<'a>>| InputGroup {
            interface: self,
            name,
            ports: ports
                .into_iter()
                .filter(|p| p.key != Some(Type::VerifierKey))
                .collect(),
        };
        if let Some(proof) = self.proof() {
            vec![
                group("public", self.public_ports().collect()),
                group(
                    "witness",
                    self.named_inputs(&self.roles()[proof.prover]).collect(),
                ),
            ]
        } else {
            self.roles()
                .iter()
                .map(|role| group(role.name.as_str(), self.named_inputs(role).collect()))
                .collect()
        }
    }
}
fn template(schema: &Schema) -> Json {
    match schema.kind {
        Kind::Tuple | Kind::Array => {
            Json::Array(schema.fields.iter().map(|f| template(&f.schema)).collect())
        }
        Kind::Record => Json::Object(
            schema
                .fields
                .iter()
                .map(|f| (f.name.clone(), template(&f.schema)))
                .collect(),
        ),
        Kind::Associated => template(&schema.fields[0].schema),
        _ => Json::Null,
    }
}
fn describe(schema: &Schema) -> Json {
    let kind = match schema.kind {
        Kind::Unit => "unit",
        Kind::Boolean => "bool",
        Kind::Index => "index",
        Kind::Field => "field",
        Kind::Group => "group",
        Kind::Tuple => "tuple",
        Kind::Array => "array",
        Kind::Record => "record",
        Kind::Associated => "associated",
        Kind::Variant => "variant",
        Kind::Builtin => "native",
    };
    let mut result = json!({"kind":kind,"type":schema.display_type});
    if !schema.leaves.is_empty() {
        result["native_types"] = json!(schema.leaves);
    }
    if matches!(
        schema.kind,
        Kind::Tuple | Kind::Array | Kind::Record | Kind::Associated
    ) {
        result["fields"] = json!(
            schema
                .fields
                .iter()
                .map(|f| json!({"name":f.name,"schema":describe(&f.schema)}))
                .collect::<Vec<_>>()
        );
    }
    if schema.kind == Kind::Variant {
        let cases = schema
            .alternatives
            .iter()
            .map(|case| {
                let fields = case
                    .fields
                    .iter()
                    .map(|field| json!({"name": field.name, "schema": describe(&field.schema)}))
                    .collect::<Vec<_>>();
                json!({"name": case.name, "fields": fields})
            })
            .collect::<Vec<_>>();
        result["cases"] = json!(cases);
    }
    result
}
/// File resolution is opt-in. Implementations return opened regular descriptors;
/// reads and cryptographic import still occur in common Host preparation.
pub trait Resolver {
    fn resolve(&mut self, relative: &str) -> Result<InputFile, String>;
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
    document: document::Budget,
    capacity: Capacity,
    inline_bytes: usize,
    references: usize,
}
impl Decoder {
    pub fn new(capacity: Capacity) -> Result<Self, String> {
        capacity.validate()?;
        Ok(Self {
            document: document::Budget::new(super::files::MAX_REQUEST_BYTES),
            capacity,
            inline_bytes: 0,
            references: 0,
        })
    }
    pub fn remaining_document_bytes(&self) -> usize {
        self.document.remaining_bytes()
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
                .remove(&port.name)
                .ok_or_else(|| InputError::at("entry-input-names", &path))?;
            let decoded = if port.key == Some(Type::ProverKey) {
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
                super::value::check_import(&port.schema).map_err(|e| InputError::at(e, &path))?;
                self.value(group.interface, &port.schema, value, &path, &mut resolver)?
            };
            result.insert(port.name.clone(), decoded);
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
    ) -> Result<InputFile, String> {
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
        interface: &Interface,
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
            (Kind::Associated, value) => Value::Associated(Box::new(self.value(
                interface,
                &schema.fields[0].schema,
                value,
                path,
                resolver,
            )?)),
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
                    InputValue::WireFile {
                        file: self.reference(&file, resolver).map_err(error)?,
                        sha256: pin,
                    }
                    .into()
                } else {
                    let logical = interface
                        .logical_type(&schema.leaves[0])
                        .expect("checked scalar schema");
                    let ty = PhysicalType::default_for(logical.clone())
                        .map_err(|_| error("entry-input-codec".into()))?;
                    let remaining = self
                        .capacity
                        .values
                        .total_bytes
                        .saturating_sub(self.inline_bytes);
                    let bytes = zkc_backends::readable_wire(
                        &ty,
                        &v,
                        remaining.min(self.capacity.wire_bytes),
                    )
                    .map_err(|e| error(e.into()))?;
                    self.inline_bytes += bytes.len();
                    InputValue::Wire(bytes).into()
                }
            }
            _ => return Err(error("entry-input-shape".into())),
        })
    }
    fn fields(
        &mut self,
        interface: &Interface,
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
