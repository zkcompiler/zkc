//! Strict file requests adapt named values to the existing in-process Host.
use super::interface::raw::{Field, Job, Kind, Port, Schema};
use super::{Interface, NamedValues, ProofRequest, RoleInputs, RunRequest, SetupAuthority, Value};
use crate::host::{
    inputs::{digest, unhex},
    request::InputValue,
};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use zkc_backends::Value as Native;
use zkc_runtime::interactive::Type;

type Result<T> = std::result::Result<T, String>;
pub const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;

#[derive(Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
struct Role {
    #[serde(deserialize_with = "crate::host::document::values")]
    inputs: BTreeMap<String, Json>,
    #[serde(default)]
    services: BTreeMap<String, u64>,
}
#[derive(Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
struct Run {
    format: String,
    session: String,
    roles: BTreeMap<String, Role>,
    #[serde(default)]
    setups: BTreeMap<String, String>,
}
#[derive(Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
struct Proof {
    format: String,
    #[serde(deserialize_with = "crate::host::document::values")]
    public: BTreeMap<String, Json>,
    #[serde(default, deserialize_with = "crate::host::document::values")]
    inputs: BTreeMap<String, Json>,
    #[serde(default)]
    services: BTreeMap<String, u64>,
    #[serde(default)]
    context: String,
    #[serde(default)]
    transcript_budget: Option<u64>,
    #[serde(default)]
    setups: BTreeMap<String, String>,
}
#[derive(Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
struct Authority {
    format: String,
    keys: BTreeMap<String, String>,
}
super::decode::objects!(Role, Run, Proof, Authority);

fn document<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T> {
    let value = crate::host::document::read(bytes, MAX_REQUEST_BYTES)?;
    serde_json::from_value(value).map_err(|_| "entry-request-format".into())
}
fn material(values: BTreeMap<String, String>) -> Result<BTreeMap<String, Vec<u8>>> {
    values
        .into_iter()
        .map(|(k, v)| Ok((k, unhex(&json!(v))?)))
        .collect()
}
/// Parse independently authorized setup pins; input material confers no authority.
pub fn authority(bytes: &[u8]) -> Result<SetupAuthority> {
    if bytes.len() > 64 * 1024 {
        return Err("entry-request-limit".into());
    }
    let value: Authority = document(bytes)?;
    if value.format != "zkc.entry-setups/1" {
        return Err("entry-request-format".into());
    }
    Ok(SetupAuthority {
        keys: value
            .keys
            .into_iter()
            .map(|(k, v)| Ok((k, digest(&v)?)))
            .collect::<Result<_>>()?,
    })
}
impl Interface {
    /// Decode named JSON without issuing protocol resources or reading key files.
    pub fn run_request(&self, bytes: &[u8]) -> Result<RunRequest> {
        if self.is_proof() {
            return Err("entry-job-kind".into());
        }
        let request: Run = document(bytes)?;
        if request.format != "zkc.entry-run/1" {
            return Err("entry-request-format".into());
        }
        let protocol = self.selected_protocol();
        let mut roles = BTreeMap::new();
        for (name, role) in request.roles {
            if !protocol.roles.contains(&name) {
                return Err("entry-input-roles".into());
            }
            roles.insert(name.clone(), self.role(role, &name)?);
        }
        Ok(RunRequest {
            session: request.session,
            roles,
            setups: material(request.setups)?,
        })
    }
    /// A verification request is decoded against verifier ports only.
    pub fn proof_request(&self, bytes: &[u8], producer: bool) -> Result<ProofRequest> {
        let Job::Proof {
            prover,
            verifier,
            public,
            ..
        } = &self.document.job
        else {
            return Err("entry-job-kind".into());
        };
        let mut request: Proof = document(bytes)?;
        if request.format != "zkc.entry-proof/1" {
            return Err("entry-request-format".into());
        }
        let protocol = self.selected_protocol();
        let role = if producer { prover } else { verifier };
        // The file's public map is this application's authority. Populate shared
        // invocation operands from it; private inputs cannot override those names.
        for index in public {
            let port = &protocol.inputs[*index as usize];
            if port.roles.contains(role) {
                if request.inputs.contains_key(&port.name) {
                    return Err("entry-input-names".into());
                }
                if let Some(value) = request.public.get(&port.name) {
                    request.inputs.insert(port.name.clone(), value.clone());
                }
            }
        }
        Ok(ProofRequest {
            public: self.named(
                public.iter().map(|i| &protocol.inputs[*i as usize]),
                request.public,
            )?,
            inputs: self.role(
                Role {
                    inputs: request.inputs,
                    services: request.services,
                },
                role,
            )?,
            context: unhex(&json!(request.context))?,
            transcript_budget: request.transcript_budget,
            setups: material(request.setups)?,
        })
    }
    fn role(&self, role: Role, name: &str) -> Result<RoleInputs> {
        Ok(RoleInputs {
            inputs: self.named(
                self.selected_protocol()
                    .inputs
                    .iter()
                    .filter(|p| p.roles.iter().any(|r| r == name)),
                role.inputs,
            )?,
            services: role.services,
        })
    }
    fn named<'a>(
        &self,
        ports: impl Iterator<Item = &'a Port>,
        mut values: BTreeMap<String, Json>,
    ) -> Result<NamedValues> {
        let mut result = NamedValues::new();
        for port in ports {
            if super::setups::key_kind(self, port) == Some(Type::VerifierKey) {
                continue;
            }
            let v = values.remove(&port.name).ok_or("entry-input-names")?;
            let value = if super::setups::key_kind(self, port) == Some(Type::ProverKey) {
                #[derive(Deserialize)]
                #[serde(remote = "Self", deny_unknown_fields)]
                struct Key {
                    path: String,
                    sha256: String,
                }
                super::decode::objects!(Key);
                let key: Key = serde_json::from_value(v).map_err(|_| "entry-input-key")?;
                if key.path.is_empty() || key.path.len() > 4096 {
                    return Err("entry-input-key".into());
                }
                InputValue::ProverKeyFile {
                    path: key.path,
                    fingerprint: digest(&key.sha256)?,
                }
                .into()
            } else {
                input(&port.schema, v)?
            };
            result.insert(port.name.clone(), value);
        }
        if !values.is_empty() {
            return Err("entry-input-names".into());
        }
        Ok(result)
    }
}
fn fields(
    schemas: &[Field],
    mut values: serde_json::Map<String, Json>,
) -> Result<BTreeMap<String, Value>> {
    let mut result = BTreeMap::new();
    for field in schemas {
        let v = values.remove(&field.name).ok_or("entry-input-fields")?;
        result.insert(field.name.clone(), input(&field.schema, v)?);
    }
    if !values.is_empty() {
        return Err("entry-input-fields".into());
    }
    Ok(result)
}
fn input(schema: &Schema, value: Json) -> Result<Value> {
    Ok(match (schema.kind, value) {
        (Kind::Unit, Json::Null) => Value::Unit,
        (Kind::Boolean, Json::Bool(v)) => Native::Bool(v).into(),
        (Kind::Index, Json::Number(v)) => {
            Native::Index(v.as_u64().ok_or("entry-input-shape")?).into()
        }
        (Kind::Tuple | Kind::Array, Json::Array(v)) => {
            if v.len() != schema.fields.len() {
                return Err("entry-input-shape".into());
            }
            let values = schema
                .fields
                .iter()
                .zip(v)
                .map(|(f, v)| input(&f.schema, v))
                .collect::<Result<_>>()?;
            if schema.kind == Kind::Tuple {
                Value::Tuple(values)
            } else {
                Value::Array(values)
            }
        }
        (Kind::Record, Json::Object(v)) => Value::Record(fields(&schema.fields, v)?),
        (Kind::Associated, v) => Value::Associated(Box::new(input(&schema.fields[0].schema, v)?)),
        (Kind::Variant, Json::Object(mut v)) => {
            let alternative = v
                .remove("case")
                .and_then(|v| v.as_str().map(str::to_owned))
                .ok_or("entry-input-alternative")?;
            let Json::Object(payload) = v.remove("fields").ok_or("entry-input-fields")? else {
                return Err("entry-input-fields".into());
            };
            if !v.is_empty() {
                return Err("entry-input-fields".into());
            }
            let arm = schema
                .alternatives
                .iter()
                .find(|a| a.name == alternative)
                .ok_or("entry-input-alternative")?;
            Value::Variant {
                alternative,
                fields: fields(&arm.fields, payload)?,
            }
        }
        (Kind::Field | Kind::Group | Kind::Builtin, Json::String(v)) => {
            InputValue::Wire(unhex(&json!(v))?).into()
        }
        _ => return Err("entry-input-shape".into()),
    })
}
mod output;
pub use output::{proof_outputs, run_outputs};

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn literal_object_keys_cannot_impersonate_numbers() {
        let role: Role =
            document(br#"{"inputs":{"x":{"$serde_json::private::Number":"7"}}}"#).unwrap();
        assert!(role.inputs["x"].is_object());
    }
}
