//! Borrowed input groups and schema-directed readable values. Schema authority
//! remains in Interface; decoders neither run protocols nor discover files.
use super::{
    FunctionInterface, Interface,
    interface::{
        InputPort,
        raw::{Kind, Schema},
    },
};
use serde_json::{Value as Json, json};
pub const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy)]
enum InputInterface<'a> {
    Deployment(&'a Interface),
    Function(&'a FunctionInterface),
}
impl InputInterface<'_> {
    fn check_input(self, schema: &Schema) -> Result<(), String> {
        super::interface::schemas::check_import(schema)?;
        let types = match self {
            Self::Deployment(v) => &v.types,
            Self::Function(v) => &v.types,
        };
        if schema
            .leaves
            .iter()
            .all(|s| types.get(s).is_some_and(|t| t.message))
        {
            Ok(())
        } else {
            Err("entry-input-codec".into())
        }
    }
}
struct InputSchemaPort<'a> {
    name: &'a str,
    schema: &'a Schema,
    key: Option<&'static str>,
}
pub struct InputGroup<'a> {
    interface: InputInterface<'a>,
    name: &'a str,
    ports: Vec<InputSchemaPort<'a>>,
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
                        p.name.to_owned(),
                        if p.key == Some("prover_key") {
                            json!({"file":null,"fingerprint":null})
                        } else {
                            template(p.schema)
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
                    "schema": describe(port.schema),
                    "initializer": (port.key == Some("prover_key")).then_some("prover_key"),
                    "constructible": port.key == Some("prover_key") ||
                        self.interface.check_input(port.schema).is_ok(),
                })
            })
            .collect::<Vec<_>>();
        json!({"name": self.name, "required": !self.is_empty(), "ports": ports})
    }
}
impl Interface {
    /// Context ports are selected by the same checked native owner that binds
    /// generated calls; ordinary source operands are excluded from these maps.
    pub(crate) fn context_input_groups(&self, operation: &str) -> Vec<InputGroup<'_>> {
        self.roles()
            .iter()
            .filter(|role| {
                operation == "run"
                    || self.proof().is_some_and(|proof| {
                        role.native_name
                            == self.roles()[if operation == "prove" {
                                proof.prover
                            } else {
                                proof.verifier
                            }]
                            .native_name
                    })
            })
            .map(|role| InputGroup {
                interface: InputInterface::Deployment(self),
                name: &role.name,
                ports: self
                    .context_ports(role)
                    .map(|p| InputSchemaPort {
                        name: &p.definition.name,
                        schema: &p.definition.schema,
                        key: p.key,
                    })
                    .collect(),
            })
            .collect()
    }
    /// Proofs expose public data once and the prover's remaining witness inputs.
    /// Run groups are role-local even when the source port names several roles.
    pub fn input_groups<'a>(&'a self) -> Vec<InputGroup<'a>> {
        let group = |name: &'a str, ports: Vec<InputPort<'a>>| InputGroup {
            interface: InputInterface::Deployment(self),
            name,
            ports: ports
                .into_iter()
                .filter(|p| p.key != Some("verifier_key"))
                .map(|p| InputSchemaPort {
                    name: &p.definition.name,
                    schema: &p.definition.schema,
                    key: p.key,
                })
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
impl FunctionInterface {
    /// Parameters form one exact named map, independent of child roles.
    pub fn input_group(&self) -> InputGroup<'_> {
        InputGroup {
            interface: InputInterface::Function(self),
            name: "arguments",
            ports: self
                .signature()
                .parameters
                .iter()
                .map(|p| InputSchemaPort {
                    name: &p.name,
                    schema: &p.schema,
                    key: None,
                })
                .collect(),
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

#[cfg(feature = "cpu")]
mod decode;
#[cfg(feature = "cpu")]
pub use decode::{Decoder, InputError, Resolver};
