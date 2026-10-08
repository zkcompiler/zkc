//! Strict decoded carrier records. Only an authenticated package and validated
//! Interface may supply their constructor permissions to an execution adapter.
use serde::{Deserialize, Deserializer};

// A nullable field is required in the carrier. serde's ordinary Option default
// would also accept an omitted field, unlike the compiler's exact object schema.
fn present_optional<'de, D, T>(decoder: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(decoder)
}

#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Interface {
    pub format: String,
    pub capture: String,
    pub original: String,
    pub toolchain: String,
    pub entry: String,
    pub protocol: String,
    pub protocols: Vec<Protocol>,
    pub relations: Vec<Relation>,
    pub job: Job,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(in crate::entry) enum Job {
    Run {},
    Proof {
        prover: String,
        verifier: String,
        public: Vec<u32>,
        acceptance: Selector,
        #[serde(deserialize_with = "present_optional")]
        target: Option<String>,
        construction: Construction,
    },
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(in crate::entry) enum Construction {
    Authored {},
    FiatShamir { suite: String, service: u32 },
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Protocol {
    pub symbol: String,
    pub roles: Vec<String>,
    pub inputs: Vec<Port>,
    pub outputs: Vec<Port>,
    pub services: Vec<Service>,
    pub clauses: Vec<Clause>,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Port {
    pub name: String,
    #[serde(rename = "type")]
    pub display_type: String,
    pub roles: Vec<String>,
    pub index: u32,
    pub native: Vec<u32>,
    pub schema: Schema,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Service {
    pub name: String,
    pub contract: String,
    pub owner: String,
    pub native: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self")]
#[serde(rename_all = "lowercase")]
pub(in crate::entry) enum Kind {
    Boolean,
    Index,
    Field,
    Group,
    Unit,
    Tuple,
    Array,
    Record,
    Variant,
    Associated,
    Builtin,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
#[serde(remote = "Self")]
pub(in crate::entry) enum Permission {
    Copy,
    Drop,
    Share,
    Wire,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Schema {
    pub kind: Kind,
    pub identity: String,
    #[serde(rename = "type")]
    pub display_type: String,
    pub custody: bool,
    pub permissions: Vec<Permission>,
    pub fields: Vec<Field>,
    pub alternatives: Vec<Alternative>,
    pub leaves: Vec<String>,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Field {
    pub name: String,
    pub offset: u32,
    pub schema: Schema,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Alternative {
    pub name: String,
    pub fields: Vec<Field>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self")]
#[serde(rename_all = "lowercase")]
pub(in crate::entry) enum Direction {
    Input,
    Output,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Selector {
    pub direction: Direction,
    pub port: u32,
    pub role: String,
    pub path: Vec<u32>,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Application {
    pub relation: String,
    pub operands: Vec<Selector>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self")]
#[serde(rename_all = "lowercase")]
pub(in crate::entry) enum ClauseKind {
    Target,
    Input,
    Output,
    Continuation,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Clause {
    pub name: String,
    pub kind: ClauseKind,
    pub subject: Application,
    #[serde(deserialize_with = "present_optional")]
    pub residual: Option<Application>,
    #[serde(deserialize_with = "present_optional")]
    pub decision: Option<Selector>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self")]
#[serde(rename_all = "lowercase")]
pub(in crate::entry) enum Purpose {
    Parameter,
    Statement,
    Witness,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct Relation {
    pub symbol: String,
    pub inputs: Vec<RelationInput>,
    pub definition: Definition,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(deny_unknown_fields)]
pub(in crate::entry) struct RelationInput {
    pub name: String,
    pub purpose: Purpose,
    pub native: Vec<u32>,
    pub schema: Schema,
}
#[derive(Debug, Deserialize)]
#[serde(remote = "Self")]
#[serde(tag = "kind", rename_all = "lowercase", deny_unknown_fields)]
pub(in crate::entry) enum Definition {
    Formula { function: String },
    Opaque {},
    R1cs { asset: String },
    Air { asset: String },
}

crate::entry::decode::objects!(
    Interface,
    Job,
    Construction,
    Protocol,
    Port,
    Service,
    Schema,
    Field,
    Alternative,
    Selector,
    Application,
    Clause,
    Relation,
    RelationInput,
    Definition
);
crate::entry::decode::names!(Kind, Permission, Direction, ClauseKind, Purpose);
