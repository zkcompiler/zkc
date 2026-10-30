//! Checked source function metadata, independent of target installation.
mod admission;
mod carrier;
#[cfg(feature = "cpu")]
pub(crate) mod cpu;
mod deployment;
mod schema;
pub use super::interface::raw::{Alternative, Field, Kind as SchemaKind, Permission, Schema};
use super::{EntryError, EntryPhase, Package};
pub use schema::{DeploymentInterface, FunctionInterface};
use serde::Deserialize;
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, EntryError>;
fn error(code: &str) -> EntryError {
    EntryError::new(EntryPhase::Admission, code)
}
fn require(ok: bool, code: &str) -> Result<()> {
    if ok { Ok(()) } else { Err(error(code)) }
}
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub struct FunctionParameter {
    pub name: String,
    pub schema: Schema,
}
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub struct FunctionSignature {
    pub symbol: String,
    pub parameters: Vec<FunctionParameter>,
    pub result: Schema,
}
crate::entry::decode::objects!(FunctionParameter, FunctionSignature);

#[cfg(test)]
mod tests;
