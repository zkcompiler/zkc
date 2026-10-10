//! Checked metadata for an authenticated source package. Reading this interface
//! checks structure and internal consistency, not MLIR meaning or native code.
mod binding;
mod ports;
pub(in crate::entry) use ports::{InputPort, RolePorts};
mod preflight;
pub(in crate::entry) mod raw;
mod schemas;
mod setups;
pub(in crate::entry) use setups::Setup;
mod validate;
use super::Package;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use zkc_runtime::interactive::LogicalType;

type Result<T> = std::result::Result<T, InterfaceError>;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterfaceError {
    Format,
    Limit,
    Identity,
    Schema,
    Selection,
    NativeBinding,
}
impl std::fmt::Display for InterfaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Format => "entry-interface-format",
            Self::Limit => "entry-interface-limit",
            Self::Identity => "entry-interface-identity",
            Self::Schema => "entry-interface-schema",
            Self::Selection => "entry-interface-selection",
            Self::NativeBinding => "entry-interface-native-binding",
        })
    }
}
impl std::error::Error for InterfaceError {}

/// Immutable source metadata. Execution must separately bind this view to the
/// admitted native artifact from the same authenticated package.
#[derive(Debug)]
pub struct Interface {
    pub(in crate::entry) document: raw::Interface,
    pub(in crate::entry) selected: usize,
    types: BTreeMap<String, LogicalType>,
    ports: ports::Ports,
    pub(in crate::entry) setups: Vec<Setup>,
}
/// Package provenance plus its checked logical view. Only this type can bind a
/// native deployment. A source inspection cannot construct it.
#[derive(Debug)]
pub struct BoundInterface {
    view: Interface,
    artifact: String,
    options: super::CompileOptions,
}
impl std::ops::Deref for BoundInterface {
    type Target = Interface;
    fn deref(&self) -> &Interface {
        &self.view
    }
}
impl BoundInterface {
    pub fn read(package: &Package) -> Result<Self> {
        let original = format!("{:x}", Sha256::digest(package.original().as_bytes()));
        let view = Interface::decode(package.interface().as_bytes(), Some(&original))?;
        Ok(Self {
            view,
            artifact: crate::host::inputs::hex(package.authenticated_artifact().identity()),
            options: package.options(),
        })
    }
    pub fn into_view(self) -> Interface {
        self.view
    }
}
impl Interface {
    pub(crate) fn from_compiler(bytes: &[u8]) -> Result<Self> {
        Self::decode(bytes, None)
    }
    fn decode(bytes: &[u8], original: Option<&str>) -> Result<Self> {
        preflight::check(bytes)?;
        let mut decoder = serde_json::Deserializer::from_slice(bytes);
        decoder.disable_recursion_limit();
        let document: raw::Interface =
            serde::Deserialize::deserialize(&mut decoder).map_err(|_| InterfaceError::Format)?;
        decoder.end().map_err(|_| InterfaceError::Format)?;
        require(hash(&document.original), InterfaceError::Identity)?;
        let checked = validate::check(&document, original.unwrap_or(&document.original))?;
        let ports =
            ports::Ports::new(&document, checked.selected, &checked.types, &checked.setups)?;
        Ok(Self {
            ports,
            document,
            selected: checked.selected,
            types: checked.types,
            setups: checked.setups,
        })
    }
    /// Describe checked source ports and invocation responsibilities without
    /// admitting native programs or executing any protocol operation.
    pub fn describe(&self) -> serde_json::Value {
        use serde_json::json;
        let port = |p: &raw::Port| json!({"name":p.name, "type":p.display_type, "roles":p.roles});
        let protocol = self.selected_protocol();
        let selection = |s: &raw::Selector| {
            json!({"port":protocol.outputs[s.port as usize].name,
                   "path":s.path, "role":s.role})
        };
        let proof = match &self.document.job {
            raw::Job::Run {} => None,
            raw::Job::Proof {
                prover,
                verifier,
                acceptance,
                completion,
                ..
            } => Some(json!({
                "prover":prover, "verifier":verifier,
                "public":self.public_ports().map(|p| port(p.definition)).collect::<Vec<_>>(),
                "acceptance":selection(acceptance),
                "completion":completion.as_deref().map(selection),
                "transcript_suite":self.proof().and_then(|p| p.suite.as_deref()),
            })),
        };
        json!({"entry":self.entry(), "protocol":self.protocol(),
            "kind":if self.is_proof() {"proof"} else {"run"}, "toolchain":self.toolchain(),
            "roles":self.roles().iter().map(|role| json!({"name":role.name,
                "inputs":self.named_inputs(role).map(|p| port(p.definition)).collect::<Vec<_>>(),
                "outputs":self.output_ports(role).map(port).collect::<Vec<_>>(),
                "services":self.services(role).map(|s| json!({"name":s.name,"contract":s.contract})).collect::<Vec<_>>()
            })).collect::<Vec<_>>(),
            "setups":self.setup_names().collect::<Vec<_>>(), "proof":proof,
            "input_groups":self.input_groups().iter().map(|g|g.describe()).collect::<Vec<_>>()})
    }
    pub fn entry(&self) -> &str {
        &self.document.entry
    }
    pub(in crate::entry) fn selected_protocol(&self) -> &raw::Protocol {
        &self.document.protocols[self.selected]
    }
    pub fn protocol(&self) -> &str {
        &self.document.protocols[self.selected].symbol
    }
    pub fn capture(&self) -> &str {
        &self.document.capture
    }
    pub fn original(&self) -> &str {
        &self.document.original
    }
    pub fn toolchain(&self) -> &str {
        &self.document.toolchain
    }
    /// Setup names required by the application's independent authority and each invocation.
    pub fn setup_names(&self) -> impl ExactSizeIterator<Item = &str> {
        self.setups.iter().map(|slot| slot.name.as_str())
    }
    pub fn is_proof(&self) -> bool {
        self.proof().is_some()
    }
    /// Types are admitted once per canonical spelling and shared within the view.
    pub fn logical_type(&self, spelling: &str) -> Option<&LogicalType> {
        self.types.get(spelling)
    }
}

fn require(condition: bool, error: InterfaceError) -> Result<()> {
    if condition { Ok(()) } else { Err(error) }
}
fn identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value.as_bytes()[0].is_ascii_alphabetic() || value.starts_with('_'))
        && value
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_')
}
fn hash(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
fn text(value: &str, limit: usize) -> Result<()> {
    require(!value.is_empty(), InterfaceError::Format)?;
    require(value.len() <= limit, InterfaceError::Limit)
}

#[cfg(test)]
mod tests;
