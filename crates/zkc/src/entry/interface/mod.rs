//! Checked metadata for an authenticated source package. Reading this interface
//! checks structure and internal consistency, not MLIR meaning or native code.
#[cfg(feature = "cpu")]
mod binding;
mod boundary;
mod common;
mod origin;
mod placement;
mod ports;
mod selection;
pub use boundary::{BoundaryRequirement, SelectionPurpose};
pub use raw::{
    Component as PortComponent, Facet as ComponentFacet, Placement as ValuePlacement,
    PublicSelection as PublicInputSelection,
};
pub use selection::{OrdinaryInput, ProtocolPort};
pub(in crate::entry) mod syntax;
pub(in crate::entry) use ports::InputPort;
#[cfg(feature = "cpu")]
pub(in crate::entry) use ports::RolePorts;
pub(in crate::entry) mod preflight;
pub(in crate::entry) mod raw;
pub(in crate::entry) mod schemas;
mod setups;
pub(in crate::entry) use setups::Setup;
mod validate;
use super::Package;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use syntax::Leaf;

type Result<T> = std::result::Result<T, InterfaceError>;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterfaceError {
    Format,
    /// A ceiling of the interface document itself: its bytes, nesting, nodes,
    /// name lengths, counts or schema shapes. No allowance selection raises it.
    Limit,
    /// The Host's selected interface work allowance: exhausted while reading,
    /// or a selection above its installed maximum.
    WorkLimit,
    /// The Host's selected interface descriptor allowance: exhausted while
    /// reading, or a selection above its installed maximum.
    DescriptorLimit,
    Identity,
    Schema,
    Selection,
    NativeBinding,
}
impl std::fmt::Display for InterfaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Format => super::EntryCondition::InterfaceFormat.code(),
            Self::Limit => "entry-interface-limit",
            Self::WorkLimit => "entry-interface-work-limit",
            Self::DescriptorLimit => "entry-interface-descriptor-bytes-limit",
            Self::Identity => super::EntryCondition::InterfaceIdentity.code(),
            Self::Schema => "entry-interface-schema",
            Self::Selection => "entry-interface-selection",
            Self::NativeBinding => "entry-interface-native-binding",
        })
    }
}
impl std::error::Error for InterfaceError {}

/// Host policy for interface admission. Schema validation and supply
/// reconstruction each have their own cumulative work allowance; the schema
/// summaries and each reconstructed input or output supply plan each charge
/// their retained descriptors against the descriptor allowance. A Host may
/// lower either allowance or raise the work allowance up to `MAXIMUM`; a
/// selection above `MAXIMUM` refuses without clamping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InterfaceLimits {
    /// Work units of one admission algorithm.
    pub work: usize,
    /// Retained descriptor bytes of one summary or supply plan.
    pub descriptor_bytes: usize,
}
impl InterfaceLimits {
    pub const DEFAULT: Self = Self {
        work: 1_000_000,
        descriptor_bytes: 16 * 1024 * 1024,
    };
    /// The most a Host may select. A Function Host's structure validation
    /// checks each schema at every signature, block argument and deployment
    /// that restates it, so the generated Host of a trivial 1,024-role
    /// Protocol needs about 1.3 million work units in that one algorithm with
    /// one port, and 1.7 million with one port placed at every role. The work
    /// maximum, 2^24, is about ten times the larger; the descriptor allowance
    /// can only be lowered.
    pub const MAXIMUM: Self = Self {
        work: 1 << 24,
        ..Self::DEFAULT
    };
    /// Refuse a selection above an installed maximum with that allowance's
    /// code, without clamping it.
    pub fn validate(&self) -> Result<()> {
        require(self.work <= Self::MAXIMUM.work, InterfaceError::WorkLimit)?;
        require(
            self.descriptor_bytes <= Self::MAXIMUM.descriptor_bytes,
            InterfaceError::DescriptorLimit,
        )
    }
}
impl Default for InterfaceLimits {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Immutable source metadata. Execution must separately bind this view to the
/// admitted native artifact from the same authenticated package.
#[derive(Debug)]
pub struct Interface {
    pub(in crate::entry) document: raw::Interface,
    pub(in crate::entry) selected: usize,
    pub(in crate::entry) types: BTreeMap<String, Leaf>,
    ports: ports::Ports,
    #[cfg_attr(not(feature = "cpu"), allow(dead_code))]
    common: Vec<common::Requirement>,
    pub(in crate::entry) setups: Vec<Setup>,
}
/// Package provenance plus its checked logical view. Only this type can bind a
/// native deployment. A source inspection cannot construct it.
#[derive(Debug)]
pub struct BoundInterface {
    view: Interface,
    #[cfg(feature = "cpu")]
    artifact: String,
    #[cfg(feature = "cpu")]
    options: super::CompileOptions,
}
impl std::ops::Deref for BoundInterface {
    type Target = Interface;
    fn deref(&self) -> &Interface {
        &self.view
    }
}
impl BoundInterface {
    /// Read under the Host's selected interface admission allowances; a caller
    /// that selects nothing passes `InterfaceLimits::DEFAULT`.
    pub fn read(package: &Package, limits: InterfaceLimits) -> Result<Self> {
        let original = crate::io::bytes::hex(&Sha256::digest(package.original().as_bytes()));
        let view = Interface::decode(package.interface().as_bytes(), Some(&original), limits)?;
        Ok(Self {
            view,
            #[cfg(feature = "cpu")]
            artifact: crate::io::bytes::hex(package.authenticated_artifact().identity()),
            #[cfg(feature = "cpu")]
            options: package.options(),
        })
    }
    pub fn into_view(self) -> Interface {
        self.view
    }
}
impl Interface {
    #[cfg(any(feature = "cpu", test))]
    pub(in crate::entry) fn check_executable_ports(&self) -> Result<()> {
        self.check_executable_role(None)
    }
    pub(in crate::entry) fn check_executable_role(&self, role: Option<&str>) -> Result<()> {
        require(
            !self
                .ports
                .residual
                .iter()
                .any(|r| role.is_none_or(|role| r.role == role)),
            InterfaceError::NativeBinding,
        )
    }
    /// Exact source public selections, including initialized keys and empty data.
    pub fn public_selections(&self) -> &[PublicInputSelection] {
        match &self.document.job {
            raw::Job::Proof { public, .. } => public,
            _ => &[],
        }
    }
    pub fn outstanding_requirements(&self) -> &[BoundaryRequirement] {
        &self.ports.residual
    }
    /// Read compiler output before packaging, under the selected allowances.
    #[cfg(feature = "project")]
    pub(crate) fn from_compiler(bytes: &[u8], limits: InterfaceLimits) -> Result<Self> {
        Self::decode(bytes, None, limits)
    }
    /// A selection above an installed maximum refuses before any byte is read.
    fn decode(bytes: &[u8], original: Option<&str>, limits: InterfaceLimits) -> Result<Self> {
        limits.validate()?;
        preflight::check(bytes)?;
        let mut decoder = serde_json::Deserializer::from_slice(bytes);
        decoder.disable_recursion_limit();
        let document: raw::Interface =
            serde::Deserialize::deserialize(&mut decoder).map_err(|_| InterfaceError::Format)?;
        decoder.end().map_err(|_| InterfaceError::Format)?;
        require(hash(&document.original), InterfaceError::Identity)?;
        let checked = validate::check(&document, original.unwrap_or(&document.original), limits)?;
        let ports = ports::Ports::new(
            &document,
            checked.selected,
            &checked.types,
            &checked.setups,
            limits,
        )?;
        Ok(Self {
            ports,
            common: checked.common,
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
        let port = |p: &raw::Port| json!({"name":p.name, "type":p.display_type, "placement":p.placement.describe()});
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
                gates,
                ..
            } => Some(json!({
                "prover":prover, "verifier":verifier,
                "public":self.public_ports().map(|p| port(p.definition)).collect::<Vec<_>>(),
                "acceptance":selection(acceptance),
                "completion":completion.as_deref().map(selection),
                "transcript_suite":self.proof().and_then(|p| p.suite.as_deref()),
                "proof_format":self.proof().map(|p| p.format.name()),
                "gates":gates.iter().map(|g| json!({"path":g.path,"bits":g.bits})).collect::<Vec<_>>(),
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
            "outstanding_requirements":self.outstanding_requirements().iter().map(|r| json!({"port":r.port,"path":r.path,"role":r.role,"direction":if r.output {"output"} else {"input"},"facet":r.facet.map(|f|format!("{f:?}")),"reason":r.reason})).collect::<Vec<_>>(),
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
}

fn require(condition: bool, error: InterfaceError) -> Result<()> {
    if condition { Ok(()) } else { Err(error) }
}
fn identifier(value: &str) -> bool {
    value.len() <= 128 && crate::source_names::is_source_identifier(value)
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
pub(in crate::entry) mod tests;
