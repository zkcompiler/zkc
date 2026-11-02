use super::{FunctionSignature, Schema};
use serde_json::{Value, json};
impl Schema {
    /// Stable logical input/output plan, including nominal and constructor facts.
    pub fn describe(&self) -> Value {
        let fields = |fs: &[crate::entry::interface::raw::Field]| {
            fs.iter()
                .map(|f| json!({"name":f.name,"offset":f.offset,"public":f.public,
                    "placement":f.placement.as_ref().map(|p|p.describe()),"schema":f.schema.describe()}))
                .collect::<Vec<_>>()
        };
        json!({"kind":format!("{:?}",self.kind).to_lowercase(),"identity":self.identity,
            "type":self.display_type,"generated":self.generated,"custody":self.custody,"sealed":self.sealed,"roles":self.roles,
            "element":self.element.as_ref().map(|e| e.describe()),"constructible":self.constructible,
            "permissions":self.permissions.iter().map(|p|format!("{p:?}")).collect::<Vec<_>>(),
            "fields":fields(&self.fields),"alternatives":self.alternatives.iter().map(|a|
                json!({"name":a.name,"fields":fields(&a.fields)})).collect::<Vec<_>>(),"leaves":self.leaves})
    }
}
impl FunctionSignature {
    pub fn describe(&self) -> Value {
        json!({"symbol":self.symbol,"parameters":self.parameters.iter().map(|p|
            json!({"name":p.name,"schema":p.schema.describe()})).collect::<Vec<_>>(),"result":self.result.describe()})
    }
}

/// Logical metadata can be inspected without admitting executable programs.
/// Only FunctionEntry binds it to the authenticated artifact.
#[derive(Debug)]
pub struct FunctionInterface {
    pub(super) document: super::carrier::Interface,
    pub(in crate::entry) types:
        std::collections::BTreeMap<String, crate::entry::interface::syntax::Leaf>,
}
impl FunctionInterface {
    /// Static context requirements. This does not import keys or grant authority.
    pub fn deployment_interfaces(
        package: &crate::entry::Package,
    ) -> super::Result<Vec<DeploymentInterface>> {
        Self::deployment_interfaces_with(package, crate::entry::InterfaceLimits::DEFAULT)
    }
    /// Static context requirements under the Host's selected interface
    /// admission allowances, the selection its `FunctionEntry` admits with
    /// (`FunctionOptions::limits.interface`).
    pub fn deployment_interfaces_with(
        package: &crate::entry::Package,
        limits: crate::entry::InterfaceLimits,
    ) -> super::Result<Vec<DeploymentInterface>> {
        super::admission::interfaces(package, limits)
    }
    /// The authenticated package of one static Run deployment, for producing
    /// its common-input context. This imports no setup authority.
    pub fn run_deployment_package(
        package: &crate::entry::Package,
        id: &str,
    ) -> super::Result<crate::entry::Package> {
        Self::run_deployment_package_with(package, id, crate::entry::InterfaceLimits::DEFAULT)
    }
    /// One Run deployment's package under the Host's selected interface
    /// admission allowances, the selection that admits the child.
    pub fn run_deployment_package_with(
        package: &crate::entry::Package,
        id: &str,
        limits: crate::entry::InterfaceLimits,
    ) -> super::Result<crate::entry::Package> {
        super::admission::run_deployment(package, id, limits)
    }
    pub fn read(package: &crate::entry::Package) -> super::Result<Self> {
        Self::read_with(package, crate::entry::InterfaceLimits::DEFAULT)
    }
    /// Read under the Host's selected interface admission allowances.
    pub fn read_with(
        package: &crate::entry::Package,
        limits: crate::entry::InterfaceLimits,
    ) -> super::Result<Self> {
        use sha2::{Digest, Sha256};
        limits
            .validate()
            .map_err(|e| super::EntryError::new(super::EntryPhase::Admission, e))?;
        let original = crate::io::bytes::hex(&Sha256::digest(package.original().as_bytes()));
        let view = Self::decode(package.interface().as_bytes(), limits)?;
        if view.document.original != original {
            return Err(crate::entry::EntryCondition::InterfaceIdentity.into());
        }
        Ok(view)
    }
    pub(crate) fn from_compiler(bytes: &[u8]) -> super::Result<Self> {
        Self::decode(bytes, crate::entry::InterfaceLimits::DEFAULT)
    }
    fn decode(bytes: &[u8], limits: crate::entry::InterfaceLimits) -> super::Result<Self> {
        crate::entry::interface::preflight::check(bytes)
            .map_err(|e| super::EntryError::new(super::EntryPhase::Interface, e))?;
        use crate::entry::EntryCondition as C;
        let document: super::carrier::Interface =
            super::admission::decode(bytes, crate::entry::package::INTERFACE_BYTES)
                .map_err(|_| C::InterfaceFormat)?;
        if document.format != "zkc.language-interface/0" {
            return Err(C::InterfaceFormat.into());
        }
        super::require(
            document.selection.kind == "function",
            "entry-host-selection",
        )?;
        super::require(
            document.protocols.is_empty()
                && document.relations.is_empty()
                && document.setups.is_empty(),
            "entry-host-stage",
        )?;
        if crate::io::bytes::digest(&document.capture).is_err()
            || document.toolchain.is_empty()
            || document.toolchain.len() > 256 * 1024
            || !crate::source_names::canonical_name(&document.entry)
        {
            return Err(C::InterfaceIdentity.into());
        }
        let mut schemas = crate::entry::interface::schemas::Schemas::with_limits(limits);
        let mut symbols = std::collections::BTreeSet::new();
        for f in &document.functions {
            super::require(
                !f.symbol.is_empty() && symbols.insert(&f.symbol),
                "entry-host-duplicate",
            )?;
            let mut names = std::collections::BTreeSet::new();
            for p in &f.parameters {
                super::require(
                    p.name.len() <= 128
                        && crate::source_names::is_source_identifier(&p.name)
                        && names.insert(&p.name),
                    "entry-host-parameter",
                )?;
                schemas
                    .check(&p.schema, 0)
                    .map_err(|e| super::EntryError::new(super::EntryPhase::Interface, e))?;
                super::require(!p.schema.is_logical(), "entry-host-schema")?;
            }
            schemas
                .check(&f.result, 0)
                .map_err(|e| super::EntryError::new(super::EntryPhase::Interface, e))?;
            super::require(!f.result.is_logical(), "entry-host-schema")?;
        }
        super::require(
            document.functions.len() <= 4096 && symbols.contains(&document.selection.function),
            "entry-host-selection",
        )?;
        crate::io::bytes::digest(&document.original).map_err(|_| C::InterfaceIdentity)?;
        let types = schemas.finish();
        Ok(Self { document, types })
    }
    pub fn signature(&self) -> &FunctionSignature {
        self.document
            .functions
            .iter()
            .find(|f| f.symbol == self.document.selection.function)
            .expect("checked selection")
    }
    pub fn functions(&self) -> impl Iterator<Item = &FunctionSignature> {
        self.document.functions.iter()
    }

    pub fn entry(&self) -> &str {
        &self.document.entry
    }
    pub fn toolchain(&self) -> &str {
        &self.document.toolchain
    }
    pub fn original(&self) -> &str {
        &self.document.original
    }
    pub fn capture(&self) -> &str {
        &self.document.capture
    }
    /// Check source construction and declared message-data permissions. CPU
    /// preparation independently checks native admission and installed codecs.
    pub fn check_input(&self, s: &Schema) -> super::Result<()> {
        crate::entry::interface::schemas::check_import(s)
            .map_err(|e| super::EntryError::new(super::EntryPhase::Request, e))?;
        super::require(
            s.leaves
                .iter()
                .all(|s| self.types.get(s).is_some_and(|t| t.message)),
            "entry-input-codec",
        )
    }
    pub fn result_requires_setup(&self) -> bool {
        self.signature()
            .result
            .leaves
            .iter()
            .any(|leaf| self.types[leaf].needs_setup)
    }
    pub fn describe(&self) -> Value {
        json!({"kind":"function","entry":self.entry(),"capture":self.capture(),"original":self.original(),"toolchain":self.toolchain(),
            "signature":self.signature().describe(),"functions":self.functions().map(FunctionSignature::describe).collect::<Vec<_>>()})
    }
}

/// Inspected static child contract, without native installation or setup authority.
/// Executable admission remains FunctionEntry::admit's separate obligation.
#[derive(Debug)]
pub struct DeploymentInterface {
    pub(super) id: String,
    pub(super) operation: String,
    pub(super) interface: crate::entry::Interface,
    pub(super) parameters: Vec<Schema>,
    pub(super) result: Schema,
}
impl DeploymentInterface {
    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn operation(&self) -> &str {
        &self.operation
    }
    pub fn interface(&self) -> &crate::entry::Interface {
        &self.interface
    }
    pub fn describe(&self) -> Value {
        let id = self.id();
        let operation = self.operation();
        let view = self.interface();
        let groups = view.context_input_groups(operation);
        let selected_role = view.proof().and_then(|proof| match operation {
            "prove" => Some(proof.prover),
            "verify" => Some(proof.verifier),
            _ => None,
        });
        let roles = view
            .roles()
            .iter()
            .enumerate()
            .filter(|(index, _)| selected_role.is_none_or(|selected| *index == selected))
            .map(|(_, role)| {
                let inputs = groups
                    .iter()
                    .find(|group| group.name() == role.name)
                    .map(|group| group.describe());
                let services = view
                    .services(role)
                    .map(|service| json!({"name": service.name, "contract": service.contract}))
                    .collect::<Vec<_>>();
                serde_json::json!({
                    "role": role.name,
                    "native_role": role.native_name,
                    "inputs": inputs,
                    "services": services,
                })
            })
            .collect::<Vec<_>>();
        let parameters = self
            .parameters
            .iter()
            .map(Schema::describe)
            .collect::<Vec<_>>();
        serde_json::json!({
            "id": id,
            "operation": operation,
            "entry": view.entry(),
            "setups": view.setup_names().collect::<Vec<_>>(),
            "roles": roles,
            "parameters": parameters,
            "result": self.result.describe(),
        })
    }
}
