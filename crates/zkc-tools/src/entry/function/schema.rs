use super::{FunctionSignature, Schema};
use serde_json::{Value, json};
impl Schema {
    /// Stable logical input/output plan, including nominal and constructor facts.
    pub fn describe(&self) -> Value {
        let fields = |fs: &[crate::entry::interface::raw::Field]| {
            fs.iter()
                .map(|f| json!({"name":f.name,"offset":f.offset,"schema":f.schema.describe()}))
                .collect::<Vec<_>>()
        };
        json!({"kind":format!("{:?}",self.kind).to_lowercase(),"identity":self.identity,
            "type":self.display_type,"custody":self.custody,"constructible":self.constructible,
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
    types: std::collections::BTreeMap<String, zkc_runtime::vm::LogicalType>,
}
impl FunctionInterface {
    /// Static context requirements. This does not import keys or grant authority.
    pub fn deployment_interfaces(
        package: &crate::entry::Package,
    ) -> super::Result<Vec<(String, String, crate::entry::Interface)>> {
        super::admission::interfaces(package)
    }
    pub fn deployment_requirements(package: &crate::entry::Package) -> super::Result<Value> {
        super::admission::requirements(package)
    }
    pub fn read(package: &crate::entry::Package) -> super::Result<Self> {
        use sha2::{Digest, Sha256};
        let original = crate::host::inputs::hex(&Sha256::digest(package.original().as_bytes()));
        let view = Self::from_compiler(package.interface().as_bytes())?;
        super::require(view.document.original == original, "entry-host-identity")?;
        Ok(view)
    }
    pub(crate) fn from_compiler(bytes: &[u8]) -> super::Result<Self> {
        crate::entry::interface::preflight::check(bytes)
            .map_err(|e| super::EntryError::new(super::EntryPhase::Interface, e))?;
        let document: super::carrier::Interface = super::admission::decode(bytes, 4 * 1024 * 1024)?;
        super::require(
            document.format == "zkc.language-interface/0" && document.selection.kind == "function",
            "entry-host-selection",
        )?;
        super::require(
            document.protocols.is_empty()
                && document.relations.is_empty()
                && document.setups.is_empty(),
            "entry-host-stage",
        )?;
        super::require(
            crate::host::inputs::digest(&document.capture).is_ok()
                && !document.toolchain.is_empty()
                && document.toolchain.len() <= 256 * 1024
                && document.entry.len() <= 4096
                && document.entry.contains("::")
                && document
                    .entry
                    .split("::")
                    .all(crate::source_names::is_source_identifier),
            "entry-host-identity",
        )?;
        let mut schemas = crate::entry::interface::schemas::Schemas::new();
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
            }
            schemas
                .check(&f.result, 0)
                .map_err(|e| super::EntryError::new(super::EntryPhase::Interface, e))?;
        }
        super::require(
            document.functions.len() <= 4096 && symbols.contains(&document.selection.function),
            "entry-host-selection",
        )?;
        crate::host::inputs::digest(&document.original)
            .map_err(|e| super::EntryError::new(super::EntryPhase::Interface, e))?;
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
    pub fn logical_type(&self, s: &str) -> Option<&zkc_runtime::vm::LogicalType> {
        self.types.get(s)
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
    pub fn check_input(&self, s: &Schema) -> super::Result<()> {
        crate::entry::value::check_import(s)
            .map_err(|e| super::EntryError::new(super::EntryPhase::Request, e))?;
        super::require(
            s.leaves.iter().all(|s| {
                self.types
                    .get(s)
                    .is_some_and(|t| t.is_native_message_data())
            }),
            "entry-input-codec",
        )
    }
    pub fn describe(&self) -> Value {
        json!({"kind":"function","entry":self.entry(),"capture":self.capture(),"original":self.original(),"toolchain":self.toolchain(),
            "signature":self.signature().describe(),"functions":self.functions().map(FunctionSignature::describe).collect::<Vec<_>>()})
    }
}
