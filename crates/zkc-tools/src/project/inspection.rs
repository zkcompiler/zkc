//! Checked logical metadata shared by source and pinned-package consumers.
use crate::entry::{FunctionInterface, Interface, Package, inputs::InputGroup};

pub enum CheckedInterface {
    Function(Box<FunctionInterface>),
    Proof(Box<Interface>),
}
impl CheckedInterface {
    pub fn from_compiler(bytes: &[u8]) -> Result<Self, String> {
        if is_function(bytes)? {
            FunctionInterface::from_compiler(bytes)
                .map(|v| Self::Function(Box::new(v)))
                .map_err(|e| e.to_string())
        } else {
            let view = Interface::from_compiler(bytes).map_err(|e| e.to_string())?;
            if !view.is_proof() {
                return Err("source-entry-selection".into());
            }
            Ok(Self::Proof(Box::new(view)))
        }
    }
    pub fn read(package: &Package) -> Result<Self, String> {
        if is_function(package.interface().as_bytes())? {
            FunctionInterface::read(package)
                .map(|v| Self::Function(Box::new(v)))
                .map_err(|e| e.to_string())
        } else {
            let view = crate::entry::BoundInterface::read(package).map_err(|e| e.to_string())?;
            if !view.is_proof() {
                return Err("source-entry-selection".into());
            }
            Ok(Self::Proof(Box::new(view.into_view())))
        }
    }
    pub fn kind(&self) -> super::EntryKind {
        match self {
            Self::Function(_) => super::EntryKind::Function,
            Self::Proof(_) => super::EntryKind::Proof,
        }
    }
    pub fn entry(&self) -> &str {
        match self {
            Self::Function(v) => v.entry(),
            Self::Proof(v) => v.entry(),
        }
    }
    pub fn toolchain(&self) -> &str {
        match self {
            Self::Function(v) => v.toolchain(),
            Self::Proof(v) => v.toolchain(),
        }
    }
    pub fn describe(&self) -> serde_json::Value {
        match self {
            Self::Function(v) => v.describe(),
            Self::Proof(v) => v.describe(),
        }
    }
    pub fn input_groups(&self) -> Vec<InputGroup<'_>> {
        match self {
            Self::Function(v) => vec![v.input_group()],
            Self::Proof(v) => v.input_groups(),
        }
    }
}

// Dispatch only. The selected checked reader owns full shape/schema validation.
// Ignored metadata does not get the narrower input-document depth ceiling.
fn is_function(bytes: &[u8]) -> Result<bool, String> {
    use serde::Deserialize;
    #[derive(Deserialize)]
    struct Kind {
        selection: Option<Selection>,
    }
    #[derive(Deserialize)]
    struct Selection {
        kind: String,
    }
    if bytes.len() > 4 * 1024 * 1024 {
        return Err("entry-interface-limit".into());
    }
    let mut decoder = serde_json::Deserializer::from_slice(bytes);
    decoder.disable_recursion_limit();
    let kind = Kind::deserialize(&mut decoder).map_err(|_| "entry-interface-format")?;
    decoder.end().map_err(|_| "entry-interface-format")?;
    Ok(kind.selection.is_some_and(|s| s.kind == "function"))
}
