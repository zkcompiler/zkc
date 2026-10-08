//! Checked metadata for an authenticated source package. Reading this interface
//! checks structure and internal consistency, not MLIR meaning or native code.
mod binding;
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
    pub(in crate::entry) setups: Vec<Setup>,
    artifact: String,
    options: super::CompileOptions,
}
impl Interface {
    pub fn read(package: &Package) -> Result<Self> {
        preflight::check(package.interface().as_bytes())?;
        let mut decoder = serde_json::Deserializer::from_str(package.interface());
        // Lexical nesting is bounded above; schema nesting has its own smaller
        // bound. The default serde limit also counts intervening records/arrays.
        decoder.disable_recursion_limit();
        let document: raw::Interface =
            serde::Deserialize::deserialize(&mut decoder).map_err(|_| InterfaceError::Format)?;
        decoder.end().map_err(|_| InterfaceError::Format)?;
        let original = format!("{:x}", Sha256::digest(package.original().as_bytes()));
        let checked = validate::check(&document, &original)?;
        Ok(Self {
            document,
            selected: checked.selected,
            types: checked.types,
            setups: checked.setups,
            artifact: format!("{:x}", Sha256::digest(package.artifact().as_bytes())),
            options: package.options(),
        })
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
    pub(in crate::entry) fn completion(&self) -> Result<Option<usize>> {
        let raw::Job::Proof { completion, .. } = &self.document.job else {
            return Ok(None);
        };
        completion
            .as_ref()
            .map(|selected| {
                let (_, native) = validate::select(self.selected_protocol(), selected)?;
                Ok(native[0] as usize)
            })
            .transpose()
    }
    pub fn is_proof(&self) -> bool {
        matches!(self.document.job, raw::Job::Proof { .. })
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
