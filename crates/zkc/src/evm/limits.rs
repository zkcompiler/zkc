use super::{Result, document};
use std::{collections::BTreeMap, path::Path};

const MAX_BYTES: usize = 64 * 1024;

/// One complete, validated deployment selection. Defaults are the installed
/// declaration's maxima; names and ranges come only from its generated rows.
/// Changing a selection produces a new value. A compiled Source or Artifact
/// retains its immutable effective selection; these are not per-call budgets.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(transparent)]
pub struct Limits(BTreeMap<&'static str, u64>);

impl Default for Limits {
    fn default() -> Self {
        Self(
            crate::evm_target::LIMITS
                .iter()
                .map(|row| (row.name, row.maximum))
                .collect(),
        )
    }
}

impl Limits {
    /// Select one declared ceiling within its inclusive minimum and maximum.
    /// Unknown names and out-of-range values refuse with `evm-limits`.
    pub fn with(mut self, name: &str, value: u64) -> Result<Self> {
        let row = crate::evm_target::LIMITS
            .iter()
            .find(|row| row.name == name)
            .ok_or("evm-limits")?;
        if !(row.minimum..=row.maximum).contains(&value) {
            return Err("evm-limits".into());
        }
        self.0.insert(row.name, value);
        Ok(self)
    }

    /// Read a partial JSON object of declared name/u64 selections. Omitted
    /// names receive the declared maxima exactly once, here in the SDK.
    /// Duplicate decoded keys, unknown names and noninteger tokens refuse.
    pub fn parse(bytes: &[u8]) -> Result<Self> {
        let value = document::read(bytes, MAX_BYTES).map_err(|_| "evm-limits")?;
        let object = value.as_object().ok_or("evm-limits")?;
        let mut limits = Self::default();
        for (name, value) in object {
            limits = limits.with(name, value.as_u64().ok_or("evm-limits")?)?;
        }
        Ok(limits)
    }

    /// Capture a regular JSON file of at most 64 KiB, then validate its partial
    /// selection. This reads no executable and starts no compiler process.
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let bytes = crate::io::read_regular(path, MAX_BYTES).map_err(|_| "evm-limits-read")?;
        Self::parse(&bytes)
    }

    pub fn get(&self, name: &str) -> Option<u64> {
        self.0.get(name).copied()
    }

    /// Complete effective object with sorted exact names and decimal u64
    /// values. The compiler command accepts this inline JSON, never a path.
    pub fn canonical_json(&self) -> String {
        serde_json::to_string(self).expect("validated deployment limits")
    }

    // The independent hostile Source reader has already required the complete
    // exact object and checked every range. Do not fill defaults on this path.
    pub(super) fn from_source(value: &serde_json::Value) -> Self {
        Self(
            crate::evm_target::LIMITS
                .iter()
                .map(|row| {
                    (
                        row.name,
                        value[row.name].as_u64().expect("checked source limit"),
                    )
                })
                .collect(),
        )
    }
}
