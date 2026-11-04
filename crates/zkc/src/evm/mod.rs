//! EVM verifier artifacts and bounded, explicitly pinned Solidity tooling.
//! This module does not execute EVM bytecode and has no CPU runtime dependency.
mod artifact;
mod calldata;
mod limits;
mod solc;
pub use artifact::{Artifact, Manifest};
pub use calldata::Invocation;
pub use limits::Limits;
pub use solc::{Build, Solc};

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{fmt, path::Path};

use crate::io::document;

/// The pinned solc release and commit, from the installed target declaration.
pub const SOLC_VERSION: &str = crate::evm_target::SOLC_VERSION;
pub const FORMAT: &str = "zkc.evm-artifact/0";
const MAX_BYTES: usize = 16 * 1024 * 1024;

/// Exact deployment fork: a fork of the installed target declaration
/// (`zkc::evm_target`). Only these typed values can reach solc settings. It is
/// spelled by its declared lowercase name and defaults to the declared default.
pub use crate::evm_target::Fork as EvmFork;
impl Default for EvmFork {
    fn default() -> Self {
        crate::evm_target::DEFAULT_FORK
    }
}
impl serde::Serialize for EvmFork {
    fn serialize<S: serde::Serializer>(&self, encoder: S) -> std::result::Result<S::Ok, S::Error> {
        encoder.serialize_str(self.as_str())
    }
}
impl<'de> serde::Deserialize<'de> for EvmFork {
    fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> std::result::Result<Self, D::Error> {
        let value = <String as serde::Deserialize>::deserialize(decoder)?;
        value.parse().map_err(serde::de::Error::custom)
    }
}
impl EvmFork {
    pub fn as_str(self) -> &'static str {
        self.row().name
    }
}
impl std::str::FromStr for EvmFork {
    type Err = Error;
    fn from_str(value: &str) -> Result<Self> {
        Self::from_name(value).ok_or_else(|| "evm-fork".into())
    }
}

/// Common resolved compiler options and a target deployment setting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Options {
    pub fork: EvmFork,
    pub compile: crate::entry::CompileOptions,
    pub limits: Limits,
}
impl Default for Options {
    fn default() -> Self {
        Self {
            fork: EvmFork::default(),
            compile: crate::project::ResolvedSettings::default().options(),
            limits: Limits::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error(pub String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
impl From<&str> for Error {
    fn from(s: &str) -> Self {
        Self(s.into())
    }
}
impl From<String> for Error {
    fn from(s: String) -> Self {
        Self(s)
    }
}
type Result<T> = std::result::Result<T, Error>;
fn hash(bytes: &[u8]) -> String {
    crate::io::bytes::hex(&Sha256::digest(bytes))
}
fn read(path: impl AsRef<Path>) -> Result<Vec<u8>> {
    crate::io::read_regular(path, MAX_BYTES).map_err(|_| "evm-artifact-read".into())
}
fn json(bytes: &[u8]) -> Result<Value> {
    if bytes.len() > MAX_BYTES {
        return Err("evm-artifact-limit".into());
    }
    serde_json::from_slice(bytes).map_err(|_| "evm-json".into())
}
fn encode(value: &impl serde::Serialize) -> Result<Vec<u8>> {
    let bytes = serde_json::to_vec(value).map_err(|_| "evm-json")?;
    if bytes.len() > MAX_BYTES {
        return Err("evm-artifact-limit".into());
    }
    Ok(bytes)
}

fn exact_object(value: &Value, fields: &[&str], code: &'static str) -> Result<()> {
    let object = value.as_object().ok_or(code)?;
    if object.len() != fields.len() || fields.iter().any(|field| !object.contains_key(*field)) {
        return Err(code.into());
    }
    Ok(())
}

fn source_limits(value: &Value) -> Result<()> {
    // Every declared ceiling, each within its declared range. A compilation may
    // lower a ceiling, never raise it.
    let limits = &crate::evm_target::LIMITS;
    let names: Vec<_> = limits.iter().map(|limit| limit.name).collect();
    exact_object(value, &names, "evm-source-limits")?;
    if limits.iter().any(|limit| {
        value[limit.name]
            .as_u64()
            .is_none_or(|n| n < limit.minimum || n > limit.maximum)
    }) {
        return Err("evm-source-limits".into());
    }
    Ok(())
}

/// The effective common-stage options: exactly the shared list a CPU Entry
/// package publishes, without CPU storage release.
fn source_options(value: &Value) -> Result<crate::entry::CompileOptions> {
    let options: crate::entry::CompileOptions =
        serde_json::from_value(value.clone()).map_err(|_| "evm-source-options")?;
    if options.release_storage {
        return Err("evm-source-options".into());
    }
    Ok(options)
}

/// Whether the target realizes the installed suite's declared hash-chain,
/// decoder and field layout. This independently mirrors the compiler's
/// supported contract, never a protocol or suite-name allowlist.
fn realized_suite(suite: &str) -> bool {
    use zkc_catalog::{
        ByteHash, ChallengeDecoder, DomainFacts, ExtensionBase, FieldStructure, TranscriptFamily,
    };
    // 2^256 in decimal.
    const BOUND: &str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    let Some(row) = zkc_catalog::DomainIdentity::parse(suite).map(zkc_catalog::installed_domain)
    else {
        return false;
    };
    let DomainFacts::Transcript(facts) = row.facts else {
        return false;
    };
    if facts.family != TranscriptFamily::HashChain
        || facts.hash != Some(ByteHash::Keccak256)
        || !facts.binds_suite
    {
        return false;
    }
    let Some(challenge) = row
        .members
        .iter()
        .find(|(member, _)| *member == "ChallengeField")
        .map(|(_, field)| zkc_catalog::installed_domain(*field))
    else {
        return false;
    };
    let DomainFacts::Field(field) = challenge.facts else {
        return false;
    };
    match (facts.decoder, field.structure) {
        (ChallengeDecoder::Fr64Be, FieldStructure::Prime) => {
            challenge.capabilities.contains(&"PrimeField")
                && (field.characteristic.len() < BOUND.len()
                    || (field.characteristic.len() == BOUND.len() && field.characteristic < BOUND))
        }
        (
            ChallengeDecoder::Rejection31Le,
            FieldStructure::Extension {
                over: ExtensionBase::BaseField,
                degree: 2..=8,
                reduction: [(0, beta)],
            },
        ) => {
            let Some(base) = challenge
                .members
                .iter()
                .find(|(member, _)| *member == "BaseField")
                .map(|(_, identity)| zkc_catalog::installed_domain(*identity))
            else {
                return false;
            };
            let DomainFacts::Field(base_field) = base.facts else {
                return false;
            };
            let (Ok(prime), Ok(beta)) = (
                base_field.characteristic.parse::<u32>(),
                beta.parse::<u32>(),
            ) else {
                return false;
            };
            challenge.capabilities.contains(&"ExtensionField")
                && base.capabilities.contains(&"PrimeField")
                && base_field.structure == FieldStructure::Prime
                && field.characteristic == base_field.characteristic
                && (2..1 << 31).contains(&prime)
                && (1..prime).contains(&beta)
        }
        _ => false,
    }
}

fn source_descriptor(record: &Value, requested: &crate::entry::OracleSelection) -> Result<()> {
    let code = "evm-source-descriptor";
    let array = |value: &Value, size| value.as_array().is_some_and(|items| items.len() == size);
    let natural = |value: &Value| {
        value
            .as_str()
            .and_then(|text| zkc_format::logical::natural_index(text).ok())
    };
    let text = |value: &Value| value.as_str().is_some_and(|s| !s.is_empty());
    let name = |value: &Value| {
        value.as_str().is_some_and(|s| {
            !s.is_empty()
                && s.len() <= 128
                && s.bytes()
                    .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
        })
    };
    let descriptor = &record["descriptor"];
    let policy = &record["policy"];
    // The descriptor is an existing string/array carrier, not arbitrary JSON.
    zkc_format::logical::tree_size(descriptor).map_err(|_| code)?;
    if !array(descriptor, 9)
        || descriptor[0] != "zkc.native-proof-descriptor/0"
        || descriptor[1] != *policy
        || descriptor[2] != "zkc.native-origin/0"
        || !array(policy, 12)
        || policy[0] != "zkc.native-proof-policy/0"
        || (1..=3).any(|i| !name(&policy[i]))
        || policy[2] == policy[3]
        || natural(&policy[4]).is_none_or(|n| n >= 1024)
        || !policy[5]
            .as_str()
            .is_some_and(|suite| suite.is_empty() || realized_suite(suite))
        || policy[9] != "zkc.framed/0"
        || policy[10] != ""
        || descriptor[6] != serde_json::json!([])
    {
        return Err(code.into());
    }
    for slot in [6, 7] {
        let ports = policy[slot].as_array().ok_or(code)?;
        let mut previous = None;
        for port in ports {
            let n = natural(port).filter(|n| *n < 1024).ok_or(code)?;
            if previous.is_some_and(|last| last >= n) {
                return Err(code.into());
            }
            previous = Some(n);
        }
        if slot == 6 && ports.len() != usize::from(policy[5] != "") {
            return Err(code.into());
        }
    }
    let draws = policy[8].as_array().ok_or(code)?;
    let mut sites = std::collections::BTreeSet::new();
    if draws.len() > 64 || (draws.is_empty() != (policy[5] == "")) {
        return Err(code.into());
    }
    for draw in draws {
        if !array(draw, 2) {
            return Err(code.into());
        }
        for site in draw.as_array().unwrap() {
            let site = site.as_str().ok_or(code)?;
            if site.is_empty()
                || site.len() > 4096
                || !site.bytes().all(|b| (33..=126).contains(&b))
                || !sites.insert(site)
            {
                return Err(code.into());
            }
        }
    }
    let mut gates = std::collections::BTreeSet::new();
    for gate in policy[11].as_array().ok_or(code)? {
        if !array(gate, 2)
            || natural(&gate[1]).is_none_or(|n| n > 64)
            || !draws.iter().any(|draw| draw[0] == gate[0])
            || !gates.insert(gate[0].as_str().ok_or(code)?)
        {
            return Err(code.into());
        }
    }
    for slot in [3, 4, 5, 7] {
        for row in descriptor[slot].as_array().ok_or(code)? {
            let row = row.as_array().ok_or(code)?;
            if policy[5] == ""
                && ((slot == 3 && row.first().and_then(Value::as_str) != Some("message"))
                    || slot == 7)
            {
                return Err(code.into());
            }
            let width = match slot {
                3 => match row.first().and_then(Value::as_str) {
                    Some("query" | "message" | "reconstructed-message") => 2,
                    Some("index" | "start") => 3,
                    Some("indices") => 4,
                    Some("gated-indices") => 5,
                    _ => return Err(code.into()),
                },
                5 => 3,
                _ => 4,
            };
            if row.len() != width {
                return Err(code.into());
            }
            if slot == 3 && row[0] == "start" {
                if !text(&row[1])
                    || !row[2]
                        .as_array()
                        .is_some_and(|types| types.iter().all(text))
                {
                    return Err(code.into());
                }
            } else if !row.iter().all(text) {
                return Err(code.into());
            }
        }
    }
    let public = descriptor[4].as_array().unwrap();
    let ports = policy[7].as_array().unwrap();
    if public.len() != ports.len()
        || public
            .iter()
            .zip(ports)
            .any(|(row, port)| row[0] != policy[3] || row[1] != *port)
    {
        return Err("evm-source-identity".into());
    }
    let selection = descriptor[8].as_str().ok_or(code)?;
    requested.check_normalized(selection).map_err(|_| code)?;
    Ok(())
}

/// Exact compiler-owned source response, `zkc.evm-source/0`. Capture is
/// transport validation, not independent authentication of the selected source
/// or compiler. The SDK owns the tool facts: the solc release and settings and
/// the verifier ABI come from the installed target declaration.
#[derive(Clone, Debug)]
pub struct Source {
    bytes: Vec<u8>,
    record: Value,
    fork: EvmFork,
    options: crate::entry::CompileOptions,
    limits: Limits,
}
impl Source {
    pub fn capture(bytes: &[u8]) -> Result<Self> {
        if bytes.len() > MAX_BYTES {
            return Err("evm-artifact-limit".into());
        }
        let record = document::read(bytes, MAX_BYTES).map_err(|_| "evm-json")?;
        exact_object(
            &record,
            &[
                "format",
                "declaration",
                "fork",
                "options",
                "limits",
                "entry",
                "capture",
                "installation",
                "original",
                "source_format",
                "compiler",
                "policy",
                "descriptor",
                "yul",
            ],
            "evm-source-format",
        )?;
        if record["format"] != "zkc.evm-source/0"
            || record["source_format"] != "zkc.original-mlir/0"
            || record["yul"].as_str().is_none_or(str::is_empty)
            || record["entry"].as_str().is_none_or(str::is_empty)
        {
            return Err("evm-source-format".into());
        }
        // The response names the compiler's installed target declaration; a
        // different one states other forks, ceilings or tool settings.
        if record["declaration"] != crate::evm_target::IDENTITY {
            return Err("evm-target-declaration".into());
        }
        let fork = record["fork"].as_str().ok_or("evm-fork")?.parse()?;
        let options = source_options(&record["options"])?;
        source_limits(&record["limits"])?;
        let limits = Limits::from_source(&record["limits"]);
        for key in ["capture", "installation", "original", "compiler"] {
            if record[key]
                .as_str()
                .is_none_or(|value| crate::io::bytes::digest(value).is_err())
            {
                return Err("evm-source-identity".into());
            }
        }
        source_descriptor(&record, &options.oracle_realization)?;
        Ok(Self {
            bytes: bytes.to_vec(),
            record,
            fork,
            options,
            limits,
        })
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn yul(&self) -> &str {
        self.record["yul"].as_str().expect("captured source")
    }
    /// The verifier ABI of the installed target declaration.
    pub fn abi(&self) -> &'static Value {
        &calldata::ABI
    }
    pub fn entry(&self) -> &str {
        self.record["entry"].as_str().expect("captured entry")
    }
    pub fn metadata(&self) -> &Value {
        &self.record
    }
    pub fn fork(&self) -> EvmFork {
        self.fork
    }
    pub fn options(&self) -> &crate::entry::CompileOptions {
        &self.options
    }
    /// Immutable effective deployment ceilings, independently checked on capture.
    pub fn limits(&self) -> &Limits {
        &self.limits
    }
}

#[cfg(test)]
pub(crate) mod tests;
