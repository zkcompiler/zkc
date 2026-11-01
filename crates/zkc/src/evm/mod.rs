//! EVM verifier artifacts and bounded, explicitly pinned Solidity tooling.
//! This module does not execute EVM bytecode and has no CPU runtime dependency.
mod artifact;
mod calldata;
mod solc;
pub use artifact::{Artifact, Manifest};
pub use calldata::Invocation;
pub use solc::{Build, Solc};

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{fmt, path::Path};

use crate::io::document;

pub const SOLC_VERSION: &str = "0.8.38+commit.1835d247";
pub const FORMAT: &str = "zkc.evm-artifact/0";
const MAX_BYTES: usize = 16 * 1024 * 1024;

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
    // Keep these ceilings aligned with EvmLimits and validateLimits in the
    // compiler. Lower positive ceilings are part of the current contract.
    let ceilings = [
        ("rounds", 10),
        ("public_elements", 1024),
        ("frame_bytes", 65536),
        ("public_bytes", 131072),
        ("context_bytes", 4096),
        ("proof_bytes", 65536),
        ("calldata_bytes", 262144),
        ("root_bytes", 262144),
        ("memory_bytes", 2097152),
        ("transcript_transitions", 64),
        ("practical_gas", 20000000),
    ];
    exact_object(value, &ceilings.map(|(key, _)| key), "evm-source-limits")?;
    if ceilings
        .iter()
        .any(|(key, ceiling)| value[key].as_u64().is_none_or(|n| n == 0 || n > *ceiling))
        || value["memory_bytes"].as_u64().unwrap() < 4096
    {
        return Err("evm-source-limits".into());
    }
    Ok(())
}

fn source_descriptor(record: &Value) -> Result<()> {
    let code = "evm-source-descriptor";
    let array = |value: &Value, size| value.as_array().is_some_and(|items| items.len() == size);
    let natural = |value: &Value| {
        value
            .as_str()
            .and_then(|text| zkc_format::logical::natural_index(text).ok())
    };
    let text = |value: &Value| value.as_str().is_some_and(|s| !s.is_empty());
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
        || (1..=3).any(|i| !text(&policy[i]))
        || policy[2] == policy[3]
        || natural(&policy[4]).is_none_or(|n| n >= 1024)
        || policy[5] != "hash-chain.keccak256.bls12-381.fr64be/0"
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
        if slot == 6 && ports.len() != 1 {
            return Err(code.into());
        }
    }
    let draws = policy[8].as_array().ok_or(code)?;
    let mut sites = std::collections::BTreeSet::new();
    if draws.is_empty() || draws.len() > 64 {
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
        || record["manifest"]["producer"] != policy[2]
        || record["manifest"]["validator"] != policy[3]
    {
        return Err("evm-source-identity".into());
    }
    let selection = descriptor[8].as_str().ok_or(code)?;
    let parsed = crate::entry::OracleSelection::parse(selection).map_err(|_| code)?;
    if !matches!(parsed.roots, crate::entry::OracleRoots::Exact(_))
        || parsed.canonical_json().map_err(|_| code)? != selection
    {
        return Err(code.into());
    }
    Ok(())
}

/// Exact compiler-owned source response. Capture is transport validation, not
/// independent authentication of the selected source or compiler.
#[derive(Clone, Debug)]
pub struct Source {
    bytes: Vec<u8>,
    record: Value,
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
                "target",
                "fork",
                "yul",
                "abi",
                "descriptor",
                "policy",
                "limits",
                "source_sha256",
                "manifest",
                "entry",
                "capture",
                "installation",
                "original",
            ],
            "evm-source-format",
        )?;
        let manifest = &record["manifest"];
        exact_object(
            manifest,
            &[
                "format",
                "target",
                "fork",
                "source_sha256",
                "source_format",
                "entry",
                "producer",
                "validator",
                "compiler",
                "yul_sha256",
                "limits",
                "solc_version",
                "optimizer_steps",
                "release_validation",
                "capture",
                "installation",
                "original",
            ],
            "evm-source-format",
        )?;
        if record["format"] != "zkc.evm-source/0"
            || record["target"] != "evm"
            || record["fork"] != "cancun"
            || record["yul"].as_str().is_none_or(str::is_empty)
            || record["entry"].as_str().is_none_or(str::is_empty)
            || record["abi"] != calldata::abi()
            || manifest["format"] != "zkc.evm-source-manifest/0"
            || manifest["source_format"] != "zkc.original-mlir/0"
            || manifest["solc_version"] != "0.8.38"
            || manifest["optimizer_steps"] != ":"
            || manifest["release_validation"] != "pending-deployment-and-dynamic-trace"
        {
            return Err("evm-source-format".into());
        }
        source_limits(&record["limits"])?;
        source_limits(&manifest["limits"])?;
        for key in ["capture", "installation", "original", "source_sha256"] {
            if record[key]
                .as_str()
                .is_none_or(|value| crate::io::bytes::digest(value).is_err())
                || record["manifest"][key] != record[key]
            {
                return Err("evm-source-identity".into());
            }
        }
        if ["entry", "target", "fork", "limits"]
            .iter()
            .any(|key| manifest[key] != record[key])
            || record["original"] != record["source_sha256"]
            || manifest["compiler"]
                .as_str()
                .is_none_or(|value| crate::io::bytes::digest(value).is_err())
            || manifest["yul_sha256"] != hash(record["yul"].as_str().unwrap().as_bytes())
        {
            return Err("evm-source-identity".into());
        }
        source_descriptor(&record)?;
        Ok(Self {
            bytes: bytes.to_vec(),
            record,
        })
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn yul(&self) -> &str {
        self.record["yul"].as_str().expect("captured source")
    }
    pub fn abi(&self) -> &Value {
        &self.record["abi"]
    }
    pub fn entry(&self) -> &str {
        self.record["entry"].as_str().expect("captured entry")
    }
    pub fn metadata(&self) -> &Value {
        &self.record
    }
}

#[cfg(test)]
pub(crate) mod tests;
