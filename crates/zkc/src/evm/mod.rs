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

/// Exact compiler-owned source response. Capture is transport validation, not
/// independent authentication of the selected source or compiler.
#[derive(Clone, Debug)]
pub struct Source {
    bytes: Vec<u8>,
    record: Value,
}
impl Source {
    pub fn capture(bytes: &[u8]) -> Result<Self> {
        let record = json(bytes)?;
        if record["format"] != "zkc.evm-source/0"
            || record["target"] != "evm"
            || record["fork"] != "cancun"
            || record["yul"].as_str().is_none_or(str::is_empty)
            || record["entry"].as_str().is_none_or(str::is_empty)
            || record["abi"] != calldata::abi()
        {
            return Err("evm-source-format".into());
        }
        for key in ["capture", "installation", "original", "source_sha256"] {
            if record[key]
                .as_str()
                .is_none_or(|value| crate::io::bytes::digest(value).is_err())
                || record["manifest"][key] != record[key]
            {
                return Err("evm-source-identity".into());
            }
        }
        if record["manifest"]["entry"] != record["entry"]
            || record["manifest"]["yul_sha256"] != hash(record["yul"].as_str().unwrap().as_bytes())
        {
            return Err("evm-source-identity".into());
        }
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
mod tests;
