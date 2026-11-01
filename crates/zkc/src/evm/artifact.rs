use super::*;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fs, io::Write, path::PathBuf};

const FILES: [&str; 6] = [
    "source.json",
    "verifier.yul",
    "abi.json",
    "solc-input.json",
    "creation.bin",
    "runtime.bin",
];
/// The expected hash of these exact manifest bytes is the external trust root.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub format: String,
    pub build_key: String,
    pub compiler_sha256: String,
    pub solc_sha256: String,
    pub solc_version: String,
    pub evm_version: String,
    pub files: BTreeMap<String, String>,
}
#[derive(Clone, Debug)]
pub struct Artifact {
    manifest: Manifest,
    manifest_bytes: Vec<u8>,
    files: BTreeMap<String, Vec<u8>>,
}
impl Artifact {
    pub(super) fn new(manifest: Manifest, files: BTreeMap<String, Vec<u8>>) -> Result<Self> {
        let manifest_bytes = encode(&manifest)?;
        let artifact = Self {
            manifest,
            manifest_bytes,
            files,
        };
        artifact.validate()?;
        Ok(artifact)
    }
    fn validate(&self) -> Result<()> {
        let m = &self.manifest;
        if m.format != FORMAT
            || m.solc_version != SOLC_VERSION
            || m.evm_version != "cancun"
            || m.files.len() != FILES.len()
            || self.files.len() != FILES.len()
            || [&m.build_key, &m.compiler_sha256, &m.solc_sha256]
                .iter()
                .any(|s| crate::io::bytes::digest(s).is_err())
        {
            return Err("evm-manifest".into());
        }
        for name in FILES {
            let bytes = self.files.get(name).ok_or("evm-artifact-files")?;
            if bytes.len() > MAX_BYTES || m.files.get(name) != Some(&hash(bytes)) {
                return Err("evm-artifact-identity".into());
            }
        }
        let source = Source::capture(&self.files["source.json"])?;
        if self.files["verifier.yul"] != source.yul().as_bytes()
            || json(&self.files["abi.json"])? != *source.abi()
        {
            return Err("evm-artifact-source".into());
        }
        let input = json(&self.files["solc-input.json"])?;
        if input != solc::input(&source) {
            return Err("evm-artifact-settings".into());
        }
        if self.files["creation.bin"].is_empty()
            || self.files["creation.bin"].len() > 49152
            || self.files["runtime.bin"].is_empty()
            || self.files["runtime.bin"].len() > 24576
        {
            return Err("evm-code-size".into());
        }
        if m.build_key != solc::build_key(&source, &m.compiler_sha256, &m.solc_sha256)? {
            return Err("evm-artifact-build-key".into());
        }
        Ok(())
    }
    pub fn manifest(&self) -> &Manifest {
        &self.manifest
    }
    pub fn identity(&self) -> String {
        hash(&self.manifest_bytes)
    }
    pub fn manifest_bytes(&self) -> &[u8] {
        &self.manifest_bytes
    }
    pub fn source(&self) -> Result<Source> {
        Source::capture(&self.files["source.json"])
    }
    pub fn creation_bytecode(&self) -> &[u8] {
        &self.files["creation.bin"]
    }
    pub fn runtime_bytecode(&self) -> &[u8] {
        &self.files["runtime.bin"]
    }
    pub fn abi(&self) -> Result<Value> {
        json(&self.files["abi.json"])
    }
    /// A self-consistent directory is insufficient: the caller supplies the
    /// independently retained manifest identity from trusted compilation.
    pub fn capture(directory: impl AsRef<Path>, expected_manifest: &str) -> Result<Self> {
        crate::io::bytes::digest(expected_manifest).map_err(|_| "evm-artifact-pin")?;
        let directory = directory.as_ref();
        if fs::symlink_metadata(directory)
            .map_err(|_| "evm-artifact-read")?
            .file_type()
            .is_symlink()
        {
            return Err("evm-artifact-directory".into());
        }
        let manifest_bytes = read(directory.join("manifest.json"))?;
        if hash(&manifest_bytes) != expected_manifest {
            return Err("evm-artifact-pin".into());
        }
        let manifest = serde_json::from_slice(&manifest_bytes).map_err(|_| "evm-manifest")?;
        let mut files = BTreeMap::new();
        for name in FILES {
            files.insert(name.into(), read(directory.join(name))?);
        }
        let result = Self {
            manifest,
            manifest_bytes,
            files,
        };
        result.validate()?;
        Ok(result)
    }
    /// Publish a fresh complete directory. Existing destinations are never
    /// replaced. Staging is a sibling, so the final rename is atomic.
    pub fn publish(&self, destination: impl AsRef<Path>) -> Result<PathBuf> {
        self.validate()?;
        let destination = std::path::absolute(destination).map_err(|_| "evm-output-path")?;
        let parent = destination
            .parent()
            .ok_or("evm-output-path")?
            .canonicalize()
            .map_err(|_| "evm-output-path")?;
        let destination = parent.join(destination.file_name().ok_or("evm-output-path")?);
        if fs::symlink_metadata(&destination).is_ok() {
            return Err("evm-output-exists".into());
        }
        let stage = tempfile::Builder::new()
            .prefix(".zkc-evm-")
            .tempdir_in(&parent)
            .map_err(|_| "evm-output-stage")?;
        for (name, bytes) in self
            .files
            .iter()
            .map(|(n, b)| (n.as_str(), b.as_slice()))
            .chain(std::iter::once((
                "manifest.json",
                self.manifest_bytes.as_slice(),
            )))
        {
            let mut f = fs::OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(stage.path().join(name))
                .map_err(|_| "evm-output-stage")?;
            f.write_all(bytes)
                .and_then(|_| f.sync_all())
                .map_err(|_| "evm-output-stage")?;
        }
        // Rename-no-replace closes the check/rename race. There is no partial
        // multi-file publication or replacement of another writer's artifact.
        #[cfg(target_os = "linux")]
        rustix::fs::renameat_with(
            rustix::fs::CWD,
            stage.path(),
            rustix::fs::CWD,
            &destination,
            rustix::fs::RenameFlags::NOREPLACE,
        )
        .map_err(|_| "evm-output-publish")?;
        #[cfg(not(target_os = "linux"))]
        return Err("evm-atomic-publication-unsupported".into());
        Ok(destination)
    }
}
