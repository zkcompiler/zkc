use super::*;
use crate::io::executable::Executable;
use std::{collections::BTreeMap, path::PathBuf, time::Duration};

/// Explicit installed tool and independent executable pin. No PATH search,
/// network download, or silently substituted compiler is performed.
#[derive(Clone, Debug)]
pub struct Solc {
    path: PathBuf,
    sha256: String,
    executable: Executable,
}
/// Reuse is an already authenticated immutable Artifact, not an untrusted cache
/// index. Imported artifacts must first pass Artifact::capture with a known pin.
pub struct Build<'a> {
    pub source: &'a Source,
    pub compiler_sha256: &'a str,
    pub reuse: Option<&'a Artifact>,
}
pub(super) fn input(source: &Source) -> Value {
    serde_json::json!({
        "language":"Yul",
        "sources":{"verifier.yul":{"content":source.yul()}},
        "settings":{
            "evmVersion":"cancun",
            "optimizer":{"enabled":true,"details":{"yul":true,"yulDetails":{"optimizerSteps":":"}}},
            "outputSelection":{"*":{"*":["evm.bytecode.object","evm.deployedBytecode.object"]}}
        }
    })
}
pub(super) fn build_key(source: &Source, compiler: &str, solc: &str) -> Result<String> {
    Ok(hash(&encode(&serde_json::json!({
        "format":"zkc.evm-build/0", "source_sha256":hash(source.bytes()),
        "compiler_sha256":compiler,"solc_sha256":solc,"solc_version":SOLC_VERSION,
        "input":input(source)
    }))?))
}
impl Solc {
    pub fn new(path: impl AsRef<Path>, expected_sha256: &str) -> Result<Self> {
        crate::io::bytes::digest(expected_sha256).map_err(|_| "evm-solc-pin")?;
        let path = path.as_ref().canonicalize().map_err(|_| "evm-solc-path")?;
        let executable = Executable::capture(&path, MAX_BYTES).map_err(snapshot_error)?;
        if executable.sha256() != expected_sha256 {
            return Err("evm-solc-pin".into());
        }
        let tool = Self {
            path,
            sha256: expected_sha256.into(),
            executable,
        };
        tool.check()?;
        Ok(tool)
    }
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn identity(&self) -> &str {
        &self.sha256
    }
    fn check_identity(&self) -> Result<()> {
        if !self
            .executable
            .matches_path(&self.path)
            .map_err(snapshot_error)?
        {
            return Err("evm-solc-pin".into());
        }
        Ok(())
    }
    fn execute(&self, arguments: &[&str], input: Option<&[u8]>) -> Result<Vec<u8>> {
        let directory = tempfile::tempdir().map_err(|_| "evm-solc-io")?;
        let captured = self
            .executable
            .command(&self.path)
            .map_err(|_| "evm-solc-io")?
            .args(arguments)
            .capture(directory.path(), Duration::from_secs(120), MAX_BYTES, input)
            .map_err(|e| match e {
                crate::io::process::Error::Timeout => Error::from("evm-solc-timeout"),
                crate::io::process::Error::OutputLimit => Error::from("evm-solc-limit"),
                _ => Error::from("evm-solc-io"),
            })?;
        if !captured.status.success() {
            return Err("evm-solc-failed".into());
        }
        read(captured.stdout.path())
    }
    fn check(&self) -> Result<()> {
        self.check_identity()?;
        let version = self.execute(&["--version"], None)?;
        let version = std::str::from_utf8(&version).map_err(|_| "evm-solc-version")?;
        if !version.lines().any(|line| {
            line.strip_prefix("Version: ")
                .is_some_and(|v| v == SOLC_VERSION || v.starts_with(&format!("{SOLC_VERSION}.")))
        }) {
            return Err("evm-solc-version".into());
        }
        self.check_identity()
    }
    pub fn compile(&self, build: Build<'_>) -> Result<Artifact> {
        crate::io::bytes::digest(build.compiler_sha256).map_err(|_| "evm-compiler-pin")?;
        self.check()?;
        let key = build_key(build.source, build.compiler_sha256, &self.sha256)?;
        if let Some(reuse) = build.reuse {
            if reuse.manifest().build_key != key {
                return Err("evm-cache-key".into());
            }
            self.check_identity()?;
            return Ok(reuse.clone());
        }
        let input_bytes = encode(&input(build.source))?;
        let response = self.execute(&["--standard-json"], Some(&input_bytes))?;
        self.check_identity()?;
        let response = json(&response)?;
        if response["errors"]
            .as_array()
            .is_some_and(|errors| errors.iter().any(|e| e["severity"] == "error"))
        {
            return Err("evm-solc-diagnostic".into());
        }
        let contracts = response["contracts"]["verifier.yul"]
            .as_object()
            .ok_or("evm-solc-contract")?;
        if contracts.len() != 1 {
            return Err("evm-solc-contract".into());
        }
        let contract = contracts.values().next().expect("one contract");
        let code = |key: &str| {
            crate::io::bytes::unhex(&contract["evm"][key]["object"])
                .map_err(|_| Error::from("evm-solc-bytecode"))
        };
        let mut files: BTreeMap<String, Vec<u8>> = BTreeMap::new();
        files.insert("source.json".into(), build.source.bytes().to_vec());
        files.insert(
            "verifier.yul".into(),
            build.source.yul().as_bytes().to_vec(),
        );
        files.insert("abi.json".into(), encode(build.source.abi())?);
        files.insert("solc-input.json".into(), input_bytes);
        files.insert("creation.bin".into(), code("bytecode")?);
        files.insert("runtime.bin".into(), code("deployedBytecode")?);
        let manifest = Manifest {
            format: FORMAT.into(),
            build_key: key,
            compiler_sha256: build.compiler_sha256.into(),
            solc_sha256: self.sha256.clone(),
            solc_version: SOLC_VERSION.into(),
            evm_version: "cancun".into(),
            files: files
                .iter()
                .map(|(name, bytes)| (name.clone(), hash(bytes)))
                .collect(),
        };
        Artifact::new(manifest, files)
    }
}

fn snapshot_error(error: crate::io::ReadError) -> Error {
    match error {
        crate::io::ReadError::Limit => "evm-solc-limit",
        crate::io::ReadError::Io(error) if error.kind() == std::io::ErrorKind::Unsupported => {
            "evm-solc-snapshot-unsupported"
        }
        crate::io::ReadError::Io(_) => "evm-solc-io",
    }
    .into()
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn script(path: &Path, bytes: &[u8]) {
        std::fs::write(path, bytes).unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
    }

    #[test]
    fn solc_keeps_original_bytes_and_rechecks_the_live_path() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("solc");
        let original = format!(
            "#!/bin/sh\nif [ \"$1\" = --version ]; then\n printf 'Version: {SOLC_VERSION}.Linux.g++\\n'\nelse\n cat\nfi\n"
        );
        script(&path, original.as_bytes());
        let tool = Solc::new(&path, &hash(original.as_bytes())).unwrap();
        let retained = tool.clone();
        drop(tool);
        for replace_inode in [true, false] {
            let replacement = b"#!/bin/sh\nprintf replaced\n";
            if replace_inode {
                let other = directory.path().join("replacement");
                script(&other, replacement);
                std::fs::rename(other, &path).unwrap();
            } else {
                script(&path, replacement);
            }
            // Check the execution boundary separately from the public route's
            // intentional refusal of a changed installation.
            let input = [42; 131072];
            assert_eq!(
                retained
                    .execute(&["--standard-json"], Some(&input))
                    .unwrap(),
                input
            );
            assert_eq!(retained.check().unwrap_err().0, "evm-solc-pin");
            script(&path, original.as_bytes());
            retained.check().unwrap();
        }
    }

    #[test]
    fn solc_snapshot_refusals_keep_their_diagnostic_codes() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("solc");
        script(&path, b"#!/bin/sh\nexit 0\n");
        assert_eq!(
            Solc::new(&path, &"00".repeat(32)).unwrap_err().0,
            "evm-solc-pin"
        );
        let file = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        file.set_len(MAX_BYTES as u64 + 1).unwrap();
        assert_eq!(
            Solc::new(&path, &"00".repeat(32)).unwrap_err().0,
            "evm-solc-limit"
        );
        drop(file);
        script(&path, b"#!/bin/sh\nexit 0\n");
        let pin = hash(&std::fs::read(&path).unwrap());
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(Solc::new(&path, &pin).unwrap_err().0, "evm-solc-io");
    }
}
