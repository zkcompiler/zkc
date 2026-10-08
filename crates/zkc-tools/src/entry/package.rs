use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::sync::Arc;

const PACKAGE_BYTES: usize = 64 * 1024 * 1024;
const ORIGINAL_BYTES: usize = 16 * 1024 * 1024;
const INTERFACE_BYTES: usize = 4 * 1024 * 1024;
const ARTIFACT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CompileOptions {
    pub simplify: bool,
    pub release_storage: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PackageError {
    Limit,
    Identity,
    Format,
}
impl std::fmt::Display for PackageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Limit => "entry-package-limit",
            Self::Identity => "entry-package-identity",
            Self::Format => "entry-package-format",
        })
    }
}
impl std::error::Error for PackageError {}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Frame {
    format: String,
    original: String,
    interface: String,
    artifact: String,
    options: CompileOptions,
}

/// Immutable authenticated container. This is not native program admission or
/// a check of the compiler's source correspondence. The application must trust
/// the digest's origin, not merely hash an incoming untrusted publication.
#[derive(Clone)]
pub struct Package {
    bytes: Arc<[u8]>,
    identity: [u8; 32],
    original: Arc<str>,
    interface: Arc<str>,
    artifact: Arc<str>,
    options: CompileOptions,
}
impl Package {
    pub const MAX_BYTES: usize = PACKAGE_BYTES;

    /// Authenticate before parsing. The caller may lower the whole-package
    /// limit; fixed component limits match the compiler's publication contract.
    /// Strict typed decoding rejects unknown/duplicate fields and nested values
    /// where exact strings or Boolean options are required.
    pub fn capture(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        byte_limit: usize,
    ) -> Result<Self, PackageError> {
        if bytes.len() > byte_limit.min(PACKAGE_BYTES) {
            return Err(PackageError::Limit);
        }
        let identity: [u8; 32] = Sha256::digest(bytes).into();
        if &identity != expected_sha256 {
            return Err(PackageError::Identity);
        }
        // Only the frame is decoded here. Embedded interface and artifact
        // decoders retain their own structure, work and admission limits.
        let frame: Frame = serde_json::from_slice(bytes).map_err(|_| PackageError::Format)?;
        if frame.format != "zkc.entry/1" {
            return Err(PackageError::Format);
        }
        if frame.original.len() > ORIGINAL_BYTES
            || frame.interface.len() > INTERFACE_BYTES
            || frame.artifact.len() > ARTIFACT_BYTES
        {
            return Err(PackageError::Limit);
        }
        Ok(Self {
            bytes: bytes.into(),
            identity,
            original: frame.original.into(),
            interface: frame.interface.into(),
            artifact: frame.artifact.into(),
            options: frame.options,
        })
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn identity(&self) -> &[u8; 32] {
        &self.identity
    }
    pub fn original(&self) -> &str {
        &self.original
    }
    pub fn interface(&self) -> &str {
        &self.interface
    }
    pub fn artifact(&self) -> &str {
        &self.artifact
    }
    pub fn options(&self) -> CompileOptions {
        self.options
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn frame() -> String {
        json!({"format":"zkc.entry/1","original":"module\n{}",
            "interface":"{\"job\":{\"kind\":\"run\"}}", "artifact":"[]",
            "options":{"simplify":true,"release_storage":false}})
        .to_string()
    }
    fn capture(bytes: &[u8]) -> Result<Package, PackageError> {
        Package::capture(bytes, &Sha256::digest(bytes).into(), Package::MAX_BYTES)
    }
    #[test]
    fn exact_bytes_and_components_are_retained() {
        let bytes = frame();
        let package = capture(bytes.as_bytes()).unwrap();
        assert_eq!(package.bytes(), bytes.as_bytes());
        assert_eq!(package.original(), "module\n{}");
        assert_eq!(package.interface(), r#"{"job":{"kind":"run"}}"#);
        assert_eq!(package.artifact(), "[]");
        assert_eq!(
            package.options(),
            CompileOptions {
                simplify: true,
                release_storage: false
            }
        );
        assert_eq!(package.clone().identity(), package.identity());
        assert!(Package::capture(bytes.as_bytes(), package.identity(), bytes.len()).is_ok());
        assert!(matches!(
            Package::capture(bytes.as_bytes(), package.identity(), bytes.len() - 1),
            Err(PackageError::Limit)
        ));
        let spaced = bytes + "\n";
        assert!(matches!(
            Package::capture(spaced.as_bytes(), package.identity(), Package::MAX_BYTES),
            Err(PackageError::Identity)
        ));
        assert_ne!(
            capture(spaced.as_bytes()).unwrap().identity(),
            package.identity()
        );
    }
    #[test]
    fn authentication_precedes_json_parsing() {
        assert!(matches!(
            Package::capture(b"not JSON", &[0; 32], Package::MAX_BYTES),
            Err(PackageError::Identity)
        ));
        assert!(matches!(capture(b"not JSON"), Err(PackageError::Format)));
    }
    #[test]
    fn strict_frame_rejects_duplicates_unknown_versions_fields_and_types() {
        let original = frame();
        for bytes in [
            original.replace("zkc.entry/1", "zkc.entry/0"),
            original.replacen('{', "{\"extra\":null,", 1),
            original.replacen('{', "{\"format\":\"zkc.entry/1\",", 1),
            original.replace("\"simplify\":true", "\"simplify\":true,\"simplify\":true"),
            original.replace("\"simplify\":true", "\"simplify\":\"true\""),
            original.replace("\"release_storage\":false", "\"other\":false"),
            original.replace("\"artifact\":\"[]\"", "\"artifact\":[]"),
            original.clone() + "{}",
        ] {
            assert!(
                matches!(capture(bytes.as_bytes()), Err(PackageError::Format)),
                "accepted {bytes}"
            );
        }
    }
    #[test]
    fn component_limits_apply_to_decoded_bytes() {
        let mut value: serde_json::Value = serde_json::from_str(&frame()).unwrap();
        value["interface"] = "a".repeat(INTERFACE_BYTES).into();
        let bytes = value.to_string();
        assert!(capture(bytes.as_bytes()).is_ok());
        value["interface"] = "a".repeat(INTERFACE_BYTES + 1).into();
        assert!(matches!(
            capture(value.to_string().as_bytes()),
            Err(PackageError::Limit)
        ));
    }
}
