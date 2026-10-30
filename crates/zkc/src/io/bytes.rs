//! Bounded ingress shared by construction and application inputs.
use serde_json::Value as Json;
#[cfg(all(feature = "files", any(feature = "cpu", feature = "project")))]
use std::path::Path;
pub(crate) type Result<T> = std::result::Result<T, String>;
pub(crate) const INPUT_LIMIT: usize = 16 * 1024 * 1024;

#[cfg(all(feature = "files", any(feature = "cpu", feature = "project")))]
pub(crate) fn read_regular(path: impl AsRef<Path>, limit: usize) -> Result<Vec<u8>> {
    crate::io::read_regular(path, limit).map_err(|error| match error {
        crate::io::ReadError::Io(_) => "artifact-io".into(),
        crate::io::ReadError::Limit => "artifact-byte-limit".into(),
    })
}
#[cfg(any(feature = "cpu", test))]
pub(crate) fn parse(bytes: &[u8], limit: usize) -> Result<Json> {
    if bytes.len() > limit {
        return Err("artifact-byte-limit".into());
    }
    super::json::preflight(bytes, 200_000, 32_768).map_err(|e| match e {
        super::json::Error::Depth => "artifact-json-depth",
        super::json::Error::Structure => "tree-limit",
        super::json::Error::Object => "artifact-json-kind",
        super::json::Error::Scalar => "tree-kind",
        super::json::Error::Syntax => "artifact-json",
    })?;
    let v = serde_json::from_slice(bytes).map_err(|_| "artifact-json")?;
    zkc_format::logical::tree_size(&v).map_err(|e| e.to_string())?;
    Ok(v)
}
#[cfg(feature = "cpu")]
pub(crate) fn list(v: &Json) -> Result<&[Json]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or("artifact-array".into())
}
#[cfg(feature = "cpu")]
pub(crate) fn array(v: &Json, n: usize) -> Result<&[Json]> {
    let a = list(v)?;
    if a.len() != n {
        return Err("artifact-record".into());
    }
    Ok(a)
}
pub(crate) fn text(v: &Json) -> Result<&str> {
    v.as_str().ok_or("artifact-string".into())
}
#[cfg(any(feature = "cpu", test))]
pub(crate) fn natural(v: &Json) -> Result<u64> {
    zkc_format::logical::natural_index(text(v)?).map_err(|e| e.to_string())
}
pub(crate) fn unhex(v: &Json) -> Result<Vec<u8>> {
    let s = text(v)?;
    if s.len() > INPUT_LIMIT * 2
        || !s.len().is_multiple_of(2)
        || !s
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err("artifact-hex".into());
    }
    Ok(s.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| {
            let digit = |b| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
            digit(p[0]) * 16 + digit(p[1])
        })
        .collect())
}
pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8] = b"0123456789abcdef";
    let mut out = vec![0; bytes.len() * 2];
    for (pair, &b) in out.as_chunks_mut::<2>().0.iter_mut().zip(bytes) {
        *pair = [DIGITS[(b >> 4) as usize], DIGITS[(b & 15) as usize]];
    }
    String::from_utf8(out).expect("hex digits are ASCII")
}

/// Decode an independently selected canonical SHA-256 identity.
pub(crate) fn digest(value: &str) -> Result<[u8; 32]> {
    if value.len() != 64 {
        return Err("host-digest".into());
    }
    unhex(&Json::String(value.into()))?
        .try_into()
        .map_err(|_| "host-digest".into())
}
#[cfg(feature = "cpu")]
pub(crate) fn hash(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    hex(&Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn hex_preserves_lowercase_wire_bytes() {
        for bytes in [vec![], (0..=255).collect(), vec![255; 65536]] {
            let expected: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
            let encoded = hex(&bytes);
            assert_eq!(encoded, expected);
            assert_eq!(unhex(&Json::String(encoded)).unwrap(), bytes);
        }
    }
    #[test]
    fn ingress_is_bounded_before_json_and_canonical_afterwards() {
        assert_eq!(parse(&[b'['; 66], 100).unwrap_err(), "artifact-json-depth");
        assert_eq!(parse(b"{}", 100).unwrap_err(), "artifact-json-kind");
        assert_eq!(parse(br#"["x",0]"#, 100).unwrap_err(), "tree-kind");
        assert_eq!(parse(b"[]junk", 100).unwrap_err(), "artifact-json");
        assert_eq!(parse(b"[]", 1).unwrap_err(), "artifact-byte-limit");
        assert!(parse(br#"["[\\\"{",[]]"#, 100).is_ok());
        for bad in ["0", "AA", "0x12", "gg", " 00", "é"] {
            assert_eq!(unhex(&json!(bad)).unwrap_err(), "artifact-hex");
        }
        assert_eq!(unhex(&json!("00abff")).unwrap(), [0, 171, 255]);
        for bad in ["", "01", "+1", " 1", "18446744073709551616"] {
            assert!(natural(&json!(bad)).is_err());
        }
        assert_eq!(natural(&json!("18446744073709551615")).unwrap(), u64::MAX);
    }

    #[test]
    fn parser_preserves_generated_trees_and_refuses_malformed_json() {
        use crate::io::json::corpus;
        for (value, bytes) in corpus::trees() {
            let bytes = bytes.as_slice();
            assert_eq!(parse(bytes, INPUT_LIMIT).unwrap(), value);
        }
        for &bytes in corpus::ESCAPED {
            assert_eq!(
                parse(bytes, INPUT_LIMIT).unwrap(),
                serde_json::from_slice::<serde_json::Value>(bytes).unwrap()
            );
        }
        for &bytes in corpus::MALFORMED {
            assert!(parse(bytes, INPUT_LIMIT).is_err(), "{bytes:?}");
        }
        for leaf in ["[]", "\"x\""] {
            for wrappers in [64, 65] {
                let text = "[".repeat(wrappers) + leaf + &"]".repeat(wrappers);
                let bytes = text.as_bytes();
                assert_eq!(parse(bytes, INPUT_LIMIT).is_ok(), wrappers == 64);
            }
        }
    }
}
