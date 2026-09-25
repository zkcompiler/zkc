//! Bounded ingress shared by construction and application inputs.
use serde_json::Value as Json;
use std::path::Path;
pub(super) type Result<T> = std::result::Result<T, String>;
pub(super) const INPUT_LIMIT: usize = 16 * 1024 * 1024;
pub(super) fn read(path: impl AsRef<Path>, limit: usize) -> Result<Vec<u8>> {
    crate::host::io::read_bounded(path, limit).map_err(|error| match error {
        crate::host::io::ReadError::Io(_) => "artifact-io".into(),
        crate::host::io::ReadError::Limit => "artifact-byte-limit".into(),
    })
}
pub(super) fn parse(bytes: &[u8], limit: usize) -> Result<Json> {
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
    zkc_runtime::logical::encode_tree(&v).map_err(|e| e.to_string())?;
    Ok(v)
}
pub(super) fn list(v: &Json) -> Result<&[Json]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or("artifact-array".into())
}
pub(super) fn array(v: &Json, n: usize) -> Result<&[Json]> {
    let a = list(v)?;
    if a.len() != n {
        return Err("artifact-record".into());
    }
    Ok(a)
}
pub(super) fn text(v: &Json) -> Result<&str> {
    v.as_str().ok_or("artifact-string".into())
}
pub(super) fn natural(v: &Json) -> Result<u64> {
    zkc_runtime::logical::natural_index(text(v)?).map_err(|e| e.to_string())
}
pub(super) fn unhex(v: &Json) -> Result<Vec<u8>> {
    let s = text(v)?;
    if s.len() > INPUT_LIMIT * 2
        || !s.len().is_multiple_of(2)
        || !s
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err("artifact-hex".into());
    }
    s.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| {
            let digit = |b| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
            Ok(digit(p[0]) * 16 + digit(p[1]))
        })
        .collect()
}
pub fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(DIGITS[(b >> 4) as usize] as char);
        s.push(DIGITS[(b & 15) as usize] as char);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
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
}
