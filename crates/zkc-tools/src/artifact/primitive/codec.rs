use super::Result;
use serde_json::{Value as Json, json};
use zkc_arkworks::{Bounds, Scalar, decode_scalar};

pub(super) const MAX_BYTES: usize = 16 * 1024 * 1024;
pub(super) const MAX_GROUPS: usize = 4096;
pub(super) fn bounds() -> Bounds {
    Bounds::new(16, 1 << 16, MAX_BYTES, 1 << 20)
}
pub(super) fn array(value: &Json) -> Result<&[Json]> {
    value.as_array().map(Vec::as_slice).ok_or("primitive-array")
}
pub(super) fn text(value: &Json) -> Result<&str> {
    value.as_str().ok_or("primitive-string")
}
pub(super) fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(2 * bytes.len());
    for b in bytes {
        result.push(DIGITS[(b >> 4) as usize] as char);
        result.push(DIGITS[(b & 15) as usize] as char);
    }
    result
}
pub(super) fn unhex(value: &str) -> Result<Vec<u8>> {
    if !value.len().is_multiple_of(2) || value.len() / 2 > MAX_BYTES {
        return Err("primitive-hex-limit");
    }
    let nibble = |byte| match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err("primitive-hex"),
    };
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok(nibble(pair[0])? * 16 + nibble(pair[1])?))
        .collect()
}
pub(super) fn value(kind: &str, tag: u8, payload: &[u8]) -> Json {
    let mut bytes = b"ZKCV\x01".to_vec();
    bytes.push(tag);
    bytes.extend_from_slice(payload);
    json!([kind, hex(&bytes)])
}
pub(super) fn boolean(value_: bool) -> Json {
    value("bool", 5, &[u8::from(value_)])
}
pub(super) fn payload(bytes: &[u8], tag: u8) -> Result<&[u8]> {
    if bytes.len() < 6 || &bytes[..5] != b"ZKCV\x01" || bytes[5] != tag {
        return Err("primitive-wire-header");
    }
    Ok(&bytes[6..])
}
pub(super) fn field(bytes: &[u8]) -> Result<Scalar> {
    decode_scalar(payload(bytes, 1)?).map_err(|_| "primitive-field")
}
/// Independent canonical public-matrix validation for the Lean interpreter.
/// This performs no matrix arithmetic or native-backend calls.
pub(super) fn matrix(identity: zkc_runtime::interactive::Identity, bytes: &[u8]) -> Result<()> {
    use zkc_runtime::interactive::Identity;
    let (tag, width) = match identity {
        Identity::Bls12381Fr => (23, 32),
        Identity::Ristretto255Scalar => (24, 32),
        Identity::KoalaBear => (25, 4),
        Identity::Bn254Fr => (45, 32),
        _ => return Err("primitive-nominal-type"),
    };
    let body = payload(bytes, tag)?;
    let number = |b: &[u8]| -> Result<usize> {
        Ok(u32::from_le_bytes(b.try_into().map_err(|_| "primitive-wire-length")?) as usize)
    };
    if body.len() < 12 {
        return Err("primitive-wire-length");
    }
    let rows = number(&body[..4])?;
    let columns = number(&body[4..8])?;
    let nnz = number(&body[8..12])?;
    if rows > 65536 || columns > 65536 || nnz > 1 << 20 {
        return Err("primitive-matrix-limit");
    }
    if rows.checked_mul(columns).is_none_or(|cells| nnz > cells)
        || nnz.checked_mul(8 + width).and_then(|n| n.checked_add(12)) != Some(body.len())
    {
        return Err("primitive-wire-length");
    }
    let mut previous = None;
    for e in body[12..].chunks_exact(8 + width) {
        let row = number(&e[..4])?;
        let column = number(&e[4..8])?;
        if row >= rows || column >= columns || previous.is_some_and(|p| p >= (row, column)) {
            return Err("primitive-matrix-order");
        }
        let a = &e[8..];
        if a.iter().all(|b| *b == 0) {
            return Err("primitive-matrix-zero");
        }
        match identity {
            Identity::Bls12381Fr => {
                decode_scalar(a).map_err(|_| "primitive-field")?;
            }
            Identity::Bn254Fr => {
                zkc_arkworks::bn254::decode_scalar(a).map_err(|_| "primitive-field")?;
            }
            Identity::Ristretto255Scalar => {
                let a = a.try_into().map_err(|_| "primitive-field")?;
                if !bool::from(curve25519_dalek::scalar::Scalar::from_canonical_bytes(a).is_some())
                {
                    return Err("primitive-field");
                }
            }
            Identity::KoalaBear => {
                if number(a)? >= 2_130_706_433 {
                    return Err("primitive-field");
                }
            }
            _ => return Err("primitive-nominal-type"),
        }
        previous = Some((row, column));
    }
    Ok(())
}
pub(super) fn counted(bytes: &[u8], tag: u8, width: usize, limit: usize) -> Result<&[u8]> {
    let body = payload(bytes, tag)?;
    let prefix = body.get(..4).ok_or("primitive-wire-length")?;
    let count =
        u32::from_le_bytes(prefix.try_into().map_err(|_| "primitive-wire-length")?) as usize;
    if count > limit || count.checked_mul(width).and_then(|n| n.checked_add(4)) != Some(body.len())
    {
        return Err("primitive-wire-length");
    }
    Ok(&body[4..])
}
