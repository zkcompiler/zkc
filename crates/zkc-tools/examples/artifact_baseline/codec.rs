//! Independent finite wire wrapper; public cryptographic codecs remain shared.
use crate::{Result, ensure};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{fs, io::Read, path::Path};
use zkc_arkworks::{Bounds, GroupPoint, Scalar, Table, decode_scalar, encode_scalar};
pub const LIMIT: usize = 16 << 20;
pub const BOUNDS: Bounds = Bounds::new(12, 4096, LIMIT, 12 * 4096);
pub fn read(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let file = fs::File::open(path)?;
    ensure(file.metadata()?.len() <= limit as u64, "file-limit")?;
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1).read_to_end(&mut bytes)?;
    ensure(bytes.len() <= limit, "file-limit")?;
    Ok(bytes)
}
pub fn json_file(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&read(path, LIMIT)?)?)
}
pub fn arr(v: &Value) -> Result<&[Value]> {
    Ok(v.as_array().ok_or("expected-array")?)
}
pub fn string(v: &Value) -> Result<&str> {
    Ok(v.as_str().ok_or("expected-string")?)
}
pub fn hash(b: &[u8]) -> String {
    hex(&Sha256::digest(b))
}
pub fn hex(b: &[u8]) -> String {
    b.iter().map(|b| format!("{b:02x}")).collect()
}
pub fn unhex(s: &str) -> Result<Vec<u8>> {
    ensure(
        s.len().is_multiple_of(2) && s.len() / 2 <= LIMIT,
        "hex-limit",
    )?;
    let nib = |b| -> Result<u8> {
        match b {
            b'0'..=b'9' => Ok(b - b'0'),
            b'a'..=b'f' => Ok(b - b'a' + 10),
            _ => Err("hex-canonical".into()),
        }
    };
    s.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| Ok(nib(p[0])? * 16 + nib(p[1])?))
        .collect()
}
pub fn wire(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut v = b"ZKCV\x01".to_vec();
    v.push(tag);
    v.extend(body);
    v
}
pub fn body(bytes: &[u8], tag: u8) -> Result<&[u8]> {
    ensure(
        bytes.len() >= 6 && bytes.len() <= LIMIT && &bytes[..5] == b"ZKCV\x01" && bytes[5] == tag,
        "wire-header",
    )?;
    Ok(&bytes[6..])
}
pub fn scalar(s: Scalar) -> Result<Vec<u8>> {
    Ok(wire(1, &encode_scalar(&s)?))
}
pub fn field(b: &[u8]) -> Result<Scalar> {
    Ok(decode_scalar(body(b, 1)?)?)
}
pub fn group(g: GroupPoint) -> Result<Vec<u8>> {
    Ok(wire(9, &g.to_bytes()?))
}
pub fn point(b: &[u8]) -> Result<GroupPoint> {
    Ok(GroupPoint::from_bytes(body(b, 9)?)?)
}
pub fn round(q: [Scalar; 3]) -> Result<Vec<u8>> {
    let mut b = Vec::with_capacity(96);
    for s in q {
        b.extend(encode_scalar(&s)?);
    }
    Ok(wire(4, &b))
}
pub fn quadratic(b: &[u8]) -> Result<[Scalar; 3]> {
    let b = body(b, 4)?;
    ensure(b.len() == 96, "round-length")?;
    Ok([
        decode_scalar(&b[..32])?,
        decode_scalar(&b[32..64])?,
        decode_scalar(&b[64..])?,
    ])
}
pub fn table(t: &Table) -> Result<Vec<u8>> {
    let mut b = (t.arity() as u32).to_le_bytes().to_vec();
    b.extend(t.to_logical_bytes(&BOUNDS)?);
    Ok(wire(2, &b))
}
pub fn decode_table(b: &[u8]) -> Result<Table> {
    let b = body(b, 2)?;
    let prefix = b.get(..4).ok_or("table-length")?;
    Ok(Table::from_logical_bytes(
        u32::from_le_bytes(prefix.try_into()?) as usize,
        &b[4..],
        &BOUNDS,
    )?)
}
/// Two passes: check the complete tree and all budgets before allocating output.
/// Only strings and arrays are admitted, root depth is zero; no JSON serialization.
pub fn logical(v: &Value) -> Result<Vec<u8>> {
    fn size(v: &Value, depth: usize, nodes: &mut usize) -> Result<usize> {
        *nodes += 1;
        ensure(depth <= 64 && *nodes <= 200_000, "logical-shape-limit")?;
        let n = match v {
            Value::String(s) => {
                ensure(s.len() <= LIMIT, "logical-string-limit")?;
                9 + s.len()
            }
            Value::Array(a) => {
                ensure(a.len() <= 32_768, "logical-array-limit")?;
                let mut n = 9;
                for item in a {
                    n += size(item, depth + 1, nodes)?;
                    ensure(n <= LIMIT, "logical-byte-limit")?;
                }
                n
            }
            _ => return Err("logical-kind".into()),
        };
        ensure(n <= LIMIT, "logical-byte-limit")?;
        Ok(n)
    }
    fn emit(v: &Value, b: &mut Vec<u8>) {
        match v {
            Value::String(s) => {
                b.push(0);
                b.extend((s.len() as u64).to_le_bytes());
                b.extend(s.as_bytes());
            }
            Value::Array(a) => {
                b.push(1);
                b.extend((a.len() as u64).to_le_bytes());
                for x in a {
                    emit(x, b);
                }
            }
            _ => unreachable!("validated tree"),
        }
    }
    let n = size(v, 0, &mut 0)?;
    let mut b = Vec::with_capacity(n);
    emit(v, &mut b);
    Ok(b)
}
pub fn write_json(p: &Path, v: &Value) -> Result<()> {
    fs::write(p, serde_json::to_vec_pretty(v)?)?;
    Ok(())
}
pub fn atomic(p: &Path, bytes: &[u8]) -> Result<()> {
    use std::io::Write;
    let mut temp = tempfile::NamedTempFile::new_in(
        p.parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new(".")),
    )?;
    temp.write_all(bytes)?;
    temp.flush()?;
    // Match the compiled producer's file-durability boundary in CLI timings.
    temp.as_file().sync_all()?;
    temp.persist(p)?;
    Ok(())
}
