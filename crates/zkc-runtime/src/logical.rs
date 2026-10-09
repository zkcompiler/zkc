//! Canonical logical construction encoding. Codec validity is not evidence that
//! an origin or root corresponds to an admitted original source/descriptor.
use serde_json::{Value, json};

/// Construction trees contain public wire hex as well as source identifiers.
/// These limits do not change the separate source admission limits.
pub struct TreeLimits;
impl TreeLimits {
    pub const BYTES: usize = 16 * 1024 * 1024;
    pub const STRING_BYTES: usize = Self::BYTES;
    pub const NODES: usize = 200_000;
    pub const ARRAY_LENGTH: usize = 32_768;
    pub const DEPTH: usize = 64;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodecError(pub &'static str);
impl std::fmt::Display for CodecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for CodecError {}
type Result<T> = std::result::Result<T, CodecError>;

/// Check the complete tree's grammar and bounds without allocating its encoding.
pub fn tree_size(tree: &Value) -> Result<usize> {
    fn measure(v: &Value, depth: usize, nodes: &mut usize) -> Result<usize> {
        *nodes += 1;
        if depth > TreeLimits::DEPTH || *nodes > TreeLimits::NODES {
            return Err(CodecError("tree-limit"));
        }
        let n = match v {
            Value::String(s) if s.len() <= TreeLimits::STRING_BYTES => 9 + s.len(),
            Value::Array(a) if a.len() <= TreeLimits::ARRAY_LENGTH => {
                let mut n = 9usize;
                for v in a {
                    n = n
                        .checked_add(measure(v, depth + 1, nodes)?)
                        .ok_or(CodecError("tree-limit"))?;
                }
                n
            }
            Value::String(_) | Value::Array(_) => return Err(CodecError("tree-limit")),
            _ => return Err(CodecError("tree-kind")),
        };
        if n > TreeLimits::BYTES {
            return Err(CodecError("tree-limit"));
        }
        Ok(n)
    }
    measure(tree, 0, &mut 0)
}

/// Encode arrays/strings with tags 1/0, u64 LE counts/UTF-8 byte lengths.
/// Preflight the whole tree before allocating; construction-tree ceilings apply.
pub fn encode_tree(tree: &Value) -> Result<Vec<u8>> {
    fn write(v: &Value, out: &mut Vec<u8>) {
        match v {
            Value::String(s) => {
                out.push(0);
                out.extend((s.len() as u64).to_le_bytes());
                out.extend(s.as_bytes());
            }
            Value::Array(a) => {
                out.push(1);
                out.extend((a.len() as u64).to_le_bytes());
                for v in a {
                    write(v, out);
                }
            }
            _ => unreachable!("preflight"),
        }
    }
    let n = tree_size(tree)?;
    let mut out = Vec::new();
    out.try_reserve_exact(n)
        .map_err(|_| CodecError("tree-allocation"))?;
    write(tree, &mut out);
    Ok(out)
}

/// Exact bounded decoder. Invalid tags, UTF-8, truncation, excess nesting and
/// trailing bytes are rejected. All attacker counts are bounded before reserve.
pub fn decode_tree(bytes: &[u8]) -> Result<Value> {
    if bytes.len() > TreeLimits::BYTES {
        return Err(CodecError("tree-limit"));
    }
    fn read(input: &mut &[u8], depth: usize, nodes: &mut usize) -> Result<Value> {
        *nodes += 1;
        if depth > TreeLimits::DEPTH || *nodes > TreeLimits::NODES {
            return Err(CodecError("tree-limit"));
        }
        if input.len() < 9 {
            return Err(CodecError("tree-truncated"));
        }
        let tag = input[0];
        let n = usize::try_from(u64::from_le_bytes(input[1..9].try_into().expect("width")))
            .map_err(|_| CodecError("tree-limit"))?;
        *input = &input[9..];
        match tag {
            0 => {
                if n > TreeLimits::STRING_BYTES {
                    return Err(CodecError("tree-limit"));
                }
                let s = input.get(..n).ok_or(CodecError("tree-truncated"))?;
                let s = std::str::from_utf8(s).map_err(|_| CodecError("tree-utf8"))?;
                let value = Value::String(s.to_owned());
                *input = &input[n..];
                Ok(value)
            }
            1 => {
                if n > TreeLimits::ARRAY_LENGTH || n > TreeLimits::NODES - *nodes {
                    return Err(CodecError("tree-limit"));
                }
                if n > input.len() / 9 {
                    return Err(CodecError("tree-truncated"));
                }
                let mut values = Vec::new();
                values
                    .try_reserve_exact(n)
                    .map_err(|_| CodecError("tree-allocation"))?;
                for _ in 0..n {
                    values.push(read(input, depth + 1, nodes)?);
                }
                Ok(Value::Array(values))
            }
            _ => Err(CodecError("tree-tag")),
        }
    }
    let mut input = bytes;
    let value = read(&mut input, 0, &mut 0)?;
    if !input.is_empty() {
        return Err(CodecError("tree-trailing"));
    }
    Ok(value)
}

/// Canonical u64 natural. Vector bounds are checked separately before indexing.
pub fn natural_index(s: &str) -> Result<u64> {
    if s.is_empty()
        || s.len() > 20
        || (s.len() > 1 && s.starts_with('0'))
        || !s.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(CodecError("natural-index"));
    }
    s.parse().map_err(|_| CodecError("natural-index"))
}
pub fn indexed_native_origin(attrs: &[String], kind: &str, indices: &[u64]) -> Result<Vec<u8>> {
    let encoded = native_origin_template(attrs, kind)?;
    let mut tree = decode_tree(&encoded)?;
    let depth = tree[2]
        .as_array()
        .ok_or(CodecError("native-origin"))?
        .iter()
        .filter(|step| step[0] == "repeat")
        .count();
    if indices.len() != depth || indices.len() > 64 {
        return Err(CodecError("native-origin-coordinates"));
    }
    tree[0] = json!("zkc.native-origin/2");
    tree[3] = json!(indices.iter().map(u64::to_string).collect::<Vec<_>>());
    if tree_size(&tree)? > 4096 {
        return Err(CodecError("native-origin-limit"));
    }
    encode_tree(&tree)
}
/// A source template contains ordered static apply/repeat steps and no dynamic
/// coordinates. Coordinates are explicit operands of its indexed transition.
pub fn native_origin_template(attrs: &[String], kind: &str) -> Result<Vec<u8>> {
    if attrs.len() != 1 {
        return Err(CodecError("native-origin"));
    }
    let hex = attrs[0].as_bytes();
    if hex.is_empty()
        || hex.len() > 4096
        || !hex.len().is_multiple_of(2)
        || !hex
            .iter()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
    {
        return Err(CodecError("native-origin"));
    }
    let digit = |b: u8| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
    let bytes: Vec<u8> = hex
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| digit(p[0]) * 16 + digit(p[1]))
        .collect();
    let tree = decode_tree(&bytes)?;
    let parts = tree.as_array().ok_or(CodecError("native-origin"))?;
    let name = |v: &Value| {
        v.as_str().is_some_and(|s| {
            !s.is_empty() && s.len() <= 128 && s.bytes().all(|b| (33..=126).contains(&b))
        })
    };
    let fields = match kind {
        "query" => 7,
        "message" => 6,
        _ => 0,
    };
    if parts.len() != 5
        || parts[0] != "zkc.native-origin-template/1"
        || !name(&parts[1])
        || !parts[2].as_array().is_some_and(|p| {
            p.len() <= 64
                && p.iter().all(|step| {
                    step.as_array().is_some_and(|a| {
                        a.len() == 3
                            && (a[0] == "apply" || a[0] == "repeat")
                            && name(&a[1])
                            && name(&a[2])
                    })
                })
        })
        || !parts[3].as_array().is_some_and(Vec::is_empty)
        || fields == 0
        || !parts[4]
            .as_array()
            .is_some_and(|e| e.len() == fields && e[0] == kind && e[1..].iter().all(name))
    {
        return Err(CodecError("native-origin"));
    }
    if kind == "query"
        && !parts[4][3]
            .as_str()
            .and_then(|s| s.strip_prefix("input_"))
            .is_some_and(|n| natural_index(n).is_ok())
    {
        return Err(CodecError("native-origin"));
    }
    Ok(bytes)
}
