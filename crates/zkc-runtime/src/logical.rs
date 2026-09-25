//! Versioned logical construction encoding. Codec validity is not evidence that
//! an origin or root corresponds to an admitted original source/descriptor.
use crate::interactive::{Limits, Origin, PathElement};
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

/// Encode arrays/strings with tags 1/0, u64 LE counts/UTF-8 byte lengths.
/// Preflight the whole tree before allocating; construction-tree ceilings apply.
pub fn encode_tree(tree: &Value) -> Result<Vec<u8>> {
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
    let n = measure(tree, 0, &mut 0)?;
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
/// Five original source identifiers, in the exact positional contract order.
/// This validates their representation only, not construction correspondence.
pub fn validate_source_attributes(attrs: &[String]) -> Result<()> {
    if attrs.len() != 5
        || attrs.iter().any(|s| {
            s.is_empty()
                || s.len() > 128
                || !s
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
        })
    {
        return Err(CodecError("source-attributes"));
    }
    Ok(())
}
fn origin(origin: &Origin, attrs: &[String], tag: &str) -> Result<Vec<u8>> {
    validate_source_attributes(attrs)?;
    if origin.path.len() > Limits::STACK_DEPTH {
        return Err(CodecError("tree-limit"));
    }
    // Origin is public host data: bound every string BEFORE json! clones it.
    let bounded = |s: &str| s.len() <= Limits::STRING_BYTES;
    if !bounded(&origin.entry)
        || !bounded(&origin.instance)
        || origin.path.iter().any(|p| match p {
            PathElement::Match { site, alternative } => !bounded(site) || !bounded(alternative),
            PathElement::Call { site, instance } => !bounded(site) || !bounded(instance),
            PathElement::Loop { site, .. }
            | PathElement::Conditional { site, .. }
            | PathElement::For { site, .. } => !bounded(site),
        })
    {
        return Err(CodecError("tree-limit"));
    }
    // Runtime fields must retain ORIGINAL entry/instance/call/loop identities.
    // Session, executor profile/role and local function frame are intentionally absent.
    let path = origin
        .path
        .iter()
        .map(|p| match p {
            PathElement::Match { site, alternative } => json!(["match", site, alternative]),
            PathElement::Conditional { site, taken } => {
                json!(["if", site, if *taken { "then" } else { "else" }])
            }
            PathElement::For { site, index } => json!(["for", site, index.to_string()]),
            PathElement::Call { site, instance } => json!(["call", site, instance]),
            PathElement::Loop { site, iteration } => json!(["loop", site, iteration.to_string()]),
        })
        .collect::<Vec<_>>();
    let mut event = vec![Value::String(tag.into())];
    event.extend(attrs.iter().cloned().map(Value::String));
    encode_tree(&json!([
        "zkc.logical-origin/1",
        origin.entry,
        origin.instance,
        path,
        event
    ]))
}
/// `[protocol, message site, schema, source sender, source receiver]`.
pub fn message_origin(runtime_origin: &Origin, attrs: &[String]) -> Result<Vec<u8>> {
    origin(runtime_origin, attrs, "message")
}
/// `[protocol, local call site, function, operation site, source role]`.
pub fn challenge_origin(runtime_origin: &Origin, attrs: &[String]) -> Result<Vec<u8>> {
    origin(runtime_origin, attrs, "challenge")
}
