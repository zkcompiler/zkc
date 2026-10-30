//! Bounded graph syntax for existing native variant spellings.
//! This is independent of the structured logical-types interchange vocabulary.
use serde_json::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VariantError(pub &'static str);
impl std::fmt::Display for VariantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "variant:{}", self.0)
    }
}
impl std::error::Error for VariantError {}
type Result<T> = std::result::Result<T, VariantError>;
fn invalid(detail: &'static str) -> VariantError {
    VariantError(detail)
}
fn canonical_decimal(s: &str) -> bool {
    !s.is_empty() && (s.len() == 1 || !s.starts_with('0')) && s.bytes().all(|b| b.is_ascii_digit())
}

const MAX_SPELLING: usize = 256 * 1024;
const MAX_NODES: usize = 16384;
const MAX_EXPANDED_BYTES: usize = 8 * 1024 * 1024;
const MAX_EXPANDED_NODES: usize = 200000;

/// Pack an arrays-and-ASCII-strings tree as the canonical native variant graph.
/// This checks graph syntax and expansion bounds, not native payload admission.
pub fn variant_spelling(tree: &Value) -> Result<String> {
    fn intern(
        tree: &Value,
        nodes: &mut Vec<Value>,
        ids: &mut std::collections::BTreeMap<String, usize>,
        visits: &mut usize,
        encoded_bytes: &mut usize,
        depth: usize,
    ) -> Result<usize> {
        *visits += 1;
        if depth >= 64 || *visits > MAX_EXPANDED_NODES {
            return Err(invalid("graph-limit"));
        }
        let node = match tree {
            Value::String(s)
                if s.len() <= MAX_SPELLING && s.bytes().all(|c| (32..=126).contains(&c)) =>
            {
                tree.clone()
            }
            Value::Array(a) => Value::Array(
                a.iter()
                    .map(|v| {
                        intern(v, nodes, ids, visits, encoded_bytes, depth + 1)
                            .map(|n| Value::String(n.to_string()))
                    })
                    .collect::<Result<_>>()?,
            ),
            _ => return Err(invalid("graph-node")),
        };
        let key = serde_json::to_string(&node).expect("serializing a JSON value");
        if let Some(id) = ids.get(&key) {
            return Ok(*id);
        }
        if nodes.len() >= MAX_NODES {
            return Err(invalid("graph-limit"));
        }
        *encoded_bytes += key.len() + 1;
        if *encoded_bytes > (MAX_SPELLING - 8) / 2 {
            return Err(invalid("limit"));
        }
        let id = nodes.len();
        ids.insert(key, id);
        nodes.push(node);
        Ok(id)
    }
    let mut nodes = Vec::new();
    intern(tree, &mut nodes, &mut Default::default(), &mut 0, &mut 0, 0)?;
    let bytes = serde_json::to_vec(&serde_json::json!(["zkc.variant/0", nodes]))
        .expect("serializing a JSON value");
    if bytes.len() > (MAX_SPELLING - 8) / 2 {
        return Err(invalid("limit"));
    }
    let mut spelling = String::from("variant:");
    use std::fmt::Write;
    for b in bytes {
        write!(spelling, "{b:02x}").expect("writing to String");
    }
    Ok(spelling)
}
/// Decode and require exact canonical spelling of an existing native variant
/// graph. Native type formation and source schema checks belong to consumers.
pub fn variant_tree(spelling: &str) -> Result<Value> {
    if spelling.len() > MAX_SPELLING {
        return Err(invalid("limit"));
    }
    let hex = spelling
        .strip_prefix("variant:")
        .ok_or_else(|| invalid("hex"))?;
    if hex.is_empty()
        || !hex.len().is_multiple_of(2)
        || !hex
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid("hex"));
    }
    let bytes: Vec<_> = hex
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| {
            let digit = |b| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
            digit(p[0]) * 16 + digit(p[1])
        })
        .collect();
    let json: Value = serde_json::from_slice(&bytes).map_err(|_| invalid("json"))?;
    let root = json
        .as_array()
        .filter(|a| a.len() == 2)
        .ok_or_else(|| invalid("descriptor"))?;
    if root[0].as_str() != Some("zkc.variant/0") {
        return Err(invalid("format"));
    }
    // A graph with no node is malformed; only a graph past the node budget
    // is over the limit.
    let nodes = root[1]
        .as_array()
        .filter(|a| !a.is_empty())
        .ok_or_else(|| invalid("descriptor"))?;
    if nodes.len() > MAX_NODES {
        return Err(invalid("graph-limit"));
    }
    let mut values: Vec<Value> = Vec::new();
    let mut sizes = Vec::new();
    let mut counts = Vec::new();
    let mut depths = Vec::new();
    let (mut total_bytes, mut total_nodes) = (0, 0);
    let byte_budget = MAX_EXPANDED_BYTES.min(512 * spelling.len());
    let node_budget = MAX_EXPANDED_NODES.min(512 * spelling.len());
    for node in nodes {
        let (mut size, mut count, mut depth) = (2, 1, 1);
        let decoded = match node {
            Value::String(_) => {
                size = serde_json::to_vec(node)
                    .expect("serializing a JSON value")
                    .len();
                node.clone()
            }
            Value::Array(refs) => {
                let mut indices = Vec::new();
                for r in refs {
                    let s = r
                        .as_str()
                        .filter(|s| canonical_decimal(s))
                        .ok_or_else(|| invalid("graph-reference"))?;
                    let index: usize = s.parse().map_err(|_| invalid("graph-reference"))?;
                    if index >= values.len() {
                        return Err(invalid("graph-reference"));
                    }
                    size += sizes[index] + usize::from(!indices.is_empty());
                    count += counts[index];
                    depth = depth.max(depths[index] + 1);
                    if size > byte_budget || count > node_budget || depth > 64 {
                        return Err(invalid("graph-limit"));
                    }
                    indices.push(index);
                }
                if total_bytes + size > byte_budget || total_nodes + count > node_budget {
                    return Err(invalid("graph-limit"));
                }
                Value::Array(indices.into_iter().map(|i| values[i].clone()).collect())
            }
            _ => return Err(invalid("graph-node")),
        };
        total_bytes += size;
        total_nodes += count;
        if total_bytes > byte_budget || total_nodes > node_budget {
            return Err(invalid("graph-limit"));
        }
        values.push(decoded);
        sizes.push(size);
        counts.push(count);
        depths.push(depth);
    }
    let tree = values.pop().expect("the node list is not empty");
    if variant_spelling(&tree)? != spelling {
        return Err(invalid("canonical"));
    }
    Ok(tree)
}
