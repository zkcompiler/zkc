//! Self-contained local sum descriptors. Construction is checked and immutable;
//! nominal identity includes every ordered alternative and payload type.
use super::{AdmissionError, ErrorCode, LogicalType, decode::valid_name};
use serde_json::Value;
use std::{collections::BTreeSet, sync::Arc};

type Result<T> = std::result::Result<T, AdmissionError>;
fn invalid(detail: &str) -> AdmissionError {
    AdmissionError {
        code: ErrorCode::Type,
        detail: format!("variant:{detail}"),
    }
}
const MAX_SPELLING: usize = 256 * 1024;
const MAX_NODES: usize = 16384;
const MAX_EXPANDED_BYTES: usize = 8 * 1024 * 1024;
const MAX_EXPANDED_NODES: usize = 200000;

fn pack(tree: &Value) -> Result<String> {
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
    let bytes = serde_json::to_vec(&serde_json::json!(["zkc.variant/1", nodes]))
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
fn unpack(spelling: &str) -> Result<Value> {
    if spelling.len() > MAX_SPELLING {
        return Err(invalid("limit"));
    }
    let hex = spelling
        .strip_prefix("variant:")
        .expect("only variant spellings are unpacked");
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
    if root[0].as_str() != Some("zkc.variant/1") {
        return Err(invalid("version"));
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
                        .filter(|s| super::decode::canonical_decimal(s))
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
    if pack(&tree)? != spelling {
        return Err(invalid("canonical"));
    }
    Ok(tree)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariantAlternative {
    label: String,
    payload: Box<[LogicalType]>,
}
impl VariantAlternative {
    pub fn label(&self) -> &str {
        &self.label
    }
    pub fn payload(&self) -> &[LogicalType] {
        &self.payload
    }
}
#[derive(Clone, Debug)]
pub struct VariantDescriptor {
    spelling: String,
    alternatives: Box<[VariantAlternative]>,
    retained_bytes: usize,
    duplicable: bool,
    discardable: bool,
    native_message_data: bool,
    program_port: bool,
    default_representation: Result<()>,
}
impl VariantDescriptor {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }
    pub fn alternatives(&self) -> &[VariantAlternative] {
        &self.alternatives
    }
    /// Stable conservative storage charge, including shared nested descriptors.
    /// This profile deliberately does not expose allocator capacities to the
    /// portable reference machine. Closed arrays use exact-length backing; each node reserves its metadata.
    pub fn retained_bytes(&self) -> usize {
        self.retained_bytes
    }
    pub fn is_duplicable(&self) -> bool {
        self.duplicable
    }
    pub fn is_discardable(&self) -> bool {
        self.discardable
    }
    pub(super) fn is_native_message_data(&self) -> bool {
        self.native_message_data
    }
    pub(super) fn is_program_port(&self) -> bool {
        self.program_port
    }
    pub(super) fn default_representation(&self) -> Result<()> {
        self.default_representation.clone()
    }
    fn compute_retained_bytes(&self) -> usize {
        const {
            assert!(std::mem::size_of::<LogicalType>() <= 256);
        }
        const {
            assert!(std::mem::size_of::<VariantAlternative>() <= 64);
        }
        const {
            assert!(std::mem::size_of::<Self>() <= 256);
        }
        let size = (|| {
            let mut bytes = 512usize.checked_add(self.spelling.len().checked_mul(4)?)?;
            bytes = bytes.checked_add(self.alternatives.len().checked_mul(256)?)?;
            for arm in &self.alternatives {
                bytes = bytes.checked_add(arm.payload.len().checked_mul(256)?)?;
                for ty in &arm.payload {
                    bytes = bytes.checked_add(ty.descriptor_bytes())?;
                }
            }
            Some(bytes)
        })();
        size.unwrap_or(usize::MAX)
    }
    pub(super) fn parse(
        spelling: &str,
        depth: usize,
        budget: &mut super::structural::ParseBudget,
    ) -> Result<Arc<Self>> {
        // Refuse a ninth constructor before expanding its descriptor graph.
        if depth >= super::TYPE_DEPTH_LIMIT {
            return Err(invalid("limit"));
        }
        if let Some(ty) = budget.cached(spelling, depth, true)? {
            return Ok(ty.variant_descriptor().expect("cached variant").clone());
        }
        let json = unpack(spelling)?;
        Self::from_tree(&json, spelling, depth, budget)
    }
    fn from_tree(
        json: &Value,
        spelling: &str,
        depth: usize,
        budget: &mut super::structural::ParseBudget,
    ) -> Result<Arc<Self>> {
        if let Some(ty) = budget.cached(spelling, depth, false)? {
            return Ok(ty.variant_descriptor().expect("cached variant").clone());
        }
        let before = budget.remaining();
        budget.node(depth)?;
        if depth >= super::TYPE_DEPTH_LIMIT {
            return Err(invalid("limit"));
        }
        let root = json
            .as_array()
            .filter(|a| a.len() == 2)
            .ok_or_else(|| invalid("descriptor"))?;
        if root[0].as_str() == Some("") {
            return Err(invalid("nominal"));
        }
        let arms = root[1]
            .as_array()
            .filter(|a| !a.is_empty() && a.len() <= 32)
            .ok_or_else(|| invalid("alternatives"))?;
        budget.allocate(512 + 4 * spelling.len() + 256 * arms.len())?;
        let mut labels = BTreeSet::new();
        let mut alternatives = Vec::new();
        for arm in arms {
            let pair = arm
                .as_array()
                .filter(|a| a.len() == 2)
                .ok_or_else(|| invalid("alternative"))?;
            let label = pair[0]
                .as_str()
                .filter(|s| valid_name(s))
                .ok_or_else(|| invalid("label"))?;
            if !labels.insert(label) {
                return Err(invalid("duplicate-label"));
            }
            let payload_json = pair[1]
                .as_array()
                .filter(|a| a.len() <= 128)
                .ok_or_else(|| invalid("payload-limit"))?;
            budget.allocate(256 * payload_json.len())?;
            let mut payload = Vec::new();
            for ty in payload_json {
                let ty = if let Some(leaf) = ty.as_str() {
                    if leaf.starts_with("variant:") || leaf.contains('@') {
                        return Err(invalid("payload"));
                    }
                    LogicalType::parse_nested(leaf, depth + 1, budget)?
                } else {
                    let spelling = pack(ty)?;
                    LogicalType::variant(Self::from_tree(ty, &spelling, depth + 1, budget)?)
                };
                payload.push(ty);
            }
            alternatives.push(VariantAlternative {
                label: label.into(),
                payload: payload.into_boxed_slice(),
            });
        }
        let mut descriptor = Self {
            spelling: spelling.into(),
            duplicable: alternatives
                .iter()
                .flat_map(|a| &a.payload)
                .all(LogicalType::is_duplicable),
            discardable: alternatives
                .iter()
                .flat_map(|a| &a.payload)
                .all(LogicalType::is_discardable),
            native_message_data: alternatives
                .iter()
                .flat_map(|a| &a.payload)
                .all(|t| t.is_duplicable() && t.is_native_message_data()),
            program_port: alternatives
                .iter()
                .flat_map(|a| &a.payload)
                .all(|t| t.is_duplicable() && t.is_program_port()),
            default_representation: alternatives
                .iter()
                .flat_map(|a| &a.payload)
                .try_for_each(|t| super::PhysicalType::default_for(t.clone()).map(|_| ())),
            alternatives: alternatives.into_boxed_slice(),
            retained_bytes: 0,
        };
        descriptor.retained_bytes = descriptor.compute_retained_bytes();
        let descriptor = Arc::new(descriptor);
        budget.remember(
            spelling,
            depth,
            LogicalType::variant(descriptor.clone()),
            before - budget.remaining(),
            false,
        );
        Ok(descriptor)
    }
}

// Canonical spelling is the complete nominal identity and layout. Avoid
// re-comparing the expanded payload structure or retaining its opaque nominal.
impl PartialEq for VariantDescriptor {
    fn eq(&self, other: &Self) -> bool {
        self.spelling == other.spelling
    }
}
impl Eq for VariantDescriptor {}
impl PartialOrd for VariantDescriptor {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for VariantDescriptor {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.spelling.cmp(&other.spelling)
    }
}
