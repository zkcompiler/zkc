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
}
impl VariantDescriptor {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }
    pub fn alternatives(&self) -> &[VariantAlternative] {
        &self.alternatives
    }
    /// Decode the opaque nominal identity for a metadata consumer. This uses the
    /// same bounded graph decoder as admission and allocates a temporary view;
    /// callers inspecting many types should cache the result. It grants no
    /// permissions beyond this descriptor's already checked payload types.
    /// An inline payload may fit its containing descriptor's expansion bound but
    /// exceed its own spelling's bound. Independent inspection then refuses.
    pub fn nominal_identity(&self) -> Result<Value> {
        match zkc_format::types::variant_tree(&self.spelling).map_err(|error| invalid(error.0))? {
            Value::Array(mut root) if root.len() == 2 => Ok(root.swap_remove(0)),
            _ => Err(invalid("descriptor")),
        }
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
        let json = zkc_format::types::variant_tree(spelling).map_err(|error| invalid(error.0))?;
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
                    let spelling = zkc_format::types::variant_spelling(ty)
                        .map_err(|error| invalid(error.0))?;
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
