//! Immutable nested data. Charges count the expanded value, even with Arc aliases.
use crate::{Policy, Result, Value, exhausted, refused};
use std::sync::Arc;
use zkc_runtime::interactive::{
    AttributeRule, Backing, BoundSignature, Invocation, KernelSignature, LogicalType,
    OperationBinding, PhysicalType, Value as RuntimeValue,
};

const _: () = assert!(std::mem::size_of::<Value>() <= 512);

/// Cumulative sequence traversal allowance. Failed calls never refund work.
pub(crate) struct Budget {
    pub limit: u64,
    pub spent: u64,
}
impl Default for Budget {
    fn default() -> Self {
        Self {
            limit: 16_777_216,
            spent: 0,
        }
    }
}
impl Budget {
    pub fn charge(&mut self, args: &[Value]) -> Result<()> {
        // Fixed work units proportional to the expanded input bound validation,
        // construction and backing walks. They do not count literal CPU visits.
        // Shared subtrees count each occurrence, independently of Arc refcounts.
        // Charge before the first recursive validation.
        let count = args.iter().try_fold(1usize, |n, v| add(n, nodes(v)?))?;
        let work = u64::try_from(count)
            .ok()
            .and_then(|n| n.checked_mul(3))
            .ok_or_else(|| exhausted("sequence-work"))?;
        let next = self
            .spent
            .checked_add(work)
            .filter(|n| *n <= self.limit)
            .ok_or_else(|| exhausted("sequence-work"))?;
        self.spent = next;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct Sequence {
    physical_type: PhysicalType,
    elements: Arc<[Value]>,
    nodes: usize,
    bytes: usize,
    /// Charge of the element allocation itself: its header, element slots and
    /// storage the elements keep inline. Elements' own allocations are separate.
    spine: usize,
    /// No element, at any depth, carries a capability.
    resource_free: bool,
}

fn add(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b).ok_or_else(|| exhausted("sequence-size"))
}
struct Measured {
    nodes: usize,
    bytes: usize,
    spine: usize,
    resource_free: bool,
}
/// Storage a value keeps in its own slot rather than in a shared allocation.
fn inline(value: &Value) -> usize {
    value.retained_parts(&mut |_| false)
}
fn nodes(value: &Value) -> Result<usize> {
    match value {
        Value::Sequence(v) => Ok(v.nodes),
        Value::Variant(v) => v.payload().iter().try_fold(1, |n, v| add(n, nodes(v)?)),
        _ => Ok(1),
    }
}
impl Sequence {
    pub fn new(element: LogicalType, values: Vec<Value>, policy: &Policy) -> Result<Self> {
        policy.vector_width(add(values.len(), 1)?, 512)?;
        let physical_type = PhysicalType::default_for(
            LogicalType::sequence(element.clone()).map_err(|_| refused("sequence-type"))?,
        )
        .map_err(|_| refused("sequence-representation"))?;
        let element_type =
            PhysicalType::default_for(element).map_err(|_| refused("sequence-element"))?;
        let measured = Self::measure(&physical_type, &element_type, &values)?;
        policy.vector_width(measured.nodes, 512)?;
        // Vec and the exact Arc allocation may coexist during conversion.
        policy.output(
            add(measured.bytes, crate::value::size(values.len(), 512)?)?,
            usize::MAX,
        )?;
        Ok(Self {
            physical_type,
            elements: values.into(),
            nodes: measured.nodes,
            bytes: measured.bytes,
            spine: measured.spine,
            resource_free: measured.resource_free,
        })
    }
    fn measure(ty: &PhysicalType, element: &PhysicalType, values: &[Value]) -> Result<Measured> {
        let mut count = 1;
        let mut bytes = add(256, ty.logical().descriptor_bytes())?;
        bytes = add(
            bytes,
            values
                .len()
                .checked_mul(512)
                .ok_or_else(|| exhausted("sequence-size"))?,
        )?;
        let mut spine = bytes;
        let mut resource_free = true;
        for value in values {
            if value.physical_type() != *element {
                return Err(refused("sequence-element"));
            }
            count = add(count, nodes(value)?)?;
            bytes = add(bytes, value.retained_bytes())?;
            spine = add(spine, inline(value))?;
            resource_free &= value.is_resource_free();
        }
        Ok(Measured {
            nodes: count,
            bytes,
            spine,
            resource_free,
        })
    }
    /// Report the element allocation and, when it is newly retained, each
    /// element's own allocations. Element slots belong to this allocation.
    pub(crate) fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        if shared(self.spine()) {
            for element in self.elements.iter() {
                element.retained_parts(shared);
            }
        }
        0
    }
    fn spine(&self) -> Backing {
        Backing::of(&self.elements, self.spine)
    }
    /// Contents fix validation only when no capability can be retired later.
    pub(crate) fn validation_backing(&self) -> Option<Backing> {
        self.resource_free.then(|| self.spine())
    }
    pub(crate) fn is_resource_free(&self) -> bool {
        self.resource_free
    }
    pub fn elements(&self) -> &[Value] {
        &self.elements
    }
    pub fn physical_type(&self) -> &PhysicalType {
        &self.physical_type
    }
    pub(crate) fn retained_bytes(&self) -> usize {
        self.bytes
    }
    pub(crate) fn validate(&self, policy: &Policy) -> Result<()> {
        // Fields and cached charges are private and immutable. Child payloads
        // still pass backend validation, including actual setup authorization.
        policy.vector_width(self.nodes, 512)?;
        policy.output(self.bytes, usize::MAX)
    }
}

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [spelling] = binding.arguments.as_slice() else {
        return None;
    };
    if binding.implementation != format!("native/{}", binding.contract) {
        return None;
    }
    let element = LogicalType::parse(spelling).ok()?;
    let sequence = PhysicalType::default_for(LogicalType::sequence(element.clone()).ok()?).ok()?;
    let element = PhysicalType::default_for(element).ok()?;
    let index = PhysicalType::default_for(LogicalType::parse("index").ok()?).ok()?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "sequence.empty" => (vec![], vec![sequence]),
        "sequence.append" => (vec![sequence.clone(), element], vec![sequence]),
        "sequence.length" => (vec![sequence], vec![index]),
        "sequence.at" => (vec![sequence, index], vec![element]),
        _ => return None,
    };
    Some(KernelSignature {
        inputs,
        outputs,
        attributes: AttributeRule::None,
    })
}
pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    // Each arm states the storage it newly allocates; shared storage is not new.
    let (result, allocated) = match (name, args) {
        ("sequence.empty", []) => {
            let empty = Value::Sequence(Sequence::new(
                invocation.binding.signature().outputs[0]
                    .logical()
                    .sequence_element()
                    .ok_or_else(|| refused("sequence-type"))?
                    .clone(),
                vec![],
                policy,
            )?);
            let bytes = empty.retained_bytes();
            (empty, bytes)
        }
        ("sequence.length", [Value::Sequence(v)]) => {
            let length = Value::Index(v.elements.len() as u64);
            let bytes = length.retained_bytes();
            (length, bytes)
        }
        ("sequence.at", [Value::Sequence(v), Value::Index(i)]) => {
            let index = usize::try_from(*i).map_err(|_| refused("sequence-index"))?;
            let element = v
                .elements
                .get(index)
                .ok_or_else(|| refused("sequence-index"))?
                .clone();
            (element, 0)
        }
        ("sequence.append", [Value::Sequence(v), element]) => {
            let logical = v.physical_type.logical();
            let expected = PhysicalType::default_for(
                logical
                    .sequence_element()
                    .ok_or_else(|| refused("sequence-type"))?
                    .clone(),
            )
            .map_err(|_| refused("sequence-element"))?;
            if element.physical_type() != expected {
                return Err(refused("sequence-element"));
            }
            let count = add(v.nodes, nodes(element)?)?;
            let bytes = add(add(v.bytes, 512)?, element.retained_bytes())?;
            let spine = add(add(v.spine, 512)?, inline(element))?;
            policy.vector_width(count, 512)?;
            let length = add(v.elements.len(), 1)?;
            policy.output(bytes, usize::MAX)?;
            // The new Vec and Arc of element slots can both be live; elements
            // and the old sequence are shared. This precedes any allocation.
            policy.output(
                add(spine, crate::value::size(length, 512)?)?,
                invocation.max_output_bytes,
            )?;
            let mut values = Vec::new();
            values
                .try_reserve_exact(length)
                .map_err(|_| exhausted("sequence-allocation"))?;
            values.extend_from_slice(&v.elements);
            values.push(element.clone());
            // The immutable prefix already owns exact cached charges. Only
            // the added element changes them; do not measure the prefix again.
            let appended = Value::Sequence(Sequence {
                physical_type: v.physical_type.clone(),
                elements: values.into(),
                nodes: count,
                bytes,
                spine,
                resource_free: v.resource_free && element.is_resource_free(),
            });
            (appended, 0)
        }
        _ => return Err(refused("kernel-operands")),
    };
    policy.output(result.retained_bytes(), usize::MAX)?;
    policy.output(allocated, invocation.max_output_bytes)?;
    Ok(vec![result])
}
pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/sequence.empty", "sequence.empty"),
    ("native/sequence.append", "sequence.append"),
    ("native/sequence.length", "sequence.length"),
    ("native/sequence.at", "sequence.at"),
];
