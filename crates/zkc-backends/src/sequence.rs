//! Immutable nested data. Charges count the expanded value, even with Arc aliases.
use crate::{Policy, Result, Value, exhausted, refused};
use std::sync::Arc;
use zkc_runtime::interactive::{
    AttributeRule, Backing, BoundSignature, Invocation, KernelSignature, LogicalType,
    OperationBinding, PhysicalType, Retained, Value as RuntimeValue,
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
    pub fn charge(&mut self, args: &[Value], retained: Retained<'_>) -> Result<()> {
        // Charge before recursive validation. A sequence already admitted and
        // still retained by this Runner needs only its root check; unretained
        // operands keep their full expanded bound. No Arc refcount is observed.
        fn examined(value: &Value, retained: Retained<'_>) -> Result<usize> {
            match value {
                Value::Sequence(sequence)
                    if sequence
                        .validation_backing()
                        .is_some_and(|b| retained.contains(b)) =>
                {
                    Ok(1)
                }
                Value::Variant(variant) => variant
                    .payload()
                    .iter()
                    .try_fold(1, |n, v| add(n, examined(v, retained)?)),
                _ => nodes(value),
            }
        }
        let count = args
            .iter()
            .try_fold(1usize, |n, v| add(n, examined(v, retained)?))?;
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

/// Immutable sequence whose canonical tree shape depends only on its length.
/// Leaves hold four values; branches hold sixteen children. Appending copies
/// only the right edge, without observing Arc reference counts or mutating an
/// allocation already visible through another value.
#[derive(Clone, Debug)]
pub struct Sequence {
    root: Arc<Root>,
}
#[derive(Debug)]
struct Root {
    physical_type: PhysicalType,
    len: usize,
    nodes: usize,
    bytes: usize,
    resource_free: bool,
    height: usize,
    top: Option<Node>,
}
#[derive(Clone, Debug)]
enum Node {
    Leaf(Arc<[Value]>),
    Branch(Arc<[Node]>),
}
const LEAF_WIDTH: usize = 4;
const BRANCH_WIDTH: usize = 16;
const NODE_HEADER: usize = 256;
const CHILD_SLOT: usize = 32;
const VALUE_SLOT: usize = 512;
const _: () = assert!(std::mem::size_of::<Node>() <= CHILD_SLOT);

fn add(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b).ok_or_else(|| exhausted("sequence-size"))
}
fn mul(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b).ok_or_else(|| exhausted("sequence-size"))
}
fn capacity(height: usize) -> Result<usize> {
    (0..height).try_fold(LEAF_WIDTH, |n, _| mul(n, BRANCH_WIDTH))
}
/// Canonical tree overhead, excluding element slots and retained element values.
/// The codec uses the same bounded size formula before decoding any payload.
pub(crate) fn tree_overhead(len: usize) -> Result<usize> {
    let mut width = len.div_ceil(LEAF_WIDTH);
    let mut bytes = mul(width, NODE_HEADER)?;
    while width > 1 {
        let parents = width.div_ceil(BRANCH_WIDTH);
        bytes = add(
            bytes,
            add(mul(parents, NODE_HEADER)?, mul(width, CHILD_SLOT)?)?,
        )?;
        width = parents;
    }
    Ok(bytes)
}
/// Storage a value keeps in its own slot rather than in a shared allocation.
fn inline(value: &Value) -> usize {
    value.retained_parts(&mut |_| false)
}
fn nodes(value: &Value) -> Result<usize> {
    match value {
        Value::Sequence(v) => Ok(v.root.nodes),
        Value::Variant(v) => v.payload().iter().try_fold(1, |n, v| add(n, nodes(v)?)),
        _ => Ok(1),
    }
}
impl Node {
    fn backing(&self) -> Backing {
        match self {
            Self::Leaf(values) => Backing::of(
                values,
                NODE_HEADER + values.len() * VALUE_SLOT + values.iter().map(inline).sum::<usize>(),
            ),
            Self::Branch(children) => {
                Backing::of(children, NODE_HEADER + children.len() * CHILD_SLOT)
            }
        }
    }
    fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) {
        if !shared(self.backing()) {
            return;
        }
        match self {
            Self::Leaf(values) => {
                for value in values.iter() {
                    value.retained_parts(shared);
                }
            }
            Self::Branch(children) => {
                for child in children.iter() {
                    child.retained_parts(shared);
                }
            }
        }
    }
    fn validate_children(
        &self,
        retained: Retained<'_>,
        validate: &mut dyn FnMut(&Value) -> Result<()>,
    ) -> Result<()> {
        if retained.contains(self.backing()) {
            return Ok(());
        }
        match self {
            Self::Leaf(values) => values.iter().try_for_each(validate),
            Self::Branch(children) => children
                .iter()
                .try_for_each(|child| child.validate_children(retained, validate)),
        }
    }
    fn singleton(value: Value, height: usize) -> Self {
        let mut node = Self::Leaf(vec![value].into());
        for _ in 0..height {
            node = Self::Branch(vec![node].into());
        }
        node
    }
    fn append(&self, len: usize, height: usize, value: &Value) -> Self {
        match self {
            Self::Leaf(values) => {
                debug_assert_eq!(height, 0);
                debug_assert!(values.len() < LEAF_WIDTH);
                let mut next = Vec::with_capacity(values.len() + 1);
                next.extend(values.iter().cloned());
                next.push(value.clone());
                Self::Leaf(next.into())
            }
            Self::Branch(children) => {
                let child_capacity = capacity(height - 1).expect("checked tree capacity");
                let mut next = Vec::with_capacity(
                    children.len() + usize::from(len.is_multiple_of(child_capacity)),
                );
                next.extend(children.iter().cloned());
                if len.is_multiple_of(child_capacity) {
                    next.push(Self::singleton(value.clone(), height - 1));
                } else {
                    let last = next.len() - 1;
                    next[last] = next[last].append(len % child_capacity, height - 1, value);
                }
                Self::Branch(next.into())
            }
        }
    }
    /// Charges of the new right edge, including an upper bound on temporary
    /// Vec slots during conversion to exact immutable allocations.
    fn append_cost(&self, len: usize, height: usize, value: &Value) -> Result<(usize, usize)> {
        match self {
            Self::Leaf(values) => {
                let slots = mul(add(values.len(), 1)?, VALUE_SLOT)?;
                let payload = values
                    .iter()
                    .try_fold(inline(value), |n, v| add(n, inline(v)))?;
                Ok((add(add(NODE_HEADER, slots)?, payload)?, slots))
            }
            Self::Branch(children) => {
                let child_capacity = capacity(height - 1)?;
                let added = len.is_multiple_of(child_capacity);
                let (edge, scratch) = if added {
                    singleton_cost(value, height - 1)?
                } else {
                    children.last().expect("nonempty branch").append_cost(
                        len % child_capacity,
                        height - 1,
                        value,
                    )?
                };
                let slots = mul(add(children.len(), usize::from(added))?, CHILD_SLOT)?;
                Ok((add(edge, add(NODE_HEADER, slots)?)?, add(scratch, slots)?))
            }
        }
    }
}
fn singleton_cost(value: &Value, height: usize) -> Result<(usize, usize)> {
    Ok((
        add(
            add(NODE_HEADER + VALUE_SLOT, inline(value))?,
            mul(height, NODE_HEADER + CHILD_SLOT)?,
        )?,
        add(VALUE_SLOT, mul(height, CHILD_SLOT)?)?,
    ))
}
struct Iter<'a> {
    stack: Vec<&'a Node>,
    leaf: std::slice::Iter<'a, Value>,
    remaining: usize,
}
impl<'a> Iterator for Iter<'a> {
    type Item = &'a Value;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(value) = self.leaf.next() {
                self.remaining -= 1;
                return Some(value);
            }
            match self.stack.pop()? {
                Node::Leaf(values) => self.leaf = values.iter(),
                Node::Branch(children) => self.stack.extend(children.iter().rev()),
            }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}
impl ExactSizeIterator for Iter<'_> {}
impl Sequence {
    pub fn new(element: LogicalType, values: Vec<Value>, policy: &Policy) -> Result<Self> {
        policy.vector_width(add(values.len(), 1)?, VALUE_SLOT)?;
        let physical_type = PhysicalType::default_for(
            LogicalType::sequence(element.clone()).map_err(|_| refused("sequence-type"))?,
        )
        .map_err(|_| refused("sequence-representation"))?;
        let element_type =
            PhysicalType::default_for(element).map_err(|_| refused("sequence-element"))?;
        let len = values.len();
        let mut count = 1;
        let mut bytes = add(
            add(NODE_HEADER, physical_type.logical().descriptor_bytes())?,
            add(tree_overhead(len)?, mul(len, VALUE_SLOT)?)?,
        )?;
        let mut resource_free = true;
        for value in &values {
            if value.physical_type() != element_type {
                return Err(refused("sequence-element"));
            }
            count = add(count, nodes(value)?)?;
            bytes = add(bytes, value.retained_bytes())?;
            resource_free &= value.is_resource_free();
        }
        policy.vector_width(count, VALUE_SLOT)?;
        // The caller's Vec and the exact leaf allocations coexist transiently.
        policy.output(add(bytes, mul(len, VALUE_SLOT)?)?, usize::MAX)?;
        let mut height = 0;
        let mut level = values
            .chunks(LEAF_WIDTH)
            .map(|chunk| Node::Leaf(Arc::from(chunk)))
            .collect::<Vec<_>>();
        while level.len() > 1 {
            level = level
                .chunks(BRANCH_WIDTH)
                .map(|chunk| Node::Branch(Arc::from(chunk)))
                .collect();
            height += 1;
        }
        Ok(Self {
            root: Arc::new(Root {
                physical_type,
                len,
                nodes: count,
                bytes,
                resource_free,
                height,
                top: level.pop(),
            }),
        })
    }
    pub(crate) fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        if shared(self.backing())
            && let Some(top) = &self.root.top
        {
            top.retained_parts(shared);
        }
        0
    }
    fn root_bytes(&self) -> usize {
        NODE_HEADER + self.root.physical_type.logical().descriptor_bytes()
    }
    fn backing(&self) -> Backing {
        Backing::of(&self.root, self.root_bytes())
    }
    pub(crate) fn validation_backing(&self) -> Option<Backing> {
        self.root.resource_free.then(|| self.backing())
    }
    pub(crate) fn is_resource_free(&self) -> bool {
        self.root.resource_free
    }
    pub fn len(&self) -> usize {
        self.root.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn get(&self, mut index: usize) -> Option<&Value> {
        if index >= self.len() {
            return None;
        }
        let mut node = self.root.top.as_ref()?;
        let mut height = self.root.height;
        loop {
            match node {
                Node::Leaf(values) => return values.get(index),
                Node::Branch(children) => {
                    let width = capacity(height - 1).ok()?;
                    node = children.get(index / width)?;
                    index %= width;
                    height -= 1;
                }
            }
        }
    }
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Value> {
        Iter {
            stack: self.root.top.iter().collect(),
            leaf: [].iter(),
            remaining: self.len(),
        }
    }
    pub fn physical_type(&self) -> &PhysicalType {
        &self.root.physical_type
    }
    pub(crate) fn retained_bytes(&self) -> usize {
        self.root.bytes
    }
    pub(crate) fn validate(&self, policy: &Policy) -> Result<()> {
        policy.vector_width(self.root.nodes, VALUE_SLOT)?;
        policy.output(self.root.bytes, usize::MAX)
    }
    pub(crate) fn validate_children(
        &self,
        retained: Retained<'_>,
        validate: &mut dyn FnMut(&Value) -> Result<()>,
    ) -> Result<()> {
        let retained = if self.root.resource_free {
            retained
        } else {
            Retained::NONE
        };
        if let Some(top) = &self.root.top {
            top.validate_children(retained, validate)?;
        }
        Ok(())
    }
    fn append_cost(&self, value: &Value) -> Result<(usize, usize)> {
        let (edge, scratch) = match &self.root.top {
            None => singleton_cost(value, 0)?,
            Some(_) if self.len() == capacity(self.root.height)? => {
                let (edge, scratch) = singleton_cost(value, self.root.height)?;
                (
                    add(edge, NODE_HEADER + 2 * CHILD_SLOT)?,
                    add(scratch, 2 * CHILD_SLOT)?,
                )
            }
            Some(top) => top.append_cost(self.len(), self.root.height, value)?,
        };
        Ok((add(self.root_bytes(), edge)?, scratch))
    }
    pub(crate) fn append_work(&self, value: &Value) -> Option<u64> {
        // Reading the old edge and the new value handle fits this conservative
        // charge. It deliberately does not credit equal contents or uniqueness.
        self.append_cost(value)
            .ok()
            .and_then(|(bytes, _)| u64::try_from(bytes).ok())
    }
    pub(crate) fn access_work(&self) -> u64 {
        (2 * VALUE_SLOT + self.root.height * CHILD_SLOT) as u64
    }
    fn appended(&self, value: &Value, policy: &Policy, allowance: usize) -> Result<Self> {
        let expected = PhysicalType::default_for(
            self.physical_type()
                .logical()
                .sequence_element()
                .ok_or_else(|| refused("sequence-type"))?
                .clone(),
        )
        .map_err(|_| refused("sequence-element"))?;
        if value.physical_type() != expected {
            return Err(refused("sequence-element"));
        }
        let count = add(self.root.nodes, nodes(value)?)?;
        let len = add(self.len(), 1)?;
        let overhead = tree_overhead(len)? - tree_overhead(self.len())?;
        let bytes = add(
            add(add(self.root.bytes, VALUE_SLOT)?, value.retained_bytes())?,
            overhead,
        )?;
        policy.vector_width(count, VALUE_SLOT)?;
        policy.output(bytes, usize::MAX)?;
        let (fresh, scratch) = self.append_cost(value)?;
        policy.output(add(fresh, scratch)?, allowance)?;
        let (top, height) = match &self.root.top {
            None => (Node::singleton(value.clone(), 0), 0),
            Some(top) if self.len() == capacity(self.root.height)? => (
                Node::Branch(
                    vec![
                        top.clone(),
                        Node::singleton(value.clone(), self.root.height),
                    ]
                    .into(),
                ),
                self.root.height + 1,
            ),
            Some(top) => (
                top.append(self.len(), self.root.height, value),
                self.root.height,
            ),
        };
        Ok(Self {
            root: Arc::new(Root {
                physical_type: self.root.physical_type.clone(),
                len,
                nodes: count,
                bytes,
                resource_free: self.root.resource_free && value.is_resource_free(),
                height,
                top: Some(top),
            }),
        })
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
            let length = Value::Index(v.len() as u64);
            let bytes = length.retained_bytes();
            (length, bytes)
        }
        ("sequence.at", [Value::Sequence(v), Value::Index(i)]) => {
            let index = usize::try_from(*i).map_err(|_| refused("sequence-index"))?;
            let element = v
                .get(index)
                .ok_or_else(|| refused("sequence-index"))?
                .clone();
            (element, 0)
        }
        ("sequence.append", [Value::Sequence(v), element]) => (
            Value::Sequence(v.appended(element, policy, invocation.max_output_bytes)?),
            0,
        ),
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn parts(sequence: &Sequence) -> Vec<usize> {
        let mut seen = HashSet::new();
        let mut bytes = vec![];
        sequence.retained_parts(&mut |backing| {
            if !seen.insert(backing) {
                return false;
            }
            bytes.push(backing.bytes());
            true
        });
        bytes.sort_unstable();
        bytes
    }

    #[test]
    fn canonical_tree_preserves_order_shape_charges_and_prefixes() {
        let policy = Policy::default();
        let ty = LogicalType::parse("index").unwrap();
        let mut appended = Sequence::new(ty.clone(), vec![], &policy).unwrap();
        let boundaries = [
            0, 1, 3, 4, 5, 63, 64, 65, 1023, 1024, 1025, 16383, 16384, 16385,
        ];
        for n in 0..=16385 {
            if boundaries.contains(&n) {
                let direct = Sequence::new(
                    ty.clone(),
                    (0..n).map(|i| Value::Index(i as u64)).collect(),
                    &policy,
                )
                .unwrap();
                assert_eq!(appended.retained_bytes(), direct.retained_bytes(), "n={n}");
                assert_eq!(parts(&appended), parts(&direct), "n={n}");
                assert_eq!(
                    parts(&appended).iter().sum::<usize>(),
                    appended.retained_bytes()
                );
                assert_eq!(appended.iter().len(), n);
                for (i, value) in appended.iter().enumerate() {
                    assert!(matches!(value, Value::Index(v) if *v == i as u64));
                    assert!(matches!(appended.get(i), Some(Value::Index(v)) if *v == i as u64));
                }
                assert!(appended.get(n).is_none());
            }
            if n < 16385 {
                let element = Value::Index(n as u64);
                let (cost, scratch) = appended.append_cost(&element).unwrap();
                assert!(
                    appended
                        .appended(&element, &policy, cost + scratch - 1)
                        .is_err()
                );
                let next = appended
                    .appended(&element, &policy, cost + scratch)
                    .unwrap();
                if boundaries.contains(&n) {
                    let mut retained = HashSet::new();
                    appended.retained_parts(&mut |backing| retained.insert(backing));
                    let mut fresh = 0;
                    next.retained_parts(&mut |backing| {
                        if !retained.insert(backing) {
                            return false;
                        }
                        fresh += backing.bytes();
                        true
                    });
                    assert_eq!(fresh, cost, "n={n}");
                }
                assert_eq!(appended.len(), n);
                assert!(appended.get(n).is_none());
                appended = next;
            }
        }
    }

    #[test]
    fn shared_nested_payloads_are_counted_once_by_retention_not_by_value_size() {
        let policy = Policy::default();
        let nested = Sequence::new(
            LogicalType::parse("index").unwrap(),
            vec![Value::Index(7); 65],
            &policy,
        )
        .unwrap();
        let inner = Value::Sequence(nested.clone());
        let mut outer =
            Sequence::new(inner.physical_type().logical().clone(), vec![], &policy).unwrap();
        for _ in 0..65 {
            outer = outer.appended(&inner, &policy, usize::MAX).unwrap();
        }
        let shared_bytes: usize = parts(&outer).iter().sum();
        assert_eq!(
            outer.retained_bytes() - shared_bytes,
            64 * nested.retained_bytes()
        );
        let original = outer.clone();
        let next = outer.appended(&inner, &policy, usize::MAX).unwrap();
        assert_eq!(original.len(), 65);
        assert_eq!(next.len(), 66);
        assert!(tree_overhead(usize::MAX).is_err());
    }
}
