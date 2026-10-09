//! Bulk substitution of admitted ring expressions over KoalaBear and Ext8.
//! Assets are immutable Host configuration; a proof message cannot install one.
use crate::{Policy, Result, Value, exhausted, refused};
use p3_field::{Field, PackedValue, PrimeCharacteristicRing};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, sync::Arc};
use zkc_runtime::{
    interactive::{Identity, Invocation},
    ring::{Expression, Node},
};

pub const DEFAULT_WORK_LIMIT: u64 = 1 << 28;
pub const COEFFICIENT_DEGREE_LIMIT: u32 = 64;
/// Canonical bytes plus decoded metadata admitted into one registry.
pub const REGISTRY_BYTE_LIMIT: usize = 32 * 1024 * 1024;
mod sealed {
    pub trait Sealed {}
    impl Sealed for crate::KoalaBear {}
    impl Sealed for crate::KoalaBearExt8 {}
}
pub trait Carrier: Field + sealed::Sealed {
    const IDENTITY: Identity;
}
impl Carrier for crate::KoalaBear {
    const IDENTITY: Identity = Identity::KoalaBear;
}
impl Carrier for crate::KoalaBearExt8 {
    const IDENTITY: Identity = Identity::KoalaBearExt8;
}

/// The expected digest must come from the authorized program's closed reference.
/// Content identity alone does not authorize an external AIR or its public data.
#[derive(Clone, Debug, Default)]
pub struct Registry {
    assets: BTreeMap<String, Arc<Expression>>,
    bytes: usize,
}
impl Registry {
    pub fn insert(&mut self, expected: &str, text: &str) -> Result<()> {
        if text.len() > REGISTRY_BYTE_LIMIT.saturating_sub(self.bytes) {
            return Err(exhausted("ring-assets-bytes"));
        }
        let expression = Expression::parse(text).map_err(|e| refused(e.0))?;
        let canonical = expression.canonical();
        let actual = format!("{:x}", Sha256::digest(canonical.as_bytes()));
        if actual != expected {
            return Err(refused("ring-asset-identity"));
        }
        if self.assets.contains_key(expected) {
            return Err(refused("ring-asset-duplicate"));
        }
        // Bound decoded metadata as well as transport. All source scalars have
        // bounded spelling, and each arena edge occupies at most a machine word.
        let charge = canonical
            .len()
            .checked_add(expression.nodes().len() * 128)
            .and_then(|n| n.checked_add(expression.inputs().len() * 16))
            .and_then(|n| n.checked_add(expression.outputs().len() * 16))
            .ok_or_else(|| exhausted("ring-assets-bytes"))?;
        if charge > REGISTRY_BYTE_LIMIT.saturating_sub(self.bytes) {
            return Err(exhausted("ring-assets-bytes"));
        }
        self.bytes += charge;
        self.assets.insert(actual, Arc::new(expression));
        Ok(())
    }
    pub fn admitted_bytes(&self) -> usize {
        self.bytes
    }
    pub(crate) fn get(&self, identity: &str) -> Result<Arc<Expression>> {
        self.assets
            .get(identity)
            .cloned()
            .ok_or_else(|| refused("ring-asset-missing"))
    }
    /// Admitted content identities in ascending order.
    pub fn identities(&self) -> impl ExactSizeIterator<Item = &str> {
        self.assets.keys().map(String::as_str)
    }
    /// The admitted expression under a content identity, if any.
    pub fn expression(&self, identity: &str) -> Option<Arc<Expression>> {
        self.assets.get(identity).cloned()
    }
    /// Check one static program reference before any execution: the asset
    /// must be admitted and interpretable in the operation's carrier field,
    /// under the same rule the bulk kernels apply at substitution time.
    pub fn check_reference(&self, identity: &str, carrier: Identity) -> Result<()> {
        let expression = self.get(identity)?;
        field_compatible(&expression, carrier)
    }
}

#[derive(Clone, Debug)]
pub struct Budget {
    pub limit: u64,
    pub spent: u64,
}
impl Default for Budget {
    fn default() -> Self {
        Self {
            limit: DEFAULT_WORK_LIMIT,
            spent: 0,
        }
    }
}
impl Budget {
    pub(crate) fn charge(&mut self, work: u64) -> Result<()> {
        let next = self
            .spent
            .checked_add(work)
            .ok_or_else(|| exhausted("ring-work"))?;
        if next > self.limit {
            return Err(exhausted("ring-work"));
        }
        self.spent = next;
        Ok(())
    }
}
fn output_cells<T>(cells: usize, policy: &Policy, available: usize) -> Result<()> {
    policy.vector_width(cells, std::mem::size_of::<T>())?;
    policy.output(
        crate::value::size(cells, std::mem::size_of::<T>())?,
        available,
    )
}
fn checked_product(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b).ok_or_else(|| exhausted("ring-shape"))
}
fn field_compatible(expression: &Expression, carrier: Identity) -> Result<()> {
    if !matches!(carrier, Identity::KoalaBear | Identity::KoalaBearExt8) {
        return Err(refused("ring-carrier"));
    }
    if expression
        .inputs()
        .iter()
        .chain(expression.facts().iter().map(|f| &f.field))
        .any(|f| {
            *f != carrier && !(carrier == Identity::KoalaBearExt8 && *f == Identity::KoalaBear)
        })
    {
        return Err(refused("ring-carrier"));
    }
    Ok(())
}

/// Scalar and packed substitution use this same arithmetic schedule. Base-field
/// variables may be assigned extension values after a bind or at an OOD point.
/// `embed` is then the compatible algebra map, which is the identity in E or E[X].
pub(crate) fn scalar<S: PrimeCharacteristicRing>(
    expression: &Expression,
    mut input: impl FnMut(usize) -> S,
    values: &mut Vec<S>,
) {
    values.clear();
    for node in expression.nodes() {
        let value = match node {
            Node::Constant(_, n) => S::from_u32(n.parse().expect("admitted KoalaBear literal")),
            Node::Input(i) => input(*i),
            Node::Add(a, b) => values[*a].clone() + values[*b].clone(),
            Node::Mul(a, b) => values[*a].clone() * values[*b].clone(),
            Node::Neg(a) => -values[*a].clone(),
            Node::Embed(_, a) => values[*a].clone(),
        };
        values.push(value);
    }
}
pub(crate) fn fresh<T>(n: usize) -> Result<Vec<T>> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(n)
        .map_err(|_| exhausted("allocation"))?;
    Ok(result)
}

/// Row-major assignments, with one column per input slot and one result column
/// per output. The explicit row count permits zero-input and zero-output arenas.
#[allow(clippy::too_many_arguments)] // Keep shape and execution limits explicit at this boundary.
pub fn rows<S: Carrier>(
    expression: &Expression,
    carrier: Identity,
    input: &[S],
    row_count: usize,
    packed: bool,
    policy: &Policy,
    budget: &mut Budget,
    available: usize,
) -> Result<Vec<S>> {
    if carrier != S::IDENTITY {
        return Err(refused("ring-carrier"));
    }
    field_compatible(expression, carrier)?;
    let columns = expression.inputs().len();
    if input.len() != checked_product(row_count, columns)? {
        return Err(refused("ring-input-shape"));
    }
    output_cells::<S>(input.len(), policy, usize::MAX)?;
    let count = checked_product(row_count, expression.outputs().len())?;
    output_cells::<S>(count, policy, available)?;
    let visits = row_count
        .checked_add(1)
        .ok_or_else(|| exhausted("ring-work"))?;
    let work = checked_product(
        visits,
        expression.nodes().len() + columns + expression.outputs().len() + 1,
    )?;
    budget.charge(work as u64)?;
    let width = if packed { S::Packing::WIDTH } else { 1 };
    // Scratch is allocated once per call. Packing uses a temporary lane gather,
    // never a different table interpolation or a transposed mathematical view.
    let packed_nodes = if packed { expression.nodes().len() } else { 0 };
    output_cells::<S::Packing>(packed_nodes, policy, usize::MAX)?;
    let scratch_width = if packed { width + 1 } else { 1 };
    output_cells::<S>(
        expression
            .nodes()
            .len()
            .checked_mul(scratch_width)
            .and_then(|n| n.checked_add(count))
            .ok_or_else(|| exhausted("ring-scratch"))?,
        policy,
        usize::MAX,
    )?;
    let mut result = fresh(count)?;
    let mut packed_values = fresh::<S::Packing>(packed_nodes)?;
    let mut scalar_values = fresh::<S>(expression.nodes().len())?;
    let mut row = 0;
    if packed {
        while row_count - row >= width {
            scalar(
                expression,
                |slot| S::Packing::from_fn(|lane| input[(row + lane) * columns + slot]),
                &mut packed_values,
            );
            for lane in 0..width {
                for node in expression.outputs() {
                    result.push(packed_values[*node].as_slice()[lane]);
                }
            }
            row += width;
        }
    }
    while row < row_count {
        scalar(
            expression,
            |slot| input[row * columns + slot],
            &mut scalar_values,
        );
        for node in expression.outputs() {
            result.push(scalar_values[*node]);
        }
        row += 1;
    }
    Ok(result)
}

struct CoefficientPlan {
    offsets: Vec<usize>,
    widths: Vec<usize>,
    scratch: usize,
    output_width: usize,
    work: u64,
}
impl CoefficientPlan {
    fn new<S: Carrier>(
        expression: &Expression,
        width: usize,
        policy: &Policy,
        available: usize,
    ) -> Result<Self> {
        if width == 0 || width > COEFFICIENT_DEGREE_LIMIT as usize + 1 {
            return Err(refused("ring-coefficient-width"));
        }
        let degrees = expression
            .degrees(&vec![(width - 1) as u32; expression.inputs().len()])
            .map_err(|e| refused(e.0))?;
        let maximum = expression
            .outputs()
            .iter()
            .map(|i| degrees[*i])
            .max()
            .unwrap_or(0);
        if maximum > COEFFICIENT_DEGREE_LIMIT {
            return Err(refused("ring-coefficient-degree"));
        }
        let output_width = maximum as usize + 1;
        let cells = checked_product(output_width, expression.outputs().len())?;
        output_cells::<S>(cells, policy, available)?;
        let mut offsets = Vec::with_capacity(degrees.len());
        let widths: Vec<_> = degrees.iter().map(|d| *d as usize + 1).collect();
        let mut scratch = 0usize;
        for width in &widths {
            offsets.push(scratch);
            scratch = scratch
                .checked_add(*width)
                .ok_or_else(|| exhausted("ring-scratch"))?;
        }
        output_cells::<S>(
            scratch
                .checked_add(cells)
                .ok_or_else(|| exhausted("ring-scratch"))?,
            policy,
            usize::MAX,
        )?;
        let mut work = checked_product(expression.inputs().len(), width)? as u64
            + scratch as u64
            + cells as u64
            + 1;
        for node in expression.nodes() {
            if let Node::Mul(a, b) = node {
                work = work
                    .checked_add(widths[*a] as u64 * widths[*b] as u64)
                    .ok_or_else(|| exhausted("ring-work"))?;
            }
        }
        Ok(Self {
            offsets,
            widths,
            scratch,
            output_width,
            work,
        })
    }
    fn evaluate<S: Carrier>(
        &self,
        expression: &Expression,
        mut input: impl FnMut(usize, usize) -> S,
        values: &mut [S],
    ) {
        values.fill(S::ZERO);
        for (i, node) in expression.nodes().iter().enumerate() {
            let dst = self.offsets[i];
            match node {
                Node::Constant(_, n) => {
                    values[dst] = S::from_u32(n.parse().expect("admitted KoalaBear literal"))
                }
                Node::Input(slot) => {
                    for d in 0..self.widths[i] {
                        values[dst + d] = input(*slot, d);
                    }
                }
                Node::Add(a, b) => {
                    for d in 0..self.widths[*a] {
                        let v = values[self.offsets[*a] + d];
                        values[dst + d] += v;
                    }
                    for d in 0..self.widths[*b] {
                        let v = values[self.offsets[*b] + d];
                        values[dst + d] += v;
                    }
                }
                Node::Mul(a, b) => {
                    for x in 0..self.widths[*a] {
                        for y in 0..self.widths[*b] {
                            let v = values[self.offsets[*a] + x] * values[self.offsets[*b] + y];
                            values[dst + x + y] += v;
                        }
                    }
                }
                Node::Neg(a) => {
                    for d in 0..self.widths[*a] {
                        values[dst + d] = -values[self.offsets[*a] + d];
                    }
                }
                Node::Embed(_, a) => {
                    for d in 0..self.widths[*a] {
                        values[dst + d] = values[self.offsets[*a] + d];
                    }
                }
            }
        }
    }
    fn add_outputs<S: Carrier>(&self, expression: &Expression, values: &[S], result: &mut [S]) {
        for (out, node) in expression.outputs().iter().enumerate() {
            for d in 0..self.widths[*node] {
                result[out * self.output_width + d] += values[self.offsets[*node] + d];
            }
        }
    }
}

/// Exact coefficient substitution. Inputs are slot-major, then ascending degree.
/// Output width follows the derived degree; high terms are never truncated.
pub fn coefficients<S: Carrier>(
    expression: &Expression,
    carrier: Identity,
    input: &[S],
    width: usize,
    policy: &Policy,
    budget: &mut Budget,
    available: usize,
) -> Result<Vec<S>> {
    if carrier != S::IDENTITY {
        return Err(refused("ring-carrier"));
    }
    field_compatible(expression, carrier)?;
    if input.len() != checked_product(expression.inputs().len(), width)? {
        return Err(refused("ring-input-shape"));
    }
    output_cells::<S>(input.len(), policy, usize::MAX)?;
    let plan = CoefficientPlan::new::<S>(expression, width, policy, available)?;
    budget.charge(plan.work)?;
    let mut scratch = fresh(plan.scratch)?;
    scratch.resize(plan.scratch, S::ZERO);
    let count = expression.outputs().len() * plan.output_width;
    let mut result = fresh(count)?;
    result.resize(count, S::ZERO);
    plan.evaluate(expression, |slot, d| input[slot * width + d], &mut scratch);
    plan.add_outputs(expression, &scratch, &mut result);
    Ok(result)
}

/// Sum P(a_i + (b_i-a_i) X) over row pairs. The shape and full scalar-work
/// charge are checked before allocating output or scratch. Scratch is reused.
#[allow(clippy::too_many_arguments)] // Keep both assignments, shape and execution limits explicit.
pub fn affine_sum<S: Carrier>(
    expression: &Expression,
    carrier: Identity,
    low: &[S],
    high: &[S],
    count: usize,
    policy: &Policy,
    budget: &mut Budget,
    available: usize,
) -> Result<Vec<S>> {
    if carrier != S::IDENTITY {
        return Err(refused("ring-carrier"));
    }
    field_compatible(expression, carrier)?;
    let columns = expression.inputs().len();
    if low.len() != checked_product(count, columns)? || high.len() != low.len() {
        return Err(refused("ring-input-shape"));
    }
    output_cells::<S>(low.len(), policy, usize::MAX)?;
    let plan = CoefficientPlan::new::<S>(expression, 2, policy, available)?;
    budget.charge(
        plan.work
            .checked_add((columns * 2 + 1) as u64)
            .and_then(|w| w.checked_mul(count as u64))
            .and_then(|w| w.checked_add(plan.work))
            .ok_or_else(|| exhausted("ring-work"))?,
    )?;
    let mut scratch = fresh(plan.scratch)?;
    scratch.resize(plan.scratch, S::ZERO);
    let cells = expression.outputs().len() * plan.output_width;
    let mut result = fresh(cells)?;
    result.resize(cells, S::ZERO);
    for row in 0..count {
        plan.evaluate(
            expression,
            |slot, d| {
                let (a, b) = (low[row * columns + slot], high[row * columns + slot]);
                if d == 0 { a } else { b - a }
            },
            &mut scratch,
        );
        plan.add_outputs(expression, &scratch, &mut result);
    }
    Ok(result)
}

pub(crate) fn apply(
    registry: &Registry,
    budget: &mut Budget,
    args: &[Value],
    i: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let [digest] = i.attributes else {
        return Err(refused("ring-asset-reference"));
    };
    let expression = registry.get(digest)?;
    let name = i.binding.declaration().contract.as_str();
    macro_rules! dispatch {
        ($vector:ident,$carrier:expr) => {
            match args {
                [Value::$vector(input)] if name == "ring.point" => rows(
                    &expression,
                    $carrier,
                    input,
                    1,
                    false,
                    policy,
                    budget,
                    i.max_output_bytes,
                ),
                [Value::$vector(input), Value::Index(count)] if name == "ring.rows" => rows(
                    &expression,
                    $carrier,
                    input,
                    usize::try_from(*count).map_err(|_| refused("ring-shape"))?,
                    true,
                    policy,
                    budget,
                    i.max_output_bytes,
                ),
                [Value::$vector(input), Value::Index(width)] if name == "ring.coefficients" => {
                    coefficients(
                        &expression,
                        $carrier,
                        input,
                        usize::try_from(*width).map_err(|_| refused("ring-shape"))?,
                        policy,
                        budget,
                        i.max_output_bytes,
                    )
                }
                [
                    Value::$vector(low),
                    Value::$vector(high),
                    Value::Index(count),
                ] if name == "ring.affine_sum" => affine_sum(
                    &expression,
                    $carrier,
                    low,
                    high,
                    usize::try_from(*count).map_err(|_| refused("ring-shape"))?,
                    policy,
                    budget,
                    i.max_output_bytes,
                ),
                _ => Err(refused("kernel-operands")),
            }
            .map(|v| vec![Value::$vector(v.into())])
        };
    }
    match args.first() {
        Some(Value::KoalaBearVector(_)) => dispatch!(KoalaBearVector, Identity::KoalaBear),
        Some(Value::KoalaBearExt8Vector(_)) => {
            dispatch!(KoalaBearExt8Vector, Identity::KoalaBearExt8)
        }
        _ => Err(refused("ring-carrier")),
    }
}

pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::poly;
    use zkc_runtime::interactive::{AttributeRule, Type::*};
    &[
        poly::operation(
            "ring.point",
            &[Vector],
            &[Vector],
            AttributeRule::AssetIdentity,
        )
        .implemented_by(&["plonky3/ring.point"]),
        poly::operation(
            "ring.rows",
            &[Vector, Index],
            &[Vector],
            AttributeRule::AssetIdentity,
        )
        .implemented_by(&["plonky3/ring.rows"]),
        poly::operation(
            "ring.coefficients",
            &[Vector, Index],
            &[Vector],
            AttributeRule::AssetIdentity,
        )
        .implemented_by(&["plonky3/ring.coefficients"]),
        poly::operation(
            "ring.affine_sum",
            &[Vector, Vector, Index],
            &[Vector],
            AttributeRule::AssetIdentity,
        )
        .implemented_by(&["plonky3/ring.affine_sum"]),
    ]
};
