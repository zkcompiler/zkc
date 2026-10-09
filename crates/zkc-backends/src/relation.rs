//! Admitted deterministic Bundle assets, actual-column assertion evaluation
//! and the polynomial view's descriptors and point substitutions.
use crate::{KoalaBear, Policy, Result, Value, exhausted, refused};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use std::{collections::BTreeMap, marker::PhantomData, sync::Arc};
use zkc_runtime::{
    interactive::{
        AttributeRule, BoundSignature, Identity, Invocation, KernelSignature, OperationBinding,
        Type,
    },
    relation::{Algebra, Bundle, Error, PolynomialView, TableView},
    ring::Expression,
};

#[derive(Clone, Debug, Default)]
pub struct Registry {
    assets: BTreeMap<String, Arc<Bundle>>,
    bytes: usize,
}
impl Registry {
    pub fn insert(&mut self, expected: &str, text: &str) -> Result<()> {
        if text.len() > crate::ring::REGISTRY_BYTE_LIMIT.saturating_sub(self.bytes) {
            return Err(exhausted("relation-assets-bytes"));
        }
        let bundle = Bundle::parse(text).map_err(|e| refused(e.0))?;
        if bundle.identity() != expected {
            return Err(refused("relation-asset-identity"));
        }
        if self.assets.contains_key(expected) {
            return Err(refused("relation-asset-duplicate"));
        }
        // The text charge covers names, literals and interaction tuple indices.
        // Include derived per-output read/public facts: these can be much larger
        // than the syntax from which they were computed.
        let mut charge = bundle.encode().to_string().len() as u64
            + bundle.publics().len() as u64 * 192
            + bundle.channels().len() as u64 * 1024;
        for (table, facts) in bundle.tables().iter().zip(bundle.facts()) {
            charge += 1024
                + arena_bytes(&table.arena) as u64
                + table.groups.len() as u64 * 256
                + table.assertions.len() as u64 * 64
                + table.interactions.len() as u64 * 1024;
            for fact in facts {
                charge += 128 + fact.reads.len() as u64 * 32 + fact.publics.len() as u64 * 16;
            }
        }
        if charge > crate::ring::REGISTRY_BYTE_LIMIT.saturating_sub(self.bytes) as u64 {
            return Err(exhausted("relation-assets-bytes"));
        }
        self.bytes += charge as usize;
        self.assets.insert(expected.into(), Arc::new(bundle));
        Ok(())
    }
    pub fn admitted_bytes(&self) -> usize {
        self.bytes
    }
    pub fn bundle(&self, identity: &str) -> Option<Arc<Bundle>> {
        self.assets.get(identity).cloned()
    }
    pub fn table_reference(
        &self,
        identity: &str,
        table: u64,
        carrier: Identity,
    ) -> Result<TableView<'_>> {
        let bundle = self
            .assets
            .get(identity)
            .ok_or_else(|| refused("relation-asset-missing"))?;
        if !matches!(carrier, Identity::KoalaBear | Identity::KoalaBearExt8) {
            return Err(refused("relation-table-carrier"));
        }
        bundle
            .table_view(
                usize::try_from(table).map_err(|_| refused("relation-table-index"))?,
                carrier,
            )
            .map_err(|e| refused(e.0))
    }
    /// The static premises of the polynomial kernels for one program
    /// reference. The check allocates nothing.
    pub fn polynomial_reference(
        &self,
        identity: &str,
        table: u64,
        carrier: Identity,
    ) -> Result<PolynomialView<'_>> {
        let bundle = self
            .assets
            .get(identity)
            .ok_or_else(|| refused("relation-asset-missing"))?;
        bundle
            .polynomial_view(
                usize::try_from(table).map_err(|_| refused("relation-table-index"))?,
                carrier,
            )
            .map_err(|e| refused(e.0))
    }
}

/// Decoded bytes charged per arena node, input and output at admission. They
/// bound an admitted arena and any sub-DAG prepared from it.
const NODE_BYTES: usize = 192;
const INPUT_BYTES: usize = 64;
const OUTPUT_BYTES: usize = 32;
fn arena_bytes(arena: &Expression) -> usize {
    arena.nodes().len() * NODE_BYTES
        + arena.inputs().len() * INPUT_BYTES
        + arena.outputs().len() * OUTPUT_BYTES
}

/// Installed Bundle kernels: (implementation, contract).
pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("plonky3/relation.table_rows", "relation.table_rows"),
    ("plonky3/relation.table_shape", "relation.table_shape"),
    ("plonky3/relation.table_input", "relation.table_input"),
    ("plonky3/relation.table_scope", "relation.table_scope"),
    ("plonky3/relation.table_point", "relation.table_point"),
    ("plonky3/relation.table_points", "relation.table_points"),
];

/// The backend advertises its own exact signature; it does not call the
/// runtime's logical operation resolver.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, table] = binding.arguments.as_slice() else {
        return None;
    };
    if !IMPLEMENTATIONS.contains(&(binding.implementation.as_str(), binding.contract.as_str()))
        || zkc_runtime::logical::natural_index(table).ok()? > 1_048_576
    {
        return None;
    }
    let domain = match field.as_str() {
        "koala-bear" => crate::domains::KOALA_BEAR,
        "koala-bear.ext8-binomial3" => crate::domains::KOALA_BEAR_EXT8,
        _ => return None,
    };
    let vector = domain.physical(Type::Vector)?;
    let index = domain.physical(Type::Index)?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "relation.table_rows" => (
            vec![vector.clone(), vector.clone(), vector.clone(), index],
            vec![vector],
        ),
        "relation.table_shape" => (vec![index.clone()], vec![index; 7]),
        "relation.table_input" => (vec![index.clone(); 2], vec![index; 3]),
        "relation.table_scope" => (vec![index.clone(); 2], vec![index; 2]),
        "relation.table_points" => (vec![vector.clone(), index], vec![vector]),
        _ => (vec![vector.clone()], vec![vector]),
    };
    Some(KernelSignature {
        inputs,
        outputs,
        attributes: AttributeRule::AssetIdentity,
    })
}

struct Arithmetic<S>(PhantomData<S>);
impl<S: crate::ring::Carrier + BasedVectorSpace<KoalaBear>> Algebra for Arithmetic<S> {
    type Value = S;
    fn value(&self, field: Identity, coordinates: &[String]) -> std::result::Result<S, Error> {
        let width = zkc_runtime::relation::degree(field).ok_or(Error("relation-table-carrier"))?;
        if coordinates.len() != width || width > S::DIMENSION {
            return Err(Error("relation-table-carrier"));
        }
        let values = coordinates
            .iter()
            .map(|s| crate::parse_koala_bear_decimal(s).map_err(|_| Error("bundle-value")))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        Ok(S::from_basis_coefficients_fn(|i| {
            values.get(i).copied().unwrap_or(KoalaBear::ZERO)
        }))
    }
    fn constant(&self, _: Identity, literal: &str) -> std::result::Result<S, Error> {
        let n = crate::parse_koala_bear_decimal(literal).map_err(|_| Error("bundle-value"))?;
        Ok(S::from_u32(n.as_canonical_u32()))
    }
    fn add(&self, _: Identity, a: &S, b: &S) -> S {
        *a + *b
    }
    fn mul(&self, _: Identity, a: &S, b: &S) -> S {
        *a * *b
    }
    fn neg(&self, _: Identity, a: &S) -> S {
        -*a
    }
    fn embed(&self, _: Identity, _: Identity, a: &S) -> std::result::Result<S, Error> {
        Ok(*a)
    }
    fn coordinates(&self, field: Identity, a: &S) -> Vec<String> {
        a.as_basis_coefficients_slice()
            [..zkc_runtime::relation::degree(field).expect("admitted field")]
            .iter()
            .map(|c| c.as_canonical_u32().to_string())
            .collect()
    }
}

#[allow(clippy::too_many_arguments)] // Keep the three distinct authorities and execution limits explicit.
fn rows<S: crate::ring::Carrier + BasedVectorSpace<KoalaBear>>(
    view: TableView<'_>,
    height: u64,
    witness: &[S],
    configuration: &[S],
    public_data: &[S],
    policy: &Policy,
    budget: &mut crate::ring::Budget,
    available: usize,
) -> Result<Vec<S>> {
    let height = u32::try_from(height).map_err(|_| refused("bundle-height"))?;
    let shape = view.lengths(height).map_err(|e| refused(e.0))?;
    policy.vector_width(shape.results, std::mem::size_of::<S>())?;
    policy.output(
        crate::value::size(shape.results, std::mem::size_of::<S>())?,
        available,
    )?;
    budget.charge(view.work(height))?;
    view.evaluate(
        height,
        witness,
        configuration,
        public_data,
        &Arithmetic(PhantomData),
    )
    .map_err(|e| refused(e.0))
}
/// Assertion expressions at `rows` row-major assignments of every arena input,
/// row-major with one column per assertion in assertion order. One row is
/// `relation.table_point`. The shared ring schedule interprets KoalaBear nodes
/// in Ext8 when the carrier is Ext8; values keep every extension coordinate.
///
/// Shape, storage and the full work charge are checked before the assertion
/// sub-DAG is prepared; every row shares that preparation and its scratch.
#[allow(clippy::too_many_arguments)] // Keep shape and execution limits explicit at this boundary.
fn points<S: crate::ring::Carrier>(
    view: &PolynomialView<'_>,
    assignments: &[S],
    rows: u64,
    packed: bool,
    policy: &Policy,
    budget: &mut crate::ring::Budget,
    available: usize,
) -> Result<Vec<S>> {
    if view.field() != S::IDENTITY {
        return Err(refused("relation-table-carrier"));
    }
    // An overflowing product never equals an actual length.
    let rows = usize::try_from(rows).ok();
    let shaped = rows.and_then(|rows| rows.checked_mul(view.input_count()));
    let (Some(rows), true) = (rows, shaped == Some(assignments.len())) else {
        return Err(refused("relation-table-point-shape"));
    };
    let count = rows
        .checked_mul(view.assertion_count())
        .ok_or_else(|| exhausted("element-limit"))?;
    let size = std::mem::size_of::<S>();
    policy.vector_width(count, size)?;
    policy.output(crate::value::size(count, size)?, available)?;
    // The result, node scratch and prepared sub-DAG are live together. The
    // sub-DAG is bounded by the admitted arena's charge plus one output per
    // assertion; scratch by the arena's node count.
    let t = view.definition();
    let cells = crate::ring::scratch_cells::<S>(t.arena.nodes().len(), packed)?
        .checked_add(count)
        .ok_or_else(|| exhausted("element-limit"))?;
    policy.vector_width(cells, size)?;
    policy.output(
        crate::value::size(cells, size)?
            .checked_add(arena_bytes(&t.arena) + t.assertions.len() * OUTPUT_BYTES)
            .ok_or_else(|| exhausted("output-bytes"))?,
        usize::MAX,
    )?;
    budget.charge(
        view.point_work()
            .checked_mul(rows as u64)
            .and_then(|w| w.checked_add(view.work()))
            .ok_or_else(|| exhausted("ring-work"))?,
    )?;
    if count == 0 {
        return Ok(Vec::new());
    }
    let prepared = view.prepare().map_err(|e| refused(e.0))?;
    crate::ring::substitute_rows(
        prepared.arena(),
        prepared.outputs(),
        assignments,
        rows,
        packed,
    )
}
fn indices(values: impl IntoIterator<Item = u64>) -> Vec<Value> {
    values.into_iter().map(Value::Index).collect()
}
fn polynomial(
    registry: &Registry,
    budget: &mut crate::ring::Budget,
    args: &[Value],
    i: &Invocation<'_>,
    policy: &Policy,
    digest: &str,
    table: u64,
) -> Result<Vec<Value>> {
    let contract = i.binding.declaration().contract.as_str();
    let carrier = i
        .binding
        .declaration()
        .arguments
        .first()
        .and_then(|field| Identity::parse(field).ok())
        .ok_or_else(|| refused("relation-table-carrier"))?;
    // The static check allocates nothing and visits at most what `work`
    // charges; every kernel charges before its height profile or preparation.
    let view = registry.polynomial_reference(digest, table, carrier)?;
    let available = i.max_output_bytes;
    match (contract, args) {
        ("relation.table_point", [Value::KoalaBearVector(v)]) => {
            points(&view, v, 1, false, policy, budget, available)
                .map(|values| vec![Value::KoalaBearVector(values.into())])
        }
        ("relation.table_point", [Value::KoalaBearExt8Vector(v)]) => {
            points(&view, v, 1, false, policy, budget, available)
                .map(|values| vec![Value::KoalaBearExt8Vector(values.into())])
        }
        ("relation.table_points", [Value::KoalaBearVector(v), Value::Index(rows)]) => {
            points(&view, v, *rows, true, policy, budget, available)
                .map(|values| vec![Value::KoalaBearVector(values.into())])
        }
        ("relation.table_points", [Value::KoalaBearExt8Vector(v), Value::Index(rows)]) => {
            points(&view, v, *rows, true, policy, budget, available)
                .map(|values| vec![Value::KoalaBearExt8Vector(values.into())])
        }
        ("relation.table_shape", [Value::Index(height)]) => {
            budget.charge(view.work())?;
            let s = view.shape(*height).map_err(|e| refused(e.0))?;
            Ok(indices([
                s.witness_width,
                s.config_width,
                s.public_width,
                s.public_slots,
                s.inputs,
                s.assertions,
                s.quotient_chunks,
            ]))
        }
        ("relation.table_input", [Value::Index(height), Value::Index(slot)]) => {
            budget.charge(view.work())?;
            let d = view.input(*height, *slot).map_err(|e| refused(e.0))?;
            Ok(indices([d.kind, d.column, d.rotation]))
        }
        ("relation.table_scope", [Value::Index(height), Value::Index(assertion)]) => {
            budget.charge(view.work())?;
            let (begin, end) = view.scope(*height, *assertion).map_err(|e| refused(e.0))?;
            Ok(indices([begin, end]))
        }
        _ => Err(refused("kernel-operands")),
    }
}
pub(crate) fn apply(
    registry: &Registry,
    budget: &mut crate::ring::Budget,
    args: &[Value],
    i: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let [digest] = i.attributes else {
        return Err(refused("relation-asset-reference"));
    };
    let table = i
        .binding
        .declaration()
        .arguments
        .get(1)
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| refused("relation-table-index"))?;
    if i.binding.declaration().contract != "relation.table_rows" {
        return polynomial(registry, budget, args, i, policy, digest, table);
    }
    macro_rules! dispatch {
        ($variant:ident, $carrier:expr) => {
            if let [
                Value::$variant(w),
                Value::$variant(c),
                Value::$variant(p),
                Value::Index(h),
            ] = args
            {
                let view = registry.table_reference(digest, table, $carrier)?;
                return rows(view, *h, w, c, p, policy, budget, i.max_output_bytes)
                    .map(|values| vec![Value::$variant(values.into())]);
            }
        };
    }
    dispatch!(KoalaBearVector, Identity::KoalaBear);
    dispatch!(KoalaBearExt8Vector, Identity::KoalaBearExt8);
    Err(refused("kernel-operands"))
}

#[cfg(test)]
mod polynomial_tests;
#[cfg(test)]
mod tests;
