//! Admitted deterministic Bundle assets and actual-column assertion evaluation.
use crate::{KoalaBear, Policy, Result, Value, exhausted, refused};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use std::{collections::BTreeMap, marker::PhantomData, sync::Arc};
use zkc_runtime::{
    interactive::{
        AttributeRule, BoundSignature, Identity, Invocation, KernelSignature, OperationBinding,
        Type,
    },
    relation::{Algebra, Bundle, Error, TableView},
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
                + table.arena.nodes().len() as u64 * 192
                + table.arena.inputs().len() as u64 * 64
                + table.arena.outputs().len() as u64 * 32
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
}

/// The backend advertises its own exact signature; it does not call the
/// runtime's logical operation resolver.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, table] = binding.arguments.as_slice() else {
        return None;
    };
    if binding.contract != "relation.table_rows"
        || binding.implementation != "plonky3/relation.table_rows"
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
    Some(KernelSignature {
        inputs: vec![
            vector.clone(),
            vector.clone(),
            vector.clone(),
            domain.physical(Type::Index)?,
        ],
        outputs: vec![vector],
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
mod tests;
