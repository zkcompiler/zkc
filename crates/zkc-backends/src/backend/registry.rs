//! Immutable exact implementation ownership, independent of runtime admission.
//! A selected entry carries its signature resolver, security premise and handler.
use super::NativeBackend;
use crate::{Result, Value, refused};
use std::{collections::BTreeMap, sync::OnceLock};
use zkc_runtime::interactive::{BoundSignature, Identity, Invocation, OperationBinding};

#[derive(Clone, Copy)]
enum Signature {
    Shaped(
        &'static crate::bindings::Contract,
        crate::bindings::Selection,
    ),
    Custom(fn(&OperationBinding) -> Option<BoundSignature>),
}
pub(crate) type Handler = fn(&mut NativeBackend, &Invocation<'_>, &[Value]) -> Result<Vec<Value>>;
#[derive(Clone, Copy)]
pub(super) struct Implementation {
    contract: &'static str,
    signature: Signature,
    pub(super) handler: Handler,
}
impl Implementation {
    pub(super) fn signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        if binding.contract != self.contract {
            return None;
        }
        match self.signature {
            Signature::Shaped(row, policy) => {
                if let crate::bindings::Selection::Alternative { primary, .. } = policy
                    && binding.arguments.first().map(String::as_str) != Some(primary.name())
                {
                    return None;
                }
                row.signature(binding, policy)
            }
            Signature::Custom(resolve) => resolve(binding),
        }
    }
}
#[derive(Clone, Default)]
pub(super) struct Registry {
    entries: BTreeMap<String, Implementation>,
}
impl Registry {
    fn insert(&mut self, identity: String, entry: Implementation) -> Result<()> {
        match self.entries.entry(identity) {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(entry);
                Ok(())
            }
            std::collections::btree_map::Entry::Occupied(_) => {
                Err(refused("duplicate-implementation-owner"))
            }
        }
    }
    fn family(
        &mut self,
        implementations: &'static [(&'static str, &'static str)],
        signature: Signature,
        handler: Handler,
    ) -> Result<()> {
        for &(identity, contract) in implementations {
            self.insert(
                identity.into(),
                Implementation {
                    contract,
                    signature,
                    handler,
                },
            )?;
        }
        Ok(())
    }
    fn shaped(
        &mut self,
        contracts: &'static [crate::bindings::Contract],
        handler: Handler,
    ) -> Result<()> {
        for row in contracts {
            for implementation in row.implementations {
                self.insert(
                    (*implementation).into(),
                    Implementation {
                        contract: row.name,
                        signature: Signature::Shaped(row, crate::bindings::Selection::Default),
                        handler,
                    },
                )?;
            }
        }
        Ok(())
    }
    fn alternative(&mut self, row: &Alternative) -> Result<()> {
        let mut entry = self
            .get(row.original)
            .ok_or_else(|| refused("implementation-owner-missing"))?;
        let Signature::Shaped(shape, crate::bindings::Selection::Default) = entry.signature else {
            return Err(refused("implementation-owner-shape"));
        };
        if !shape.alternatives {
            return Err(refused("implementation-owner-shape"));
        }
        entry.signature = Signature::Shaped(
            shape,
            crate::bindings::Selection::Alternative {
                primary: row.primary,
                ports: row.ports,
            },
        );
        entry.handler = row.handler.unwrap_or(entry.handler);
        self.insert(row.identity.into(), entry)
    }
    pub(super) fn implementations(&self) -> Vec<(String, &'static str)> {
        self.entries
            .iter()
            .map(|(identity, entry)| (identity.clone(), entry.contract))
            .collect()
    }
    pub(super) fn get(&self, identity: &str) -> Option<Implementation> {
        self.entries.get(identity).copied()
    }
}
/// Owner rows bind applicability, physical ports, leakage premise and execution.
pub(crate) struct Alternative {
    pub(crate) identity: &'static str,
    pub(crate) original: &'static str,
    /// Exact first domain argument: field, group, scheme or transcript suite.
    pub(crate) primary: Identity,
    pub(crate) ports: crate::bindings::PortTransform,
    /// Omit for a layout-only alternative to retain the original algorithm.
    pub(crate) handler: Option<Handler>,
}
pub(super) fn alternatives() -> impl Iterator<Item = &'static Alternative> {
    [
        super::execute::ALTERNATIVES,
        crate::kernels::conversions::ALTERNATIVES,
        crate::diagonal::ALTERNATIVES,
        crate::kernels::pairwise::ALTERNATIVES,
    ]
    .into_iter()
    .flatten()
}

pub(super) fn installed() -> Result<&'static Registry> {
    static REGISTRY: OnceLock<Result<Registry>> = OnceLock::new();
    REGISTRY
        .get_or_init(|| {
            let mut r = Registry::default();
            r.shaped(crate::ring::CONTRACTS, ring)?;
            r.family(
                crate::relation::IMPLEMENTATIONS,
                Signature::Custom(crate::relation::signature),
                relation,
            )?;
            r.shaped(super::execute::CONTRACTS, basic)?;
            r.shaped(crate::kernels::arithmetic::CONTRACTS, arithmetic)?;
            r.shaped(crate::kernels::conversions::CONTRACTS, conversions)?;
            r.shaped(crate::kernels::curve::CONTRACTS, curve)?;
            r.shaped(crate::kernels::resources::CONTRACTS, resources)?;
            r.shaped(crate::plonky3::numerical::CONTRACTS, numerical)?;
            r.family(
                crate::kernels::indices::IMPLEMENTATIONS,
                Signature::Custom(crate::kernels::indices::signature),
                indices,
            )?;
            r.family(
                crate::external_kernels::IMPLEMENTATIONS,
                Signature::Custom(crate::external_kernels::signature),
                external,
            )?;
            r.family(
                crate::oracle::IMPLEMENTATIONS,
                Signature::Custom(crate::oracle::signature),
                oracle,
            )?;
            r.family(
                crate::field_array::IMPLEMENTATIONS,
                Signature::Custom(crate::field_array::signature),
                field_array,
            )?;
            r.family(
                crate::sequence::IMPLEMENTATIONS,
                Signature::Custom(crate::sequence::signature),
                sequence,
            )?;
            r.family(
                crate::fixed_vector::IMPLEMENTATIONS,
                Signature::Custom(crate::fixed_vector::signature),
                fixed_vector,
            )?;
            r.family(
                &[
                    ("logical/resource_unit.create", "resource_unit.create"),
                    ("logical/resource_unit.pass", "resource_unit.pass"),
                    ("logical/resource_unit.consume", "resource_unit.consume"),
                ],
                Signature::Custom(super::resource_unit::signature),
                super::resource_unit::execute,
            )?;
            r.family(
                super::execute::SPECIAL_IMPLEMENTATIONS,
                Signature::Custom(crate::bindings::table::relayout),
                basic,
            )?;
            r.shaped(crate::kernels::arithmetic::EMBEDDINGS, arithmetic)?;
            r.shaped(crate::kernels::curve::PAIRINGS, curve)?;
            for row in alternatives() {
                r.alternative(row)?;
            }
            Ok(r)
        })
        .as_ref()
        .map_err(Clone::clone)
}
fn field(i: &Invocation<'_>) -> Option<Identity> {
    i.binding
        .signature()
        .inputs
        .iter()
        .chain(&i.binding.signature().outputs)
        .find_map(|t| t.logical().identity().scalar_field())
}
fn ring(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::ring::apply(&b.ring_assets, &mut b.ring_work, args, i, &b.core.policy)
}
fn relation(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::relation::apply(
        &b.relation_assets,
        &mut b.ring_work,
        args,
        i,
        &b.core.policy,
    )
}
pub(crate) fn basic(
    b: &mut NativeBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    b.execute_basic(&i.binding.declaration().contract, i, args)
}
fn fixed_vector(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::fixed_vector::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
fn sequence(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::sequence::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
fn arithmetic(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::kernels::arithmetic::apply(
        &i.binding.declaration().contract,
        field(i),
        args,
        i,
        &b.core.policy,
    )
}
pub(crate) fn conversions(
    b: &mut NativeBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::kernels::conversions::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
fn curve(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::kernels::curve::apply(
        &i.binding.declaration().contract,
        field(i),
        args,
        i,
        &b.core.policy,
    )
}

fn resources(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::kernels::resources::apply(
        &i.binding.declaration().contract,
        args,
        i,
        &b.core.policy,
        &mut b.core.resources,
        &b.core.setups,
    )
}
fn numerical(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    // One owner selects its typed specialization from the admitted closed ports.
    let name = &i.binding.declaration().contract;
    if field(i) == Some(Identity::Bn254Fr) {
        crate::kernels::bn254::apply(name, field(i), args, i, &b.core.policy)
    } else {
        crate::plonky3::numerical::apply(
            name,
            field(i),
            args,
            i,
            &b.core.policy,
            &b.core.polynomial,
        )
    }
}
fn indices(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::kernels::indices::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
    )
}
fn external(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::external_kernels::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
        &mut b.external_work,
    )
}
fn oracle(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::oracle::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
pub(crate) fn diagonal(
    b: &mut NativeBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::diagonal::apply(i, args, &b.core.policy)
}

pub(crate) fn pairwise(
    b: &mut NativeBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::kernels::pairwise::apply(args, &b.core.policy, i.max_output_bytes)
}

#[cfg(test)]
#[path = "registry_tests.rs"]
mod tests;

fn field_array(b: &mut NativeBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::field_array::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
