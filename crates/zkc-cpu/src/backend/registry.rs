//! Immutable exact implementation ownership, independent of runtime admission.
//! A selected entry carries its signature resolver, security premise and handler.
use super::{CpuBackend, dispatch::Dispatch};
use crate::{Result, Value, refused};
use std::{collections::BTreeMap, sync::OnceLock};
use zkc_runtime::vm::{BoundSignature, Identity, Invocation, OperationBinding};

#[derive(Clone, Copy)]
enum Signature {
    Shaped(
        &'static crate::bindings::Contract,
        crate::bindings::Selection,
    ),
    Custom(fn(&OperationBinding) -> Option<BoundSignature>),
}
pub(crate) type Handler = fn(&mut CpuBackend, &Invocation<'_>, &[Value]) -> Result<Vec<Value>>;
pub(crate) fn blst(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::blst::apply(&i.binding.declaration().contract, i, args, &b.core.policy)
}
pub(super) type PreparedHandler =
    fn(&mut CpuBackend, &Invocation<'_>, &[Value], &super::CpuCall) -> Result<Vec<Value>>;
#[derive(Clone, Copy)]
pub(super) struct Implementation {
    contract: &'static str,
    signature: Signature,
    pub(super) handler: Dispatch,
    pub(super) prepared_handler: Option<PreparedHandler>,
    pub(super) deterministic: bool,
    pub(super) requirements: zkc_runtime::vm::ImplementationRequirements,
}
impl Implementation {
    pub(super) fn signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        if binding.contract != self.contract {
            return None;
        }
        if !binding.physical_arguments.is_empty()
            && !binding.contract.starts_with("sequence.")
            && !binding.contract.starts_with("field_array.")
            && !binding.contract.starts_with("fixed_vector.")
            && binding.contract != "representation.convert"
            && binding.contract != "transcript.native.indexed.observe.data"
        {
            return None;
        }
        match self.signature {
            Signature::Shaped(row, policy) => {
                if let crate::bindings::Selection::Alternative { domains, .. } = policy
                    && !domains.iter().any(|domain| {
                        binding.arguments.first().map(String::as_str) == Some(domain.name())
                    })
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
pub(crate) struct Registry {
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
    fn install_family(
        &mut self,
        implementations: &'static [(&'static str, &'static str)],
        signature: Signature,
        handler: Handler,
        deterministic: bool,
    ) -> Result<()> {
        for &(identity, contract) in implementations {
            self.insert(
                identity.into(),
                Implementation {
                    contract,
                    signature,
                    handler: Dispatch::Direct(handler),
                    prepared_handler: None,
                    deterministic,
                    requirements: Default::default(),
                },
            )?;
        }
        Ok(())
    }
    fn family(
        &mut self,
        rows: &'static [(&'static str, &'static str)],
        signature: Signature,
        handler: Handler,
    ) -> Result<()> {
        self.install_family(rows, signature, handler, false)
    }
    fn pure_family(
        &mut self,
        rows: &'static [(&'static str, &'static str)],
        signature: Signature,
        handler: Handler,
    ) -> Result<()> {
        self.install_family(rows, signature, handler, true)
    }
    /// The ordinary handler remains a complete invocation-local implementation;
    /// installed callers can additionally retain immutable reached-call facts.
    fn prepared_family(
        &mut self,
        rows: &'static [(&'static str, &'static str)],
        signature: Signature,
        handler: Handler,
        prepared: PreparedHandler,
    ) -> Result<()> {
        self.pure_family(rows, signature, handler)?;
        for &(identity, _) in rows {
            self.entries
                .get_mut(identity)
                .expect("installed family")
                .prepared_handler = Some(prepared);
        }
        Ok(())
    }
    fn install_shaped(
        &mut self,
        contracts: &'static [crate::bindings::Contract],
        handler: Dispatch,
        deterministic: bool,
    ) -> Result<()> {
        for row in contracts {
            for implementation in row.implementations {
                self.insert(
                    (*implementation).into(),
                    Implementation {
                        contract: row.name,
                        signature: Signature::Shaped(row, crate::bindings::Selection::Default),
                        handler,
                        prepared_handler: None,
                        deterministic,
                        requirements: Default::default(),
                    },
                )?;
            }
        }
        Ok(())
    }
    fn shaped(
        &mut self,
        rows: &'static [crate::bindings::Contract],
        handler: Handler,
    ) -> Result<()> {
        self.install_shaped(rows, Dispatch::Direct(handler), false)
    }
    fn pure_shaped(
        &mut self,
        rows: &'static [crate::bindings::Contract],
        handler: Handler,
    ) -> Result<()> {
        self.install_shaped(rows, Dispatch::Direct(handler), true)
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
                domains: row.domains,
                ports: row.ports,
            },
        );
        if let Some(handler) = row.handler {
            entry.handler = Dispatch::Direct(handler);
            entry.prepared_handler = None;
        }
        entry.deterministic &= row.deterministic;
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
    /// Admitted first domain arguments: fields, groups, schemes or transcript suites.
    pub(crate) domains: &'static [Identity],
    pub(crate) ports: crate::bindings::PortTransform,
    /// Omit for a layout-only alternative to retain the original algorithm.
    pub(crate) handler: Option<Handler>,
    pub(crate) deterministic: bool,
}
pub(super) fn alternatives() -> impl Iterator<Item = &'static Alternative> {
    [
        super::execute::ALTERNATIVES,
        crate::operations::conversions::ALTERNATIVES,
        crate::diagonal::ALTERNATIVES,
        crate::operations::pairwise::ALTERNATIVES,
    ]
    .into_iter()
    .flatten()
}

pub(crate) fn installed() -> Result<&'static Registry> {
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
            r.pure_shaped(super::execute::CONTRACTS, basic)?;
            r.shaped(super::execute::PCS_CONTRACTS, basic)?;
            r.install_shaped(
                crate::operations::arithmetic::CONTRACTS,
                Dispatch::Resolve(super::dispatch::arithmetic),
                true,
            )?;
            // Reuse the owning contract row, including all installed providers.
            for constants in crate::operations::arithmetic::CONTRACTS
                .iter()
                .filter(|row| matches!(row.name, "field.constant" | "vector.constant"))
            {
                for implementation in constants.implementations {
                    r.entries
                        .get_mut(*implementation)
                        .expect("installed literal constant")
                        .prepared_handler = Some(prepared_literal);
                }
            }
            r.prepared_family(
                crate::numerical::expression::IMPLEMENTATIONS,
                Signature::Custom(crate::numerical::expression::signature),
                expression,
                prepared_expression,
            )?;
            r.pure_shaped(crate::operations::conversions::CONTRACTS, conversions)?;
            r.pure_shaped(crate::operations::curve::CONTRACTS, curve)?;
            r.shaped(crate::operations::resources::CONTRACTS, resources)?;
            r.pure_shaped(crate::bindings::poly::COSET_CONTRACTS, numerical)?;
            r.pure_family(
                crate::operations::encoding::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::encoding::signature),
                encoding,
            )?;
            r.pure_family(
                crate::hash::IMPLEMENTATIONS,
                Signature::Custom(crate::hash::signature),
                hash,
            )?;
            r.pure_family(
                crate::operations::poseidon2::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::poseidon2::signature),
                poseidon2,
            )?;
            r.pure_family(
                crate::operations::bytes::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::bytes::signature),
                bytes,
            )?;
            r.pure_family(
                crate::operations::quotient::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::quotient::signature),
                quotient,
            )?;
            r.pure_family(
                crate::operations::selection::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::selection::signature),
                selection,
            )?;
            r.pure_family(
                crate::operations::indices::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::indices::signature),
                indices,
            )?;
            r.prepared_family(
                crate::operations::indices::CONSTANT_IMPLEMENTATIONS,
                Signature::Custom(crate::operations::indices::signature),
                indices,
                prepared_index_constant,
            )?;
            r.pure_family(
                crate::operations::external::IMPLEMENTATIONS,
                Signature::Custom(crate::operations::external::signature),
                external,
            )?;
            r.family(
                crate::oracle::IMPLEMENTATIONS,
                Signature::Custom(crate::oracle::signature),
                oracle,
            )?;
            r.family(
                crate::merkle::IMPLEMENTATIONS,
                Signature::Custom(crate::merkle::signature),
                merkle,
            )?;
            r.pure_family(
                crate::field_array::IMPLEMENTATIONS,
                Signature::Custom(crate::field_array::signature),
                field_array,
            )?;
            r.pure_family(
                crate::field_array::RESIDENT_IMPLEMENTATIONS,
                Signature::Custom(crate::field_array::signature),
                field_array,
            )?;
            r.pure_family(
                crate::fixed_vector::RESIDENT_IMPLEMENTATIONS,
                Signature::Custom(crate::fixed_vector::signature),
                fixed_vector,
            )?;
            r.pure_family(
                crate::sequence::IMPLEMENTATIONS,
                Signature::Custom(crate::sequence::signature),
                sequence,
            )?;
            r.pure_family(
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
            r.pure_family(
                super::execute::SPECIAL_IMPLEMENTATIONS,
                Signature::Custom(crate::bindings::table::relayout),
                basic,
            )?;
            r.pure_shaped(crate::operations::arithmetic::EMBEDDINGS, arithmetic)?;
            r.pure_shaped(crate::operations::curve::PAIRINGS, curve)?;
            // Resident installation derives actual ports from native-owned shapes.
            for row in crate::operations::arithmetic::CONTRACTS
                .iter()
                .chain(crate::operations::curve::CONTRACTS)
                .chain(crate::operations::curve::PAIRINGS)
            {
                let domain = if row.name.starts_with("curve.") {
                    "bls12-381.g1"
                } else {
                    "bls12-381.fr"
                };
                let binding = OperationBinding {
                    contract: row.name.into(),
                    implementation: format!("blst/resident/{}", row.name),
                    arguments: vec![domain.into()],
                    physical_arguments: vec![],
                };
                if crate::operations::blst::signature(&binding).is_some() {
                    r.insert(
                        binding.implementation.clone(),
                        Implementation {
                            contract: row.name,
                            signature: Signature::Custom(crate::operations::blst::signature),
                            handler: Dispatch::Resolve(super::dispatch::resident),
                            prepared_handler: if matches!(
                                row.name,
                                "field.constant" | "vector.constant"
                            ) {
                                Some(prepared_literal)
                            } else {
                                None
                            },
                            deterministic: true,
                            // Actual handler premises are authored here, independently
                            // of expected Contracts contribution metadata.
                            requirements: zkc_runtime::vm::ImplementationRequirements {
                                timing: if row.name == "curve.msm" {
                                    zkc_runtime::vm::TimingRequirement::VariableTime
                                } else {
                                    zkc_runtime::vm::TimingRequirement::Unspecified
                                },
                                timing_operands: if row.name == "curve.msm" {
                                    &[0, 1]
                                } else {
                                    &[]
                                },
                            },
                        },
                    )?;
                }
            }
            for &contract in crate::operations::halo2curves::CONTRACTS {
                r.insert(
                    format!("halo2curves-axiom/resident/{contract}"),
                    Implementation {
                        contract,
                        signature: Signature::Custom(crate::operations::halo2curves::signature),
                        handler: Dispatch::Resolve(super::dispatch::halo2curves),
                        prepared_handler: if matches!(
                            contract,
                            "field.constant" | "vector.constant"
                        ) {
                            Some(prepared_literal)
                        } else {
                            None
                        },
                        deterministic: true,
                        requirements: zkc_runtime::vm::ImplementationRequirements {
                            timing: if contract == "curve.msm" {
                                zkc_runtime::vm::TimingRequirement::VariableTime
                            } else {
                                zkc_runtime::vm::TimingRequirement::Unspecified
                            },
                            timing_operands: if contract == "curve.msm" {
                                &[0, 1]
                            } else {
                                &[]
                            },
                        },
                    },
                )?;
            }
            r.pure_family(
                &[("native/representation.convert", "representation.convert")],
                Signature::Custom(crate::operations::resident::conversion_signature),
                resident_conversion,
            )?;
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
fn ring(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::ring::apply(&b.ring_assets, &mut b.ring_work, args, i, &b.core.policy)
}
fn relation(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::relation::apply(
        &b.relation_assets,
        &mut b.ring_work,
        args,
        i,
        &b.core.policy,
    )
}
pub(crate) fn basic(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    b.execute_basic(&i.binding.declaration().contract, i, args)
}
fn fixed_vector(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::fixed_vector::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
fn sequence(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::sequence::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
pub(super) fn arithmetic(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::operations::arithmetic::apply(
        &i.binding.declaration().contract,
        field(i),
        args,
        i,
        &b.core.policy,
    )
}
fn prepared_literal(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    _args: &[Value],
    call: &super::CpuCall,
) -> Result<Vec<Value>> {
    crate::operations::literal::publish(call.literal()?, i, &b.core.policy)
}
fn expression(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::numerical::expression::prepare(
        i.binding.declaration(),
        i.binding.signature(),
        i.attributes,
    )?
    .apply(args, i, &b.core.policy)
}
fn prepared_expression(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
    call: &super::CpuCall,
) -> Result<Vec<Value>> {
    call.expression()?.apply(args, i, &b.core.policy)
}
pub(crate) fn conversions(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::operations::conversions::apply(
        &i.binding.declaration().contract,
        args,
        i,
        &b.core.policy,
    )
}
fn curve(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::curve::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}

fn resources(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::resources::apply(
        &i.binding.declaration().contract,
        args,
        i,
        &b.core.policy,
        &mut b.core.resources,
        &b.core.setups,
    )
}
fn numerical(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    // One owner selects its typed specialization from the admitted closed ports.
    let name = &i.binding.declaration().contract;
    if field(i) == Some(Identity::Bn254Fr) {
        crate::operations::bn254::apply(name, field(i), args, i, &b.core.policy)
    } else {
        crate::operations::plonky3::apply(
            name,
            field(i),
            args,
            i,
            &b.core.policy,
            &b.core.polynomial,
        )
    }
}
fn encoding(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::encoding::apply(
        &i.binding.declaration().contract,
        i.binding
            .declaration()
            .arguments
            .first()
            .map(|domain| Identity::parse(domain))
            .transpose()
            .map_err(|_| crate::refused("encoding-domain"))?
            .unwrap_or(Identity::None),
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
        &mut b.external_work,
    )
}
fn hash(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::hash::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
        &mut b.external_work,
    )
}
fn poseidon2(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::poseidon2::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
        &mut b.external_work,
    )
}
fn bytes(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::bytes::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
    )
}
fn quotient(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::quotient::apply(
        &i.binding.declaration().contract,
        args,
        &b.core.policy,
        i.max_output_bytes,
    )
}
fn selection(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::selection::apply(args, &b.core.policy, i.max_output_bytes)
}
fn indices(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::indices::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
    )
}
fn prepared_index_constant(
    _b: &mut CpuBackend,
    _i: &Invocation<'_>,
    _args: &[Value],
    call: &super::CpuCall,
) -> Result<Vec<Value>> {
    // Core checked the exact binding, signature and attributes at this reach;
    // its ordinary output checks still run after constructing the fresh value.
    Ok(vec![Value::Index(call.unsigned64()?)])
}
fn external(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::operations::external::apply(
        &i.binding.declaration().contract,
        args,
        i.attributes,
        &b.core.policy,
        i.max_output_bytes,
        &mut b.external_work,
    )
}
fn oracle(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::oracle::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
fn merkle(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::merkle::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}
pub(crate) fn diagonal(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::diagonal::apply(i, args, &b.core.policy)
}

pub(crate) fn pairwise(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::operations::pairwise::apply(args, &b.core.policy, i.max_output_bytes)
}

#[cfg(test)]
#[path = "registry_tests.rs"]
mod tests;

fn field_array(b: &mut CpuBackend, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
    crate::field_array::apply(&i.binding.declaration().contract, args, i, &b.core.policy)
}

fn resident_conversion(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::operations::resident::convert(i, args, &b.core.policy)
}

pub(super) fn halo2curves(
    b: &mut CpuBackend,
    i: &Invocation<'_>,
    args: &[Value],
) -> Result<Vec<Value>> {
    crate::operations::halo2curves::apply(
        &i.binding.declaration().contract,
        i,
        args,
        &b.core.policy,
    )
}
