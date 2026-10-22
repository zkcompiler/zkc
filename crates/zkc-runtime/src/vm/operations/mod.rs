//! Finite independently authored runtime installation. Artifact declarations can
//! select these owners, never install or override them.
mod bytes;
mod control;
mod curve;
mod encoding;
mod external;
mod field;
mod hash;
mod index;
mod matrix;
pub(super) mod numerical;
mod oracle;
mod pcs;
mod poly;
mod random;
mod relation;
mod representation;
mod support;
mod table;
mod transcript;
mod vector;

use super::{
    AdmissionError, AttributeRule, BoundSignature, ErrorCode, Identity, LogicalType,
    OperationBinding, OperationSignature, TimingRequirement, Type,
};
use std::{collections::BTreeMap, sync::OnceLock};
type Result<T> = std::result::Result<T, AdmissionError>;
type LogicalResolver = fn(&OperationBinding, &Contract) -> Result<OperationSignature<LogicalType>>;
type PhysicalResolver =
    fn(&OperationBinding, &OperationSignature<LogicalType>, Selection) -> Result<BoundSignature>;

pub(super) struct Contract {
    name: &'static str,
    implementations: &'static [&'static str],
    shape: Option<(&'static [Type], &'static [Type], AttributeRule)>,
    alternatives: bool,
    history: bool,
}
impl Contract {
    pub(super) const fn new(
        name: &'static str,
        shape: (&'static [Type], &'static [Type], AttributeRule),
    ) -> Self {
        Self {
            name,
            implementations: &[],
            shape: Some(shape),
            alternatives: false,
            history: false,
        }
    }
    pub(super) const fn selectable(
        name: &'static str,
        shape: (&'static [Type], &'static [Type], AttributeRule),
    ) -> Self {
        Self {
            alternatives: true,
            ..Self::new(name, shape)
        }
    }
    pub(super) const fn custom(name: &'static str) -> Self {
        Self {
            name,
            implementations: &[],
            shape: None,
            alternatives: false,
            history: false,
        }
    }
    /// Exact default owners, independent of domain applicability and alternatives.
    pub(super) const fn implemented_by(mut self, implementations: &'static [&'static str]) -> Self {
        self.implementations = implementations;
        self
    }
    /// A transition of protocol-visible observation or sampling history.
    /// This facet does not imply purity, totality, or a sampling law.
    pub(super) const fn history(mut self) -> Self {
        self.history = true;
        self
    }
    fn shape(&self) -> Result<OperationSignature> {
        let (inputs, outputs, attributes) = self
            .shape
            .ok_or_else(|| AdmissionError::new(ErrorCode::Signature, "contract-shape-missing"))?;
        Ok(OperationSignature {
            inputs: inputs.to_vec(),
            outputs: outputs.to_vec(),
            attributes,
        })
    }
}

/// Physical policy authored by the operation owner, separate from default selection.
pub(super) struct Alternative {
    pub(super) implementation: &'static str,
    pub(super) contract: &'static str,
    pub(super) domains: &'static [Identity],
    pub(super) timing: TimingRequirement,
    pub(super) ports: super::domain_bindings::PortTransform,
}
#[derive(Clone, Copy)]
pub(super) enum Selection {
    Default,
    Alternative(&'static Alternative),
}
impl Selection {
    pub(super) fn require_default(self) -> Result<()> {
        if matches!(self, Self::Default) {
            Ok(())
        } else {
            Err(support::failure())
        }
    }
}

pub(super) struct Contribution {
    pub(super) contracts: &'static [Contract],
    pub(super) resolve: LogicalResolver,
    pub(super) select: PhysicalResolver,
    pub(super) alternatives: &'static [Alternative],
    pub(super) physical_error: &'static str,
    pub(super) physical_only: bool,
}
pub(super) struct Registry {
    logical: BTreeMap<&'static str, (&'static Contract, &'static Contribution)>,
    physical: BTreeMap<String, PhysicalOwner>,
}
enum PhysicalOwner {
    Family(&'static str, Selection),
    Exact(BTreeMap<(Vec<String>, Vec<String>), super::contracts::ExactImplementation>),
    Aggregate {
        contract: String,
        family: Box<super::AggregateImplementationFamily>,
        id: super::ImplementationId,
        requirements: super::ImplementationRequirements,
    },
}
impl Registry {
    pub(super) fn installed_implementations(&self) -> Vec<(String, &'static str)> {
        self.physical
            .iter()
            .filter_map(|(implementation, owner)| {
                let contract = match owner {
                    PhysicalOwner::Family(contract, _) => *contract,
                    PhysicalOwner::Exact(rows) => {
                        rows.values().next()?.declaration.contract.as_str()
                    }
                    PhysicalOwner::Aggregate { contract, .. } => contract,
                };
                self.logical
                    .get(contract)
                    .map(|(row, _)| (implementation.clone(), row.name))
            })
            .collect()
    }
    pub(super) fn logical_selection(
        &self,
        binding: &OperationBinding,
    ) -> Result<OperationSignature<LogicalType>> {
        if !binding.physical_arguments.is_empty() {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "logical-physical-arguments",
            ));
        }
        let logical = logical_signature(binding)?;
        if binding.implementation.is_empty() {
            return Ok(logical);
        }
        let fail = || AdmissionError::new(ErrorCode::Signature, "implementation-binding-mismatch");
        match self
            .physical
            .get(&binding.implementation)
            .ok_or_else(fail)?
        {
            PhysicalOwner::Family(contract, _) => {
                if *contract != binding.contract {
                    return Err(fail());
                }
                if let Some(result) = super::aggregate_bindings::standard_logical(binding, &logical)
                {
                    result?;
                } else {
                    self.select(binding, &logical)?;
                }
            }
            PhysicalOwner::Exact(rows) => {
                if !rows.values().any(|row| {
                    row.declaration.contract == binding.contract
                        && row.declaration.arguments == binding.arguments
                }) {
                    return Err(fail());
                }
            }
            PhysicalOwner::Aggregate {
                contract, family, ..
            } => {
                if *contract != binding.contract {
                    return Err(fail());
                }
                family.check_logical(binding, &logical)?;
            }
        }
        Ok(logical)
    }
    pub(super) fn clear_implementations(&mut self) {
        self.physical.clear();
    }
    pub(super) fn add_exact(&mut self, row: super::contracts::ExactImplementation) -> Result<()> {
        // Standard names remain reserved even when their deployment contribution
        // is absent. One physical owner may support several static specializations.
        if installed()?
            .physical
            .contains_key(&row.declaration.implementation)
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "duplicate-implementation-owner",
            ));
        }
        match self.physical.entry(row.declaration.implementation.clone()) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(PhysicalOwner::Exact(BTreeMap::from([(
                    (
                        row.declaration.arguments.clone(),
                        row.declaration.physical_arguments.clone(),
                    ),
                    row,
                )])));
                Ok(())
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                let PhysicalOwner::Exact(rows) = entry.get_mut() else {
                    return Err(AdmissionError::new(
                        ErrorCode::Signature,
                        "duplicate-implementation-owner",
                    ));
                };
                if rows
                    .values()
                    .any(|installed| installed.declaration.contract != row.declaration.contract)
                    || rows.contains_key(&(
                        row.declaration.arguments.clone(),
                        row.declaration.physical_arguments.clone(),
                    ))
                {
                    return Err(AdmissionError::new(
                        ErrorCode::Signature,
                        "duplicate-implementation-owner",
                    ));
                }
                rows.insert(
                    (
                        row.declaration.arguments.clone(),
                        row.declaration.physical_arguments.clone(),
                    ),
                    row,
                );
                Ok(())
            }
        }
    }
    pub(super) fn resolve_physical(
        &self,
        binding: &OperationBinding,
        physical: &[super::PhysicalType],
    ) -> Result<(
        BoundSignature,
        Option<super::ImplementationId>,
        super::ImplementationRequirements,
    )> {
        if let Some(PhysicalOwner::Aggregate {
            contract,
            family,
            id,
            requirements,
        }) = self.physical.get(&binding.implementation)
        {
            if *contract != binding.contract {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "implementation-binding-mismatch",
                ));
            }
            let signature = family.signature(binding, &logical_signature(binding)?, physical)?;
            return Ok((signature, Some(*id), *requirements));
        }
        if let Some(PhysicalOwner::Exact(rows)) = self.physical.get(&binding.implementation) {
            let row = rows
                .get(&(
                    binding.arguments.clone(),
                    binding.physical_arguments.clone(),
                ))
                .ok_or_else(|| {
                    AdmissionError::new(ErrorCode::Signature, "implementation-binding-mismatch")
                })?;
            if row.declaration != *binding {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "implementation-binding-mismatch",
                ));
            }
            return Ok((row.signature.clone(), Some(row.id), row.requirements));
        }
        let (_, owner) = self.logical.get(binding.contract.as_str()).ok_or_else(|| {
            AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding")
        })?;
        let logical = if owner.physical_only {
            OperationSignature {
                inputs: vec![],
                outputs: vec![],
                attributes: AttributeRule::None,
            }
        } else {
            logical_signature(binding)?
        };
        let signature = self.select_physical(binding, &logical, physical)?;
        let timing = match self.physical.get(&binding.implementation) {
            Some(PhysicalOwner::Family(_, Selection::Alternative(row))) => row.timing,
            _ => TimingRequirement::Unspecified,
        };
        Ok((
            signature,
            None,
            super::ImplementationRequirements {
                timing,
                timing_operands: &[],
            },
        ))
    }
    pub(super) fn add_family(
        &mut self,
        implementation: String,
        contract: String,
        family: super::AggregateImplementationFamily,
        id: super::ImplementationId,
        requirements: super::ImplementationRequirements,
    ) -> Result<()> {
        if installed()?.physical.contains_key(&implementation)
            || self.physical.contains_key(&implementation)
            || !family.supports(&contract)
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "duplicate-or-invalid-implementation-family",
            ));
        }
        self.physical.insert(
            implementation,
            PhysicalOwner::Aggregate {
                contract,
                family: Box::new(family),
                id,
                requirements,
            },
        );
        Ok(())
    }
    fn assemble(contributions: &[&'static Contribution]) -> Result<Self> {
        let mut registry = Self {
            logical: BTreeMap::new(),
            physical: BTreeMap::new(),
        };
        for &contribution in contributions {
            for contract in contribution.contracts {
                if registry
                    .logical
                    .insert(contract.name, (contract, contribution))
                    .is_some()
                {
                    return Err(AdmissionError::new(
                        ErrorCode::Signature,
                        "duplicate-logical-owner",
                    ));
                }
                for implementation in contract.implementations {
                    registry.install_physical(implementation, contract.name, Selection::Default)?;
                }
            }
            for alternative in contribution.alternatives {
                registry.install_physical(
                    alternative.implementation,
                    alternative.contract,
                    Selection::Alternative(alternative),
                )?;
            }
        }
        if registry
            .physical
            .values()
            .any(|row| matches!(row, PhysicalOwner::Family(contract, _) if !registry.logical.contains_key(contract)))
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "implementation-owner-missing",
            ));
        }
        if registry.physical.values().any(|row| {
            matches!(row, PhysicalOwner::Family(name, Selection::Alternative(_)) if !registry.logical[name].0.alternatives)
        }) {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "implementation-owner-shape",
            ));
        }
        Ok(registry)
    }
    fn install_physical(
        &mut self,
        implementation: &str,
        contract: &'static str,
        select: Selection,
    ) -> Result<()> {
        match self.physical.entry(implementation.into()) {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(PhysicalOwner::Family(contract, select));
                Ok(())
            }
            std::collections::btree_map::Entry::Occupied(_) => Err(AdmissionError::new(
                ErrorCode::Signature,
                "duplicate-implementation-owner",
            )),
        }
    }
}
fn installed() -> Result<&'static Registry> {
    static REGISTRY: OnceLock<Result<Registry>> = OnceLock::new();
    REGISTRY
        .get_or_init(|| Ok(standard_registry()))
        .as_ref()
        .map_err(Clone::clone)
}
pub(super) fn standard_registry() -> Registry {
    Registry::assemble(&[
        &bytes::CONTRIBUTION,
        &encoding::CONTRIBUTION,
        &hash::CONTRIBUTION,
        &control::CONTRIBUTION,
        &curve::CONTRIBUTION,
        &external::CONTRIBUTION,
        &field::CONTRIBUTION,
        &index::CONTRIBUTION,
        &matrix::CONTRIBUTION,
        &numerical::CONTRIBUTION,
        &oracle::CONTRIBUTION,
        &pcs::CONTRIBUTION,
        &poly::CONTRIBUTION,
        &random::CONTRIBUTION,
        &relation::CONTRIBUTION,
        &representation::CONTRIBUTION,
        &transcript::CONTRIBUTION,
        &vector::CONTRIBUTION,
        &table::CONTRIBUTION,
        &super::fixed_vector::CONTRIBUTION,
        &super::sequence::CONTRIBUTION,
        &super::field_array::CONTRIBUTION,
        &super::resource_unit::CONTRIBUTION,
    ])
    .expect("valid standard operation contribution")
}
pub(super) fn installed_implementations() -> Result<Vec<(String, &'static str)>> {
    Ok(installed()?
        .physical
        .iter()
        .filter_map(|(implementation, row)| match row {
            PhysicalOwner::Family(contract, _) => Some((implementation.clone(), *contract)),
            PhysicalOwner::Exact(_) | PhysicalOwner::Aggregate { .. } => None,
        })
        .collect())
}

pub(super) fn observes_history(contract: &str) -> Result<bool> {
    installed()?.observes_history(contract)
}

pub(super) fn logical_signature(
    binding: &OperationBinding,
) -> Result<OperationSignature<LogicalType>> {
    let registry = installed()?;
    let (_, owner) = registry
        .logical
        .get(binding.contract.as_str())
        .ok_or_else(|| {
            AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding")
        })?;
    if owner.physical_only {
        return Err(AdmissionError::new(
            ErrorCode::Signature,
            "binding-adapter-at-logical-stage",
        ));
    }
    declared_logical_signature(binding)
}

/// Mathematical erasure used when a trusted owner contributes a physical
/// implementation. This does not admit a physical adapter at the source stage.
pub(super) fn declared_logical_signature(
    binding: &OperationBinding,
) -> Result<OperationSignature<LogicalType>> {
    let registry = installed()?;
    let (contract, owner) = registry
        .logical
        .get(binding.contract.as_str())
        .ok_or_else(|| {
            AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding")
        })?;
    (owner.resolve)(binding, contract)
}
pub(super) fn signature(binding: &OperationBinding) -> Result<BoundSignature> {
    let registry = installed()?;
    if registry
        .logical
        .get(binding.contract.as_str())
        .is_some_and(|(_, owner)| owner.physical_only)
    {
        return select_signature(
            binding,
            &OperationSignature {
                inputs: vec![],
                outputs: vec![],
                attributes: AttributeRule::None,
            },
        );
    }
    select_signature(binding, &logical_signature(binding)?)
}
pub(super) fn select_signature(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
) -> Result<BoundSignature> {
    installed()?.select(binding, logical)
}
impl Registry {
    fn observes_history(&self, contract: &str) -> Result<bool> {
        self.logical
            .get(contract)
            .map(|(row, _)| row.history)
            .ok_or_else(|| {
                AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding")
            })
    }
    fn select(
        &self,
        binding: &OperationBinding,
        logical: &OperationSignature<LogicalType>,
    ) -> Result<BoundSignature> {
        let physical = binding
            .physical_arguments
            .iter()
            .map(|s| super::PhysicalType::parse(s))
            .collect::<Result<Vec<_>>>()?;
        self.select_physical(binding, logical, &physical)
    }
    fn select_physical(
        &self,
        binding: &OperationBinding,
        logical: &OperationSignature<LogicalType>,
        physical: &[super::PhysicalType],
    ) -> Result<BoundSignature> {
        let fail = || {
            AdmissionError::new(
                ErrorCode::Signature,
                self.logical
                    .get(binding.contract.as_str())
                    .map_or("uninstalled operation binding", |(_, owner)| {
                        owner.physical_error
                    }),
            )
        };
        let PhysicalOwner::Family(contract, select) = self
            .physical
            .get(&binding.implementation)
            .ok_or_else(fail)?
        else {
            return Err(fail());
        };
        if *contract != binding.contract {
            return Err(fail());
        }
        let (contract, owner) = self.logical.get(contract).ok_or_else(fail)?;
        if let Selection::Alternative(row) = select
            && (!contract.alternatives
                || !row.domains.iter().any(|domain| {
                    binding.arguments.first().map(String::as_str) == Some(domain.name())
                }))
        {
            return Err(fail());
        }
        if binding.contract == "transcript.native.indexed.observe.data" {
            return transcript::select_payload(binding, logical, *select, physical);
        }
        if let Some(result) =
            super::aggregate_bindings::standard_signature(binding, logical, physical)
        {
            return result;
        }
        if !physical.is_empty() {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "unexpected-physical-arguments",
            ));
        }
        (owner.select)(binding, logical, *select)
    }
}

pub(super) fn default_ports(
    _: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    selection.require_default()?;
    super::domain_bindings::physical_signature(
        logical,
        super::domain_bindings::PortTransform::Default,
    )
}

#[cfg(test)]
mod tests;
