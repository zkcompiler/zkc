//! Finite independently authored runtime installation. Artifact declarations can
//! select these owners, never install or override them.
mod control;
mod curve;
mod external;
mod field;
mod index;
mod matrix;
mod oracle;
mod pcs;
mod poly;
mod random;
mod support;
mod table;
mod transcript;
mod vector;

use super::{
    AdmissionError, AttributeRule, BoundSignature, ErrorCode, Identity, KernelSignature,
    LogicalType, OperationBinding, Type,
};
use std::{collections::BTreeMap, sync::OnceLock};
type Result<T> = std::result::Result<T, AdmissionError>;
type LogicalResolver = fn(&OperationBinding, &Contract) -> Result<KernelSignature<LogicalType>>;
type PhysicalResolver =
    fn(&OperationBinding, &KernelSignature<LogicalType>, Selection) -> Result<BoundSignature>;

pub(super) struct Contract {
    name: &'static str,
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
            shape: None,
            alternatives: false,
            history: false,
        }
    }
    /// A transition of protocol-visible observation or sampling history.
    /// This facet does not imply purity, totality, or a sampling law.
    pub(super) const fn history(mut self) -> Self {
        self.history = true;
        self
    }
    fn shape(&self) -> Result<KernelSignature> {
        let (inputs, outputs, attributes) = self
            .shape
            .ok_or_else(|| AdmissionError::new(ErrorCode::Signature, "contract-shape-missing"))?;
        Ok(KernelSignature {
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
    pub(super) primary: Identity,
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
    pub(super) providers: &'static [&'static str],
    pub(super) select: PhysicalResolver,
    pub(super) alternatives: &'static [Alternative],
    pub(super) logical_refusals: &'static [(&'static str, &'static str)],
    pub(super) physical_error: &'static str,
    pub(super) physical_only: bool,
}
struct Registry {
    logical: BTreeMap<&'static str, (&'static Contract, &'static Contribution)>,
    refusals: BTreeMap<&'static str, &'static str>,
    physical: BTreeMap<String, (&'static str, Selection)>,
}
impl Registry {
    fn assemble(contributions: &[&'static Contribution]) -> Result<Self> {
        let mut registry = Self {
            logical: BTreeMap::new(),
            refusals: BTreeMap::new(),
            physical: BTreeMap::new(),
        };
        for &contribution in contributions {
            for &(contract, detail) in contribution.logical_refusals {
                if registry.refusals.insert(contract, detail).is_some() {
                    return Err(AdmissionError::new(
                        ErrorCode::Signature,
                        "duplicate-logical-owner",
                    ));
                }
            }
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
                for provider in contribution.providers {
                    registry.install_physical(
                        &format!("{provider}/{}", contract.name),
                        contract.name,
                        Selection::Default,
                    )?;
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
            .refusals
            .keys()
            .any(|name| registry.logical.contains_key(name))
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "duplicate-logical-owner",
            ));
        }
        if registry
            .physical
            .values()
            .any(|(contract, _)| !registry.logical.contains_key(contract))
        {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "implementation-owner-missing",
            ));
        }
        if registry.physical.values().any(|(name, selection)| {
            matches!(selection, Selection::Alternative(_)) && !registry.logical[name].0.alternatives
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
                slot.insert((contract, select));
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
        .get_or_init(|| {
            let registry = Registry::assemble(&[
                &control::CONTRIBUTION,
                &curve::CONTRIBUTION,
                &external::CONTRIBUTION,
                &field::CONTRIBUTION,
                &index::CONTRIBUTION,
                &matrix::CONTRIBUTION,
                &oracle::CONTRIBUTION,
                &pcs::CONTRIBUTION,
                &poly::CONTRIBUTION,
                &random::CONTRIBUTION,
                &transcript::CONTRIBUTION,
                &vector::CONTRIBUTION,
                &table::CONTRIBUTION,
                &super::fixed_vector::CONTRIBUTION,
                &super::sequence::CONTRIBUTION,
                &super::field_array::CONTRIBUTION,
                &super::resource_unit::CONTRIBUTION,
            ])?;
            Ok(registry)
        })
        .as_ref()
        .map_err(Clone::clone)
}
pub(super) fn installed_implementations() -> Result<Vec<(String, &'static str)>> {
    Ok(installed()?
        .physical
        .iter()
        .map(|(implementation, (contract, _))| (implementation.clone(), *contract))
        .collect())
}

pub(super) fn observes_history(contract: &str) -> Result<bool> {
    installed()?.observes_history(contract)
}

pub(super) fn logical_signature(
    binding: &OperationBinding,
) -> Result<KernelSignature<LogicalType>> {
    let registry = installed()?;
    if let Some(detail) = registry.refusals.get(binding.contract.as_str()) {
        return Err(AdmissionError::new(ErrorCode::Signature, *detail));
    }
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
            &KernelSignature {
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
    logical: &KernelSignature<LogicalType>,
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
        logical: &KernelSignature<LogicalType>,
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
        let (contract, select) = self
            .physical
            .get(&binding.implementation)
            .ok_or_else(fail)?;
        if *contract != binding.contract {
            return Err(fail());
        }
        let (contract, owner) = self.logical.get(contract).ok_or_else(fail)?;
        if let Selection::Alternative(row) = select
            && (!contract.alternatives
                || binding.arguments.first().map(String::as_str) != Some(row.primary.name()))
        {
            return Err(fail());
        }
        (owner.select)(binding, logical, *select)
    }
}

pub(super) fn default_ports(
    _: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
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
