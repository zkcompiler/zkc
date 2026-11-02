//! Family-owned admission callbacks over the runtime's catalog-resolved
//! signatures. A row declares only its contract and implementation identities;
//! ports and parameter rules come from the catalog declaration, and a family
//! chooses the physical representation of each declared port.
pub(crate) mod control;
pub(crate) mod curve;
pub(crate) mod field;
pub(crate) mod pcs;
pub(crate) mod poly;
pub(crate) mod random;
mod support;
pub(crate) mod table;
pub(crate) mod transcript;

use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    Representation, Type,
};
type Resolver = fn(&OperationBinding, &Contract, Selection) -> Option<BoundSignature>;

pub(crate) struct Contract {
    pub(crate) name: &'static str,
    pub(crate) implementations: &'static [&'static str],
    resolve: Resolver,
    pub(crate) alternatives: bool,
}
impl Contract {
    const fn new(name: &'static str, resolve: Resolver) -> Self {
        Self {
            name,
            implementations: &[],
            resolve,
            alternatives: false,
        }
    }
    pub(crate) const fn implemented_by(mut self, implementations: &'static [&'static str]) -> Self {
        self.implementations = implementations;
        self
    }
    pub(crate) const fn selectable(self) -> Self {
        Self {
            alternatives: true,
            ..self
        }
    }
    pub(crate) fn signature(
        &self,
        binding: &OperationBinding,
        selection: Selection,
    ) -> Option<BoundSignature> {
        (self.resolve)(binding, self, selection)
    }
}

/// The runtime's catalog-resolved logical signature of the binding's contract
/// and static arguments, independent of the implementation that realizes it.
pub(crate) fn declared(binding: &OperationBinding) -> Option<OperationSignature<LogicalType>> {
    OperationBinding {
        contract: binding.contract.clone(),
        arguments: binding.arguments.clone(),
        implementation: String::new(),
        physical_arguments: vec![],
    }
    .logical_signature()
    .ok()
}

/// Independent native policy; exact registry lookup owns implementation identity.
#[derive(Clone, Copy)]
pub(crate) enum Selection {
    Default,
    Alternative {
        domains: &'static [Identity],
        ports: PortTransform,
    },
}
#[derive(Clone, Copy)]
pub(crate) enum PortTransform {
    Default,
    Msb,
    Diagonal {
        output: bool,
        port: usize,
        representation: Representation,
    },
}
