//! Exact native signature shapes and family-owned admission callbacks.
//! Independent of the runtime's logical contract resolver.
pub(crate) mod control;
pub(crate) mod curve;
pub(crate) mod field;
pub(crate) mod pcs;
pub(crate) mod poly;
pub(crate) mod random;
mod support;
pub(crate) mod table;
pub(crate) mod transcript;

use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, OperationBinding, Representation, Type,
};
type Resolver = fn(&OperationBinding, &Contract, Selection) -> Option<BoundSignature>;

pub(crate) struct Contract {
    pub(crate) name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
    resolve: Resolver,
    pub(crate) alternatives: bool,
}
impl Contract {
    const fn new(
        name: &'static str,
        inputs: &'static [Type],
        outputs: &'static [Type],
        attributes: AttributeRule,
        resolve: Resolver,
    ) -> Self {
        Self {
            name,
            inputs,
            outputs,
            attributes,
            resolve,
            alternatives: false,
        }
    }
    const fn selectable(self) -> Self {
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

/// Independent native policy; exact registry lookup owns implementation identity.
#[derive(Clone, Copy)]
pub(crate) enum Selection {
    Default,
    Alternative {
        primary: Identity,
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
