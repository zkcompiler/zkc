//! Resolve immutable handler facts from independently reported Native ports.
use super::{NativeBackend, registry::Handler};
use crate::{Result, Value, operations::field::Family};
use zkc_runtime::vm::{BoundSignature, Invocation, OperationBinding};

#[derive(Clone, Copy)]
pub(super) enum Dispatch {
    Direct(Handler),
    Resolve(fn(&OperationBinding, &BoundSignature) -> Option<Handler>),
}
impl Dispatch {
    pub(super) fn resolve(
        self,
        binding: &OperationBinding,
        signature: &BoundSignature,
    ) -> Option<Handler> {
        match self {
            Self::Direct(handler) => Some(handler),
            Self::Resolve(resolve) => resolve(binding, signature),
        }
    }
}

macro_rules! scalar_handlers {
    ($($function:ident => $contract:literal),+ $(,)?) => {
        $(fn $function<S: Family>(
            backend: &mut NativeBackend,
            invocation: &Invocation<'_>,
            args: &[Value],
        ) -> Result<Vec<Value>> {
            crate::operations::arithmetic::scalar::<S>(
                $contract, args, invocation, &backend.core.policy,
            )
        })+

        fn scalar<S: Family>(name: &str) -> Option<Handler> {
            match name {
                $($contract => Some($function::<S>),)+
                _ => None,
            }
        }
    };
}
scalar_handlers! {
    add => "field.add",
    subtract => "field.sub",
    multiply => "field.mul",
    negate => "field.neg",
    inverse => "field.inverse",
    equal => "field.equal",
    from_index => "field.from_index",
}

pub(super) fn arithmetic(
    binding: &OperationBinding,
    signature: &BoundSignature,
) -> Option<Handler> {
    let field = signature
        .inputs
        .iter()
        .chain(&signature.outputs)
        .find_map(|ty| ty.logical().identity().scalar_field());
    crate::operations::field::with_field!(field?, |S| {
        Ok(scalar::<S>(&binding.contract).unwrap_or(super::registry::arithmetic))
    })
    .ok()
}

pub(super) fn resident(binding: &OperationBinding, _signature: &BoundSignature) -> Option<Handler> {
    Some(
        scalar::<zkc_kernels::blst::bls12_381::ScalarElement>(&binding.contract)
            .unwrap_or(super::registry::blst),
    )
}

// Keep the existing blst resolver monomorphized; Halo has its own typed leaves.
pub(super) fn halo2curves(
    binding: &OperationBinding,
    _signature: &BoundSignature,
) -> Option<Handler> {
    Some(
        scalar::<zkc_kernels::halo2curves::bn254::ScalarElement>(&binding.contract)
            .unwrap_or(super::registry::halo2curves),
    )
}
