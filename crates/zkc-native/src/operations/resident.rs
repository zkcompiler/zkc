//! Shared resident port mechanics. Providers own positive inventories and codecs.
use super::{arithmetic, curve};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type,
};

// Arithmetic stays on validated wrappers. Bulk views and destinations use
// provider-owned accessors, preserving validation without raw reconstruction.
macro_rules! group_family {
    ($kernel:ident, $group:ident, $bulk:ident, $point:ident, $points:ident,
     $wrap:expr, $read:expr, $scaling:ident) => {
        impl $crate::operations::curve::Group for $kernel::$group {
            type Scalar = $kernel::ScalarElement;
            type Error = $kernel::Error;
            fn generator() -> Self {
                Self::generator()
            }
            fn identity() -> Self {
                Self::identity()
            }
            fn add(self, rhs: Self) -> Self {
                Self::add(&self, &rhs)
            }
            fn neg(self) -> Self {
                Self::neg(&self)
            }
            fn scale(self, scalar: Self::Scalar) -> Self {
                Self::scale(&self, $kernel::Scalar::from_element(scalar))
            }
        }
        impl $crate::operations::curve::PointView<$kernel::$group> for &$kernel::$bulk {
            fn len(self) -> usize {
                self.len()
            }
            fn get(self, index: usize) -> Option<$kernel::$group> {
                self.get(index)
            }
        }
        impl $crate::operations::curve::PointStorage<$kernel::$group> for $kernel::$bulk {
            type View<'a> = &'a Self;
            type Output = Self;
            fn reserve(len: usize) -> $crate::Result<Self> {
                Self::with_capacity(len).map_err(failure)
            }
            fn push(output: &mut Self, point: $kernel::$group) {
                output.push(point);
            }
            $scaling!($kernel, $group);
        }
        impl $crate::operations::curve::Family<$kernel::$bulk> for $kernel::$group {
            const RESIDENT_STORAGE: bool = true;
            // MSM has a separate handler borrowing complete bulk carriers.
            fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
                failure(error)
            }
            fn point(value: &$crate::Value) -> $crate::Result<Self> {
                if let $crate::Value::$point(value) = value {
                    Ok(($read)(value))
                } else {
                    Err($crate::refused("kernel-operands"))
                }
            }
            fn points(value: &$crate::Value) -> $crate::Result<&$kernel::$bulk> {
                if let $crate::Value::$points(value) = value {
                    Ok(value)
                } else {
                    Err($crate::refused("kernel-operands"))
                }
            }
            fn scalar(value: &$crate::Value) -> $crate::Result<Self::Scalar> {
                <$kernel::ScalarElement as $crate::operations::field::Family>::field(value)
            }
            fn scalars(value: &$crate::Value) -> $crate::Result<&[Self::Scalar]> {
                <$kernel::ScalarElement as $crate::operations::field::Family>::vector(value)
            }
            fn value(value: Self) -> $crate::Value {
                $crate::Value::$point(($wrap)(value))
            }
            fn values(values: $kernel::$bulk) -> $crate::Value {
                $crate::Value::$points(std::sync::Arc::new(values))
            }
            fn limit(policy: &$crate::Policy, len: usize) -> $crate::Result<()> {
                policy.typed_groups::<Self>(len)
            }
            fn width() -> usize {
                std::mem::size_of::<Self>()
            }
        }
    };
}
pub(crate) use group_family;

#[cfg(test)]
#[path = "resident_point_tests.rs"]
mod point_tests;

pub(crate) fn signature_with(
    binding: &OperationBinding,
    provider: &str,
    physical: &impl Fn(Type, Identity) -> Option<PhysicalType>,
) -> Option<BoundSignature> {
    if binding.implementation != format!("{provider}/resident/{}", binding.contract) {
        return None;
    }
    let source = OperationBinding {
        implementation: format!("arkworks/{}", binding.contract),
        ..binding.clone()
    };
    let rows = if binding.contract.starts_with("field.") || binding.contract.starts_with("vector.")
    {
        arithmetic::CONTRACTS
    } else if binding.contract.starts_with("curve.") {
        curve::CONTRACTS
    } else if binding.contract == "pairing.check" {
        curve::PAIRINGS
    } else {
        return None;
    };
    let row = rows.iter().find(|row| row.name == binding.contract)?;
    let mut signature = row.signature(&source, crate::bindings::Selection::Default)?;
    let mut changed = false;
    for ty in signature.inputs.iter_mut().chain(&mut signature.outputs) {
        if matches!(ty.kind(), Type::Bool | Type::Index | Type::Indices) {
            continue;
        }
        *ty = physical(ty.kind(), ty.logical().identity())?;
        changed = true;
    }
    changed.then_some(signature)
}

pub(crate) fn conversion_signature_with(
    binding: &OperationBinding,
    physical: &impl Fn(Type, Identity) -> Option<PhysicalType>,
) -> Option<BoundSignature> {
    if binding.contract != "representation.convert"
        || binding.implementation != "native/representation.convert"
    {
        return None;
    }
    let [logical] = binding.arguments.as_slice() else {
        return None;
    };
    let [source, target] = binding.physical_arguments.as_slice() else {
        return None;
    };
    let logical = LogicalType::parse(logical).ok()?;
    let resident = physical(logical.kind(), logical.identity())?;
    let ark = PhysicalType::default_for(logical.clone()).ok()?;
    let source = [ark.clone(), resident.clone()]
        .into_iter()
        .find(|ty| &ty.spelling() == source)?;
    let target = [ark.clone(), resident.clone()]
        .into_iter()
        .find(|ty| &ty.spelling() == target)?;
    if !((source == ark && target == resident) || (source == resident && target == ark)) {
        return None;
    }
    Some(OperationSignature {
        inputs: vec![source],
        outputs: vec![target],
        attributes: AttributeRule::None,
    })
}

pub(crate) fn is_resident(ty: &PhysicalType) -> bool {
    super::blst::is_resident(ty) || super::halo2curves::is_resident(ty)
}
pub(crate) fn conversion_signature(binding: &OperationBinding) -> Option<BoundSignature> {
    super::blst::conversion_signature(binding)
        .or_else(|| super::halo2curves::conversion_signature(binding))
}
pub(crate) fn convert(
    invocation: &zkc_runtime::vm::Invocation<'_>,
    args: &[crate::Value],
    policy: &crate::Policy,
) -> crate::Result<Vec<crate::Value>> {
    let signature = invocation.binding.signature();
    if signature
        .inputs
        .iter()
        .chain(&signature.outputs)
        .any(super::blst::is_resident)
    {
        super::blst::convert(invocation, args, policy)
    } else if signature
        .inputs
        .iter()
        .chain(&signature.outputs)
        .any(super::halo2curves::is_resident)
    {
        super::halo2curves::convert(invocation, args, policy)
    } else {
        Err(crate::refused("representation-conversion"))
    }
}

pub(crate) fn collect_iter<T, U>(
    values: impl ExactSizeIterator<Item = T>,
    convert: impl Fn(T) -> crate::Result<U>,
) -> crate::Result<std::sync::Arc<[U]>> {
    let mut converted = arithmetic::reserve(values.len())?;
    for value in values {
        converted.push(convert(value)?);
    }
    Ok(converted.into())
}

/// Shared conversion admission; endpoints provide explicit typed transitions.
fn conversion_output(
    value: &crate::Value,
    len: usize,
    width: usize,
    policy: &crate::Policy,
) -> crate::Result<usize> {
    if value.ty() == Type::Vector {
        policy.vector(len)?;
    }
    if value.ty() == Type::Groups && len > policy.max_groups.min(32768) {
        return Err(crate::exhausted("group-limit"));
    }
    if width == 0 {
        Ok(512)
    } else {
        crate::value::size(len, width)
    }
}
pub(crate) fn convert_value(
    invocation: &zkc_runtime::vm::Invocation<'_>,
    args: &[crate::Value],
    policy: &crate::Policy,
    shape: impl FnOnce(&crate::Value) -> (usize, usize),
    convert: impl FnOnce(&crate::Value) -> crate::Result<crate::Value>,
) -> crate::Result<Vec<crate::Value>> {
    use zkc_runtime::vm::Value as _;
    let [value] = args else {
        return Err(crate::refused("kernel-operands"));
    };
    let signature = invocation.binding.signature();
    if !value.has_type(&signature.inputs[0]) {
        return Err(crate::refused("kernel-operands"));
    }
    let (len, width) = shape(value);
    let retained = conversion_output(value, len, width, policy)?;
    let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
    call.work_items(len.max(1), 4096, 1)?;
    let output = call.scalar(retained)?;
    // Exporting provider bulk storage to Arc<[T]> overlaps the temporary Vec
    // and final allocation. Imports adopt the private destination Vec directly.
    let staging = if width != 0 && is_resident(&signature.inputs[0]) {
        retained
    } else {
        0
    };
    let _workspace = call.reserve_workspace::<u8>(staging)?;
    let value = output.finish(|| convert(value))?;
    if !value.has_type(&signature.outputs[0]) {
        return Err(crate::refused("representation-conversion"));
    }
    Ok(vec![value])
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn providers_own_only_their_exact_installed_leaves() {
        for (identity, kind) in [
            (Identity::Bn254Fr, Type::Field),
            (Identity::Bn254Fr, Type::Vector),
            (Identity::Bn254G1, Type::Group),
            (Identity::Bn254G1, Type::Groups),
            (Identity::Bn254G2, Type::Group),
            (Identity::Bn254G2, Type::Groups),
        ] {
            let ty = super::super::halo2curves::physical(kind, identity).unwrap();
            assert!(super::super::halo2curves::is_resident(&ty));
            assert!(!super::super::blst::is_resident(&ty));
            assert!(super::super::blst::physical(kind, identity).is_none());
            assert!(!is_resident(
                &PhysicalType::default_for(ty.logical().clone()).unwrap()
            ));
        }
        assert!(super::super::halo2curves::physical(Type::Group, Identity::Bn254Gt).is_none());
        assert!(super::super::halo2curves::physical(Type::Matrix, Identity::Bn254Fr).is_none());
    }
}
