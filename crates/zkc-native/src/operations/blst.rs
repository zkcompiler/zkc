//! Resident blst adaptation. Arithmetic reuses the ordinary dense families;
//! provider changes occur only in the explicit representation conversion call.
use super::{arithmetic, curve, field};
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_kernels::blst::bls12_381::{self as kernel, arkworks as bridge};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, Invocation, LogicalType, OperationBinding,
    OperationSignature, PhysicalType, Type,
};

pub(crate) fn failure(error: kernel::Error) -> zkc_runtime::vm::BackendError {
    match error {
        kernel::Error::Allocation => exhausted("allocation"),
        kernel::Error::CapacityOverflow => exhausted("capacity-overflow"),
        kernel::Error::LengthMismatch => refused("length-mismatch"),
        kernel::Error::InvalidEncoding => refused("provider-conversion"),
    }
}

/// Positive flat inventory: sharing a nominal domain never enables GT or PCS.
pub(crate) fn physical(kind: Type, identity: Identity) -> Option<PhysicalType> {
    crate::contracts::physical(kind, identity)
}
pub(crate) fn is_resident(ty: &PhysicalType) -> bool {
    physical(ty.kind(), ty.logical().identity()).as_ref() == Some(ty)
}

// The native shape inventory is authored separately from runtime expectations.
// Reuse the family shapes, then substitute only the positive resident inventory.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    signature_with(binding, &physical)
}
pub(crate) fn signature_with(
    binding: &OperationBinding,
    physical: &impl Fn(Type, Identity) -> Option<PhysicalType>,
) -> Option<BoundSignature> {
    if binding.implementation != format!("blst/resident/{}", binding.contract) {
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

pub(crate) fn conversion_signature(binding: &OperationBinding) -> Option<BoundSignature> {
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

impl field::Family for kernel::ScalarElement {
    const RESIDENT_STORAGE: bool = true;
    fn field(v: &Value) -> Result<Self> {
        if let Value::BlstField(v) = v {
            Ok(v.into_element())
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn vector(v: &Value) -> Result<&[Self]> {
        if let Value::BlstVector(v) = v {
            Ok(v.as_elements())
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn field_value(v: Self) -> Value {
        Value::BlstField(kernel::Scalar::from_element(v))
    }
    fn vector_value(v: Vec<Self>) -> Value {
        Value::BlstVector(Arc::new(kernel::ScalarVector::from_elements(v)))
    }
    fn decimal(s: &str) -> Result<Self> {
        #[cfg(test)]
        super::field::LITERAL_DECODES.with(|count| count.set(count.get() + 1));
        kernel::parse_decimal(s)
            .map(kernel::Scalar::into_element)
            .map_err(crate::field_error)
    }
}

macro_rules! resident_group {
    ($element:ty, $group:ty, $bulk:ty, $point:ident, $points:ident, $wrap:expr, $read:expr) => {
        impl curve::Group for $element {
            type Scalar = kernel::ScalarElement;
            type Error = std::convert::Infallible;
            fn generator() -> Self {
                <$group>::generator().into_element()
            }
            fn identity() -> Self {
                <$group>::identity().into_element()
            }
            fn add(self, rhs: Self) -> Self {
                <$group>::from_element(self)
                    .add(&<$group>::from_element(rhs))
                    .into_element()
            }
            fn neg(self) -> Self {
                <$group>::from_element(self).neg().into_element()
            }
            fn scale(self, s: Self::Scalar) -> Self {
                <$group>::from_element(self)
                    .scale(kernel::Scalar::from_element(s))
                    .into_element()
            }
        }
        impl curve::Family for $element {
            const RESIDENT_STORAGE: bool = true;
            // Slice MSM is absent: apply() borrows the retained provider bulk
            // carriers directly, without reconstructing their buffers.
            fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
                match error {}
            }
            fn point(v: &Value) -> Result<Self> {
                if let Value::$point(v) = v {
                    Ok(($read)(v).into_element())
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn points(v: &Value) -> Result<&[Self]> {
                if let Value::$points(v) = v {
                    Ok(v.as_elements())
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn scalar(v: &Value) -> Result<Self::Scalar> {
                <kernel::ScalarElement as field::Family>::field(v)
            }
            fn scalars(v: &Value) -> Result<&[Self::Scalar]> {
                <kernel::ScalarElement as field::Family>::vector(v)
            }
            fn value(v: Self) -> Value {
                Value::$point(($wrap)(<$group>::from_element(v)))
            }
            fn values(v: Vec<Self>) -> Value {
                Value::$points(Arc::new(<$bulk>::from_elements(v)))
            }
            fn limit(p: &Policy, n: usize) -> Result<()> {
                p.typed_groups::<Self>(n)
            }
            fn width() -> usize {
                std::mem::size_of::<Self>()
            }
        }
    };
}
resident_group!(
    kernel::G1Element,
    kernel::G1,
    kernel::G1Vector,
    BlstG1,
    BlstG1Vector,
    |v| v,
    |v: &kernel::G1| *v
);
resident_group!(
    kernel::G2Element,
    kernel::G2,
    kernel::G2Vector,
    BlstG2,
    BlstG2Vector,
    Arc::new,
    |v: &Arc<kernel::G2>| **v
);

pub(crate) fn apply(
    name: &str,
    invocation: &Invocation<'_>,
    args: &[Value],
    policy: &Policy,
) -> Result<Vec<Value>> {
    if name.starts_with("field.") || name.starts_with("vector.") {
        return arithmetic::dense::<kernel::ScalarElement>(name, args, invocation, policy);
    }
    if name == "pairing.check" {
        let [Value::BlstG1Vector(left), Value::BlstG2Vector(right)] = args else {
            return Err(refused("kernel-operands"));
        };
        arithmetic::equal_len(left.len(), right.len())?;
        policy.typed_groups::<kernel::G1>(left.len())?;
        policy.typed_groups::<kernel::G2>(right.len())?;
        let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
        call.work_items(left.len(), 8192, 8192)?;
        let output = call.scalar(512)?;
        let _workspace = call.reserve_workspace::<u8>(kernel::PAIRING_WORKSPACE_BYTES)?;
        return Ok(vec![output.finish(|| {
            Ok(Value::Bool(
                kernel::pairing_check_bulk(left, right).map_err(failure)?,
            ))
        })?]);
    }
    // MSM owns a genuine foreign workspace. Other group operations reuse the
    // complete existing dense family with typed resident projections.
    if name == "curve.msm" {
        let len = match args {
            [Value::BlstVector(s), Value::BlstG1Vector(p)] => {
                arithmetic::equal_len(s.len(), p.len())?;
                p.len()
            }
            [Value::BlstVector(s), Value::BlstG2Vector(p)] => {
                arithmetic::equal_len(s.len(), p.len())?;
                p.len()
            }
            _ => return Err(refused("kernel-operands")),
        };
        let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
        call.work_items(len, 256, 1)?;
        let output = call.scalar(512)?;
        let _workspace =
            call.reserve_workspace::<u8>(kernel::msm_workspace_bytes(len).map_err(failure)?)?;
        return Ok(vec![output.finish(|| {
            Ok(match args {
                [Value::BlstVector(s), Value::BlstG1Vector(p)] => {
                    Value::BlstG1(p.msm(s).map_err(failure)?)
                }
                [Value::BlstVector(s), Value::BlstG2Vector(p)] => {
                    Value::BlstG2(Arc::new(p.msm(s).map_err(failure)?))
                }
                _ => return Err(refused("kernel-operands")),
            })
        })?]);
    }
    group_apply(name, invocation, args, policy)
}
fn group_apply(
    name: &str,
    invocation: &Invocation<'_>,
    args: &[Value],
    policy: &Policy,
) -> Result<Vec<Value>> {
    match invocation
        .binding
        .declaration()
        .arguments
        .first()
        .map(String::as_str)
    {
        Some("bls12-381.g1") => curve::dense::<kernel::G1Element>(name, args, invocation, policy),
        Some("bls12-381.g2") => curve::dense::<kernel::G2Element>(name, args, invocation, policy),
        _ => Err(refused("resident-group-unsupported")),
    }
}

fn collect_iter<T, U>(
    values: impl ExactSizeIterator<Item = T>,
    convert: impl Fn(T) -> Result<U>,
) -> Result<Arc<[U]>> {
    let mut converted = arithmetic::reserve(values.len())?;
    for value in values {
        converted.push(convert(value)?);
    }
    Ok(converted.into())
}
pub(crate) fn convert(
    invocation: &Invocation<'_>,
    args: &[Value],
    policy: &Policy,
) -> Result<Vec<Value>> {
    let [value] = args else {
        return Err(refused("kernel-operands"));
    };
    let signature = conversion_signature(invocation.binding.declaration())
        .ok_or_else(|| refused("representation-conversion"))?;
    use zkc_runtime::vm::Value as _;
    if !value.has_type(&signature.inputs[0]) {
        return Err(refused("kernel-operands"));
    }
    let (len, width) = match value {
        Value::Vector(v) => (v.len(), 32),
        Value::BlstVector(v) => (v.len(), 32),
        Value::Groups(v) => (v.len(), std::mem::size_of::<kernel::G1>()),
        Value::BlstG1Vector(v) => (v.len(), std::mem::size_of::<crate::G1>()),
        Value::Bls12381G2Vector(v) => (v.len(), std::mem::size_of::<kernel::G2>()),
        Value::BlstG2Vector(v) => (v.len(), std::mem::size_of::<crate::Bls12381G2>()),
        _ => (0, 0),
    };
    if value.ty() == Type::Vector {
        policy.vector(len)?;
    }
    if value.ty() == Type::Groups && len > policy.max_groups.min(32768) {
        return Err(exhausted("group-limit"));
    }
    let retained = if width == 0 { 512 } else { size(len, width)? };
    let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
    call.work_items(len.max(1), 4096, 1)?;
    let output = call.scalar(retained)?;
    // Vec-to-Arc freezing retains both destination buffers briefly. No source
    // imports occur in any resident arithmetic handler.
    let _workspace =
        call.reserve_workspace::<u8>(if width == 0 { 256 } else { size(len, width)? })?;
    let value = output.finish(|| {
        Ok(match value {
            Value::Field(s) => Value::BlstField(bridge::import_scalar(*s).map_err(failure)?),
            Value::BlstField(s) => Value::Field(bridge::export_scalar(*s).map_err(failure)?),
            Value::Curve(p) => Value::BlstG1(bridge::import_g1(*p).map_err(failure)?),
            Value::BlstG1(p) => Value::Curve(bridge::export_g1(*p).map_err(failure)?),
            Value::Bls12381G2(p) => {
                Value::BlstG2(Arc::new(bridge::import_g2(*p).map_err(failure)?))
            }
            Value::BlstG2(p) => Value::Bls12381G2(bridge::export_g2(**p).map_err(failure)?),
            Value::Vector(v) => Value::BlstVector(Arc::new(
                kernel::ScalarVector::try_from_fn(v.len(), |i| bridge::import_scalar(v[i]))
                    .map_err(failure)?,
            )),
            Value::BlstVector(v) => Value::Vector(collect_iter(v.iter(), |s| {
                bridge::export_scalar(s).map_err(failure)
            })?),
            Value::Groups(v) => Value::BlstG1Vector(Arc::new(
                kernel::G1Vector::try_from_fn(v.len(), |i| bridge::import_g1(v[i]))
                    .map_err(failure)?,
            )),
            Value::BlstG1Vector(v) => Value::Groups(collect_iter(v.iter(), |p| {
                bridge::export_g1(p).map_err(failure)
            })?),
            Value::Bls12381G2Vector(v) => Value::BlstG2Vector(Arc::new(
                kernel::G2Vector::try_from_fn(v.len(), |i| bridge::import_g2(v[i]))
                    .map_err(failure)?,
            )),
            Value::BlstG2Vector(v) => Value::Bls12381G2Vector(collect_iter(v.iter(), |p| {
                bridge::export_g2(p).map_err(failure)
            })?),
            _ => return Err(refused("representation-conversion")),
        })
    })?;
    if !value.has_type(&signature.outputs[0]) {
        return Err(refused("representation-conversion"));
    }
    Ok(vec![value])
}
