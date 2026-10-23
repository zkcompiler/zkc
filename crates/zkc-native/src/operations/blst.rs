//! Resident blst adaptation. Arithmetic reuses the ordinary dense families;
//! provider changes occur only in the explicit representation conversion call.
use super::{arithmetic, curve, field};
use crate::{Policy, Result, Value, exhausted, refused};
use std::sync::Arc;
use zkc_kernels::blst::bls12_381::{self as kernel, arkworks as bridge};
use zkc_runtime::vm::{BoundSignature, Identity, Invocation, OperationBinding, PhysicalType, Type};

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
    if !matches!(
        (kind, identity),
        (Type::Field | Type::Vector, Identity::Bls12381Fr)
            | (
                Type::Group | Type::Groups,
                Identity::Bls12381G1 | Identity::Bls12381G2
            )
    ) {
        return None;
    }
    crate::contracts::physical(kind, identity).cloned()
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
    super::resident::signature_with(binding, "blst", physical)
}
pub(crate) fn conversion_signature(binding: &OperationBinding) -> Option<BoundSignature> {
    super::resident::conversion_signature_with(binding, &physical)
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

super::resident::group_family!(
    kernel,
    G1,
    G1Vector,
    BlstG1,
    BlstG1Vector,
    |v| v,
    |v: &kernel::G1| *v
);

super::resident::group_family!(
    kernel,
    G2,
    G2Vector,
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
        Some("bls12-381.g1") => curve::dense_with_storage::<kernel::G1, kernel::G1Vector>(
            name, args, invocation, policy,
        ),
        Some("bls12-381.g2") => curve::dense_with_storage::<kernel::G2, kernel::G2Vector>(
            name, args, invocation, policy,
        ),
        _ => Err(refused("resident-group-unsupported")),
    }
}

pub(crate) fn convert(
    invocation: &Invocation<'_>,
    args: &[Value],
    policy: &Policy,
) -> Result<Vec<Value>> {
    super::resident::convert_value(
        invocation,
        args,
        policy,
        |value| match value {
            Value::Vector(v) => (v.len(), 32),
            Value::BlstVector(v) => (v.len(), 32),
            Value::Groups(v) => (v.len(), std::mem::size_of::<kernel::G1>()),
            // Native's conservative Arkworks G1-vector retention is 128 bytes per
            // point, even when the concrete affine wrapper is smaller.
            Value::BlstG1Vector(v) => (v.len(), 128),
            Value::Bls12381G2Vector(v) => (v.len(), std::mem::size_of::<kernel::G2>()),
            Value::BlstG2Vector(v) => (v.len(), std::mem::size_of::<crate::Bls12381G2>()),
            _ => (0, 0),
        },
        |value| {
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
                Value::BlstVector(v) => {
                    Value::Vector(super::resident::collect_iter(v.iter(), |s| {
                        bridge::export_scalar(s).map_err(failure)
                    })?)
                }
                Value::Groups(v) => Value::BlstG1Vector(Arc::new(
                    kernel::G1Vector::try_from_fn(v.len(), |i| bridge::import_g1(v[i]))
                        .map_err(failure)?,
                )),
                Value::BlstG1Vector(v) => {
                    Value::Groups(super::resident::collect_iter(v.iter(), |p| {
                        bridge::export_g1(p).map_err(failure)
                    })?)
                }
                Value::Bls12381G2Vector(v) => Value::BlstG2Vector(Arc::new(
                    kernel::G2Vector::try_from_fn(v.len(), |i| bridge::import_g2(v[i]))
                        .map_err(failure)?,
                )),
                Value::BlstG2Vector(v) => {
                    Value::Bls12381G2Vector(super::resident::collect_iter(v.iter(), |p| {
                        bridge::export_g2(p).map_err(failure)
                    })?)
                }
                _ => return Err(refused("representation-conversion")),
            })
        },
    )
}
