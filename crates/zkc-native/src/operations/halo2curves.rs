//! Resident halo2curves-axiom BN254 adaptation. Arithmetic reuses the ordinary dense families;
//! provider changes occur only in the explicit representation conversion call.
use super::{arithmetic, curve, field};
use crate::{Policy, Result, Value, exhausted, refused};
use std::sync::Arc;
use zkc_kernels::halo2curves::bn254::{self as kernel, arkworks as bridge};
use zkc_runtime::vm::{BoundSignature, Identity, Invocation, OperationBinding, PhysicalType, Type};

// Actual Native operation inventory, independent of expected Contracts.
pub(crate) const CONTRACTS: &[&str] = &[
    "field.constant",
    "field.from_index",
    "field.add",
    "field.sub",
    "field.neg",
    "field.mul",
    "field.inverse",
    "field.equal",
    "vector.empty",
    "vector.constant",
    "vector.splat",
    "vector.append",
    "vector.at",
    "vector.get",
    "vector.length",
    "vector.length_check",
    "vector.add",
    "vector.sub",
    "vector.mul",
    "vector.dot",
    "vector.scale",
    "vector.sum",
    "vector.product",
    "vector.split",
    "vector.concat",
    "vector.slice",
    "vector.equal",
    "curve.generator",
    "curve.identity",
    "curve.add",
    "curve.neg",
    "curve.equal",
    "curve.nonidentity",
    "curve.scale",
    "curve.empty",
    "curve.append",
    "curve.at",
    "curve.get",
    "curve.length",
    "curve.vector_add",
    "curve.scale_each",
    "curve.vector_scale",
    "curve.split",
    "curve.concat",
    "curve.msm",
    "pairing.check",
];

pub(crate) fn failure(error: kernel::Error) -> zkc_runtime::vm::BackendError {
    match error {
        kernel::Error::Allocation => exhausted("allocation"),
        kernel::Error::CapacityOverflow => exhausted("capacity-overflow"),
        kernel::Error::LengthMismatch => refused("length-mismatch"),
        kernel::Error::InvalidEncoding => refused("provider-conversion"),
        kernel::Error::InvalidPlan => refused("invalid-plan"),
    }
}

/// Positive flat inventory: sharing a nominal domain never enables GT or PCS.
pub(crate) fn physical(kind: Type, identity: Identity) -> Option<PhysicalType> {
    if !matches!(
        (kind, identity),
        (Type::Field | Type::Vector, Identity::Bn254Fr)
            | (
                Type::Group | Type::Groups,
                Identity::Bn254G1 | Identity::Bn254G2
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
    if !CONTRACTS.contains(&binding.contract.as_str()) {
        return None;
    }
    super::resident::signature_with(binding, "halo2curves-axiom", physical)
}
pub(crate) fn conversion_signature(binding: &OperationBinding) -> Option<BoundSignature> {
    super::resident::conversion_signature_with(binding, &physical)
}

impl field::Family for kernel::ScalarElement {
    const RESIDENT_STORAGE: bool = true;
    fn field(v: &Value) -> Result<Self> {
        if let Value::HaloField(v) = v {
            Ok(v.into_element())
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn vector(v: &Value) -> Result<&[Self]> {
        if let Value::HaloVector(v) = v {
            Ok(v.as_elements())
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn field_value(v: Self) -> Value {
        Value::HaloField(kernel::Scalar::from_element(v))
    }
    fn vector_value(v: Vec<Self>) -> Value {
        Value::HaloVector(Arc::new(
            kernel::ScalarVector::from_elements(v).expect("typed field elements"),
        ))
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
    HaloG1,
    HaloG1Vector,
    |v| v,
    |v: &kernel::G1| *v
);

super::resident::group_family!(
    kernel,
    G2,
    G2Vector,
    HaloG2,
    HaloG2Vector,
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
        let [Value::HaloG1Vector(left), Value::HaloG2Vector(right)] = args else {
            return Err(refused("kernel-operands"));
        };
        arithmetic::equal_len(left.len(), right.len())?;
        policy.typed_groups::<kernel::G1>(left.len())?;
        policy.typed_groups::<kernel::G2>(right.len())?;
        let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
        call.work(kernel::pairing_work(left.len()).map_err(failure)?)?;
        let output = call.scalar(512)?;
        let _workspace = call.reserve_workspace::<u8>(
            kernel::pairing_workspace_bytes(left.len()).map_err(failure)?,
        )?;
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
            [Value::HaloVector(s), Value::HaloG1Vector(p)] => {
                arithmetic::equal_len(s.len(), p.len())?;
                p.len()
            }
            [Value::HaloVector(s), Value::HaloG2Vector(p)] => {
                arithmetic::equal_len(s.len(), p.len())?;
                p.len()
            }
            _ => return Err(refused("kernel-operands")),
        };
        let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
        call.work(kernel::msm_work(len).map_err(failure)?)?;
        let output = call.scalar(512)?;
        let _workspace =
            call.reserve_workspace::<u8>(kernel::msm_workspace_bytes(len).map_err(failure)?)?;
        return Ok(vec![output.finish(|| {
            Ok(match args {
                [Value::HaloVector(s), Value::HaloG1Vector(p)] => {
                    Value::HaloG1(p.msm(s).map_err(failure)?)
                }
                [Value::HaloVector(s), Value::HaloG2Vector(p)] => {
                    Value::HaloG2(Arc::new(p.msm(s).map_err(failure)?))
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
        Some("bn254.g1") => curve::dense_with_storage::<kernel::G1, kernel::G1Vector>(
            name, args, invocation, policy,
        ),
        Some("bn254.g2") => curve::dense_with_storage::<kernel::G2, kernel::G2Vector>(
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
            Value::Bn254Vector(v) => (v.len(), 32),
            Value::HaloVector(v) => (v.len(), 32),
            Value::Bn254G1Vector(v) => (v.len(), std::mem::size_of::<kernel::G1>()),
            // Exports retain the canonical Arkworks affine carrier.
            Value::HaloG1Vector(v) => (v.len(), std::mem::size_of::<crate::Bn254G1>()),
            Value::Bn254G2Vector(v) => (v.len(), std::mem::size_of::<kernel::G2>()),
            Value::HaloG2Vector(v) => (v.len(), std::mem::size_of::<crate::Bn254G2>()),
            _ => (0, 0),
        },
        |value| {
            Ok(match value {
                Value::Bn254Field(s) => {
                    Value::HaloField(bridge::import_scalar(*s).map_err(failure)?)
                }
                Value::HaloField(s) => {
                    Value::Bn254Field(bridge::export_scalar(*s).map_err(failure)?)
                }
                Value::Bn254G1(p) => Value::HaloG1(bridge::import_g1(*p).map_err(failure)?),
                Value::HaloG1(p) => Value::Bn254G1(bridge::export_g1(*p).map_err(failure)?),
                Value::Bn254G2(p) => {
                    Value::HaloG2(Arc::new(bridge::import_g2(*p).map_err(failure)?))
                }
                Value::HaloG2(p) => Value::Bn254G2(bridge::export_g2(**p).map_err(failure)?),
                Value::Bn254Vector(v) => Value::HaloVector(Arc::new(
                    kernel::ScalarVector::try_from_fn(v.len(), |i| bridge::import_scalar(v[i]))
                        .map_err(failure)?,
                )),
                Value::HaloVector(v) => {
                    Value::Bn254Vector(super::resident::collect_iter(v.iter(), |s| {
                        bridge::export_scalar(s).map_err(failure)
                    })?)
                }
                Value::Bn254G1Vector(v) => Value::HaloG1Vector(Arc::new(
                    kernel::G1Vector::try_from_fn(v.len(), |i| bridge::import_g1(v[i]))
                        .map_err(failure)?,
                )),
                Value::HaloG1Vector(v) => {
                    Value::Bn254G1Vector(super::resident::collect_iter(v.iter(), |p| {
                        bridge::export_g1(p).map_err(failure)
                    })?)
                }
                Value::Bn254G2Vector(v) => Value::HaloG2Vector(Arc::new(
                    kernel::G2Vector::try_from_fn(v.len(), |i| bridge::import_g2(v[i]))
                        .map_err(failure)?,
                )),
                Value::HaloG2Vector(v) => {
                    Value::Bn254G2Vector(super::resident::collect_iter(v.iter(), |p| {
                        bridge::export_g2(p).map_err(failure)
                    })?)
                }
                _ => return Err(refused("representation-conversion")),
            })
        },
    )
}
