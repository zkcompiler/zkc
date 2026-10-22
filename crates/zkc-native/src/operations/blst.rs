//! blst alternatives with the existing Arkworks physical ports.
//!
//! Staging, arithmetic and export form one admitted call. No foreign value can
//! escape into the VM, change wire encoding or bypass backend output accounting.
use super::arithmetic::{equal_len, reserve};
use super::curve::Group;
use crate::{Policy, Result, Scalar, Value, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_kernels::blst::bls12_381::{self as kernel, arkworks as bridge};
use zkc_runtime::vm::{Identity, Invocation};

fn failure(error: kernel::Error) -> zkc_runtime::vm::BackendError {
    match error {
        kernel::Error::Allocation => exhausted("allocation"),
        kernel::Error::CapacityOverflow => exhausted("capacity-overflow"),
        kernel::Error::LengthMismatch => refused("length-mismatch"),
        kernel::Error::InvalidEncoding => refused("provider-conversion"),
    }
}

/// The resident type belongs to the kernel provider; VM projection is reused
/// from the ordinary curve family rather than creating another Value hierarchy.
trait Bridge: Group<Scalar = Scalar> {
    type Resident: Copy;
    const WORK_PER_POINT: u64;
    fn import(point: Self) -> std::result::Result<Self::Resident, kernel::Error>;
    fn export(point: Self::Resident) -> std::result::Result<Self, kernel::Error>;
    fn scale(point: Self::Resident, scalar: kernel::Scalar) -> Self::Resident;
    fn msm(
        scalars: &[kernel::Scalar],
        points: &[Self::Resident],
    ) -> std::result::Result<Self::Resident, kernel::Error>;
}
macro_rules! bridge {
    ($represented:ty, $resident:ty, $import:ident, $export:ident, $work:expr) => {
        impl Bridge for $represented {
            type Resident = $resident;
            const WORK_PER_POINT: u64 = $work;
            fn import(point: Self) -> std::result::Result<Self::Resident, kernel::Error> {
                bridge::$import(point)
            }
            fn export(point: Self::Resident) -> std::result::Result<Self, kernel::Error> {
                bridge::$export(point)
            }
            fn scale(point: Self::Resident, scalar: kernel::Scalar) -> Self::Resident {
                point.scale(scalar)
            }
            fn msm(
                scalars: &[kernel::Scalar],
                points: &[Self::Resident],
            ) -> std::result::Result<Self::Resident, kernel::Error> {
                <$resident>::msm(scalars, points)
            }
        }
    };
}
// Admission weights cover canonical bridges, subgroup checks and arithmetic.
// These are stable work-budget units, not cycle predictions or timing guarantees.
bridge!(crate::G1, kernel::G1, import_g1, export_g1, 8192);
bridge!(crate::Bls12381G2, kernel::G2, import_g2, export_g2, 16384);

fn collect<T, U>(values: &[T], convert: impl Fn(&T) -> Result<U>) -> Result<Vec<U>> {
    let mut converted = reserve(values.len())?;
    for value in values {
        converted.push(convert(value)?);
    }
    Ok(converted)
}

fn execute<G: Bridge>(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let arg = |index| args.get(index).ok_or_else(|| refused("kernel-operands"));
    let point = |index| G::point(arg(index)?);
    let points = |index| G::points(arg(index)?);
    let scalar = |index| G::scalar(arg(index)?);
    let scalars = |index| G::scalars(arg(index)?);
    let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);

    if name == "curve.scale" {
        let (p, s) = (point(0)?, scalar(1)?);
        policy.output(512, invocation.max_output_bytes)?;
        call.work(G::WORK_PER_POINT)?;
        let output = call.scalar(512)?;
        let _staging = call.reserve_workspace::<G::Resident>(1)?;
        let p = G::import(p).map_err(failure)?;
        let s = bridge::import_scalar(s).map_err(failure)?;
        return output
            .finish(|| {
                Ok(G::value(
                    G::export(<G as Bridge>::scale(p, s)).map_err(failure)?,
                ))
            })
            .map(|value| vec![value]);
    }

    let (points, factors, shared) = match name {
        "curve.msm" | "curve.scale_each" => {
            let (s, p) = (scalars(0)?, points(1)?);
            equal_len(s.len(), p.len())?;
            (p.as_ref(), s, None)
        }
        "curve.vector_scale" => (points(0)?.as_ref(), &[][..], Some(scalar(1)?)),
        _ => return Err(refused("kernel-operands")),
    };
    G::limit(policy, points.len())?;
    let msm = name == "curve.msm";
    let retained = if msm {
        512
    } else {
        size(points.len(), G::width())?
    };
    policy.output(retained, invocation.max_output_bytes)?;
    call.work_items(points.len(), G::WORK_PER_POINT, 0)?;

    // Reserve all caller-owned staging and upstream MSM workspace before any
    // conversion or allocation. The guard outlives buffers and output freezing.
    let staging = size(points.len(), std::mem::size_of::<G::Resident>())?
        .checked_add(size(factors.len(), std::mem::size_of::<kernel::Scalar>())?)
        .and_then(|n| {
            n.checked_add(if msm {
                kernel::msm_workspace_bytes(points.len()).ok()?
            } else {
                0
            })
        })
        .ok_or_else(|| exhausted("capacity-overflow"))?;
    let _staging = call.reserve_workspace::<u8>(staging)?;
    let points = collect(points, |&p| G::import(p).map_err(failure))?;
    let factors = collect(factors, |&s| bridge::import_scalar(s).map_err(failure))?;

    if msm {
        let output = call.scalar(retained)?;
        return output
            .finish(|| {
                let point = <G as Bridge>::msm(&factors, &points).map_err(failure)?;
                Ok(G::value(G::export(point).map_err(failure)?))
            })
            .map(|value| vec![value]);
    }
    let mut output = call.output(points.len(), G::identity(), retained)?;
    let shared = shared
        .map(bridge::import_scalar)
        .transpose()
        .map_err(failure)?;
    for (index, (&p, out)) in points.iter().zip(output.as_mut_slice()).enumerate() {
        let s = shared.unwrap_or_else(|| factors[index]);
        *out = G::export(<G as Bridge>::scale(p, s)).map_err(failure)?;
    }
    output
        .finish(|values| Ok(G::values(Arc::from(values))))
        .map(|value| vec![value])
}

pub(crate) fn apply(
    name: &str,
    invocation: &Invocation<'_>,
    args: &[Value],
    policy: &Policy,
) -> Result<Vec<Value>> {
    if name == "pairing.check" {
        let [Value::Groups(left), Value::Bls12381G2Vector(right)] = args else {
            return Err(refused("kernel-operands"));
        };
        equal_len(left.len(), right.len())?;
        policy.groups(left.len())?;
        policy.typed_groups::<crate::Bls12381G2>(right.len())?;
        policy.output(512, invocation.max_output_bytes)?;
        let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
        call.work_items(left.len(), 32768, 32768)?;
        let output = call.scalar(512)?;
        let bytes = size(left.len(), std::mem::size_of::<kernel::G1>())?
            .checked_add(size(right.len(), std::mem::size_of::<kernel::G2>())?)
            .and_then(|n| n.checked_add(kernel::PAIRING_WORKSPACE_BYTES))
            .ok_or_else(|| exhausted("capacity-overflow"))?;
        let _staging = call.reserve_workspace::<u8>(bytes)?;
        let left = collect(left, |&p| bridge::import_g1(p).map_err(failure))?;
        let right = collect(right, |&p| bridge::import_g2(p).map_err(failure))?;
        return output
            .finish(|| {
                Ok(Value::Bool(
                    kernel::pairing_check(&left, &right).map_err(failure)?,
                ))
            })
            .map(|value| vec![value]);
    }
    match invocation
        .binding
        .declaration()
        .arguments
        .first()
        .map(String::as_str)
    {
        Some("bls12-381.g1") => execute::<crate::G1>(name, args, invocation, policy),
        Some("bls12-381.g2") => execute::<crate::Bls12381G2>(name, args, invocation, policy),
        _ => Err(refused("kernel-operands")),
    }
}

macro_rules! alternatives {
    ($($name:literal),* $(,)?) => {
        &[$(crate::backend::registry::Alternative {
            identity: concat!("blst/", $name),
            original: concat!("arkworks/", $name),
            domains: &[Identity::Bls12381G1, Identity::Bls12381G2],
            ports: crate::bindings::PortTransform::Default,
            handler: Some(crate::backend::registry::blst),
            // Pippenger is variable-time; no runtime-wide timing claim is made.
            deterministic: true,
        }),*, crate::backend::registry::Alternative {
            identity: "blst/pairing.check",
            original: "arkworks/pairing.check",
            domains: &[Identity::Bls12381Fr],
            ports: crate::bindings::PortTransform::Default,
            handler: Some(crate::backend::registry::blst),
            deterministic: true,
        }]
    };
}
pub(crate) const ALTERNATIVES: &[crate::backend::registry::Alternative] = alternatives!(
    "curve.scale",
    "curve.scale_each",
    "curve.vector_scale",
    "curve.msm"
);
