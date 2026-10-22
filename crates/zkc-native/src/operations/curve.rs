//! Checked module contractions. Default Ristretto MSM uses MultiscalarMul.
//! Kernel choice does not establish a whole-runtime timing guarantee.
use crate::operations::arithmetic::{equal_len, natural, reserve, split_len};
use crate::{
    G1, Policy, Result, RistrettoPoint, RistrettoScalar, Scalar, Value, exhausted, refused,
    value::size,
};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    traits::{Identity, MultiscalarMul},
};
use std::sync::Arc;
use zkc_runtime::vm::Invocation;
/// Typed group algebra and provider scaling plans, independent of Native values
/// and policy. Destinations are reserved by the calling family adapter.
pub(super) trait Group: Copy + PartialEq {
    type Scalar: Copy;
    type Error;
    fn generator() -> Self;
    fn identity() -> Self;
    fn add(self, other: Self) -> Self;
    fn neg(self) -> Self;
    fn scale(self, scalar: Self::Scalar) -> Self;
    fn scaling_workspace_bound(_len: usize, _max_workspace: usize) -> usize {
        0
    }
    fn scale_many(
        points: &[Self],
        scalar: Self::Scalar,
        output: &mut Vec<Self>,
        _workspace_bytes: usize,
    ) -> std::result::Result<(), Self::Error> {
        output.extend(points.iter().map(|point| point.scale(scalar)));
        Ok(())
    }
    fn scale_each(
        scalars: &[Self::Scalar],
        points: &[Self],
        output: &mut Vec<Self>,
        _workspace_bytes: usize,
    ) -> std::result::Result<(), Self::Error> {
        output.extend(
            points
                .iter()
                .zip(scalars)
                .map(|(point, scalar)| point.scale(*scalar)),
        );
        Ok(())
    }
}

type SliceMsm<G> = fn(&[<G as Group>::Scalar], &[G]) -> Result<G>;

/// Native projection, publication and resource admission for group families.
pub(super) trait Family: Group {
    const RESIDENT_STORAGE: bool = false;
    /// None means this adapter requires a distinct bulk MSM handler. It does
    /// not imply that the provider lacks MSM on its own retained bulk carriers.
    const SLICE_MSM: Option<SliceMsm<Self>> = None;
    fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError;
    fn point(v: &Value) -> Result<Self>;
    fn points(v: &Value) -> Result<&[Self]>;
    fn scalar(v: &Value) -> Result<Self::Scalar>;
    fn scalars(v: &Value) -> Result<&[Self::Scalar]>;
    fn value(v: Self) -> Value;
    fn values(v: Vec<Self>) -> Value;
    fn limit(p: &Policy, n: usize) -> Result<()>;
    fn width() -> usize;
}
// The destination has already passed the historical group/output preflights
// and exact reservation. Only arkworks needs an initialized affine destination.
macro_rules! ark_scaling {
    () => {
        fn scaling_workspace_bound(len: usize, max_workspace: usize) -> usize {
            Self::scaling_workspace_bound(len, max_workspace)
        }
        fn scale_many(
            points: &[Self],
            scalar: Self::Scalar,
            output: &mut Vec<Self>,
            workspace_bytes: usize,
        ) -> std::result::Result<(), Self::Error> {
            let mut plan = Self::scaling_plan(
                points.len(),
                zkc_kernels::arkworks::scaling::Selection::Automatic {
                    max_workspace: workspace_bytes,
                },
            )?;
            output.resize(points.len(), Self::identity());
            Self::scale_many_into(points, scalar, output, &mut plan)
        }
        fn scale_each(
            scalars: &[Self::Scalar],
            points: &[Self],
            output: &mut Vec<Self>,
            workspace_bytes: usize,
        ) -> std::result::Result<(), Self::Error> {
            let mut plan = Self::scaling_plan(
                points.len(),
                zkc_kernels::arkworks::scaling::Selection::Automatic {
                    max_workspace: workspace_bytes,
                },
            )?;
            output.resize(points.len(), Self::identity());
            Self::scale_each_into(scalars, points, output, &mut plan)
        }
    };
}

fn with_scaling_workspace<G: Group>(
    len: usize,
    policy: &Policy,
    available: usize,
    scale: impl FnOnce(usize) -> Result<()>,
) -> Result<()> {
    // Existing output storage retains its historical owner and admission order.
    // Call accounts only for optional, scoped projective/Z/prefix payload. These
    // operations historically have no numerical work charge; do not add one.
    let call = crate::numerical::Call::new(policy, available);
    let bytes = G::scaling_workspace_bound(len, policy.max_numerical_bytes);
    let workspace = if bytes > 0 {
        call.reserve_workspace::<u8>(bytes).ok()
    } else {
        None
    };
    // The guard outlives every adapter vector, including on error or unwind.
    scale(if workspace.is_some() { bytes } else { 0 })
}

#[cfg(test)]
mod scaling_workspace_tests {
    use super::*;

    fn check<G: Group>(unit: usize) {
        for (len, bytes, expected) in [
            (0, usize::MAX, 0),
            (1, usize::MAX, 0),
            (257, 0, 0),
            (257, 2 * unit - 1, 0),
            (257, 2 * unit, 2 * unit),
            (257, 17 * unit, 17 * unit),
            (257, 256 * unit - 1, 255 * unit),
            (257, 256 * unit, 256 * unit),
            (3, usize::MAX, 3 * unit),
        ] {
            let policy = Policy {
                max_numerical_bytes: bytes,
                max_numerical_work: 0,
                ..Policy::default()
            };
            // No output or work floor is attached to this optional scope.
            with_scaling_workspace::<G>(len, &policy, 0, |workspace_bytes| {
                assert_eq!(workspace_bytes, expected);
                Ok(())
            })
            .unwrap();
        }
    }

    #[test]
    fn public_length_group_and_scratch_allowance_admit_kernel_bounds() {
        check::<G1>(G1::scaling_workspace_bytes(1).unwrap());
        check::<crate::Bls12381G2>(crate::Bls12381G2::scaling_workspace_bytes(1).unwrap());
        check::<crate::Bn254G1>(crate::Bn254G1::scaling_workspace_bytes(1).unwrap());
        check::<crate::Bn254G2>(crate::Bn254G2::scaling_workspace_bytes(1).unwrap());
    }

    #[test]
    fn dalek_never_requests_arkworks_workspace() {
        for len in [0, 1, 257] {
            with_scaling_workspace::<RistrettoPoint>(len, &Policy::default(), 0, |chunk| {
                assert_eq!(chunk, 0);
                Ok(())
            })
            .unwrap();
            with_scaling_workspace::<crate::EdwardsPrime>(len, &Policy::default(), 0, |chunk| {
                assert_eq!(chunk, 0);
                Ok(())
            })
            .unwrap();
        }
    }
}
impl Group for G1 {
    type Scalar = Scalar;
    type Error = zkc_kernels::arkworks::Error;
    ark_scaling!();
    fn generator() -> Self {
        Self::generator()
    }
    fn identity() -> Self {
        Self::identity()
    }
    fn add(self, other: Self) -> Self {
        Self::add(&self, &other)
    }
    fn neg(self) -> Self {
        Self::neg(&self)
    }
    fn scale(self, scalar: Scalar) -> Self {
        Self::scale(&self, scalar)
    }
}
impl Family for G1 {
    const SLICE_MSM: Option<SliceMsm<Self>> = Some(|s, p| Self::msm(s, p).map_err(crate::ark));
    fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
        crate::ark(error)
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::Curve(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn points(v: &Value) -> Result<&[Self]> {
        if let Value::Groups(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalar(v: &Value) -> Result<Scalar> {
        if let Value::Field(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalars(v: &Value) -> Result<&[Scalar]> {
        if let Value::Vector(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn value(v: Self) -> Value {
        Value::Curve(v)
    }
    fn values(v: Vec<Self>) -> Value {
        Value::Groups(v.into())
    }
    fn limit(p: &Policy, n: usize) -> Result<()> {
        p.groups(n)
    }
    fn width() -> usize {
        128
    }
}
impl Group for RistrettoPoint {
    type Scalar = RistrettoScalar;
    type Error = std::convert::Infallible;
    fn generator() -> Self {
        RISTRETTO_BASEPOINT_POINT
    }
    fn identity() -> Self {
        Identity::identity()
    }
    fn add(self, other: Self) -> Self {
        self + other
    }
    fn neg(self) -> Self {
        -self
    }
    fn scale(self, scalar: RistrettoScalar) -> Self {
        self * scalar
    }
}
impl Family for RistrettoPoint {
    const SLICE_MSM: Option<SliceMsm<Self>> = Some(|s, p| {
        equal_len(s.len(), p.len())?;
        Ok(Self::multiscalar_mul(s, p))
    });
    fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
        match error {}
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::RistrettoGroup(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn points(v: &Value) -> Result<&[Self]> {
        if let Value::RistrettoGroups(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalar(v: &Value) -> Result<RistrettoScalar> {
        if let Value::RistrettoField(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalars(v: &Value) -> Result<&[RistrettoScalar]> {
        if let Value::RistrettoVector(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn value(v: Self) -> Value {
        Value::RistrettoGroup(v)
    }
    fn values(v: Vec<Self>) -> Value {
        Value::RistrettoGroups(v.into())
    }
    fn limit(p: &Policy, n: usize) -> Result<()> {
        p.dalek_groups(n)
    }
    fn width() -> usize {
        std::mem::size_of::<Self>()
    }
}
impl Group for crate::EdwardsPrime {
    type Scalar = RistrettoScalar;
    type Error = std::convert::Infallible;
    fn generator() -> Self {
        Self::generator()
    }
    fn identity() -> Self {
        Self::identity()
    }
    fn add(self, other: Self) -> Self {
        self + other
    }
    fn neg(self) -> Self {
        -self
    }
    fn scale(self, scalar: RistrettoScalar) -> Self {
        self.scale(scalar)
    }
}
impl Family for crate::EdwardsPrime {
    const SLICE_MSM: Option<SliceMsm<Self>> = Some(|s, p| {
        equal_len(s.len(), p.len())?;
        Self::msm(s, p).ok_or_else(|| refused("length-mismatch"))
    });
    fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
        match error {}
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::EdwardsGroup(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn points(v: &Value) -> Result<&[Self]> {
        if let Value::EdwardsGroups(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalar(v: &Value) -> Result<RistrettoScalar> {
        if let Value::RistrettoField(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalars(v: &Value) -> Result<&[RistrettoScalar]> {
        if let Value::RistrettoVector(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn value(v: Self) -> Value {
        Value::EdwardsGroup(v)
    }
    fn values(v: Vec<Self>) -> Value {
        Value::EdwardsGroups(v.into())
    }
    fn limit(p: &Policy, n: usize) -> Result<()> {
        p.dalek_groups(n)
    }
    fn width() -> usize {
        std::mem::size_of::<Self>()
    }
}
macro_rules! bn_group {
    ($t:ty,$one:ident,$many:ident) => {
        impl Group for $t {
            type Scalar = crate::Bn254Scalar;
            type Error = zkc_kernels::arkworks::Error;
            ark_scaling!();
            fn generator() -> Self {
                Self::generator()
            }
            fn identity() -> Self {
                Self::identity()
            }
            fn add(self, b: Self) -> Self {
                Self::add(&self, &b)
            }
            fn neg(self) -> Self {
                Self::neg(&self)
            }
            fn scale(self, s: Self::Scalar) -> Self {
                Self::scale(&self, s)
            }
        }
        impl Family for $t {
            const SLICE_MSM: Option<SliceMsm<Self>> =
                Some(|s, p| Self::msm(s, p).map_err(crate::ark));
            fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
                crate::ark(error)
            }
            fn point(v: &Value) -> Result<Self> {
                if let Value::$one(v) = v {
                    Ok(*v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn points(v: &Value) -> Result<&[Self]> {
                if let Value::$many(v) = v {
                    Ok(v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn scalar(v: &Value) -> Result<Self::Scalar> {
                if let Value::Bn254Field(v) = v {
                    Ok(*v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn scalars(v: &Value) -> Result<&[Self::Scalar]> {
                if let Value::Bn254Vector(v) = v {
                    Ok(v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn value(v: Self) -> Value {
                Value::$one(v)
            }
            fn values(v: Vec<Self>) -> Value {
                Value::$many(v.into())
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
bn_group!(crate::Bn254G1, Bn254G1, Bn254G1Vector);
bn_group!(crate::Bn254G2, Bn254G2, Bn254G2Vector);
impl Group for crate::Bls12381G2 {
    type Scalar = Scalar;
    type Error = zkc_kernels::arkworks::Error;
    ark_scaling!();
    fn generator() -> Self {
        Self::generator()
    }
    fn identity() -> Self {
        Self::identity()
    }
    fn add(self, b: Self) -> Self {
        Self::add(&self, &b)
    }
    fn neg(self) -> Self {
        Self::neg(&self)
    }
    fn scale(self, s: Scalar) -> Self {
        Self::scale(&self, s)
    }
}
impl Family for crate::Bls12381G2 {
    const SLICE_MSM: Option<SliceMsm<Self>> = Some(|s, p| Self::msm(s, p).map_err(crate::ark));
    fn scaling_failure(error: Self::Error) -> zkc_runtime::vm::BackendError {
        crate::ark(error)
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::Bls12381G2(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn points(v: &Value) -> Result<&[Self]> {
        if let Value::Bls12381G2Vector(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalar(v: &Value) -> Result<Scalar> {
        if let Value::Field(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn scalars(v: &Value) -> Result<&[Scalar]> {
        if let Value::Vector(v) = v {
            Ok(v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn value(v: Self) -> Value {
        Value::Bls12381G2(v)
    }
    fn values(v: Vec<Self>) -> Value {
        Value::Bls12381G2Vector(v.into())
    }
    fn limit(p: &Policy, n: usize) -> Result<()> {
        p.typed_groups::<Self>(n)
    }
    fn width() -> usize {
        std::mem::size_of::<Self>()
    }
}
pub(crate) fn apply(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    if name == "pairing.apply" {
        p.output(512, i.max_output_bytes)?;
        // Bound pairing preparation scratch independently of the GT result.
        p.output(32768, usize::MAX)?;
        return match args {
            [Value::Bn254G1(a), Value::Bn254G2(b)] => Ok(vec![Value::Bn254Gt(
                zkc_kernels::arkworks::bn254::pairing(a, b),
            )]),
            [Value::Curve(a), Value::Bls12381G2(b)] => Ok(vec![Value::Bls12381Gt(Arc::new(
                zkc_kernels::arkworks::bls12_381::pairing(a, b),
            ))]),
            _ => Err(refused("kernel-operands")),
        };
    }
    if name == "pairing.check" {
        let check = match args {
            [Value::Bn254G1Vector(a), Value::Bn254G2Vector(b)] => {
                equal_len(a.len(), b.len())?;
                p.typed_groups::<crate::Bn254G1>(a.len())?;
                p.typed_groups::<crate::Bn254G2>(b.len())?;
                p.output(512, i.max_output_bytes)?;
                // BN254 G2 preparations retain 91 line coefficients (three Fq2 each),
                // plus G1 preparation and multi-Miller loop working vectors.
                p.output(size(a.len(), 32768)?, usize::MAX)?;
                zkc_kernels::arkworks::bn254::pairing_check(a, b)
            }
            [Value::Groups(a), Value::Bls12381G2Vector(b)] => {
                equal_len(a.len(), b.len())?;
                p.groups(a.len())?;
                p.typed_groups::<crate::Bls12381G2>(b.len())?;
                p.output(512, i.max_output_bytes)?;
                // BLS12-381 G2 preparations retain 68 line coefficients (three
                // Fq2 each), plus G1 preparation and multi-Miller loop vectors.
                p.output(size(a.len(), 32768)?, usize::MAX)?;
                zkc_kernels::arkworks::bls12_381::pairing_check(a, b)
            }
            _ => return Err(refused("kernel-operands")),
        };
        return Ok(vec![Value::Bool(check.map_err(crate::ark)?)]);
    }
    if !name.starts_with("curve.") || matches!(name, "curve.commit" | "curve.response") {
        return Err(refused("kernel-operands"));
    }
    use zkc_runtime::vm::Identity;
    let group = i
        .binding
        .declaration()
        .arguments
        .first()
        .and_then(|name| Identity::parse(name).ok());
    match group {
        Some(Identity::Bls12381G1) => dense::<G1>(name, args, i, p),
        Some(Identity::Bn254G1) => dense::<crate::Bn254G1>(name, args, i, p),
        Some(Identity::Bn254G2) => dense::<crate::Bn254G2>(name, args, i, p),
        Some(Identity::Bn254Gt) => target::<crate::Bn254Gt>(name, args, i, p),
        Some(Identity::Bls12381G2) => dense::<crate::Bls12381G2>(name, args, i, p),
        Some(Identity::Bls12381Gt) => target::<crate::Bls12381Gt>(name, args, i, p),
        Some(Identity::Ristretto255Group) => dense::<RistrettoPoint>(name, args, i, p),
        Some(Identity::Edwards25519Prime) => dense::<crate::EdwardsPrime>(name, args, i, p),
        _ => Err(refused("kernel-operands")),
    }
}
pub(super) fn dense<G: Family>(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    let arg = |j| args.get(j).ok_or_else(|| refused("kernel-operands"));
    let point = |j| G::point(arg(j)?);
    let points = |j| G::points(arg(j)?);
    let call = crate::numerical::Call::new(p, i.max_output_bytes);
    let reservations = std::cell::RefCell::new([None, None]);
    let alloc = |n| {
        G::limit(p, n)?;
        let bytes = size(n, G::width())?;
        p.output(bytes, i.max_output_bytes)?;
        if G::RESIDENT_STORAGE {
            let reservation = call.reserve_workspace::<u8>(bytes)?;
            *reservations
                .borrow_mut()
                .iter_mut()
                .find(|slot| slot.is_none())
                .ok_or_else(|| refused("kernel-output-count"))? = Some(reservation);
        }
        reserve::<G>(n)
    };
    let scalar_output = i
        .binding
        .signature()
        .outputs
        .iter()
        .all(|ty| ty.kind() != zkc_runtime::vm::Type::Groups);
    let _scalar_reservation = if G::RESIDENT_STORAGE && scalar_output {
        p.output(512, i.max_output_bytes)?;
        Some(call.reserve_workspace::<u8>(512)?)
    } else {
        None
    };
    if i.binding
        .signature()
        .outputs
        .iter()
        .all(|t| t.kind() != zkc_runtime::vm::Type::Groups)
    {
        p.output(512, i.max_output_bytes)?;
    }
    let result = match name {
        "curve.identity" => G::value(G::identity()),
        "curve.generator" => G::value(G::generator()),
        "curve.add" => G::value(point(0)?.add(point(1)?)),
        "curve.neg" => G::value(point(0)?.neg()),
        "curve.scale" => G::value(point(0)?.scale(G::scalar(arg(1)?)?)),
        "curve.equal" => Value::Bool(point(0)? == point(1)?),
        "curve.nonidentity" => Value::Bool(point(0)? != G::identity()),
        "curve.empty" => G::values(alloc(0)?),
        "curve.at" => G::value(
            *points(0)?
                .get(natural(i.attributes, 0)?)
                .ok_or_else(|| refused("group-index"))?,
        ),
        "curve.get" => {
            let Value::Index(index) = arg(1)? else {
                return Err(refused("kernel-operands"));
            };
            // Conversion failure is out of bounds too, including on 32-bit hosts.
            let index = usize::try_from(*index).map_err(|_| refused("group-index"))?;
            G::value(
                *points(0)?
                    .get(index)
                    .ok_or_else(|| refused("group-index"))?,
            )
        }
        "curve.length" => {
            Value::Index(u64::try_from(points(0)?.len()).map_err(|_| exhausted("size-overflow"))?)
        }
        "curve.msm" => {
            let (s, b) = (G::scalars(arg(0)?)?, points(1)?);
            equal_len(s.len(), b.len())?;
            G::limit(p, b.len())?;
            if i.binding
                .declaration()
                .arguments
                .first()
                .is_some_and(|a| a.starts_with("bn254."))
            {
                p.output(
                    size(
                        b.len(),
                        G::width()
                            .checked_mul(32)
                            .ok_or_else(|| exhausted("size-overflow"))?,
                    )?
                    .checked_add(65536)
                    .ok_or_else(|| exhausted("size-overflow"))?,
                    usize::MAX,
                )?;
            }
            let msm = G::SLICE_MSM.ok_or_else(|| refused("resident-msm-bulk-required"))?;
            G::value(msm(s, b)?)
        }
        "curve.scale_each" => {
            let (s, b) = (G::scalars(arg(0)?)?, points(1)?);
            equal_len(s.len(), b.len())?;
            let mut out = alloc(b.len())?;
            with_scaling_workspace::<G>(b.len(), p, i.max_output_bytes, |workspace_bytes| {
                G::scale_each(s, b, &mut out, workspace_bytes).map_err(G::scaling_failure)
            })?;
            G::values(out)
        }
        "curve.append" => {
            let b = points(0)?;
            let x = point(1)?;
            let mut out = alloc(
                b.len()
                    .checked_add(1)
                    .ok_or_else(|| exhausted("size-overflow"))?,
            )?;
            out.extend_from_slice(b);
            out.push(x);
            G::values(out)
        }
        "curve.vector_scale" => {
            let b = points(0)?;
            let x = G::scalar(arg(1)?)?;
            let mut out = alloc(b.len())?;
            with_scaling_workspace::<G>(b.len(), p, i.max_output_bytes, |workspace_bytes| {
                G::scale_many(b, x, &mut out, workspace_bytes).map_err(G::scaling_failure)
            })?;
            G::values(out)
        }
        "curve.vector_add" | "curve.concat" => {
            let (a, b) = (points(0)?, points(1)?);
            let n = if name == "curve.concat" {
                a.len()
                    .checked_add(b.len())
                    .ok_or_else(|| exhausted("size-overflow"))?
            } else {
                equal_len(a.len(), b.len())?;
                a.len()
            };
            let mut out = alloc(n)?;
            if name == "curve.concat" {
                out.extend_from_slice(a);
                out.extend_from_slice(b);
            } else {
                out.extend(a.iter().zip(b.iter()).map(|(a, b)| a.add(*b)));
            }
            G::values(out)
        }
        "curve.split" => {
            let a = points(0)?;
            let half = split_len(a.len())?;
            p.output(
                size(half, G::width())?
                    .checked_mul(2)
                    .ok_or_else(|| exhausted("size-overflow"))?,
                i.max_output_bytes,
            )?;
            let mut left = alloc(half)?;
            let mut right = alloc(half)?;
            left.extend_from_slice(&a[..half]);
            right.extend_from_slice(&a[half..]);
            return Ok(vec![G::values(left), G::values(right)]);
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![result])
}

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::curve;
    use zkc_runtime::vm::{AttributeRule, Type::*};
    &[
        curve::operation("curve.identity", &[], &[Group], AttributeRule::None)
            .implemented_by(&["arkworks/curve.identity", "dalek/curve.identity"]),
        curve::operation("curve.generator", &[], &[Group], AttributeRule::None)
            .implemented_by(&["arkworks/curve.generator", "dalek/curve.generator"]),
        curve::operation("curve.add", &[Group, Group], &[Group], AttributeRule::None)
            .implemented_by(&["arkworks/curve.add", "dalek/curve.add"]),
        curve::operation(
            "curve.scale",
            &[Group, Field],
            &[Group],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.scale", "dalek/curve.scale"]),
        curve::operation("curve.equal", &[Group, Group], &[Bool], AttributeRule::None)
            .implemented_by(&["arkworks/curve.equal", "dalek/curve.equal"]),
        curve::operation("curve.empty", &[], &[Groups], AttributeRule::None)
            .implemented_by(&["arkworks/curve.empty", "dalek/curve.empty"]),
        curve::operation(
            "curve.append",
            &[Groups, Group],
            &[Groups],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.append", "dalek/curve.append"]),
        curve::operation("curve.at", &[Groups], &[Group], AttributeRule::NaturalIndex)
            .implemented_by(&["arkworks/curve.at", "dalek/curve.at"]),
        curve::operation("curve.get", &[Groups, Index], &[Group], AttributeRule::None)
            .implemented_by(&["arkworks/curve.get", "dalek/curve.get"]),
        curve::operation("curve.length", &[Groups], &[Index], AttributeRule::None)
            .implemented_by(&["arkworks/curve.length", "dalek/curve.length"]),
        curve::operation("curve.neg", &[Group], &[Group], AttributeRule::None)
            .implemented_by(&["arkworks/curve.neg", "dalek/curve.neg"]),
        curve::operation("curve.nonidentity", &[Group], &[Bool], AttributeRule::None)
            .implemented_by(&["arkworks/curve.nonidentity", "dalek/curve.nonidentity"]),
        curve::operation(
            "curve.msm",
            &[Vector, Groups],
            &[Group],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.msm", "dalek/curve.msm"]),
        curve::operation(
            "curve.scale_each",
            &[Vector, Groups],
            &[Groups],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.scale_each", "dalek/curve.scale_each"]),
        curve::operation(
            "curve.vector_add",
            &[Groups, Groups],
            &[Groups],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.vector_add", "dalek/curve.vector_add"]),
        curve::operation(
            "curve.vector_scale",
            &[Groups, Field],
            &[Groups],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.vector_scale", "dalek/curve.vector_scale"]),
        curve::operation(
            "curve.split",
            &[Groups],
            &[Groups, Groups],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.split", "dalek/curve.split"]),
        curve::operation(
            "curve.concat",
            &[Groups, Groups],
            &[Groups],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/curve.concat", "dalek/curve.concat"]),
    ]
};
pub(crate) const PAIRINGS: &[crate::bindings::Contract] = &[
    crate::bindings::curve::pairing(
        "pairing.apply",
        &[zkc_runtime::vm::Type::Group, zkc_runtime::vm::Type::Group],
        &[zkc_runtime::vm::Type::Group],
        zkc_runtime::vm::AttributeRule::None,
    )
    .implemented_by(&["arkworks/pairing.apply"]),
    crate::bindings::curve::pairing(
        "pairing.check",
        &[zkc_runtime::vm::Type::Groups, zkc_runtime::vm::Type::Groups],
        &[zkc_runtime::vm::Type::Bool],
        zkc_runtime::vm::AttributeRule::None,
    )
    .implemented_by(&["arkworks/pairing.check"])
    .selectable(),
];

/// Prime-order pairing targets: individual values only, no target vectors.
trait Target: Group {
    /// Conservative retained charge of one value, as in `Value::retained_bytes`.
    const RETAINED: usize;
    fn scalar(v: &Value) -> Result<Self::Scalar>;
    fn point(v: &Value) -> Result<Self>;
    fn value(v: Self) -> Value;
}
impl Group for crate::Bn254Gt {
    type Scalar = crate::Bn254Scalar;
    type Error = std::convert::Infallible;
    fn identity() -> Self {
        Self::identity()
    }
    fn generator() -> Self {
        Self::generator()
    }
    fn add(self, other: Self) -> Self {
        Self::add(&self, &other)
    }
    fn neg(self) -> Self {
        Self::neg(&self)
    }
    fn scale(self, scalar: Self::Scalar) -> Self {
        Self::scale(&self, scalar)
    }
}
impl Target for crate::Bn254Gt {
    const RETAINED: usize = 512;
    fn scalar(scalar: &Value) -> Result<Self::Scalar> {
        let Value::Bn254Field(s) = scalar else {
            return Err(refused("kernel-operands"));
        };
        Ok(*s)
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::Bn254Gt(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn value(v: Self) -> Value {
        Value::Bn254Gt(v)
    }
}
impl Group for crate::Bls12381Gt {
    type Scalar = Scalar;
    type Error = std::convert::Infallible;
    fn identity() -> Self {
        Self::identity()
    }
    fn generator() -> Self {
        Self::generator()
    }
    fn add(self, other: Self) -> Self {
        Self::add(&self, &other)
    }
    fn neg(self) -> Self {
        Self::neg(&self)
    }
    fn scale(self, scalar: Self::Scalar) -> Self {
        Self::scale(&self, scalar)
    }
}
impl Target for crate::Bls12381Gt {
    const RETAINED: usize = 1024;
    fn scalar(scalar: &Value) -> Result<Self::Scalar> {
        let Value::Field(s) = scalar else {
            return Err(refused("kernel-operands"));
        };
        Ok(*s)
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::Bls12381Gt(v) = v {
            Ok(**v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn value(v: Self) -> Value {
        Value::Bls12381Gt(Arc::new(v))
    }
}
fn target<G: Target>(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    p.output(G::RETAINED, i.max_output_bytes)?;
    let v = match (name, args) {
        ("curve.identity", []) => G::value(G::identity()),
        ("curve.generator", []) => {
            p.output(32768, usize::MAX)?;
            G::value(G::generator())
        }
        ("curve.neg", [a]) => G::value(G::point(a)?.neg()),
        ("curve.nonidentity", [a]) => Value::Bool(G::point(a)? != G::identity()),
        ("curve.add", [a, b]) => G::value(G::point(a)?.add(G::point(b)?)),
        ("curve.scale", [a, s]) => G::value(G::point(a)?.scale(G::scalar(s)?)),
        ("curve.equal", [a, b]) => Value::Bool(G::point(a)? == G::point(b)?),
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![v])
}
