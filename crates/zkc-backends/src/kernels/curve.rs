//! Checked module contractions. Default Ristretto MSM uses MultiscalarMul.
//! The explicit public-operand implementation requires the backend role gate.
//! Neither choice establishes a whole-runtime timing guarantee.
use crate::kernels::arithmetic::{equal_len, natural, reserve, split_len};
use crate::{
    GroupPoint, Policy, Result, RistrettoPoint, RistrettoScalar, Scalar, Value, exhausted, refused,
    value::size,
};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    traits::{Identity, MultiscalarMul, VartimeMultiscalarMul},
};
use std::sync::Arc;
use zkc_runtime::interactive::Invocation;
trait Group: Copy + PartialEq {
    type Scalar: Copy;
    fn generator() -> Self;
    fn identity() -> Self;
    fn add(self, other: Self) -> Self;
    fn neg(self) -> Self;
    fn scale(self, scalar: Self::Scalar) -> Self;
    fn msm(s: &[Self::Scalar], p: &[Self], public: bool) -> Result<Self>;
    fn point(v: &Value) -> Result<Self>;
    fn points(v: &Value) -> Result<&Arc<[Self]>>;
    fn scalar(v: &Value) -> Result<Self::Scalar>;
    fn scalars(v: &Value) -> Result<&[Self::Scalar]>;
    fn value(v: Self) -> Value;
    fn values(v: Arc<[Self]>) -> Value;
    fn limit(p: &Policy, n: usize) -> Result<()>;
    fn width() -> usize;
}
impl Group for GroupPoint {
    type Scalar = Scalar;
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
    fn msm(s: &[Scalar], p: &[Self], _public: bool) -> Result<Self> {
        Self::msm(s, p).map_err(crate::ark)
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::Curve(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn points(v: &Value) -> Result<&Arc<[Self]>> {
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
    fn values(v: Arc<[Self]>) -> Value {
        Value::Groups(v)
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
    fn msm(s: &[RistrettoScalar], p: &[Self], public: bool) -> Result<Self> {
        equal_len(s.len(), p.len())?;
        Ok(if public {
            Self::vartime_multiscalar_mul(s, p)
        } else {
            Self::multiscalar_mul(s, p)
        })
    }
    fn point(v: &Value) -> Result<Self> {
        if let Value::RistrettoGroup(v) = v {
            Ok(*v)
        } else {
            Err(refused("kernel-operands"))
        }
    }
    fn points(v: &Value) -> Result<&Arc<[Self]>> {
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
    fn values(v: Arc<[Self]>) -> Value {
        Value::RistrettoGroups(v)
    }
    fn limit(p: &Policy, n: usize) -> Result<()> {
        p.ristretto_groups(n)
    }
    fn width() -> usize {
        std::mem::size_of::<Self>()
    }
}
macro_rules! bn_group {
    ($t:ty,$one:ident,$many:ident) => {
        impl Group for $t {
            type Scalar = crate::Bn254Scalar;
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
            fn msm(s: &[Self::Scalar], p: &[Self], _: bool) -> Result<Self> {
                Self::msm(s, p).map_err(crate::ark)
            }
            fn point(v: &Value) -> Result<Self> {
                if let Value::$one(v) = v {
                    Ok(*v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn points(v: &Value) -> Result<&Arc<[Self]>> {
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
            fn values(v: Arc<[Self]>) -> Value {
                Value::$many(v)
            }
            fn limit(p: &Policy, n: usize) -> Result<()> {
                p.bn254_groups::<Self>(n)
            }
            fn width() -> usize {
                std::mem::size_of::<Self>()
            }
        }
    };
}
bn_group!(crate::Bn254G1, Bn254G1, Bn254G1Vector);
bn_group!(crate::Bn254G2, Bn254G2, Bn254G2Vector);
pub(crate) fn apply(
    name: &str,
    field: Option<zkc_runtime::interactive::Identity>,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Option<Result<Vec<Value>>> {
    if name == "pairing.check" {
        return Some((|| {
            let [Value::Bn254G1Vector(a), Value::Bn254G2Vector(b)] = args else {
                return Err(refused("kernel-operands"));
            };
            equal_len(a.len(), b.len())?;
            p.bn254_groups::<crate::Bn254G1>(a.len())?;
            p.bn254_groups::<crate::Bn254G2>(b.len())?;
            p.output(512, i.max_output_bytes)?;
            // BN254 G2 preparations retain 91 line coefficients (three Fq2 each),
            // plus G1 preparation and multi-Miller loop working vectors.
            p.output(size(a.len(), 32768)?, usize::MAX)?;
            Ok(vec![Value::Bool(
                zkc_arkworks::bn254::pairing_check(a, b).map_err(crate::ark)?,
            )])
        })());
    }
    if !name.starts_with("curve.") || matches!(name, "curve.commit" | "curve.response") {
        return None;
    }
    Some(match field {
        Some(zkc_runtime::interactive::Identity::Bn254Fr) => {
            match i
                .binding
                .declaration()
                .arguments
                .first()
                .map(String::as_str)
            {
                Some("bn254.g1") => dense::<crate::Bn254G1>(name, args, i, p),
                Some("bn254.g2") => dense::<crate::Bn254G2>(name, args, i, p),
                _ => Err(refused("kernel-operands")),
            }
        }
        Some(zkc_runtime::interactive::Identity::Ristretto255Scalar) => {
            dense::<RistrettoPoint>(name, args, i, p)
        }
        Some(zkc_runtime::interactive::Identity::Bls12381Fr) => {
            dense::<GroupPoint>(name, args, i, p)
        }
        _ => Err(refused("kernel-operands")),
    })
}
fn dense<G: Group>(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    let arg = |j| args.get(j).ok_or_else(|| refused("kernel-operands"));
    let point = |j| G::point(arg(j)?);
    let points = |j| G::points(arg(j)?);
    let alloc = |n| {
        G::limit(p, n)?;
        p.output(size(n, G::width())?, i.max_output_bytes)?;
        reserve::<G>(n)
    };
    if i.binding
        .signature()
        .outputs
        .iter()
        .all(|t| t.kind() != zkc_runtime::interactive::Type::Groups)
    {
        p.output(512, i.max_output_bytes)?;
    }
    let result = match name {
        "curve.generator" => G::value(G::generator()),
        "curve.add" => G::value(point(0)?.add(point(1)?)),
        "curve.neg" => G::value(point(0)?.neg()),
        "curve.scale" => G::value(point(0)?.scale(G::scalar(arg(1)?)?)),
        "curve.equal" => Value::Bool(point(0)? == point(1)?),
        "curve.nonidentity" => Value::Bool(point(0)? != G::identity()),
        "curve.empty" => {
            p.output(size(0, G::width())?, i.max_output_bytes)?;
            G::values(Arc::from([]))
        }
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
            G::value(G::msm(
                s,
                b,
                crate::requires_public_operands(i.binding.implementation()),
            )?)
        }
        "curve.scale_each" => {
            let (s, b) = (G::scalars(arg(0)?)?, points(1)?);
            equal_len(s.len(), b.len())?;
            let mut out = alloc(b.len())?;
            out.extend(b.iter().zip(s).map(|(b, s)| b.scale(*s)));
            G::values(out.into())
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
            G::values(out.into())
        }
        "curve.vector_scale" => {
            let b = points(0)?;
            let x = G::scalar(arg(1)?)?;
            let mut out = alloc(b.len())?;
            out.extend(b.iter().map(|b| b.scale(x)));
            G::values(out.into())
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
            G::values(out.into())
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
            return Ok(vec![G::values(left.into()), G::values(right.into())]);
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![result])
}
