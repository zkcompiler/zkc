//! Independent public Dalek requests for Lean. No Runner/backend dispatch or
//! protocol constructor; scalar arithmetic and source control remain in Lean.
use super::{Result, codec};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::{Identity, MultiscalarMul},
};
use serde_json::{Value as Json, json};
enum Public {
    Index(u64),
    Scalar(Scalar),
    Vector(Vec<Scalar>),
    Polynomial,
    Round,
    Group(RistrettoPoint),
    Groups(Vec<RistrettoPoint>),
}
fn scalar(b: &[u8]) -> Result<Scalar> {
    Option::from(Scalar::from_canonical_bytes(
        b.try_into().map_err(|_| "primitive-field")?,
    ))
    .ok_or("primitive-field")
}
fn point(b: &[u8]) -> Result<RistrettoPoint> {
    let c = CompressedRistretto(b.try_into().map_err(|_| "primitive-group")?);
    let p = c.decompress().ok_or("primitive-group")?;
    if p.compress() != c {
        return Err("primitive-group");
    }
    Ok(p)
}
fn decode(v: &Json) -> Result<Public> {
    let [ty, bytes] = codec::array(v)? else {
        return Err("primitive-value");
    };
    let ty = codec::text(ty)?;
    let bytes = codec::unhex(codec::text(bytes)?)?;
    Ok(match ty {
        "index" => Public::Index(u64::from_le_bytes(
            codec::payload(&bytes, 31)?
                .try_into()
                .map_err(|_| "primitive-index")?,
        )),
        "field:ristretto255.scalar" => Public::Scalar(scalar(codec::payload(&bytes, 13)?)?),
        "vector:ristretto255.scalar" | "polynomial:ristretto255.scalar" => {
            let polynomial = ty.starts_with("polynomial:");
            let body = codec::counted(&bytes, if polynomial { 15 } else { 14 }, 32, 1 << 16)?;
            let v = body
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| scalar(b))
                .collect::<Result<Vec<_>>>()?;
            if polynomial {
                if v.last().is_some_and(|s| *s == Scalar::ZERO) {
                    return Err("primitive-polynomial");
                }
                Public::Polynomial
            } else {
                Public::Vector(v)
            }
        }
        "round:ristretto255.scalar" => {
            let body = codec::payload(&bytes, 18)?;
            if body.len() != 96 {
                return Err("primitive-round");
            }
            for b in body.as_chunks::<32>().0 {
                scalar(b)?;
            }
            Public::Round
        }
        "group:ristretto255.group" => Public::Group(point(codec::payload(&bytes, 16)?)?),
        "groups:ristretto255.group" => Public::Groups(
            codec::counted(&bytes, 17, 32, codec::MAX_GROUPS)?
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| point(b))
                .collect::<Result<_>>()?,
        ),
        _ => return Err("primitive-nominal-type"),
    })
}
fn group(p: RistrettoPoint) -> Json {
    codec::value("group:ristretto255.group", 16, &p.compress().to_bytes())
}
fn groups(p: &[RistrettoPoint]) -> Result<Json> {
    if p.len() > codec::MAX_GROUPS {
        return Err("primitive-group-limit");
    }
    let mut body = (p.len() as u32).to_le_bytes().to_vec();
    for p in p {
        body.extend(p.compress().to_bytes());
    }
    Ok(codec::value("groups:ristretto255.group", 17, &body))
}
pub(super) fn evaluate(
    name: &str,
    arguments: &[Json],
    attrs: &Json,
    inputs: &Json,
) -> Result<Vec<Json>> {
    if (name == "validate" && !arguments.is_empty())
        || (name != "validate" && arguments != [json!("ristretto255.group")])
    {
        return Err("primitive-static-arguments");
    }
    let attrs = codec::array(attrs)?;
    let index = if name == "curve.at" {
        let [a] = attrs else {
            return Err("primitive-attributes");
        };
        let a = codec::text(a)?;
        let n = a.parse::<usize>().map_err(|_| "primitive-index")?;
        if n.to_string() != a {
            return Err("primitive-index");
        }
        Some(n)
    } else {
        if !attrs.is_empty() {
            return Err("primitive-attributes");
        }
        None
    };
    let input = codec::array(inputs)?;
    if input.len() > 2 {
        return Err("primitive-operands");
    }
    let v = input.iter().map(decode).collect::<Result<Vec<_>>>()?;
    use Public::*;
    Ok(match (name, v.as_slice()) {
        ("validate", [_]) => vec![],
        ("curve.generator", []) => vec![group(RISTRETTO_BASEPOINT_POINT)],
        ("curve.add", [Group(a), Group(b)]) => vec![group(a + b)],
        ("curve.neg", [Group(a)]) => vec![group(-a)],
        ("curve.scale", [Group(a), Scalar(b)]) => vec![group(a * b)],
        ("curve.equal", [Group(a), Group(b)]) => vec![codec::boolean(a == b)],
        ("curve.nonidentity", [Group(a)]) => vec![codec::boolean(*a != RistrettoPoint::identity())],
        ("curve.empty", []) => vec![groups(&[])?],
        ("curve.get", [Groups(a), Index(i)]) => vec![group(
            *a.get(usize::try_from(*i).map_err(|_| "primitive-index")?)
                .ok_or("primitive-index")?,
        )],
        ("curve.length", [Groups(a)]) => {
            vec![codec::value("index", 31, &(a.len() as u64).to_le_bytes())]
        }
        ("curve.at", [Groups(a)]) => vec![group(
            *a.get(index.ok_or("primitive-index")?)
                .ok_or("primitive-index")?,
        )],
        ("curve.append", [Groups(a), Group(b)]) => {
            if a.len() >= codec::MAX_GROUPS {
                return Err("primitive-group-limit");
            }
            let mut out = a.clone();
            out.push(*b);
            vec![groups(&out)?]
        }
        ("curve.msm", [Vector(w), Groups(b)]) => {
            if w.len() != b.len() {
                return Err("primitive-length-mismatch");
            }
            vec![group(RistrettoPoint::multiscalar_mul(w, b))]
        }
        ("curve.scale_each", [Vector(w), Groups(b)]) => {
            if w.len() != b.len() {
                return Err("primitive-length-mismatch");
            }
            vec![groups(
                &w.iter().zip(b).map(|(w, b)| w * b).collect::<Vec<_>>(),
            )?]
        }
        ("curve.vector_scale", [Groups(b), Scalar(w)]) => {
            vec![groups(&b.iter().map(|b| b * w).collect::<Vec<_>>())?]
        }
        ("curve.vector_add", [Groups(a), Groups(b)]) => {
            if a.len() != b.len() {
                return Err("primitive-length-mismatch");
            }
            vec![groups(
                &a.iter().zip(b).map(|(a, b)| a + b).collect::<Vec<_>>(),
            )?]
        }
        ("curve.concat", [Groups(a), Groups(b)]) => {
            if a.len()
                .checked_add(b.len())
                .is_none_or(|n| n > codec::MAX_GROUPS)
            {
                return Err("primitive-group-limit");
            }
            let mut out = a.clone();
            out.extend_from_slice(b);
            vec![groups(&out)?]
        }
        ("curve.split", [Groups(a)]) => {
            if a.is_empty() || !a.len().is_multiple_of(2) {
                return Err("primitive-split-length");
            }
            vec![groups(&a[..a.len() / 2])?, groups(&a[a.len() / 2..])?]
        }
        _ => return Err("primitive-operation"),
    })
}
