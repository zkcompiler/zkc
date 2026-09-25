//! Public BN254 primitive requests for the independent source interpreter.
//!
//! No NativeBackend or protocol evaluator is used here. Lean owns scalar and
//! polynomial arithmetic and protocol control; upstream group cryptography is
//! the explicitly shared trusted service. Nominal types and wire framing are
//! checked independently of the native runtime.
use super::{Result, codec};
use serde_json::{Value as Json, json};
use zkc_arkworks::bn254::{G1 as Group1, G2 as Group2, Scalar, decode_scalar, pairing_check};

const MAX_ELEMENTS: usize = 32768;

enum Public {
    Scalar(Scalar),
    Vector(Vec<Scalar>),
    G1(Group1),
    G2(Group2),
    G1s(Vec<Group1>),
    G2s(Vec<Group2>),
    Index(u64),
    Validated,
}

fn decode(value: &Json) -> Result<Public> {
    let [ty, bytes] = codec::array(value)? else {
        return Err("primitive-value");
    };
    let ty = codec::text(ty)?;
    let bytes = codec::unhex(codec::text(bytes)?)?;
    Ok(match ty {
        "field:bn254.fr" => Public::Scalar(
            decode_scalar(codec::payload(&bytes, 40)?).map_err(|_| "primitive-field")?,
        ),
        "vector:bn254.fr" | "polynomial:bn254.fr" => {
            let polynomial = ty.starts_with("polynomial:");
            let body = codec::counted(&bytes, if polynomial { 42 } else { 41 }, 32, MAX_ELEMENTS)?;
            let values = body
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| decode_scalar(b).map_err(|_| "primitive-field"))
                .collect::<Result<Vec<_>>>()?;
            if polynomial {
                if values.last().is_some_and(|x| *x == Scalar::from(0)) {
                    return Err("primitive-polynomial");
                }
                Public::Validated
            } else {
                Public::Vector(values)
            }
        }
        "round:bn254.fr" => {
            let body = codec::payload(&bytes, 43)?;
            if body.len() != 96 {
                return Err("primitive-wire-length");
            }
            for b in body.as_chunks::<32>().0.iter() {
                decode_scalar(b).map_err(|_| "primitive-field")?;
            }
            Public::Validated
        }
        "matrix:bn254.fr" => {
            codec::matrix(zkc_runtime::interactive::Identity::Bn254Fr, &bytes)?;
            Public::Validated
        }
        "group:bn254.g1" => Public::G1(
            Group1::from_bytes(codec::payload(&bytes, 46)?).map_err(|_| "primitive-group")?,
        ),
        "group:bn254.g2" => Public::G2(
            Group2::from_bytes(codec::payload(&bytes, 48)?).map_err(|_| "primitive-group")?,
        ),
        "groups:bn254.g1" => Public::G1s(
            codec::counted(&bytes, 47, 32, MAX_ELEMENTS)?
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| Group1::from_bytes(b).map_err(|_| "primitive-group"))
                .collect::<Result<_>>()?,
        ),
        "groups:bn254.g2" => Public::G2s(
            codec::counted(&bytes, 49, 64, MAX_ELEMENTS)?
                .as_chunks::<64>()
                .0
                .iter()
                .map(|b| Group2::from_bytes(b).map_err(|_| "primitive-group"))
                .collect::<Result<_>>()?,
        ),
        "index" => Public::Index(u64::from_le_bytes(
            codec::payload(&bytes, 31)?
                .try_into()
                .map_err(|_| "primitive-index")?,
        )),
        _ => return Err("primitive-nominal-type"),
    })
}

fn index(value: &Json) -> Result<usize> {
    let text = codec::text(value)?;
    let value = text.parse::<usize>().map_err(|_| "primitive-index")?;
    if value.to_string() != text {
        return Err("primitive-index");
    }
    Ok(value)
}

macro_rules! group_evaluator {
    ($fn:ident, $group:ident, $point:ident, $points:ident, $domain:literal, $tag:literal, $tags:literal) => {
        fn $fn(name: &str, selected: Option<usize>, values: &[Public]) -> Result<Vec<Json>> {
            fn point(p: &$group) -> Result<Json> {
                Ok(codec::value(
                    concat!("group:", $domain),
                    $tag,
                    &p.to_bytes().map_err(|_| "primitive-group")?,
                ))
            }
            fn points(p: &[$group]) -> Result<Json> {
                if p.len() > MAX_ELEMENTS {
                    return Err("primitive-group-limit");
                }
                let mut out = (p.len() as u32).to_le_bytes().to_vec();
                for p in p {
                    out.extend(p.to_bytes().map_err(|_| "primitive-group")?);
                }
                Ok(codec::value(concat!("groups:", $domain), $tags, &out))
            }
            use Public::*;
            Ok(match (name, values) {
                ("curve.generator", []) => vec![point(&$group::generator())?],
                ("curve.add", [$point(a), $point(b)]) => vec![point(&a.add(b))?],
                ("curve.neg", [$point(a)]) => vec![point(&a.neg())?],
                ("curve.scale", [$point(a), Scalar(s)]) => vec![point(&a.scale(*s))?],
                ("curve.equal", [$point(a), $point(b)]) => vec![codec::boolean(a == b)],
                ("curve.nonidentity", [$point(a)]) => {
                    vec![codec::boolean(*a != $group::identity())]
                }
                ("curve.empty", []) => vec![points(&[])?],
                ("curve.at", [$points(p)]) => vec![point(
                    p.get(selected.ok_or("primitive-index")?)
                        .ok_or("primitive-index")?,
                )?],
                ("curve.get", [$points(p), Index(i)]) => vec![point(
                    p.get(usize::try_from(*i).map_err(|_| "primitive-index")?)
                        .ok_or("primitive-index")?,
                )?],
                ("curve.length", [$points(p)]) => {
                    vec![codec::value("index", 31, &(p.len() as u64).to_le_bytes())]
                }
                ("curve.append", [$points(p), $point(q)]) => {
                    if p.len() >= MAX_ELEMENTS {
                        return Err("primitive-group-limit");
                    }
                    let mut out = p.clone();
                    out.push(*q);
                    vec![points(&out)?]
                }
                ("curve.msm", [Vector(s), $points(p)]) => {
                    if s.len() != p.len() {
                        return Err("primitive-length-mismatch");
                    }
                    vec![point(&$group::msm(s, p).map_err(|_| "primitive-msm")?)?]
                }
                ("curve.scale_each", [Vector(s), $points(p)]) => {
                    if s.len() != p.len() {
                        return Err("primitive-length-mismatch");
                    }
                    vec![points(
                        &s.iter()
                            .zip(p)
                            .map(|(s, p)| p.scale(*s))
                            .collect::<Vec<_>>(),
                    )?]
                }
                ("curve.vector_scale", [$points(p), Scalar(s)]) => {
                    vec![points(&p.iter().map(|p| p.scale(*s)).collect::<Vec<_>>())?]
                }
                ("curve.vector_add", [$points(p), $points(q)]) => {
                    if p.len() != q.len() {
                        return Err("primitive-length-mismatch");
                    }
                    vec![points(
                        &p.iter().zip(q).map(|(p, q)| p.add(q)).collect::<Vec<_>>(),
                    )?]
                }
                ("curve.concat", [$points(p), $points(q)]) => {
                    if p.len()
                        .checked_add(q.len())
                        .is_none_or(|n| n > MAX_ELEMENTS)
                    {
                        return Err("primitive-group-limit");
                    }
                    let mut out = p.clone();
                    out.extend_from_slice(q);
                    vec![points(&out)?]
                }
                ("curve.split", [$points(p)]) => {
                    if p.is_empty() || !p.len().is_multiple_of(2) {
                        return Err("primitive-split-length");
                    }
                    vec![points(&p[..p.len() / 2])?, points(&p[p.len() / 2..])?]
                }
                _ => return Err("primitive-operation"),
            })
        }
    };
}
group_evaluator!(g1, Group1, G1, G1s, "bn254.g1", 46, 47);
group_evaluator!(g2, Group2, G2, G2s, "bn254.g2", 48, 49);

pub(super) fn evaluate(
    name: &str,
    arguments: &[Json],
    attrs: &Json,
    inputs: &Json,
) -> Result<Vec<Json>> {
    let attrs = codec::array(attrs)?;
    let selected = if name == "curve.at" {
        let [a] = attrs else {
            return Err("primitive-attributes");
        };
        Some(index(a)?)
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
    let values = input.iter().map(decode).collect::<Result<Vec<_>>>()?;
    if name == "validate" {
        if !arguments.is_empty() {
            return Err("primitive-static-arguments");
        }
        return if values.len() == 1 {
            Ok(vec![])
        } else {
            Err("primitive-operands")
        };
    }
    if name == "pairing.check" {
        if arguments != [json!("bn254.fr")] {
            return Err("primitive-static-arguments");
        }
        let [Public::G1s(a), Public::G2s(b)] = values.as_slice() else {
            return Err("primitive-nominal-type");
        };
        if a.len() != b.len() {
            return Err("primitive-length-mismatch");
        }
        return Ok(vec![codec::boolean(
            pairing_check(a, b).map_err(|_| "primitive-pairing")?,
        )]);
    }
    match arguments {
        [domain] if domain == "bn254.g1" => g1(name, selected, &values),
        [domain] if domain == "bn254.g2" => g2(name, selected, &values),
        _ => Err("primitive-static-arguments"),
    }
}
