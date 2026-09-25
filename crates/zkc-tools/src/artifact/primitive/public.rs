use super::{Result, codec};
use serde_json::Value as Json;
use zkc_arkworks::{Commitment, GroupPoint, OpeningProof, Scalar, VerifierKey, decode_scalar};

enum PublicValue {
    Index(u64),
    Field(Scalar),
    Point(Vec<Scalar>),
    Vector(Vec<Scalar>),
    Polynomial,
    Round,
    Bool,
    Group(GroupPoint),
    Groups(Vec<GroupPoint>),
    Key(VerifierKey),
    Commitment(Commitment),
    Proof(OpeningProof),
}

struct Key {
    bytes: Vec<u8>,
    verifier: VerifierKey,
}

fn configuration(json: &Json) -> Result<Vec<Key>> {
    let records = codec::array(json)?;
    if records.len() > 1024 {
        return Err("primitive-key-limit");
    }
    // Validate the complete nominal declaration list before importing any key,
    // preserving the request's fail-closed type-check order.
    for record in records {
        let [_, kind, _] = codec::array(record)? else {
            return Err("primitive-key-record");
        };
        if codec::text(kind)? != "verifier_key:multilinear.kzg.bls12-381/1" {
            return Err("primitive-key-type");
        }
    }
    let mut names = std::collections::BTreeSet::new();
    records
        .iter()
        .map(|record| {
            let [port, _, wire] = codec::array(record)? else {
                return Err("primitive-key-record");
            };
            let port = codec::text(port)?;
            if port.is_empty() || port.len() > 128 || !names.insert(port) {
                return Err("primitive-key-record");
            }
            let bytes = codec::unhex(codec::text(wire)?)?;
            // These complete bytes are the expected application configuration, not
            // a key learned from the candidate proof. The embedded identity is also
            // reconstructed by VerifierKey::from_bytes below.
            let pin = bytes
                .get(49..81)
                .ok_or("primitive-key-header")?
                .try_into()
                .map_err(|_| "primitive-key-header")?;
            let verifier = VerifierKey::from_bytes(&bytes, pin, &codec::bounds())
                .map_err(|_| "primitive-key")?;
            Ok(Key { bytes, verifier })
        })
        .collect()
}

fn selected_key<'a>(keys: &'a [Key], payload: &[u8]) -> Result<&'a VerifierKey> {
    let metadata = payload.get(9..81).ok_or("primitive-key-header")?;
    keys.iter()
        .find(|key| key.bytes.get(9..81) == Some(metadata))
        .map(|key| &key.verifier)
        .ok_or("primitive-key-identity")
}

fn decode(json: &Json, keys: &[Key]) -> Result<PublicValue> {
    let [kind, wire] = codec::array(json)? else {
        return Err("primitive-value");
    };
    let kind = codec::text(kind)?;
    let bytes = codec::unhex(codec::text(wire)?)?;
    Ok(match kind {
        "index" => PublicValue::Index(u64::from_le_bytes(
            codec::payload(&bytes, 31)?
                .try_into()
                .map_err(|_| "primitive-index")?,
        )),
        "field" => PublicValue::Field(codec::field(&bytes)?),
        "bool" => {
            if !matches!(codec::payload(&bytes, 5)?, [0] | [1]) {
                return Err("primitive-bool");
            }
            PublicValue::Bool
        }
        "vector" | "polynomial" => {
            let b = codec::counted(&bytes, if kind == "vector" { 11 } else { 12 }, 32, 1 << 16)?;
            let v = b
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| decode_scalar(b).map_err(|_| "primitive-field"))
                .collect::<Result<Vec<_>>>()?;
            if kind == "polynomial" {
                if v.last().is_some_and(|s| *s == Scalar::from(0)) {
                    return Err("primitive-polynomial");
                }
                PublicValue::Polynomial
            } else {
                PublicValue::Vector(v)
            }
        }
        "round" => {
            let b = codec::payload(&bytes, 4)?;
            if b.len() != 96 {
                return Err("primitive-round");
            }
            for b in b.as_chunks::<32>().0 {
                decode_scalar(b).map_err(|_| "primitive-field")?;
            }
            PublicValue::Round
        }
        "point" => {
            let bytes = codec::counted(&bytes, 3, 32, 16)?;
            PublicValue::Point(
                bytes
                    .as_chunks::<32>()
                    .0
                    .iter()
                    .map(|bytes| decode_scalar(bytes).map_err(|_| "primitive-field"))
                    .collect::<Result<_>>()?,
            )
        }
        "group" => PublicValue::Group(
            GroupPoint::from_bytes(codec::payload(&bytes, 9)?).map_err(|_| "primitive-group")?,
        ),
        "groups" => {
            let bytes = codec::counted(&bytes, 10, 48, codec::MAX_GROUPS)?;
            PublicValue::Groups(
                bytes
                    .as_chunks::<48>()
                    .0
                    .iter()
                    .map(|bytes| GroupPoint::from_bytes(bytes).map_err(|_| "primitive-group"))
                    .collect::<Result<_>>()?,
            )
        }
        "verifier_key" => PublicValue::Key(
            keys.iter()
                .find(|key| key.bytes == bytes)
                .map(|key| key.verifier.clone())
                .ok_or("primitive-key-identity")?,
        ),
        "commitment" => {
            let body = codec::payload(&bytes, 6)?;
            PublicValue::Commitment(
                selected_key(keys, body)?
                    .decode_commitment(body, &codec::bounds())
                    .map_err(|_| "primitive-commitment")?,
            )
        }
        "proof" => {
            let body = codec::payload(&bytes, 7)?;
            PublicValue::Proof(
                selected_key(keys, body)?
                    .decode_proof(body, &codec::bounds())
                    .map_err(|_| "primitive-proof")?,
            )
        }
        _ => return Err("primitive-value-kind"),
    })
}

fn group(point: &GroupPoint) -> Result<Json> {
    Ok(codec::value(
        "group",
        9,
        &point.to_bytes().map_err(|_| "primitive-group")?,
    ))
}
fn groups(points: &[GroupPoint]) -> Result<Json> {
    if points.len() > codec::MAX_GROUPS {
        return Err("primitive-group-limit");
    }
    let mut bytes = (points.len() as u32).to_le_bytes().to_vec();
    for point in points {
        bytes.extend(point.to_bytes().map_err(|_| "primitive-group")?);
    }
    Ok(codec::value("groups", 10, &bytes))
}

fn evaluate_bls(keys: &[Key], name: &str, attrs: &Json, inputs: &Json) -> Result<Vec<Json>> {
    let attrs = codec::array(attrs)?;
    let index = if name == "curve.at" {
        let [value] = attrs else {
            return Err("primitive-attributes");
        };
        let value = codec::text(value)?;
        let n = value.parse::<u64>().map_err(|_| "primitive-index")?;
        if n.to_string() != value {
            return Err("primitive-index");
        }
        Some(usize::try_from(n).map_err(|_| "primitive-index")?)
    } else {
        if !attrs.is_empty() {
            return Err("primitive-attributes");
        }
        None
    };
    let inputs = codec::array(inputs)?;
    if inputs.len() > 5 {
        return Err("primitive-operands");
    }
    let values = inputs
        .iter()
        .map(|v| decode(v, keys))
        .collect::<Result<Vec<_>>>()?;
    use PublicValue::*;
    Ok(match (name, values.as_slice()) {
        ("validate", [_]) => vec![],
        ("curve.generator", []) => vec![group(&GroupPoint::generator())?],
        ("curve.neg", [Group(a)]) => vec![group(&a.neg())?],
        ("curve.nonidentity", [Group(a)]) => vec![codec::boolean(*a != GroupPoint::identity())],
        ("curve.msm", [Vector(w), Groups(b)]) => {
            if w.len() != b.len() {
                return Err("primitive-length-mismatch");
            }
            vec![group(&GroupPoint::msm(w, b).map_err(|_| "primitive-msm")?)?]
        }
        ("curve.scale_each", [Vector(w), Groups(b)]) => {
            if w.len() != b.len() {
                return Err("primitive-length-mismatch");
            }
            vec![groups(
                &w.iter()
                    .zip(b)
                    .map(|(w, b)| b.scale(*w))
                    .collect::<Vec<_>>(),
            )?]
        }
        ("curve.vector_scale", [Groups(b), Field(w)]) => {
            vec![groups(&b.iter().map(|b| b.scale(*w)).collect::<Vec<_>>())?]
        }
        ("curve.vector_add", [Groups(a), Groups(b)]) => {
            if a.len() != b.len() {
                return Err("primitive-length-mismatch");
            }
            vec![groups(
                &a.iter().zip(b).map(|(a, b)| a.add(b)).collect::<Vec<_>>(),
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
        ("curve.add", [Group(a), Group(b)]) => vec![group(&a.add(b))?],
        ("curve.scale", [Group(a), Field(b)]) => vec![group(&a.scale(*b))?],
        ("curve.equal", [Group(a), Group(b)]) => vec![codec::boolean(a == b)],
        ("curve.empty", []) => vec![groups(&[])?],
        ("curve.append", [Groups(a), Group(b)]) => {
            if a.len() >= codec::MAX_GROUPS {
                return Err("primitive-group-limit");
            }
            let mut next = a.clone();
            next.push(*b);
            vec![groups(&next)?]
        }
        ("curve.get", [Groups(a), Index(i)]) => vec![group(
            a.get(usize::try_from(*i).map_err(|_| "primitive-index")?)
                .ok_or("primitive-index")?,
        )?],
        ("curve.length", [Groups(a)]) => {
            vec![codec::value("index", 31, &(a.len() as u64).to_le_bytes())]
        }
        ("curve.at", [Groups(a)]) => vec![group(
            a.get(index.ok_or("primitive-index")?)
                .ok_or("primitive-index")?,
        )?],
        ("pcs.check", [Key(k), Commitment(c), Point(p), Field(v), Proof(proof)]) => {
            vec![codec::boolean(
                k.check(c, p, *v, proof)
                    .map_err(|_| "primitive-pcs-check")?,
            )]
        }
        _ => return Err("primitive-operation"),
    })
}

/// Full nominal public-primitive requests. The authorized keys are supplied by
/// the reference application's configuration; for a receive this list contains
/// only its selected key. Payload metadata cannot expand that authority.
pub(super) fn evaluate_explicit(
    records: &Json,
    operation: &Json,
    arguments: &Json,
    attrs: &Json,
    inputs: &Json,
) -> Result<Vec<Json>> {
    use serde_json::json;
    use zkc_runtime::interactive::LogicalType;
    let name = codec::text(operation)?;
    let arguments = codec::array(arguments)?;
    // Configuration belongs to the complete request, not its operation's
    // curve. Validate every installed key even when this operation uses none.
    let keys = configuration(records)?;
    if name == "validate" && codec::array(inputs)?.len() != 1 {
        return Err("primitive-operation");
    }
    if matches!(
        arguments.first().and_then(Json::as_str),
        Some("bn254.fr" | "bn254.g1" | "bn254.g2")
    ) {
        return super::bn254::evaluate(name, arguments, attrs, inputs);
    }
    if arguments.first().and_then(Json::as_str) == Some("ristretto255.group") {
        return super::ristretto::evaluate(name, arguments, attrs, inputs);
    }
    let expected = match name {
        "validate" => None,
        "pcs.check" => Some("multilinear.kzg.bls12-381/1"),
        "curve.generator" | "curve.add" | "curve.scale" | "curve.equal" | "curve.empty"
        | "curve.append" | "curve.get" | "curve.length" | "curve.at" | "curve.neg"
        | "curve.nonidentity" | "curve.msm" | "curve.scale_each" | "curve.vector_add"
        | "curve.vector_scale" | "curve.split" | "curve.concat" => Some("bls12-381.g1"),
        _ => return Err("primitive-operation"),
    };
    let expected = expected.into_iter().map(Json::from).collect::<Vec<_>>();
    if arguments != expected {
        return Err("primitive-static-arguments");
    }
    let mut values = Vec::new();
    for input in codec::array(inputs)? {
        let [ty, wire] = codec::array(input)? else {
            return Err("primitive-value");
        };
        let ty = LogicalType::parse(codec::text(ty)?).map_err(|_| "primitive-nominal-type")?;
        if name == "validate" && ty.kind() == zkc_runtime::interactive::Type::Matrix {
            if !codec::array(attrs)?.is_empty() {
                return Err("primitive-attributes");
            }
            codec::matrix(ty.identity(), &codec::unhex(codec::text(wire)?)?)?;
            return Ok(vec![]);
        }
        if name == "validate" && ty.identity() == zkc_runtime::interactive::Identity::KoalaBear {
            return super::koala_bear::validate(&ty.spelling(), codec::text(wire)?, attrs);
        }
        if name == "validate"
            && matches!(
                ty.identity(),
                zkc_runtime::interactive::Identity::Bn254Fr
                    | zkc_runtime::interactive::Identity::Bn254G1
                    | zkc_runtime::interactive::Identity::Bn254G2
            )
        {
            return super::bn254::evaluate(name, arguments, attrs, inputs);
        }
        if name == "validate"
            && matches!(
                ty.identity(),
                zkc_runtime::interactive::Identity::Ristretto255Scalar
                    | zkc_runtime::interactive::Identity::Ristretto255Group
            )
        {
            return super::ristretto::evaluate(name, arguments, attrs, inputs);
        }
        if !matches!(
            ty.identity(),
            zkc_runtime::interactive::Identity::None
                | zkc_runtime::interactive::Identity::Bls12381Fr
                | zkc_runtime::interactive::Identity::Bls12381G1
                | zkc_runtime::interactive::Identity::MultilinearKzgBls12381
        ) {
            return Err("primitive-nominal-type");
        }
        values.push(json!([ty.kind().name(), wire]));
    }
    let outputs = evaluate_bls(&keys, name, attrs, &json!(values))?;
    outputs
        .into_iter()
        .map(|output| {
            let [kind, wire] = codec::array(&output)? else {
                return Err("primitive-output");
            };
            let kind = codec::text(kind)?;
            let ty = match kind {
                "bool" | "index" => kind.to_owned(),
                "group" | "groups" => format!("{kind}:bls12-381.g1"),
                _ => return Err("primitive-output"),
            };
            Ok(json!([ty, wire]))
        })
        .collect()
}
