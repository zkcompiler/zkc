//! Native wire and host-input codecs.
mod bn254;
mod domains;
use crate::{NativeBackend, Policy, Result, Value, ark, exhausted, refused};
use std::{collections::BTreeMap, sync::Arc};
use zkc_arkworks::{Scalar, Table, VerifierKey, decode_scalar, encode_scalar, parse_decimal};
use zkc_runtime::interactive::{
    Backend, EntryRole, Identity, LogicalType, PhysicalType, Representation, Type,
    Value as RuntimeValue,
};
/// Installed public wire carriers that require a host-authorized KZG setup.
/// Kind alone is insufficient: Merkle roots and paths have no setup key.
pub fn requires_setup(ty: LogicalType) -> bool {
    ty.identity() == Identity::MultilinearKzgBls12381
        && matches!(ty.kind(), Type::Commitment | Type::Proof)
}
const MAGIC: &[u8] = b"ZKCV\x01";
fn tag(ty: Type) -> Result<u8> {
    Ok(match ty {
        Type::Field => 1,
        Type::Table => 2,
        Type::Point => 3,
        Type::Round => 4,
        Type::Bool => 5,
        Type::Commitment => 6,
        Type::Proof => 7,
        Type::Group => 9,
        Type::Groups => 10,
        _ => return Err(refused("nonserializable")),
    })
}
pub(crate) fn encode(value: &Value, policy: &Policy) -> Result<Vec<u8>> {
    value.validate_serializable()?;
    policy.output(value.retained_bytes(), usize::MAX)?;
    if let Some(encoded) = crate::oracle::encode(value, policy) {
        return encoded;
    }
    if let Some(encoded) = crate::kernels::indices::encode(value, policy) {
        return encoded;
    }
    if let Some(encoded) = crate::matrix::encode(value, policy) {
        return encoded;
    }
    if let Some(encoded) = crate::codec::bn254::encode(value, policy) {
        return encoded;
    }
    if let Some(encoded) = crate::codec::domains::encode(value, policy) {
        return encoded;
    }
    let encoded_size = match value {
        Value::Field(_) => Some(38),
        Value::Bool(_) => Some(7),
        Value::Curve(_) => Some(54),
        Value::Groups(p) => p.len().checked_mul(48).and_then(|n| n.checked_add(10)),
        Value::Table(t) => t.len().checked_mul(32).and_then(|n| n.checked_add(10)),
        Value::TableMsb(t) => t.len().checked_mul(32).and_then(|n| n.checked_add(10)),
        Value::Point(p) => p.len().checked_mul(32).and_then(|n| n.checked_add(10)),
        Value::Round(_) => Some(102),
        Value::Commitment(_) => Some(135),
        Value::Proof(p) => p
            .metadata()
            .arity()
            .checked_mul(96)
            .and_then(|n| n.checked_add(87)),
        _ => return Err(refused("nonserializable")),
    }
    .ok_or_else(|| exhausted("wire-bytes"))?;
    policy.wire(encoded_size)?;
    let mut out = Vec::new();
    out.try_reserve_exact(encoded_size)
        .map_err(|_| exhausted("allocation"))?;
    out.extend_from_slice(MAGIC);
    out.push(tag(value.ty())?);
    if let Value::TableMsb(t) = value {
        policy.table_len(t.arity())?;
        out.extend(
            u32::try_from(t.arity())
                .map_err(|_| exhausted("arity-limit"))?
                .to_le_bytes(),
        );
        for value in t.logical_values() {
            out.extend(encode_scalar(value).map_err(ark)?);
        }
        return Ok(out);
    }
    let body = match value {
        Value::Field(s) => encode_scalar(s).map_err(ark)?.to_vec(),
        Value::Curve(p) => p.to_bytes().map_err(ark)?.to_vec(),
        Value::Groups(points) => {
            policy.groups(points.len())?;
            let mut bytes = Vec::new();
            bytes
                .try_reserve_exact(encoded_size - 6)
                .map_err(|_| exhausted("allocation"))?;
            bytes.extend((points.len() as u32).to_le_bytes());
            for point in points.iter() {
                bytes.extend(point.to_bytes().map_err(ark)?);
            }
            bytes
        }
        Value::Bool(b) => vec![u8::from(*b)],
        Value::Table(t) => {
            policy.table_len(t.arity())?;
            let mut b = u32::try_from(t.arity())
                .map_err(|_| exhausted("arity-limit"))?
                .to_le_bytes()
                .to_vec();
            b.extend(t.to_logical_bytes(&policy.ark_bounds()).map_err(ark)?);
            b
        }
        Value::Point(p) => {
            policy.arity(p.len())?;
            let mut b = u32::try_from(p.len())
                .map_err(|_| exhausted("arity-limit"))?
                .to_le_bytes()
                .to_vec();
            for s in p.iter() {
                b.extend(encode_scalar(s).map_err(ark)?);
            }
            b
        }
        Value::Round(q) => {
            let mut b = Vec::with_capacity(96);
            for s in q {
                b.extend(encode_scalar(s).map_err(ark)?);
            }
            b
        }
        Value::Commitment(c) => c.to_bytes(&policy.ark_bounds()).map_err(ark)?,
        Value::Proof(p) => p.to_bytes(&policy.ark_bounds()).map_err(ark)?,
        _ => return Err(refused("nonserializable")),
    };
    policy.wire(
        body.len()
            .checked_add(out.len())
            .ok_or_else(|| exhausted("wire-bytes"))?,
    )?;
    out.extend(body);
    Ok(out)
}
fn length(body: &[u8]) -> Result<(usize, &[u8])> {
    if body.len() < 4 {
        return Err(refused("wire-length"));
    }
    let n = u32::from_le_bytes(body[..4].try_into().map_err(|_| refused("wire-length"))?);
    Ok((
        usize::try_from(n).map_err(|_| exhausted("size-overflow"))?,
        &body[4..],
    ))
}
fn scalars(bytes: &[u8], n: usize) -> Result<Vec<Scalar>> {
    if n.checked_mul(32) != Some(bytes.len()) {
        return Err(refused("wire-length"));
    }
    let mut values = Vec::new();
    values
        .try_reserve_exact(n)
        .map_err(|_| exhausted("allocation"))?;
    for chunk in bytes.as_chunks::<32>().0 {
        values.push(decode_scalar(chunk).map_err(ark)?);
    }
    Ok(values)
}
fn decode(
    policy: &Policy,
    vk: Option<&VerifierKey>,
    physical: PhysicalType,
    bytes: &[u8],
) -> Result<Value> {
    policy.wire(bytes.len())?;
    if !physical.is_serializable() {
        return Err(refused("nonserializable"));
    }
    if let Some(decoded) = crate::oracle::decode(physical.clone(), bytes, policy) {
        return decoded;
    }
    if let Some(decoded) = crate::kernels::indices::decode(physical.clone(), bytes, policy) {
        return decoded;
    }
    if let Some(decoded) = crate::matrix::decode(physical.clone(), bytes, policy) {
        return decoded;
    }
    if let Some(decoded) = crate::codec::bn254::decode(physical.clone(), bytes, policy) {
        return decoded;
    }
    if let Some(decoded) = crate::codec::domains::decode(physical.clone(), bytes, policy) {
        return decoded;
    }
    let ty = physical.kind();
    let expected_tag = tag(ty)?; // Private types have no wire decoder, even for empty bytes.
    if bytes.len() < 6 || &bytes[..5] != MAGIC || bytes[5] != expected_tag {
        return Err(refused("wire-header"));
    }
    let body = &bytes[6..];
    let value = match ty {
        Type::Field => Value::Field(decode_scalar(body).map_err(ark)?),
        Type::Group => Value::Curve(crate::GroupPoint::from_bytes(body).map_err(ark)?),
        Type::Groups => {
            let (n, body) = length(body)?;
            policy.groups(n)?;
            if n.checked_mul(48) != Some(body.len()) {
                return Err(refused("wire-length"));
            }
            let mut points = Vec::new();
            points
                .try_reserve_exact(n)
                .map_err(|_| exhausted("allocation"))?;
            for bytes in body.as_chunks::<48>().0 {
                points.push(crate::GroupPoint::from_bytes(bytes).map_err(ark)?);
            }
            Value::Groups(points.into())
        }
        Type::Bool => Value::Bool(match body {
            [0] => false,
            [1] => true,
            _ => return Err(refused("wire-bool")),
        }),
        Type::Table => {
            let (n, body) = length(body)?;
            let count = policy.table_len(n)?;
            if physical.representation() == Representation::TableMsb {
                Value::TableMsb(Arc::new(
                    zkc_arkworks::MsbTable::from_logical_vec(
                        scalars(body, count)?,
                        &policy.ark_bounds(),
                    )
                    .map_err(ark)?,
                ))
            } else {
                Value::Table(Arc::new(
                    Table::from_logical_bytes(n, body, &policy.ark_bounds()).map_err(ark)?,
                ))
            }
        }
        Type::Point => {
            let (n, body) = length(body)?;
            policy.arity(n)?;
            policy.output(crate::value::size(n, 32)?, usize::MAX)?;
            Value::Point(scalars(body, n)?.into())
        }
        Type::Round => Value::Round(
            scalars(body, 3)?
                .try_into()
                .map_err(|_| refused("wire-round"))?,
        ),
        Type::Commitment => Value::Commitment(Arc::new(
            vk.ok_or_else(|| refused("receiving-key-required"))?
                .decode_commitment(body, &policy.ark_bounds())
                .map_err(ark)?,
        )),
        Type::Proof => Value::Proof(Arc::new(
            vk.ok_or_else(|| refused("receiving-key-required"))?
                .decode_proof(body, &policy.ark_bounds())
                .map_err(ark)?,
        )),
        _ => return Err(refused("nonserializable")),
    };
    if value.physical_type() != physical {
        return Err(refused("wire-type"));
    }
    policy.output(value.retained_bytes(), usize::MAX)?;
    Ok(value)
}
/// A host-populated, role-local registry. Untrusted JSON may reference a name;
/// it cannot issue tokens/opening states, import keys, change generations, or select key pins.
/// Build a distinct registry for each role and session.
#[derive(Default)]
pub struct InputBindings {
    values: BTreeMap<String, Value>,
}
impl InputBindings {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&mut self, name: &str, value: Value) -> Result<()> {
        if name.is_empty() || name.len() > 128 || self.values.contains_key(name) {
            return Err(refused("binding-name"));
        }
        self.values.insert(name.into(), value);
        Ok(())
    }
}
impl NativeBackend {
    /// Encode a public value only. The runtime envelope must be transported
    /// and checked separately; value bytes do not authenticate a session.
    pub fn encode_value(&self, value: &Value) -> Result<Vec<u8>> {
        self.validate_value(value)?;
        encode(value, self.policy())
    }
    /// Decode the admitted nominal type and storage representation.
    /// Storage layout is selected by the receiving port, never wire bytes.
    pub fn decode_typed_value(&self, ty: PhysicalType, bytes: &[u8]) -> Result<Value> {
        let vk: Option<&VerifierKey> = self.verifier_key();
        let v = decode(self.policy(), vk, ty, bytes)?;
        self.validate_value(&v)?;
        Ok(v)
    }
    /// Parse a bounded exact tagged input document in admitted port order.
    /// Aliases and entry shape/public pins are checked again by Runner::new.
    pub fn inputs_from_json(
        &self,
        role: &EntryRole,
        bytes: &[u8],
        host: &InputBindings,
    ) -> Result<Vec<Value>> {
        input_json(self, self.policy(), role, bytes, host, |port, ty, bytes| {
            self.decode_input_value(port, ty, bytes)
        })
    }
    fn decode_input_value(&self, port: &str, ty: PhysicalType, bytes: &[u8]) -> Result<Value> {
        if self.has_setup_registry() && requires_setup(ty.logical()) {
            let setup = self
                .input_setup(port)
                .ok_or_else(|| refused("input-setup-required"))?;
            self.decode_for_setup(ty, setup, bytes)
        } else {
            self.decode_typed_value(ty, bytes)
        }
    }
    /// Decode a PCS value for a host-selected, already authorized setup. The
    /// canonical value header must match that key in full. Peer bytes cannot
    /// select or register the receiving key.
    pub fn decode_for_setup(
        &self,
        ty: PhysicalType,
        setup: zkc_arkworks::Metadata,
        bytes: &[u8],
    ) -> Result<Value> {
        if !requires_setup(ty.logical()) {
            return Err(refused("wire-setup-type"));
        }
        let key = self
            .authorized_verifier_key(setup)
            .ok_or_else(|| refused("unauthorized-setup"))?;
        let value = decode(self.policy(), Some(key), ty, bytes)?;
        self.validate_value(&value)?;
        Ok(value)
    }
}

fn array(v: &serde_json::Value) -> Result<&[serde_json::Value]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| refused("input-array"))
}
fn string(v: &serde_json::Value) -> Result<&str> {
    v.as_str().ok_or_else(|| refused("input-string"))
}
fn decimal(v: &serde_json::Value) -> Result<Scalar> {
    parse_decimal(string(v)?).map_err(ark)
}
fn hex(text: &str, policy: &Policy) -> Result<Vec<u8>> {
    if !text.len().is_multiple_of(2) {
        return Err(refused("input-hex"));
    }
    policy.wire(text.len() / 2)?;
    fn digit(b: u8) -> Result<u8> {
        match b {
            b'0'..=b'9' => Ok(b - b'0'),
            b'a'..=b'f' => Ok(b - b'a' + 10),
            _ => Err(refused("input-hex")),
        }
    }
    text.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| Ok(digit(p[0])? * 16 + digit(p[1])?))
        .collect()
}
fn input_json<B: Backend<Value = Value>>(
    backend: &B,
    policy: &Policy,
    role: &EntryRole,
    bytes: &[u8],
    host: &InputBindings,
    wire: impl Fn(&str, PhysicalType, &[u8]) -> Result<Value>,
) -> Result<Vec<Value>> {
    if bytes.len() > policy.max_wire_bytes.min(1024 * 1024) {
        return Err(exhausted("input-bytes"));
    }
    // Default serde depth limit remains enabled. No objects/numbers are admitted
    // by the schema below; duplicate named records are explicitly refused.
    let document: serde_json::Value =
        serde_json::from_slice(bytes).map_err(|_| refused("input-json"))?;
    let root = array(&document)?;
    if root.len() != 2 || string(&root[0])? != "zkc.inputs/1" {
        return Err(refused("input-header"));
    }
    let records = array(&root[1])?;
    if records.len() != role.inputs.len() || records.len() > 1024 {
        return Err(refused("input-ports"));
    }
    let mut provided = BTreeMap::new();
    for record in records {
        let r = array(record)?;
        if r.len() != 2 {
            return Err(refused("input-record"));
        }
        if provided.insert(string(&r[0])?, &r[1]).is_some() {
            return Err(refused("input-duplicate"));
        }
    }
    let mut result = Vec::with_capacity(role.inputs.len());
    for (name, ty) in &role.inputs {
        let record = array(
            provided
                .get(name.as_str())
                .ok_or_else(|| refused("input-port"))?,
        )?;
        if record.len() != 2 {
            return Err(refused("input-value"));
        }
        let v = match string(&record[0])? {
            "host" => host
                .values
                .get(string(&record[1])?)
                .cloned()
                .ok_or_else(|| refused("input-host-handle"))?,
            "wire" => wire(name, ty.clone(), &hex(string(&record[1])?, policy)?)?,
            "field" if ty.kind() == Type::Field => match ty.logical().identity() {
                Identity::Bn254Fr => {
                    Value::Bn254Field(crate::parse_bn254_decimal(string(&record[1])?).map_err(ark)?)
                }
                Identity::Bls12381Fr => Value::Field(decimal(&record[1])?),
                Identity::Ristretto255Scalar => {
                    Value::RistrettoField(crate::parse_ristretto_decimal(string(&record[1])?)?)
                }
                Identity::KoalaBear => {
                    Value::KoalaBearField(crate::plonky3::parse_decimal(string(&record[1])?)?)
                }
                _ => return Err(refused("input-type")),
            },
            "vector" | "polynomial" | "round"
                if string(&record[0])? == ty.kind().name()
                    && (ty.logical().identity() != Identity::Bls12381Fr
                        || ty.kind() != Type::Round) =>
            {
                let elements = array(&record[1])?;
                let identity = ty.logical().identity();
                let width = match identity {
                    Identity::Bn254Fr | Identity::Bls12381Fr | Identity::Ristretto255Scalar => 32,
                    Identity::KoalaBear => 4,
                    _ => return Err(refused("input-type")),
                };
                policy.vector_width(elements.len(), width)?;
                if ty.kind() == Type::Round && elements.len() != 3 {
                    return Err(refused("input-shape"));
                }
                macro_rules! sequence {
                    ($parse:expr, $vector:ident, $poly:ident, $round:ident) => {{
                        let mut values = crate::kernels::arithmetic::reserve(elements.len())?;
                        for v in elements {
                            values.push(($parse)(v)?);
                        }
                        match ty.kind() {
                            Type::Vector => Value::$vector(values.into()),
                            Type::Polynomial => Value::$poly(values.into()),
                            Type::Round => Value::$round(
                                values.try_into().map_err(|_| refused("input-shape"))?,
                            ),
                            _ => return Err(refused("input-type")),
                        }
                    }};
                }
                match identity {
                    Identity::Bn254Fr => sequence!(
                        |v| crate::parse_bn254_decimal(string(v)?).map_err(ark),
                        Bn254Vector,
                        Bn254Polynomial,
                        Bn254Round
                    ),
                    Identity::Bls12381Fr => sequence!(decimal, Vector, Polynomial, Round),
                    Identity::Ristretto255Scalar => sequence!(
                        |v| crate::parse_ristretto_decimal(string(v)?),
                        RistrettoVector,
                        RistrettoPolynomial,
                        RistrettoRound
                    ),
                    Identity::KoalaBear => sequence!(
                        |v| crate::plonky3::parse_decimal(string(v)?),
                        KoalaBearVector,
                        KoalaBearPolynomial,
                        KoalaBearRound
                    ),
                    _ => return Err(refused("input-type")),
                }
            }
            "bool" if ty.kind() == Type::Bool => {
                Value::Bool(record[1].as_bool().ok_or_else(|| refused("input-bool"))?)
            }
            "table" | "point" | "round" if string(&record[0])? == ty.kind().name() => {
                let elements = array(&record[1])?;
                match ty.kind() {
                    Type::Table => {
                        if !elements.len().is_power_of_two() {
                            return Err(refused("invalid-table-length"));
                        }
                        policy.table_len(elements.len().trailing_zeros() as usize)?;
                    }
                    Type::Point => {
                        policy.arity(elements.len())?;
                        policy.output(crate::value::size(elements.len(), 32)?, usize::MAX)?;
                    }
                    Type::Round if elements.len() == 3 => (),
                    _ => return Err(refused("input-shape")),
                }
                let values = elements.iter().map(decimal).collect::<Result<Vec<_>>>()?;
                match ty.kind() {
                    Type::Table if ty.representation() == Representation::TableMsb => {
                        Value::TableMsb(Arc::new(
                            zkc_arkworks::MsbTable::from_logical_vec(values, &policy.ark_bounds())
                                .map_err(ark)?,
                        ))
                    }
                    Type::Table => Value::Table(Arc::new(
                        Table::from_logical_vec(values, &policy.ark_bounds()).map_err(ark)?,
                    )),
                    Type::Point => Value::Point(values.into()),
                    Type::Round => {
                        Value::Round(values.try_into().map_err(|_| refused("input-shape"))?)
                    }
                    _ => return Err(refused("input-type")),
                }
            }
            _ => return Err(refused("input-tag")),
        };
        if v.physical_type() != *ty {
            return Err(refused("input-type"));
        }
        backend.validate_value(&v)?;
        result.push(v);
    }
    Ok(result)
}
