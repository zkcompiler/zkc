//! Exact mathematical encodings, separate from native transport and observation.
use crate::{Binary64, Binary64Ext3, G1, Policy, Result, Scalar, Value, ark, refused, value::size};
#[cfg(test)]
use crate::{KoalaBear, KoalaBearExt8};
#[cfg(test)]
use p3_field::BasedVectorSpace;
use zkc_kernels::plonky3::words::{self, Form};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Bytes, Field, Group, Groups, Index, Vector};
    let (identity, provider) = match binding.arguments.as_slice() {
        [] => (Identity::None, "native"),
        [domain] => {
            let identity = Identity::parse(domain).ok()?;
            let provider = crate::domains::INSTALLED
                .iter()
                .find(|domain| domain.field == identity || domain.group == Some(identity))?
                .provider;
            (identity, provider)
        }
        _ => return None,
    };
    if binding.implementation != format!("{provider}/{}", binding.contract) {
        return None;
    }
    let (inputs, outputs): (&[Type], &[Type]) = match (binding.contract.as_str(), identity) {
        ("encoding.index_uleb128", Identity::None) => (&[Index], &[Bytes]),
        ("encoding.field_be", Identity::Bls12381Fr)
        | ("encoding.field_le", Identity::Ristretto255Scalar) => (&[Field], &[Bytes]),
        ("encoding.fields_be", Identity::Bls12381Fr)
        | ("encoding.fields_le", Identity::Ristretto255Scalar) => (&[Vector], &[Bytes]),
        ("encoding.fields_from_be", Identity::Bls12381Fr) => (&[Bytes], &[Bool, Vector]),
        ("encoding.groups_compressed", Identity::Bls12381G1 | Identity::Edwards25519Prime) => {
            (&[Groups], &[Bytes])
        }
        ("encoding.field_from_be", Identity::Bls12381Fr)
        | ("encoding.field_from_le", Identity::Ristretto255Scalar) => (&[Bytes], &[Bool, Field]),
        ("encoding.field_reduce_be", Identity::Bls12381Fr)
        | ("encoding.field_reduce_le", Identity::Ristretto255Scalar) => (&[Bytes], &[Field]),
        (
            "encoding.group_compressed",
            Identity::Bls12381G1 | Identity::Bls12381G2 | Identity::Edwards25519Prime,
        ) => (&[Group], &[Bytes]),
        (
            "encoding.group_from_compressed",
            Identity::Bls12381G1 | Identity::Bls12381G2 | Identity::Edwards25519Prime,
        )
        | ("encoding.group_decode_cofactor", Identity::Edwards25519Prime) => {
            (&[Bytes], &[Bool, Group])
        }
        ("encoding.cryptonote_map", Identity::Edwards25519Prime) => (&[Bytes], &[Group]),
        ("encoding.field_le", field) if crate::fields::contains(field) => (&[Field], &[Bytes]),
        ("encoding.fields_le", field) if crate::fields::contains(field) => (&[Vector], &[Bytes]),
        ("encoding.field_from_le", field) if crate::fields::contains(field) => {
            (&[Bytes], &[Bool, Field])
        }
        ("encoding.fields_from_le", field) if crate::fields::contains(field) => {
            (&[Bytes], &[Bool, Vector])
        }
        ("encoding.field_montgomery_le", field) if crate::fields::montgomery(field) => {
            (&[Field], &[Bytes])
        }
        ("encoding.fields_montgomery_le", field) if crate::fields::montgomery(field) => {
            (&[Vector], &[Bytes])
        }
        ("encoding.field_from_montgomery_le", field) if crate::fields::montgomery(field) => {
            (&[Bytes], &[Bool, Field])
        }
        ("encoding.fields_from_montgomery_le", field) if crate::fields::montgomery(field) => {
            (&[Bytes], &[Bool, Vector])
        }
        // Binary fields have little-endian bit patterns and no Montgomery form.
        ("encoding.field_le", Identity::Binary64 | Identity::Binary64Ext3) => (&[Field], &[Bytes]),
        ("encoding.fields_le", Identity::Binary64 | Identity::Binary64Ext3) => {
            (&[Vector], &[Bytes])
        }
        ("encoding.field_from_le", Identity::Binary64 | Identity::Binary64Ext3) => {
            (&[Bytes], &[Bool, Field])
        }
        ("encoding.fields_from_le", Identity::Binary64 | Identity::Binary64Ext3) => {
            (&[Bytes], &[Bool, Vector])
        }
        _ => return None,
    };
    let port = |kind| {
        let domain = if matches!(kind, Field | Group | Vector | Groups) {
            identity
        } else {
            Identity::None
        };
        PhysicalType::default_for(LogicalType::new(kind, domain).ok()?).ok()
    };
    Some(OperationSignature {
        inputs: inputs.iter().copied().map(port).collect::<Option<_>>()?,
        outputs: outputs.iter().copied().map(port).collect::<Option<_>>()?,
        attributes: AttributeRule::None,
    })
}

fn field_be(value: &Scalar) -> Result<[u8; 32]> {
    let mut bytes = zkc_kernels::arkworks::bls12_381::encode_scalar(value).map_err(ark)?;
    bytes.reverse();
    Ok(bytes)
}

// Ordered, fixed-width scalar encodings with no framing or transcript effects.
// Preflight the whole output before allocation; a failed element publishes no
// partial byte string. Vec-to-Arc conversion can temporarily retain both copies.
fn encode_collection<T, const WIDTH: usize>(
    values: &[T],
    policy: &Policy,
    available: usize,
    preflight: impl FnOnce() -> Result<()>,
    encode: impl Fn(&T) -> Result<[u8; WIDTH]>,
) -> Result<Vec<Value>> {
    let length = values
        .len()
        .checked_mul(WIDTH)
        .ok_or_else(|| crate::exhausted("size-overflow"))?;
    policy.bytes(length)?;
    policy.output(size(length, 2)?, available)?;
    preflight()?;
    let mut bytes = crate::operations::arithmetic::reserve(length)?;
    for value in values {
        bytes.extend_from_slice(&encode(value)?);
    }
    Ok(vec![Value::Bytes(bytes.into())])
}

/// Coordinate-word form selected by an installed prime-field codec name.
fn word_form(name: &str) -> Option<Form> {
    match name {
        "encoding.field_le"
        | "encoding.fields_le"
        | "encoding.field_from_le"
        | "encoding.fields_from_le" => Some(Form::Canonical),
        "encoding.field_montgomery_le"
        | "encoding.fields_montgomery_le"
        | "encoding.field_from_montgomery_le"
        | "encoding.fields_from_montgomery_le" => Some(Form::Montgomery),
        _ => None,
    }
}

use crate::fields::Registered;
/// Four-byte coordinate words of KoalaBear and its installed extensions.
/// Encoders preflight the whole output; decoders validate every word before
/// allocating and return false with a zero or empty value on any invalid word
/// or width.
fn residue_words<E: Registered>(
    name: &str,
    form: Form,
    args: &[Value],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    let width = words::width::<E>();
    let element = std::mem::size_of::<E>();
    match (name, args) {
        ("encoding.field_le" | "encoding.field_montgomery_le", [value]) => {
            let value = E::field(value)?;
            policy.bytes(width)?;
            policy.output(size(width, 1)?, available)?;
            let mut bytes = crate::operations::arithmetic::reserve(width)?;
            words::encode_into(&value, form, &mut bytes);
            Ok(vec![Value::Bytes(bytes.into())])
        }
        ("encoding.fields_le" | "encoding.fields_montgomery_le", [values]) => {
            let values = E::vector(values)?;
            policy.vector_width(values.len(), element)?;
            let length = values
                .len()
                .checked_mul(width)
                .ok_or_else(|| crate::exhausted("size-overflow"))?;
            policy.bytes(length)?;
            policy.output(size(length, 2)?, available)?;
            let mut bytes = crate::operations::arithmetic::reserve(length)?;
            for value in values {
                words::encode_into(value, form, &mut bytes);
            }
            Ok(vec![Value::Bytes(bytes.into())])
        }
        ("encoding.field_from_le" | "encoding.field_from_montgomery_le", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            let value = words::decode::<E>(bytes, form);
            Ok(vec![
                Value::Bool(value.is_some()),
                E::field_value(value.unwrap_or_default()),
            ])
        }
        (
            "encoding.fields_from_le" | "encoding.fields_from_montgomery_le",
            [Value::Bytes(bytes)],
        ) => {
            if !words::valid_elements::<E>(bytes) {
                policy.output(512usize.saturating_add(size(0, element)?), available)?;
                return Ok(vec![Value::Bool(false), E::vector_value(Vec::new())]);
            }
            let count = bytes.len() / width;
            policy.vector_width(count, element)?;
            policy.output(
                size(count, element)?
                    .checked_add(512)
                    .ok_or_else(|| crate::exhausted("size-overflow"))?,
                available,
            )?;
            let mut values = crate::operations::arithmetic::reserve(count)?;
            for chunk in bytes.chunks_exact(width) {
                values
                    .push(words::decode::<E>(chunk, form).ok_or_else(|| refused("encoding-word"))?);
            }
            Ok(vec![Value::Bool(true), E::vector_value(values)])
        }
        _ => Err(refused("encoding-operands")),
    }
}

/// Binary-field elements as little-endian bit patterns: 8 bytes for the base
/// field and 24 for the cubic extension (docs/spec/realization/external-constructions.md).
trait BitPattern: Copy + Default {
    const WIDTH: usize;
    fn encode_into(self, out: &mut Vec<u8>);
    /// Exact width; every bit pattern is an element.
    fn decode(bytes: &[u8]) -> Option<Self>;
    fn field(value: &Value) -> Option<Self>;
    fn vector(value: &Value) -> Option<&[Self]>;
    fn field_value(self) -> Value;
    fn vector_value(values: crate::Buffer<Self>) -> Value;
}
impl BitPattern for Binary64 {
    const WIDTH: usize = zkc_kernels::plonky3::binary::WIDTH;
    fn encode_into(self, out: &mut Vec<u8>) {
        out.extend_from_slice(&zkc_kernels::plonky3::binary::encode(self));
    }
    fn decode(bytes: &[u8]) -> Option<Self> {
        zkc_kernels::plonky3::binary::decode(bytes).ok()
    }
    fn field(value: &Value) -> Option<Self> {
        match value {
            Value::Binary64Field(x) => Some(*x),
            _ => None,
        }
    }
    fn vector(value: &Value) -> Option<&[Self]> {
        match value {
            Value::Binary64Vector(x) => Some(x),
            _ => None,
        }
    }
    fn field_value(self) -> Value {
        Value::Binary64Field(self)
    }
    fn vector_value(values: crate::Buffer<Self>) -> Value {
        Value::Binary64Vector(values)
    }
}
impl BitPattern for Binary64Ext3 {
    const WIDTH: usize = zkc_kernels::plonky3::binary::EXT3_WIDTH;
    fn encode_into(self, out: &mut Vec<u8>) {
        out.extend_from_slice(&zkc_kernels::plonky3::binary::encode_ext3(self));
    }
    fn decode(bytes: &[u8]) -> Option<Self> {
        zkc_kernels::plonky3::binary::decode_ext3(bytes).ok()
    }
    fn field(value: &Value) -> Option<Self> {
        match value {
            Value::Binary64Ext3Field(x) => Some(*x),
            _ => None,
        }
    }
    fn vector(value: &Value) -> Option<&[Self]> {
        match value {
            Value::Binary64Ext3Vector(x) => Some(x),
            _ => None,
        }
    }
    fn field_value(self) -> Value {
        Value::Binary64Ext3Field(self)
    }
    fn vector_value(values: crate::Buffer<Self>) -> Value {
        Value::Binary64Ext3Vector(values)
    }
}
/// Same preflight and failure rules as the coordinate-word codecs, except that
/// no bit pattern of the exact width is invalid: only a wrong length decodes
/// to false with zero or an empty vector.
fn bit_patterns<E: BitPattern>(
    name: &str,
    args: &[Value],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    let width = E::WIDTH;
    let element = std::mem::size_of::<E>();
    match (name, args) {
        ("encoding.field_le", [value]) => {
            let value = E::field(value).ok_or_else(|| refused("encoding-operands"))?;
            policy.bytes(width)?;
            policy.output(size(width, 1)?, available)?;
            let mut bytes = crate::operations::arithmetic::reserve(width)?;
            value.encode_into(&mut bytes);
            Ok(vec![Value::Bytes(bytes.into())])
        }
        ("encoding.fields_le", [values]) => {
            let values = E::vector(values).ok_or_else(|| refused("encoding-operands"))?;
            policy.vector_width(values.len(), element)?;
            let length = values
                .len()
                .checked_mul(width)
                .ok_or_else(|| crate::exhausted("size-overflow"))?;
            policy.bytes(length)?;
            policy.output(size(length, 2)?, available)?;
            let mut bytes = crate::operations::arithmetic::reserve(length)?;
            for value in values {
                value.encode_into(&mut bytes);
            }
            Ok(vec![Value::Bytes(bytes.into())])
        }
        ("encoding.field_from_le", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            let value = E::decode(bytes);
            Ok(vec![
                Value::Bool(value.is_some()),
                E::field_value(value.unwrap_or_default()),
            ])
        }
        ("encoding.fields_from_le", [Value::Bytes(bytes)]) => {
            if !bytes.len().is_multiple_of(width) {
                policy.output(512usize.saturating_add(size(0, element)?), available)?;
                return Ok(vec![Value::Bool(false), E::vector_value(Vec::new().into())]);
            }
            let count = bytes.len() / width;
            policy.vector_width(count, element)?;
            policy.output(
                size(count, element)?
                    .checked_add(512)
                    .ok_or_else(|| crate::exhausted("size-overflow"))?,
                available,
            )?;
            let mut values = crate::operations::arithmetic::reserve(count)?;
            for chunk in bytes.chunks_exact(width) {
                values.push(E::decode(chunk).ok_or_else(|| refused("encoding-word"))?);
            }
            Ok(vec![Value::Bool(true), E::vector_value(values.into())])
        }
        _ => Err(refused("encoding-operands")),
    }
}

pub(crate) fn apply(
    name: &str,
    identity: Identity,
    args: &[Value],
    attributes: &[String],
    policy: &Policy,
    available: usize,
    budget: &mut crate::operations::external::Budget,
) -> Result<Vec<Value>> {
    if !attributes.is_empty() {
        return Err(refused("encoding-attributes"));
    }
    for value in args {
        if let Value::Bytes(bytes) = value {
            policy.bytes(bytes.len())?;
        }
    }
    if let Some(form) = word_form(name) {
        match identity {
            field if crate::fields::contains(field) => {
                if form == Form::Montgomery && !crate::fields::montgomery(field) {
                    return Err(refused("encoding-operands"));
                }
                return crate::fields::with_residue!(field, |E| residue_words::<E>(
                    name, form, args, policy, available
                ));
            }
            Identity::Binary64 if form == Form::Canonical => {
                return bit_patterns::<Binary64>(name, args, policy, available);
            }
            Identity::Binary64Ext3 if form == Form::Canonical => {
                return bit_patterns::<Binary64Ext3>(name, args, policy, available);
            }
            Identity::Binary64 | Identity::Binary64Ext3 => {
                return Err(refused("encoding-operands"));
            }
            // The Ristretto little-endian codecs below keep their own rows.
            _ => {}
        }
    }
    match (name, args) {
        ("encoding.index_uleb128", [Value::Index(value)]) => {
            // u64 needs at most ten bytes. Compute into bounded stack storage,
            // then preflight its single immutable allocation before publishing.
            let mut encoded = [0u8; 10];
            let mut remaining = *value;
            let mut length = 0;
            loop {
                let byte = (remaining & 0x7f) as u8;
                remaining >>= 7;
                encoded[length] = byte | if remaining == 0 { 0 } else { 0x80 };
                length += 1;
                if remaining == 0 {
                    break;
                }
            }
            policy.bytes(length)?;
            policy.output(size(length, 1)?, available)?;
            Ok(vec![Value::Bytes(encoded[..length].into())])
        }
        ("encoding.fields_be", [Value::Vector(values)]) => {
            policy.vector(values.len())?;
            encode_collection(values, policy, available, || Ok(()), field_be)
        }
        ("encoding.fields_le", [Value::RistrettoVector(values)]) => {
            policy.vector(values.len())?;
            encode_collection(
                values,
                policy,
                available,
                || Ok(()),
                |value| Ok(value.to_bytes()),
            )
        }
        ("encoding.groups_compressed", [Value::Groups(values)]) => {
            policy.groups(values.len())?;
            encode_collection(
                values,
                policy,
                available,
                || Ok(()),
                |value| value.to_bytes().map_err(ark),
            )
        }
        ("encoding.groups_compressed", [Value::EdwardsGroups(values)]) => {
            policy.dalek_groups(values.len())?;
            encode_collection(
                values,
                policy,
                available,
                || budget.charge_units((values.len() as u64).saturating_mul(256)),
                |value| Ok(value.to_bytes()),
            )
        }
        ("encoding.field_be", [Value::Field(value)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            let bytes = field_be(value)?;
            Ok(vec![Value::Bytes(bytes.as_slice().into())])
        }
        ("encoding.fields_from_be", [Value::Bytes(bytes)]) => {
            // All-or-nothing: a ragged length or any noncanonical element
            // returns false with an empty vector, never a partial prefix.
            let canonical = bytes.len() % 32 == 0;
            let count = if canonical { bytes.len() / 32 } else { 0 };
            // Like fields_be and field_from_be, canonical decoding debits no
            // external work; element, output and operand charges still apply.
            policy.vector(count)?;
            policy.output(size(count, 32)?.saturating_add(1024), available)?;
            let mut values = crate::operations::arithmetic::reserve(count)?;
            let mut valid = canonical;
            for chunk in bytes.as_chunks::<32>().0.iter().take(count) {
                let mut little = *chunk;
                little.reverse();
                match zkc_kernels::arkworks::bls12_381::decode_scalar(&little) {
                    Ok(value) => values.push(value),
                    Err(_) => {
                        valid = false;
                        break;
                    }
                }
            }
            if !valid {
                values.clear();
            }
            Ok(vec![Value::Bool(valid), Value::Vector(values.into())])
        }
        ("encoding.field_from_be", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            let value = if let Ok(mut bytes) = <[u8; 32]>::try_from(bytes.as_ref()) {
                bytes.reverse();
                zkc_kernels::arkworks::bls12_381::decode_scalar(&bytes).ok()
            } else {
                None
            };
            Ok(vec![
                Value::Bool(value.is_some()),
                Value::Field(value.unwrap_or_default()),
            ])
        }
        ("encoding.field_reduce_be", [Value::Bytes(bytes)]) => {
            policy.output(512, available)?;
            budget.charge_units((bytes.len() as u64).saturating_mul(2))?;
            // Horner reduction reads the input directly: no input-sized copy.
            let radix = Scalar::from(256u64);
            let value = bytes.iter().fold(Scalar::from(0u64), |value, byte| {
                value * radix + Scalar::from(u64::from(*byte))
            });
            Ok(vec![Value::Field(value)])
        }
        ("encoding.field_le", [Value::RistrettoField(value)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            Ok(vec![Value::Bytes(value.to_bytes().as_slice().into())])
        }
        ("encoding.field_from_le", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            let value = <[u8; 32]>::try_from(bytes.as_ref()).ok().and_then(|b| {
                Option::<crate::RistrettoScalar>::from(
                    crate::RistrettoScalar::from_canonical_bytes(b),
                )
            });
            Ok(vec![
                Value::Bool(value.is_some()),
                Value::RistrettoField(value.unwrap_or_default()),
            ])
        }
        ("encoding.field_reduce_le", [Value::Bytes(bytes)]) => {
            policy.output(512, available)?;
            budget.charge_units((bytes.len() as u64).saturating_mul(2))?;
            let radix = crate::RistrettoScalar::from(256u64);
            let value = bytes
                .iter()
                .rev()
                .fold(crate::RistrettoScalar::ZERO, |a, b| {
                    a * radix + crate::RistrettoScalar::from(u64::from(*b))
                });
            Ok(vec![Value::RistrettoField(value)])
        }
        ("encoding.group_compressed", [Value::EdwardsGroup(point)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            budget.charge_units(256)?;
            Ok(vec![Value::Bytes(point.to_bytes().as_slice().into())])
        }
        (
            "encoding.group_from_compressed" | "encoding.group_decode_cofactor",
            [Value::Bytes(bytes)],
        ) if identity == Identity::Edwards25519Prime => {
            policy.output(1024, available)?;
            budget.charge_units(if name == "encoding.group_decode_cofactor" {
                2048
            } else {
                4096
            })?;
            let point = if name == "encoding.group_decode_cofactor" {
                crate::EdwardsPrime::decode_cofactor(bytes)
            } else {
                crate::EdwardsPrime::from_bytes(bytes)
            };
            Ok(vec![
                Value::Bool(point.is_some()),
                Value::EdwardsGroup(point.unwrap_or_else(crate::EdwardsPrime::identity)),
            ])
        }
        ("encoding.cryptonote_map", [Value::Bytes(bytes)]) => {
            policy.output(512, available)?;
            let input: [u8; 32] = bytes
                .as_ref()
                .try_into()
                .map_err(|_| refused("encoding-width"))?;
            budget.charge_units(2048)?;
            Ok(vec![Value::EdwardsGroup(
                zkc_kernels::interop::monero::cryptonote_map(input)
                    .ok_or_else(|| refused("edwards-map"))?,
            )])
        }
        ("encoding.group_compressed", [Value::Bls12381G2(point)]) => {
            policy.bytes(96)?;
            policy.output(size(96, 1)?, available)?;
            Ok(vec![Value::Bytes(
                point.to_bytes().map_err(ark)?.as_slice().into(),
            )])
        }
        ("encoding.group_from_compressed", [Value::Bytes(bytes)])
            if identity == Identity::Bls12381G2 =>
        {
            policy.output(1024, available)?;
            let point = crate::Bls12381G2::from_bytes(bytes).ok();
            Ok(vec![
                Value::Bool(point.is_some()),
                Value::Bls12381G2(point.unwrap_or_else(crate::Bls12381G2::identity)),
            ])
        }
        ("encoding.group_compressed", [Value::Curve(point)]) => {
            policy.bytes(48)?;
            policy.output(size(48, 1)?, available)?;
            Ok(vec![Value::Bytes(
                point.to_bytes().map_err(ark)?.as_slice().into(),
            )])
        }
        ("encoding.group_from_compressed", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            // Exact width, subgroup validation and canonical re-encoding are
            // owned by the checked group adapter; no transcript state is touched.
            let point = G1::from_bytes(bytes).ok();
            Ok(vec![
                Value::Bool(point.is_some()),
                Value::Curve(point.unwrap_or_else(G1::identity)),
            ])
        }
        _ => Err(refused("encoding-operands")),
    }
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/encoding.index_uleb128", "encoding.index_uleb128"),
    ("arkworks/encoding.fields_be", "encoding.fields_be"),
    (
        "arkworks/encoding.fields_from_be",
        "encoding.fields_from_be",
    ),
    ("dalek/encoding.fields_le", "encoding.fields_le"),
    (
        "arkworks/encoding.groups_compressed",
        "encoding.groups_compressed",
    ),
    (
        "dalek/encoding.groups_compressed",
        "encoding.groups_compressed",
    ),
    ("dalek/encoding.field_le", "encoding.field_le"),
    ("dalek/encoding.field_from_le", "encoding.field_from_le"),
    ("dalek/encoding.field_reduce_le", "encoding.field_reduce_le"),
    (
        "dalek/encoding.group_compressed",
        "encoding.group_compressed",
    ),
    (
        "dalek/encoding.group_from_compressed",
        "encoding.group_from_compressed",
    ),
    (
        "dalek/encoding.group_decode_cofactor",
        "encoding.group_decode_cofactor",
    ),
    ("dalek/encoding.cryptonote_map", "encoding.cryptonote_map"),
    ("plonky3/encoding.field_le", "encoding.field_le"),
    ("plonky3/encoding.field_from_le", "encoding.field_from_le"),
    ("plonky3/encoding.fields_le", "encoding.fields_le"),
    ("plonky3/encoding.fields_from_le", "encoding.fields_from_le"),
    (
        "plonky3/encoding.field_montgomery_le",
        "encoding.field_montgomery_le",
    ),
    (
        "plonky3/encoding.field_from_montgomery_le",
        "encoding.field_from_montgomery_le",
    ),
    (
        "plonky3/encoding.fields_montgomery_le",
        "encoding.fields_montgomery_le",
    ),
    (
        "plonky3/encoding.fields_from_montgomery_le",
        "encoding.fields_from_montgomery_le",
    ),
    ("arkworks/encoding.field_be", "encoding.field_be"),
    ("arkworks/encoding.field_from_be", "encoding.field_from_be"),
    (
        "arkworks/encoding.field_reduce_be",
        "encoding.field_reduce_be",
    ),
    (
        "arkworks/encoding.group_compressed",
        "encoding.group_compressed",
    ),
    (
        "arkworks/encoding.group_from_compressed",
        "encoding.group_from_compressed",
    ),
];

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, PrimeField};
    use p3_field::PrimeField32;
    fn bytes(b: &[u8]) -> Value {
        Value::Bytes(b.to_vec().into())
    }
    fn run(name: &str, args: &[Value]) -> Vec<Value> {
        apply(
            name,
            Identity::Bls12381Fr,
            args,
            &[],
            &Policy::default(),
            usize::MAX,
            &mut Default::default(),
        )
        .unwrap()
    }
    fn dalek(name: &str, args: &[Value]) -> Vec<Value> {
        let identity = if name.starts_with("encoding.field_") {
            Identity::Ristretto255Scalar
        } else {
            Identity::Edwards25519Prime
        };
        apply(
            name,
            identity,
            args,
            &[],
            &Policy::default(),
            usize::MAX,
            &mut Default::default(),
        )
        .unwrap()
    }
    #[test]
    fn unsigned_leb128_is_minimal_over_the_full_index_domain() {
        let run = |value| {
            let output = apply(
                "encoding.index_uleb128",
                Identity::None,
                &[Value::Index(value)],
                &[],
                &Policy::default(),
                usize::MAX,
                &mut Default::default(),
            )
            .unwrap();
            let Value::Bytes(bytes) = &output[0] else {
                panic!("bytes")
            };
            bytes.to_vec()
        };
        assert_eq!(run(0), [0]);
        assert_eq!(run(127), [127]);
        assert_eq!(run(128), [0x80, 0x01]);
        assert_eq!(run(300), [0xac, 0x02]);
        assert_eq!(run(624485), [0xe5, 0x8e, 0x26]);
        assert_eq!(
            run(u64::MAX),
            [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1]
        );
        let mut values = vec![0, 1, u64::MAX];
        for bit in (7..64).step_by(7) {
            values.extend([(1u64 << bit) - 1, 1u64 << bit, (1u64 << bit) + 1]);
        }
        for value in values {
            let bytes = run(value);
            assert!((1..=10).contains(&bytes.len()));
            assert!(bytes[..bytes.len() - 1].iter().all(|b| b & 0x80 != 0));
            assert_eq!(bytes.last().unwrap() & 0x80, 0);
            assert!(bytes.len() == 1 || *bytes.last().unwrap() != 0);
            let decoded = bytes
                .iter()
                .enumerate()
                .fold(0u64, |n, (i, b)| n | (u64::from(b & 0x7f) << (i * 7)));
            assert_eq!(decoded, value);
        }
    }
    #[test]
    fn unsigned_leb128_keeps_exact_binding_and_capacity_checks() {
        let mut binding = OperationBinding {
            contract: "encoding.index_uleb128".into(),
            arguments: vec![],
            implementation: "native/encoding.index_uleb128".into(),
            physical_arguments: vec![],
        };
        assert!(signature(&binding).is_some());
        binding.arguments.push("bls12-381.fr".into());
        assert!(signature(&binding).is_none());
        binding.arguments.clear();
        binding.implementation = "arkworks/encoding.index_uleb128".into();
        assert!(signature(&binding).is_none());
        binding.arguments.push("bls12-381.fr".into());
        assert!(signature(&binding).is_none()); // right provider, wrong domain arity
        binding.arguments.clear();
        binding.contract = "encoding.field_be".into();
        binding.implementation = "native/encoding.field_be".into();
        assert!(signature(&binding).is_none()); // a domain codec still needs its domain
        let run = |args: &[Value], attributes: &[String], policy: &Policy, available| {
            apply(
                "encoding.index_uleb128",
                Identity::None,
                args,
                attributes,
                policy,
                available,
                &mut Default::default(),
            )
        };
        let args = [Value::Index(u64::MAX)];
        let allowance = size(10, 1).unwrap();
        assert!(run(&args, &[], &Policy::default(), allowance).is_ok());
        assert_eq!(
            run(&args, &[], &Policy::default(), allowance - 1)
                .unwrap_err()
                .code,
            "exhausted:output-bytes"
        );
        assert_eq!(
            run(
                &args,
                &[],
                &Policy {
                    max_wire_bytes: 9,
                    ..Default::default()
                },
                usize::MAX
            )
            .unwrap_err()
            .code,
            "exhausted:wire-bytes"
        );
        assert_eq!(
            run(&args, &["extra".into()], &Policy::default(), usize::MAX)
                .unwrap_err()
                .code,
            "refused:encoding-attributes"
        );
        assert_eq!(
            run(&[Value::Bool(true)], &[], &Policy::default(), usize::MAX)
                .unwrap_err()
                .code,
            "refused:encoding-operands"
        );
    }
    #[test]
    fn collection_encodings_match_scalar_codecs_in_order() {
        let cases = [
            (
                "encoding.fields_be",
                "encoding.field_be",
                Identity::Bls12381Fr,
                Value::Vector(
                    vec![
                        Scalar::from(0u64),
                        Scalar::from(0x1234u64),
                        -Scalar::from(1u64),
                    ]
                    .into(),
                ),
                vec![
                    Value::Field(Scalar::from(0u64)),
                    Value::Field(Scalar::from(0x1234u64)),
                    Value::Field(-Scalar::from(1u64)),
                ],
            ),
            (
                "encoding.fields_le",
                "encoding.field_le",
                Identity::Ristretto255Scalar,
                Value::RistrettoVector(
                    vec![crate::RistrettoScalar::ZERO, crate::RistrettoScalar::ONE].into(),
                ),
                vec![
                    Value::RistrettoField(crate::RistrettoScalar::ZERO),
                    Value::RistrettoField(crate::RistrettoScalar::ONE),
                ],
            ),
            (
                "encoding.groups_compressed",
                "encoding.group_compressed",
                Identity::Bls12381G1,
                Value::Groups(vec![G1::identity(), G1::generator()].into()),
                vec![Value::Curve(G1::identity()), Value::Curve(G1::generator())],
            ),
            (
                "encoding.groups_compressed",
                "encoding.group_compressed",
                Identity::Edwards25519Prime,
                Value::EdwardsGroups(
                    vec![
                        crate::EdwardsPrime::identity(),
                        crate::EdwardsPrime::generator(),
                    ]
                    .into(),
                ),
                vec![
                    Value::EdwardsGroup(crate::EdwardsPrime::identity()),
                    Value::EdwardsGroup(crate::EdwardsPrime::generator()),
                ],
            ),
        ];
        for (bulk, scalar, identity, values, elements) in cases {
            let mut expected = vec![];
            for value in elements {
                let encoded = apply(
                    scalar,
                    identity,
                    &[value],
                    &[],
                    &Policy::default(),
                    usize::MAX,
                    &mut Default::default(),
                )
                .unwrap();
                let Value::Bytes(bytes) = &encoded[0] else {
                    panic!("bytes")
                };
                expected.extend_from_slice(bytes);
            }
            let limit = size(expected.len(), 2).unwrap();
            let encoded = apply(
                bulk,
                identity,
                std::slice::from_ref(&values),
                &[],
                &Policy::default(),
                limit,
                &mut Default::default(),
            )
            .unwrap();
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.as_ref() == expected));
            assert_eq!(
                apply(
                    bulk,
                    identity,
                    std::slice::from_ref(&values),
                    &[],
                    &Policy::default(),
                    limit - 1,
                    &mut Default::default()
                )
                .unwrap_err()
                .code,
                "exhausted:output-bytes"
            );
            let policy = Policy {
                max_wire_bytes: expected.len() - 1,
                ..Default::default()
            };
            assert_eq!(
                apply(
                    bulk,
                    identity,
                    &[values],
                    &[],
                    &policy,
                    usize::MAX,
                    &mut Default::default()
                )
                .unwrap_err()
                .code,
                "exhausted:wire-bytes"
            );
        }
        for (op, value) in [
            ("encoding.fields_be", Value::Vector(vec![].into())),
            ("encoding.fields_le", Value::RistrettoVector(vec![].into())),
            ("encoding.groups_compressed", Value::Groups(vec![].into())),
            (
                "encoding.groups_compressed",
                Value::EdwardsGroups(vec![].into()),
            ),
        ] {
            let encoded = apply(
                op,
                Identity::None,
                &[value],
                &[],
                &Policy::default(),
                256,
                &mut Default::default(),
            )
            .unwrap();
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.is_empty()));
        }
    }

    #[test]
    fn collection_output_preflight_precedes_external_work() {
        let values = [Value::EdwardsGroups(
            vec![crate::EdwardsPrime::generator(); 2].into(),
        )];
        let mut budget = crate::operations::external::Budget {
            limit: 511,
            spent: 0,
        };
        let invoke = |available, budget: &mut crate::operations::external::Budget| {
            apply(
                "encoding.groups_compressed",
                Identity::Edwards25519Prime,
                &values,
                &[],
                &Policy::default(),
                available,
                budget,
            )
        };
        assert_eq!(
            invoke(383, &mut budget).unwrap_err().code,
            "exhausted:output-bytes"
        );
        assert_eq!(budget.spent, 0);
        assert_eq!(
            invoke(384, &mut budget).unwrap_err().code,
            "exhausted:external-work-limit"
        );
        assert_eq!(budget.spent, 0);
        budget.limit = 512;
        assert!(invoke(384, &mut budget).is_ok());
        assert_eq!(budget.spent, 512);
    }

    #[test]
    fn little_endian_scalars_are_canonical_and_reduction_is_explicit() {
        use crate::RistrettoScalar as S;
        for value in [S::ZERO, S::ONE, -S::ONE, S::from(0x1234u64)] {
            let encoded = dalek("encoding.field_le", &[Value::RistrettoField(value)]);
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.as_ref() == value.to_bytes()));
            assert!(
                matches!(dalek("encoding.field_from_le", &encoded).as_slice(),
                [Value::Bool(true), Value::RistrettoField(v)] if *v == value)
            );
        }
        let mut modulus = (-S::ONE).to_bytes();
        modulus[0] += 1;
        for invalid in [
            vec![],
            vec![0; 31],
            vec![0; 33],
            modulus.to_vec(),
            vec![255; 32],
        ] {
            assert!(
                matches!(dalek("encoding.field_from_le", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::RistrettoField(v)] if *v == S::ZERO)
            );
        }
        assert!(
            matches!(dalek("encoding.field_reduce_le", &[bytes(&modulus)]).as_slice(),
            [Value::RistrettoField(v)] if *v == S::ZERO)
        );
        for input in [[0x5a; 64], [255; 64], [0; 64]] {
            assert!(
                matches!(dalek("encoding.field_reduce_le", &[bytes(&input)]).as_slice(),
                [Value::RistrettoField(v)] if *v == S::from_bytes_mod_order_wide(&input))
            );
        }
        assert!(
            matches!(dalek("encoding.field_reduce_le", &[bytes(&[0x34,0x12])]).as_slice(),
            [Value::RistrettoField(v)] if *v == S::from(0x1234u64))
        );
    }
    #[test]
    fn edwards_encoding_distinguishes_raw_curve_and_subgroup_admission() {
        use crate::EdwardsPrime as G;
        use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, EIGHT_TORSION};
        for point in [G::identity(), G::generator(), -G::generator()] {
            let raw = dalek("encoding.group_compressed", &[Value::EdwardsGroup(point)]);
            assert!(
                matches!(dalek("encoding.group_from_compressed", &raw).as_slice(),
                [Value::Bool(true), Value::EdwardsGroup(v)] if *v == point)
            );
        }
        for torsion in EIGHT_TORSION.iter().skip(1) {
            let raw = bytes(&(ED25519_BASEPOINT_POINT + torsion).compress().to_bytes());
            assert!(
                matches!(dalek("encoding.group_from_compressed", std::slice::from_ref(&raw)).as_slice(),
                [Value::Bool(false), Value::EdwardsGroup(v)] if *v == G::identity())
            );
            assert!(
                matches!(dalek("encoding.group_decode_cofactor", &[raw]).as_slice(),
                [Value::Bool(true), Value::EdwardsGroup(v)] if *v == G::generator().scale(8u64.into()))
            );
        }
        for raw in [vec![], vec![0; 31], vec![0; 33], vec![255; 32]] {
            assert!(
                matches!(dalek("encoding.group_decode_cofactor", &[bytes(&raw)]).as_slice(),
                [Value::Bool(false), Value::EdwardsGroup(v)] if *v == G::identity())
            );
        }
    }
    #[test]
    fn map_and_little_endian_reduction_charge_before_work() {
        for (name, identity, input, work) in [
            (
                "encoding.cryptonote_map",
                Identity::Edwards25519Prime,
                vec![1; 32],
                2048,
            ),
            (
                "encoding.field_reduce_le",
                Identity::Ristretto255Scalar,
                vec![1; 64],
                128,
            ),
        ] {
            let mut budget = crate::operations::external::Budget {
                limit: work - 1,
                spent: 0,
            };
            assert_eq!(
                apply(
                    name,
                    identity,
                    &[bytes(&input)],
                    &[],
                    &Policy::default(),
                    usize::MAX,
                    &mut budget
                )
                .unwrap_err()
                .code,
                "exhausted:external-work-limit"
            );
            assert_eq!(budget.spent, 0);
        }
        assert_eq!(
            apply(
                "encoding.cryptonote_map",
                Identity::Edwards25519Prime,
                &[bytes(&[0; 31])],
                &[],
                &Policy::default(),
                usize::MAX,
                &mut Default::default()
            )
            .unwrap_err()
            .code,
            "refused:encoding-width"
        );
    }
    #[test]
    fn field_encoding_is_exact_and_reduction_is_separate() {
        for value in [Scalar::from(0u64), Scalar::from(1u64), -Scalar::from(1u64)] {
            let encoded = run("encoding.field_be", &[Value::Field(value)]);
            let Value::Bytes(b) = &encoded[0] else {
                panic!("bytes")
            };
            assert_eq!(b.as_ref(), value.into_bigint().to_bytes_be());
            assert!(matches!(run("encoding.field_from_be", &encoded).as_slice(),
                [Value::Bool(true), Value::Field(v)] if *v == value));
        }
        let modulus = Scalar::MODULUS.to_bytes_be();
        for invalid in [
            vec![],
            vec![0; 31],
            vec![0; 33],
            modulus.clone(),
            vec![255; 32],
        ] {
            assert!(
                matches!(run("encoding.field_from_be", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::Field(v)] if *v == Scalar::from(0u64))
            );
        }
        assert!(
            matches!(run("encoding.field_reduce_be", &[bytes(&modulus)]).as_slice(),
            [Value::Field(v)] if *v == Scalar::from(0u64))
        );
        let wide = [0x5a; 64];
        assert!(
            matches!(run("encoding.field_reduce_be", &[bytes(&wide)]).as_slice(),
            [Value::Field(v)] if *v == zkc_kernels::arkworks::bls12_381::scalar_from_wide_be(&wide))
        );
    }
    #[test]
    fn reduction_debits_bounded_work_before_computation() {
        let input = bytes(&[0xa5; 4096]);
        let mut budget = crate::operations::external::Budget {
            limit: 8191,
            spent: 0,
        };
        let denied = apply(
            "encoding.field_reduce_be",
            Identity::Bls12381Fr,
            std::slice::from_ref(&input),
            &[],
            &Policy::default(),
            512,
            &mut budget,
        );
        assert_eq!(denied.unwrap_err().code, "exhausted:external-work-limit");
        assert_eq!(budget.spent, 0);
        budget.limit = 8192;
        let value = apply(
            "encoding.field_reduce_be",
            Identity::Bls12381Fr,
            &[input],
            &[],
            &Policy::default(),
            512,
            &mut budget,
        )
        .unwrap();
        assert!(
            matches!(value.as_slice(), [Value::Field(v)] if *v == Scalar::from_be_bytes_mod_order(&[0xa5;4096]))
        );
        assert_eq!(budget.spent, 8192);
    }
    #[test]
    fn group_decoder_rejects_malformed_encodings_without_failing_the_kernel() {
        for value in [G1::generator(), G1::identity(), G1::generator().neg()] {
            let encoded = run("encoding.group_compressed", &[Value::Curve(value)]);
            assert!(
                matches!(run("encoding.group_from_compressed", &encoded).as_slice(),
                [Value::Bool(true), Value::Curve(p)] if *p == value)
            );
        }
        let mut bad_infinity = G1::identity().to_bytes().unwrap();
        bad_infinity[47] = 1;
        let mut bad_flags = G1::identity().to_bytes().unwrap();
        bad_flags[0] |= 0x20;
        // x=0 has y=2 on the curve, but is not in the prime-order subgroup.
        let mut torsion = vec![0; 48];
        torsion[0] = 0x80;
        // x=1 gives x^3+4=5, a nonsquare in this base field.
        let mut off_curve = torsion.clone();
        off_curve[47] = 1;
        let modulus = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
        let mut noncanonical: Vec<u8> = (0..modulus.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&modulus[i..i + 2], 16).unwrap())
            .collect();
        noncanonical[0] |= 0x80;
        for invalid in [
            torsion,
            off_curve,
            noncanonical,
            vec![],
            vec![0; 47],
            vec![0; 49],
            vec![255; 48],
            bad_infinity.to_vec(),
            bad_flags.to_vec(),
        ] {
            assert!(
                matches!(run("encoding.group_from_compressed", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::Curve(p)] if *p == G1::identity())
            );
        }
        assert!(
            apply(
                "encoding.group_from_compressed",
                Identity::Bls12381G1,
                &[bytes(&[0; 48])],
                &[],
                &Policy::default(),
                1023,
                &mut Default::default()
            )
            .is_err()
        );
    }
    fn g2(name: &str, args: &[Value]) -> Vec<Value> {
        apply(
            name,
            Identity::Bls12381G2,
            args,
            &[],
            &Policy::default(),
            usize::MAX,
            &mut Default::default(),
        )
        .unwrap()
    }
    #[test]
    fn g2_codec_round_trips_and_rejects_malformed_encodings() {
        let generator = crate::Bls12381G2::generator();
        for value in [generator, crate::Bls12381G2::identity(), generator.neg()] {
            let encoded = g2("encoding.group_compressed", &[Value::Bls12381G2(value)]);
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.len() == 96));
            assert!(
                matches!(g2("encoding.group_from_compressed", &encoded).as_slice(),
                [Value::Bool(true), Value::Bls12381G2(p)] if *p == value)
            );
        }
        let identity = crate::Bls12381G2::identity().to_bytes().unwrap();
        let mut signed_infinity = identity;
        signed_infinity[0] |= 0x20;
        let mut uncompressed = generator.to_bytes().unwrap();
        uncompressed[0] &= 0x7f;
        for invalid in [
            vec![],
            vec![0; 95],
            vec![0; 97],
            vec![255; 96],
            signed_infinity.to_vec(),
            uncompressed.to_vec(),
            G1::generator().to_bytes().unwrap().to_vec(),
        ] {
            assert!(
                matches!(g2("encoding.group_from_compressed", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::Bls12381G2(p)] if *p == crate::Bls12381G2::identity())
            );
        }
    }
    #[test]
    fn whole_vector_big_endian_decoding_is_all_or_nothing() {
        let values = [Scalar::from(0u64), Scalar::from(7u64), -Scalar::from(1u64)];
        let encoded = run(
            "encoding.fields_be",
            &[Value::Vector(values.to_vec().into())],
        );
        assert!(
            matches!(run("encoding.fields_from_be", &encoded).as_slice(),
            [Value::Bool(true), Value::Vector(v)] if v.as_ref() == values)
        );
        assert!(
            matches!(run("encoding.fields_from_be", &[bytes(&[])]).as_slice(),
            [Value::Bool(true), Value::Vector(v)] if v.is_empty())
        );
        let Value::Bytes(valid) = &encoded[0] else {
            panic!("bytes")
        };
        let modulus = Scalar::MODULUS.to_bytes_be();
        let mut late = valid.to_vec();
        late[64..96].copy_from_slice(&modulus);
        for invalid in [
            valid[..95].to_vec(),
            [valid.as_ref(), &[0]].concat(),
            late,
            modulus.clone(),
            vec![255; 32],
        ] {
            assert!(
                matches!(run("encoding.fields_from_be", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::Vector(v)] if v.is_empty())
            );
        }
        let mut budget = crate::operations::external::Budget { limit: 0, spent: 0 };
        assert!(
            apply(
                "encoding.fields_from_be",
                Identity::Bls12381Fr,
                std::slice::from_ref(&encoded[0]),
                &[],
                &Policy::default(),
                usize::MAX,
                &mut budget,
            )
            .is_ok()
        );
        assert_eq!(budget.spent, 0);
        assert_eq!(
            apply(
                "encoding.fields_from_be",
                Identity::Bls12381Fr,
                std::slice::from_ref(&encoded[0]),
                &[],
                &Policy::default(),
                size(3, 32).unwrap(),
                &mut Default::default(),
            )
            .unwrap_err()
            .code,
            "exhausted:output-bytes"
        );
        assert_eq!(
            apply(
                "encoding.fields_from_be",
                Identity::Bls12381Fr,
                &encoded,
                &[],
                &Policy {
                    max_table_elements: 2,
                    ..Default::default()
                },
                usize::MAX,
                &mut Default::default(),
            )
            .unwrap_err()
            .code,
            "exhausted:element-limit"
        );
    }

    fn koala(
        name: &str,
        identity: Identity,
        args: &[Value],
        policy: &Policy,
    ) -> Result<Vec<Value>> {
        apply(
            name,
            identity,
            args,
            &[],
            policy,
            usize::MAX,
            &mut Default::default(),
        )
    }
    fn words_of(value: &Value) -> Vec<u32> {
        let Value::Bytes(bytes) = value else {
            panic!("bytes")
        };
        bytes
            .as_chunks::<4>()
            .0
            .iter()
            .map(|w| u32::from_le_bytes(*w))
            .collect()
    }

    #[test]
    fn koala_bear_word_codecs_bind_only_their_family() {
        for (contract, domain, provider, admitted) in [
            ("encoding.field_le", "koala-bear", "plonky3", true),
            (
                "encoding.field_le",
                "koala-bear.ext8-binomial3",
                "plonky3",
                true,
            ),
            ("encoding.field_le", "koala-bear", "dalek", false),
            ("encoding.field_reduce_le", "koala-bear", "plonky3", false),
            ("encoding.fields_from_le", "koala-bear", "plonky3", true),
            (
                "encoding.fields_from_le",
                "ristretto255.scalar",
                "dalek",
                false,
            ),
            (
                "encoding.field_montgomery_le",
                "koala-bear",
                "plonky3",
                true,
            ),
            (
                "encoding.field_montgomery_le",
                "bls12-381.fr",
                "arkworks",
                false,
            ),
            (
                "encoding.field_from_montgomery_le",
                "koala-bear.ext8-binomial3",
                "plonky3",
                true,
            ),
            (
                "encoding.fields_montgomery_le",
                "koala-bear",
                "plonky3",
                true,
            ),
            (
                "encoding.fields_from_montgomery_le",
                "koala-bear",
                "plonky3",
                true,
            ),
        ] {
            let binding = OperationBinding {
                contract: contract.into(),
                arguments: vec![domain.into()],
                implementation: format!("{provider}/{contract}"),
                physical_arguments: vec![],
            };
            assert_eq!(
                signature(&binding).is_some(),
                admitted,
                "{contract} {domain}"
            );
        }
    }

    #[test]
    fn koala_bear_words_round_trip_both_residue_forms() {
        let p = zkc_kernels::plonky3::MODULUS;
        let values = [0, 1, 2, p - 1, 1 << 24, 987_654_321];
        let vector = Value::KoalaBearVector(values.map(KoalaBear::new).to_vec().into());
        let policy = Policy::default();
        for (encode, decode, montgomery) in [
            ("encoding.fields_le", "encoding.fields_from_le", false),
            (
                "encoding.fields_montgomery_le",
                "encoding.fields_from_montgomery_le",
                true,
            ),
        ] {
            let bytes = koala(
                encode,
                Identity::KoalaBear,
                std::slice::from_ref(&vector),
                &policy,
            )
            .unwrap();
            let expected: Vec<u32> = values
                .iter()
                .map(|&x| {
                    if montgomery {
                        ((u64::from(x) << 32) % u64::from(p)) as u32
                    } else {
                        x
                    }
                })
                .collect();
            assert_eq!(words_of(&bytes[0]), expected);
            let decoded = koala(decode, Identity::KoalaBear, &bytes, &policy).unwrap();
            assert!(
                matches!(&decoded[..], [Value::Bool(true), Value::KoalaBearVector(v)]
                if v.iter().map(|x| x.as_canonical_u32()).eq(values))
            );
            let Value::Bytes(raw) = &bytes[0] else {
                unreachable!()
            };
            // Each scalar codec agrees with the collection codec element by element.
            let (scalar_encode, scalar_decode) = if montgomery {
                (
                    "encoding.field_montgomery_le",
                    "encoding.field_from_montgomery_le",
                )
            } else {
                ("encoding.field_le", "encoding.field_from_le")
            };
            for (i, &x) in values.iter().enumerate() {
                let one = koala(
                    scalar_encode,
                    Identity::KoalaBear,
                    &[Value::KoalaBearField(KoalaBear::new(x))],
                    &policy,
                )
                .unwrap();
                assert!(matches!(&one[0], Value::Bytes(b) if **b == raw[4 * i..4 * i + 4]));
                let back = koala(scalar_decode, Identity::KoalaBear, &one, &policy).unwrap();
                assert!(
                    matches!(&back[..], [Value::Bool(true), Value::KoalaBearField(y)]
                    if y.as_canonical_u32() == x)
                );
            }
        }
    }

    #[test]
    fn koala_bear_word_decoders_reject_noncanonical_words_and_widths() {
        let p = zkc_kernels::plonky3::MODULUS;
        let policy = Policy::default();
        for name in [
            "encoding.field_from_le",
            "encoding.field_from_montgomery_le",
        ] {
            for invalid in [
                p.to_le_bytes().to_vec(),
                u32::MAX.to_le_bytes().to_vec(),
                vec![],
                vec![1, 0, 0],
                vec![1, 0, 0, 0, 0],
            ] {
                let out = koala(name, Identity::KoalaBear, &[bytes(&invalid)], &policy).unwrap();
                assert!(
                    matches!(&out[..], [Value::Bool(false), Value::KoalaBearField(x)]
                        if *x == KoalaBear::new(0)),
                    "{name} {invalid:?}"
                );
            }
        }
        for name in [
            "encoding.fields_from_le",
            "encoding.fields_from_montgomery_le",
        ] {
            let mut late = [1u32, 2, 3].map(u32::to_le_bytes).concat();
            late.extend((p + 7).to_le_bytes());
            for invalid in [late, vec![0; 7], vec![0; 9]] {
                let out = koala(name, Identity::KoalaBear, &[bytes(&invalid)], &policy).unwrap();
                assert!(
                    matches!(&out[..], [Value::Bool(false), Value::KoalaBearVector(v)] if v.is_empty()),
                    "{name} {invalid:?}"
                );
            }
            let empty = koala(name, Identity::KoalaBear, &[bytes(&[])], &policy).unwrap();
            assert!(
                matches!(&empty[..], [Value::Bool(true), Value::KoalaBearVector(v)] if v.is_empty())
            );
            // A canonical but oversized input exhausts the element ceiling.
            let small = Policy {
                max_table_elements: 2,
                ..Policy::default()
            };
            assert_eq!(
                koala(name, Identity::KoalaBear, &[bytes(&[0; 12])], &small)
                    .unwrap_err()
                    .code,
                "exhausted:element-limit"
            );
        }
    }

    #[test]
    fn koala_bear_extension_words_are_ascending_coordinates() {
        let p = zkc_kernels::plonky3::MODULUS;
        let policy = Policy::default();
        let x = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(100 + i as u32));
        let canonical = koala(
            "encoding.field_le",
            Identity::KoalaBearExt8,
            &[Value::KoalaBearExt8Field(x)],
            &policy,
        )
        .unwrap();
        assert_eq!(words_of(&canonical[0]), (100..108).collect::<Vec<u32>>());
        let montgomery = koala(
            "encoding.fields_montgomery_le",
            Identity::KoalaBearExt8,
            &[Value::KoalaBearExt8Vector(vec![x, x].into())],
            &policy,
        )
        .unwrap();
        let word = |c: u32| ((u64::from(c) << 32) % u64::from(p)) as u32;
        let once: Vec<u32> = (100..108).map(word).collect();
        assert_eq!(words_of(&montgomery[0]), [once.clone(), once].concat());
        let back = koala(
            "encoding.fields_from_montgomery_le",
            Identity::KoalaBearExt8,
            &montgomery,
            &policy,
        )
        .unwrap();
        assert!(
            matches!(&back[..], [Value::Bool(true), Value::KoalaBearExt8Vector(v)]
            if v[..] == [x, x])
        );
        // A whole number of base words that is not a whole number of elements.
        let partial = koala(
            "encoding.fields_from_le",
            Identity::KoalaBearExt8,
            &[bytes(&[0; 36])],
            &policy,
        )
        .unwrap();
        assert!(
            matches!(&partial[..], [Value::Bool(false), Value::KoalaBearExt8Vector(v)] if v.is_empty())
        );
        let narrow = koala(
            "encoding.field_from_le",
            Identity::KoalaBearExt8,
            &[bytes(&[0; 4])],
            &policy,
        )
        .unwrap();
        assert!(matches!(
            &narrow[..],
            [Value::Bool(false), Value::KoalaBearExt8Field(_)]
        ));
    }
}
