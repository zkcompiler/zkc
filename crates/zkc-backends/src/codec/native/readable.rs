//! Human-readable native values lower to the same canonical frames as typed
//! inputs. This module allocates bytes only; Host admission owns native decoding.
use super::{bulk, frame, structured, table_type};
use serde_json::Value as Json;
use zkc_runtime::interactive::{Identity, LogicalType, PhysicalType, Type};
type Result<T> = std::result::Result<T, &'static str>;

/// Decode readable JSON using an independently checked expected physical type.
/// `limit` bounds the complete returned frame, including nested sequences.
pub fn readable_wire(ty: &PhysicalType, value: &Json, limit: usize) -> Result<Vec<u8>> {
    let mut out = Buffer {
        bytes: Vec::new(),
        limit,
    };
    write(ty, value, &mut out, 0)?;
    Ok(out.bytes)
}
struct Buffer {
    bytes: Vec<u8>,
    limit: usize,
}
impl Buffer {
    fn put(&mut self, bytes: &[u8]) -> Result<()> {
        if bytes.len() > self.limit.saturating_sub(self.bytes.len()) {
            return Err("entry-input-limit");
        }
        self.bytes
            .try_reserve(bytes.len())
            .map_err(|_| "entry-input-limit")?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }
    fn header(&mut self, tag: u8) -> Result<()> {
        self.put(super::super::MAGIC)?;
        self.put(&[tag])
    }
    fn count(&mut self, count: usize) -> Result<()> {
        self.put(
            &u32::try_from(count)
                .map_err(|_| "entry-input-limit")?
                .to_le_bytes(),
        )
    }
}
fn object<'a>(value: &'a Json, names: &[&str]) -> Result<&'a serde_json::Map<String, Json>> {
    let object = value.as_object().ok_or("entry-input-shape")?;
    if object.len() != names.len() || names.iter().any(|key| !object.contains_key(*key)) {
        return Err("entry-input-shape");
    }
    Ok(object)
}
fn array(value: &Json) -> Result<&[Json]> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or("entry-input-shape")
}
fn hex(value: &Json, out: &mut Buffer) -> Result<()> {
    let s = value.as_str().ok_or("entry-input-shape")?;
    if s.len() % 2 != 0 {
        return Err("entry-input-encoding");
    }
    if s.len() / 2 > out.limit.saturating_sub(out.bytes.len()) {
        return Err("entry-input-limit");
    }
    for pair in s.as_bytes().as_chunks::<2>().0.iter() {
        let digit = |b: u8| match b {
            b'0'..=b'9' => Ok(b - b'0'),
            b'a'..=b'f' => Ok(b - b'a' + 10),
            _ => Err("entry-input-encoding"),
        };
        out.put(&[digit(pair[0])? * 16 + digit(pair[1])?])?;
    }
    Ok(())
}
fn decimal<'a>(value: &'a Json, modulus: &str) -> Result<&'a str> {
    let s = value.as_str().ok_or("entry-input-shape")?;
    if s.is_empty()
        || s.len() > modulus.len()
        || (s.len() > 1 && s.starts_with('0'))
        || !s.bytes().all(|b| b.is_ascii_digit())
        || s.len() == modulus.len() && s >= modulus
    {
        return Err("entry-input-decimal");
    }
    Ok(s)
}
fn natural(value: &Json) -> Result<u64> {
    decimal(value, "18446744073709551616")?
        .parse()
        .map_err(|_| "entry-input-decimal")
}
fn scalar(identity: Identity, value: &Json, out: &mut Buffer) -> Result<()> {
    use Identity::*;
    if identity == KoalaBearExt8 {
        if value.is_string() {
            scalar(KoalaBear, value, out)?;
            return out.put(&[0; 28]);
        }
        let values = array(value)?;
        if values.len() != 8 {
            return Err("entry-input-shape");
        }
        for v in values {
            scalar(KoalaBear, v, out)?;
        }
        return Ok(());
    }
    let (modulus, width) = match identity {
        Bls12381Fr => (crate::SCALAR_MODULUS_DECIMAL, 32),
        Bn254Fr => (
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            32,
        ),
        Ristretto255Scalar => (crate::RISTRETTO_SCALAR_MODULUS_DECIMAL, 32),
        KoalaBear => ("2130706433", 4),
        _ => return Err("entry-input-codec"),
    };
    let s = decimal(value, modulus)?;
    let mut bytes = [0u8; 32];
    for digit in s.bytes() {
        let mut carry = u16::from(digit - b'0');
        for byte in &mut bytes[..width] {
            let n = u16::from(*byte) * 10 + carry;
            *byte = n as u8;
            carry = n >> 8;
        }
        if carry != 0 {
            return Err("entry-input-decimal");
        }
    }
    out.put(&bytes[..width])
}
fn physical(logical: LogicalType) -> Result<PhysicalType> {
    PhysicalType::default_for(logical).map_err(|_| "entry-input-codec")
}
fn write(ty: &PhysicalType, value: &Json, out: &mut Buffer, depth: usize) -> Result<()> {
    if depth > 32 || !super::has_native_wire(ty) {
        return Err("entry-input-codec");
    }
    if value.get("wire").is_some() {
        object(value, &["wire"])?;
        return hex(&value["wire"], out);
    }
    if let Some((tag, width)) = frame(ty) {
        let start = out.bytes.len();
        out.header(tag)?;
        match ty.kind() {
            Type::Bool => out.put(&[u8::from(value.as_bool().ok_or("entry-input-shape")?)])?,
            Type::Index => out.put(&natural(value)?.to_le_bytes())?,
            Type::Field => scalar(ty.logical().identity(), value, out)?,
            Type::Group => {
                object(value, &["bytes"])?;
                hex(&value["bytes"], out)?;
            }
            Type::FieldArray => {
                // The installed FieldArray representation supports BLS Fr only;
                // PhysicalType admission rejects other logical field identities.
                let (identity, length) = ty
                    .logical()
                    .field_array_parts()
                    .ok_or("entry-input-codec")?;
                let values = array(value)?;
                if values.len() as u64 != length {
                    return Err("entry-input-shape");
                }
                for value in values {
                    scalar(identity, value, out)?;
                }
            }
            _ => return Err("entry-input-codec"),
        }
        if out.bytes.len() - start != width {
            return Err("entry-input-shape");
        }
        return Ok(());
    }
    if let Some((tag, width, _)) = bulk::format(ty) {
        match ty.kind() {
            Type::Vector | Type::Groups => {
                let values = array(value)?;
                out.header(tag)?;
                out.count(values.len())?;
                for v in values {
                    let start = out.bytes.len();
                    if ty.kind() == Type::Vector {
                        scalar(ty.logical().identity(), v, out)?;
                    } else {
                        object(v, &["bytes"])?;
                        hex(&v["bytes"], out)?;
                    }
                    if out.bytes.len() - start != width {
                        return Err("entry-input-shape");
                    }
                }
            }
            Type::Matrix => {
                object(value, &["rows", "columns", "entries"])?;
                let rows = natural(&value["rows"])?;
                let columns = natural(&value["columns"])?;
                let values = array(&value["entries"])?;
                if rows > crate::matrix::MATRIX_DIMENSION_LIMIT as u64
                    || columns > crate::matrix::MATRIX_DIMENSION_LIMIT as u64
                    || values.len() > crate::matrix::MATRIX_NONZERO_LIMIT
                {
                    return Err("entry-input-limit");
                }
                out.header(tag)?;
                out.count(rows as usize)?;
                out.count(columns as usize)?;
                out.count(values.len())?;
                for v in values {
                    let entry = array(v)?;
                    if entry.len() != 3 {
                        return Err("entry-input-shape");
                    }
                    for index in &entry[..2] {
                        let n = u32::try_from(natural(index)?).map_err(|_| "entry-input-shape")?;
                        out.put(&n.to_le_bytes())?;
                    }
                    scalar(ty.logical().identity(), &entry[2], out)?;
                }
            }
            _ => return Err("entry-input-codec"),
        }
        return Ok(());
    }
    if let Some(tag) = structured::tag(ty) {
        match ty.kind() {
            Type::Indices => {
                let values = array(value)?;
                out.header(tag)?;
                out.count(values.len())?;
                for v in values {
                    out.put(&natural(v)?.to_le_bytes())?;
                }
            }
            Type::Sequence => {
                let values = array(value)?;
                out.header(tag)?;
                out.count(values.len())?;
                let logical = ty.logical();
                let element = physical(
                    logical
                        .sequence_element()
                        .ok_or("entry-input-codec")?
                        .clone(),
                )?;
                for v in values {
                    let at = out.bytes.len();
                    out.count(0)?;
                    write(&element, v, out, depth + 1)?;
                    let length =
                        u32::try_from(out.bytes.len() - at - 4).map_err(|_| "entry-input-limit")?;
                    out.bytes[at..at + 4].copy_from_slice(&length.to_le_bytes());
                }
            }
            _ => return Err("entry-input-codec"),
        }
        return Ok(());
    }
    if table_type(ty) {
        let values = array(value)?;
        if !values.len().is_power_of_two() {
            return Err("entry-input-shape");
        }
        out.header(2)?;
        out.count(values.len().trailing_zeros() as usize)?;
        for v in values {
            scalar(Identity::Bls12381Fr, v, out)?;
        }
        return Ok(());
    }
    Err("entry-input-codec")
}
fn decimal_text(bytes: &[u8]) -> String {
    let mut digits = vec![0u8];
    for byte in bytes.iter().rev() {
        let mut carry = u16::from(*byte);
        for d in &mut digits {
            let n = u16::from(*d) * 256 + carry;
            *d = (n % 10) as u8;
            carry = n / 10;
        }
        while carry != 0 {
            digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}
// Serialize one canonical frame directly into the caller's serializer. This
// avoids constructing an unbounded intermediate JSON tree before the caller's
// output byte limit can stop serialization.
struct Hex<'a>(&'a [u8]);
impl std::fmt::Display for Hex<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}
impl serde::Serialize for Hex<'_> {
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> std::result::Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}
struct Scalar<'a>(Identity, &'a [u8]);
impl serde::Serialize for Scalar<'_> {
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> std::result::Result<S::Ok, S::Error> {
        if self.0 == Identity::KoalaBearExt8 {
            serializer.collect_seq(self.1.as_chunks::<4>().0.iter().map(|b| decimal_text(b)))
        } else {
            serializer.serialize_str(&decimal_text(self.1))
        }
    }
}
struct Encoded<'a>(&'static str, &'a [u8]);
impl serde::Serialize for Encoded<'_> {
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> std::result::Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        let mut map = serializer.serialize_map(Some(1))?;
        map.serialize_entry(self.0, &Hex(self.1))?;
        map.end()
    }
}
struct Frame<'a>(&'a PhysicalType, &'a [u8]);
impl serde::Serialize for Frame<'_> {
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> std::result::Result<S::Ok, S::Error> {
        use serde::ser::{SerializeMap, SerializeSeq};
        let Self(ty, bytes) = *self;
        if frame(ty).is_some() {
            let body = &bytes[6..];
            return match ty.kind() {
                Type::Bool => serializer.serialize_bool(body[0] != 0),
                Type::Index => serializer
                    .serialize_str(&u64::from_le_bytes(body.try_into().unwrap()).to_string()),
                Type::Field => Scalar(ty.logical().identity(), body).serialize(serializer),
                Type::Group => Encoded("bytes", body).serialize(serializer),
                Type::FieldArray => serializer.collect_seq(
                    body.as_chunks::<32>()
                        .0
                        .iter()
                        .map(|b| Scalar(Identity::Bls12381Fr, b)),
                ),
                _ => Encoded("wire", bytes).serialize(serializer),
            };
        }
        if let Some((_, width, _)) = bulk::format(ty) {
            return match ty.kind() {
                Type::Vector => serializer.collect_seq(
                    bytes[10..]
                        .chunks_exact(width)
                        .map(|b| Scalar(ty.logical().identity(), b)),
                ),
                Type::Groups => serializer
                    .collect_seq(bytes[10..].chunks_exact(width).map(|b| Encoded("bytes", b))),
                Type::Matrix => {
                    struct Entries<'a>(Identity, usize, &'a [u8]);
                    impl serde::Serialize for Entries<'_> {
                        fn serialize<S: serde::Serializer>(
                            &self,
                            serializer: S,
                        ) -> std::result::Result<S::Ok, S::Error> {
                            serializer.collect_seq(self.2.chunks_exact(self.1).map(|b| {
                                (
                                    u32::from_le_bytes(b[..4].try_into().unwrap()).to_string(),
                                    u32::from_le_bytes(b[4..8].try_into().unwrap()).to_string(),
                                    Scalar(self.0, &b[8..]),
                                )
                            }))
                        }
                    }
                    let mut map = serializer.serialize_map(Some(3))?;
                    map.serialize_entry(
                        "rows",
                        &u32::from_le_bytes(bytes[6..10].try_into().unwrap()).to_string(),
                    )?;
                    map.serialize_entry(
                        "columns",
                        &u32::from_le_bytes(bytes[10..14].try_into().unwrap()).to_string(),
                    )?;
                    map.serialize_entry(
                        "entries",
                        &Entries(ty.logical().identity(), width, &bytes[18..]),
                    )?;
                    map.end()
                }
                _ => Encoded("wire", bytes).serialize(serializer),
            };
        }
        if structured::tag(ty).is_some() {
            if ty.kind() == Type::Indices {
                return serializer.collect_seq(
                    bytes[10..]
                        .as_chunks::<8>()
                        .0
                        .iter()
                        .map(|b| u64::from_le_bytes(*b).to_string()),
                );
            }
            if ty.kind() == Type::Sequence {
                let logical = ty.logical();
                let child = physical(logical.sequence_element().expect("native sequence").clone())
                    .expect("native sequence element");
                let count = u32::from_le_bytes(bytes[6..10].try_into().unwrap()) as usize;
                let mut sequence = serializer.serialize_seq(Some(count))?;
                let mut rest = &bytes[10..];
                while !rest.is_empty() {
                    let n = u32::from_le_bytes(rest[..4].try_into().unwrap()) as usize;
                    sequence.serialize_element(&Frame(&child, &rest[4..4 + n]))?;
                    rest = &rest[4 + n..];
                }
                return sequence.end();
            }
        }
        if table_type(ty) {
            return serializer.collect_seq(
                bytes[10..]
                    .as_chunks::<32>()
                    .0
                    .iter()
                    .map(|b| Scalar(Identity::Bls12381Fr, b)),
            );
        }
        Encoded("wire", bytes).serialize(serializer)
    }
}
impl crate::NativeBackend {
    /// Encode an admitted value for readable serialization. The native frame is
    /// bounded by backend policy; JSON is streamed into the caller's serializer.
    pub fn encode_readable_value(
        &self,
        value: &crate::Value,
    ) -> std::result::Result<impl serde::Serialize, super::NativeWireError> {
        use zkc_runtime::interactive::Value as _;
        struct Readable {
            ty: PhysicalType,
            bytes: Vec<u8>,
        }
        impl serde::Serialize for Readable {
            fn serialize<S: serde::Serializer>(
                &self,
                serializer: S,
            ) -> std::result::Result<S::Ok, S::Error> {
                Frame(&self.ty, &self.bytes).serialize(serializer)
            }
        }
        Ok(Readable {
            ty: value.physical_type(),
            bytes: self.encode_native_value(value)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Domain, EntryPolicy, NativeBackend, Policy, SetupRegistry, Value};
    use serde_json::json;
    use zkc_runtime::interactive::Value as _;
    fn backend() -> NativeBackend {
        NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "readable", "test", None), None),
            SetupRegistry::default(),
        )
        .unwrap()
    }
    #[test]
    fn readable_and_typed_values_have_identical_canonical_frames() {
        let backend = backend();
        let values = vec![
            Value::Bool(true),
            Value::Index(u64::MAX),
            Value::Field(crate::parse_decimal("12345678901234567890").unwrap()),
            Value::Bn254Field(crate::parse_bn254_decimal("2345678901234567890").unwrap()),
            Value::RistrettoField(crate::parse_ristretto_decimal("345678901234567890").unwrap()),
            Value::KoalaBearField(crate::parse_koala_bear_decimal("2130706432").unwrap()),
            Value::KoalaBearExt8Field(
                crate::plonky3::decode_extension(&[
                    1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 7, 0,
                    0, 0, 8, 0, 0, 0,
                ])
                .unwrap(),
            ),
            Value::Curve(crate::GroupPoint::identity()),
            Value::Bn254G1(crate::Bn254G1::identity()),
            Value::Bn254G2(crate::Bn254G2::identity()),
            Value::RistrettoGroup(crate::RistrettoPoint::default()),
            Value::Vector(vec![crate::Scalar::from(1), crate::Scalar::from(2)].into()),
            Value::Indices(vec![0, u64::MAX].into()),
            Value::FieldArray(
                crate::FieldArray::new(
                    LogicalType::field_array(Identity::Bls12381Fr, 2).unwrap(),
                    vec![crate::Scalar::from(1), crate::Scalar::from(2)].into(),
                )
                .unwrap(),
            ),
            Value::groups(&[crate::GroupPoint::identity()], &Policy::default()).unwrap(),
            Value::Sequence(
                crate::Sequence::new(
                    LogicalType::parse("index").unwrap(),
                    vec![Value::Index(1), Value::Index(2)],
                    &Policy::default(),
                )
                .unwrap(),
            ),
            Value::table(
                &[crate::Scalar::from(1), crate::Scalar::from(2)],
                &Policy::default(),
            )
            .unwrap(),
        ];
        for value in values {
            let wire = backend.encode_native_value(&value).unwrap();
            let readable =
                serde_json::to_value(backend.encode_readable_value(&value).unwrap()).unwrap();
            let encoded = readable_wire(&value.physical_type(), &readable, wire.len()).unwrap();
            assert_eq!(wire, encoded, "{readable}");
            assert!(
                backend
                    .decode_native_value(&value.physical_type(), &encoded)
                    .is_ok()
            );
            assert_eq!(
                readable_wire(&value.physical_type(), &readable, wire.len() - 1).unwrap_err(),
                "entry-input-limit"
            );
        }
        for identity in [
            Identity::Bn254Fr,
            Identity::Ristretto255Scalar,
            Identity::KoalaBear,
            Identity::KoalaBearExt8,
        ] {
            assert!(physical(LogicalType::field_array(identity, 8).unwrap()).is_err());
        }
    }
    #[test]
    fn scalar_spelling_is_exact_bounded_and_never_reduced() {
        let ty = Value::Field(crate::Scalar::from(0)).physical_type();
        for bad in [
            json!(1),
            json!(null),
            json!("01"),
            json!("-1"),
            json!("+1"),
            json!("1e2"),
            json!(crate::SCALAR_MODULUS_DECIMAL),
            json!("9".repeat(10000)),
        ] {
            assert!(readable_wire(&ty, &bad, 38).is_err(), "{bad}");
        }
        let ext = Value::KoalaBearExt8Field(crate::plonky3::parse_extension_decimal("0").unwrap())
            .physical_type();
        assert_eq!(
            readable_wire(&ext, &json!("7"), 38).unwrap(),
            readable_wire(&ext, &json!(["7", "0", "0", "0", "0", "0", "0", "0"]), 38).unwrap()
        );
        assert!(readable_wire(&ext, &json!(["7"]), 38).is_err());
        assert!(
            readable_wire(
                &ext,
                &json!(["0", "0", "0", "0", "0", "0", "0", "2130706433"]),
                38
            )
            .is_err()
        );
    }
    #[test]
    fn matrix_bounds_and_sparse_canonicality_use_native_admission() {
        let backend = backend();
        let ty = physical(LogicalType::new(Type::Matrix, Identity::Bls12381Fr).unwrap()).unwrap();
        let good = json!({"rows":"2","columns":"2","entries":[["0","1","7"],["1","0","11"]]});
        let wire = readable_wire(&ty, &good, 4096).unwrap();
        let value = backend.decode_native_value(&ty, &wire).unwrap();
        assert_eq!(
            serde_json::to_value(backend.encode_readable_value(&value).unwrap()).unwrap(),
            good
        );
        for entries in [
            json!([["1", "0", "11"], ["0", "1", "7"]]),
            json!([["0", "1", "7"], ["0", "1", "11"]]),
            json!([["0", "1", "0"]]),
            json!([["2", "0", "7"]]),
        ] {
            let wire = readable_wire(
                &ty,
                &json!({"rows":"2","columns":"2","entries":entries}),
                4096,
            )
            .unwrap();
            assert!(backend.decode_native_value(&ty, &wire).is_err());
        }
        assert_eq!(
            readable_wire(
                &ty,
                &json!({"rows":u64::MAX.to_string(),"columns":"2","entries":[]}),
                4096
            )
            .unwrap_err(),
            "entry-input-limit"
        );
    }
}
