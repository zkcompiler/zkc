//! Closed native wire profile. Errors are classified where they occur; opaque
//! BackendError strings are never parsed into receive failures.
mod bulk;
mod pcs;
mod structured;
use crate::{NativeBackend, Policy, Value};
use zkc_runtime::interactive::{BackendError, DecodeReason, PhysicalType, Value as RuntimeValue};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeWireError {
    Invalid(DecodeReason),
    Limit,
    Backend(BackendError),
}
impl std::fmt::Display for NativeWireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(reason) => write!(f, "native-wire-invalid:{}", reason.as_str()),
            Self::Limit => f.write_str("native-wire-limit"),
            Self::Backend(error) => write!(f, "native-wire-backend:{error}"),
        }
    }
}
impl std::error::Error for NativeWireError {}

fn frame(ty: &PhysicalType) -> Option<(u8, usize)> {
    // Exact physical identities, including storage. Other providers never fall
    // through merely because their coarse kind is Field or Group.
    if *ty == Value::Bool(false).physical_type() {
        Some((5, 7))
    } else if *ty == Value::Field(crate::Scalar::from(0)).physical_type() {
        Some((1, 38))
    } else if *ty == Value::Curve(crate::GroupPoint::identity()).physical_type() {
        Some((9, 54))
    } else if *ty == Value::Index(0).physical_type() {
        Some((31, 14))
    } else if ty.has_native_array_frame() {
        let (field, length) = ty.logical().field_array_parts()?;
        if field != zkc_runtime::interactive::Identity::Bls12381Fr {
            return None;
        }
        Some((
            64,
            usize::try_from(length)
                .ok()?
                .checked_mul(32)?
                .checked_add(6)?,
        ))
    } else if PhysicalType::default_for(ty.logical()).ok().as_ref() == Some(ty) {
        use zkc_runtime::interactive::{Identity::*, Type::*};
        match (ty.kind(), ty.logical().identity()) {
            (Field, Bn254Fr) => Some((40, 38)),
            (Group, Bn254G1) => Some((46, 38)),
            (Group, Bn254Gt) => Some((50, 390)),
            (Group, Bn254G2) => Some((48, 70)),
            (Field, KoalaBear) => Some((19, 10)),
            (Field, KoalaBearExt8) => Some((26, 38)),
            (Field, Ristretto255Scalar) => Some((13, 38)),
            (Group, Ristretto255Group) => Some((16, 38)),
            _ => Option::None,
        }
    } else {
        None
    }
}
pub fn native_wire_size(ty: &PhysicalType) -> Option<usize> {
    frame(ty).map(|(_, width)| width)
}
fn unsupported() -> NativeWireError {
    NativeWireError::Backend(BackendError::new("native-wire-type"))
}
/// Whether this closed native codec accepts a complete physical type. Tables
/// are length-prefixed; `native_wire_size` intentionally remains fixed-width.
pub fn has_native_wire(ty: &PhysicalType) -> bool {
    frame(ty).is_some()
        || bulk::format(ty).is_some()
        || table_type(ty)
        || pcs::tag(ty).is_some()
        || structured::tag(ty).is_some()
}
fn table_type(ty: &PhysicalType) -> bool {
    ty.representation() == zkc_runtime::interactive::Representation::TableLsb
        && ty.logical().spelling() == "table:bls12-381.fr"
}

/// Shared by proof-message production and transcript observation.
pub(crate) fn encode(
    value: &Value,
    policy: &Policy,
    key: &crate::setups::Setups,
) -> Result<Vec<u8>, NativeWireError> {
    if bulk::format(&value.physical_type()).is_some() {
        return bulk::encode(value, policy);
    }
    if structured::tag(&value.physical_type()).is_some() {
        return structured::encode(value, policy, key);
    }
    if pcs::tag(&value.physical_type()).is_some() {
        if key.is_registered() {
            pcs::encoded_width(value, key)?;
        }
        return pcs::encode(value, policy);
    }
    if let Value::Table(table) = value {
        use NativeWireError::Limit;
        let count = policy.table_len(table.arity()).map_err(|_| Limit)?;
        let width = count
            .checked_mul(32)
            .and_then(|n| n.checked_add(10))
            .ok_or(Limit)?;
        policy.wire(width).map_err(|_| Limit)?;
        policy
            .output(value.retained_bytes(), usize::MAX)
            .map_err(|_| Limit)?;
        // Bound both the scalar encoding and final frame before either buffer.
        policy
            .output(width.checked_mul(2).ok_or(Limit)?, usize::MAX)
            .map_err(|_| Limit)?;
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(width).map_err(|_| Limit)?;
        bytes.extend_from_slice(super::MAGIC);
        bytes.push(2);
        bytes.extend_from_slice(
            &u32::try_from(table.arity())
                .map_err(|_| Limit)?
                .to_le_bytes(),
        );
        bytes.extend_from_slice(
            &table
                .to_logical_bytes(&policy.ark_bounds())
                .map_err(|e| NativeWireError::Backend(crate::ark(e)))?,
        );
        return Ok(bytes);
    }
    encode_fixed(value, policy)
}
fn encode_fixed(value: &Value, policy: &Policy) -> Result<Vec<u8>, NativeWireError> {
    // Existing scalar frames use public ZKCV bytes. Tag 64 is a native-only,
    // shape-bound field-array frame; the checked cut supplies its complete type.

    let (tag, width) = frame(&value.physical_type()).ok_or_else(unsupported)?;
    policy.wire(width).map_err(|_| NativeWireError::Limit)?;
    policy
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| NativeWireError::Limit)?;
    if let Value::FieldArray(array) = value {
        policy
            .vector(array.elements().len())
            .map_err(|_| NativeWireError::Limit)?;
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(width)
        .map_err(|_| NativeWireError::Limit)?;
    bytes.extend_from_slice(super::MAGIC);
    bytes.push(tag);
    let encoding = |e| NativeWireError::Backend(crate::ark(e));
    match value {
        Value::FieldArray(array) => {
            array.validate().map_err(NativeWireError::Backend)?;
            for element in array.elements() {
                bytes.extend_from_slice(&zkc_arkworks::encode_scalar(element).map_err(encoding)?);
            }
        }
        Value::Index(v) => bytes.extend_from_slice(&v.to_le_bytes()),
        Value::Bool(v) => bytes.push(u8::from(*v)),
        Value::Field(v) => {
            bytes.extend_from_slice(&zkc_arkworks::encode_scalar(v).map_err(encoding)?)
        }
        Value::Curve(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bn254Field(v) => {
            bytes.extend_from_slice(&zkc_arkworks::bn254::encode_scalar(v).map_err(encoding)?)
        }
        Value::Bn254G1(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bn254Gt(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bn254G2(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::KoalaBearField(v) => bytes.extend_from_slice(&crate::plonky3::encode_scalar(*v)),
        Value::KoalaBearExt8Field(v) => {
            bytes.extend_from_slice(&crate::plonky3::encode_extension(*v))
        }
        Value::RistrettoField(v) => bytes.extend_from_slice(&v.to_bytes()),
        Value::RistrettoGroup(v) => bytes.extend_from_slice(&v.compress().to_bytes()),
        _ => return Err(unsupported()),
    }
    if bytes.len() != width {
        return Err(NativeWireError::Backend(BackendError::new(
            "native-wire-width",
        )));
    }
    Ok(bytes)
}
impl NativeBackend {
    /// Bound native input retention before expensive payload decoding. This
    /// uses byte lengths and, for recursive/bulk encodings, shape scans.
    /// Callers must still decode and check complete framing and values.
    pub fn native_input_retained_bytes(
        &self,
        ty: &PhysicalType,
        bytes: &[u8],
    ) -> Result<usize, NativeWireError> {
        if table_type(ty) || frame(ty).is_some() && !ty.has_native_array_frame() {
            // These branches select supported serializable types. Their
            // retention failures are quota failures, as in native decoding.
            return Value::typed_wire_retained_bytes_bound(ty.clone(), bytes.len(), self.policy())
                .map_err(|_| NativeWireError::Limit);
        }
        structured::retained(self, ty, bytes)
    }
    pub fn encode_native_value(&self, value: &Value) -> Result<Vec<u8>, NativeWireError> {
        encode(value, self.policy(), self.setups())
    }
    /// Parse the closed native wire profile. Fixed leaves check length/header
    /// before policy; recursive frames preflight wire, structure and aggregate
    /// policy before allocating payload values. Excessive counts are limits.
    /// The receive transition owns backend validation of the resulting value.
    /// `ty` must come from the caller's admitted receive action, not the packet.
    /// This method validates the frame against that supplied type; the session
    /// layer is responsible for associating it with the actual protocol cut.
    pub fn decode_native_value(
        &self,
        ty: &PhysicalType,
        bytes: &[u8],
    ) -> Result<Value, NativeWireError> {
        use NativeWireError::{Invalid, Limit};
        if bulk::format(ty).is_some() {
            return bulk::decode(self, ty, bytes);
        }
        if structured::tag(ty).is_some() {
            return structured::decode(self, ty, bytes);
        }
        if let Some(tag) = pcs::tag(ty) {
            return pcs::decode(self, tag, bytes);
        }
        if table_type(ty) {
            return decode_table(self.policy(), bytes);
        }
        let (tag, width) = frame(ty).ok_or_else(unsupported)?;
        if bytes.len() != width {
            return Err(Invalid(DecodeReason::Length));
        }
        if &bytes[..5] != super::MAGIC || bytes[5] != tag {
            return Err(Invalid(DecodeReason::Header));
        }
        self.policy().wire(width).map_err(|_| Limit)?;
        if tag != 64 {
            // Every installed fixed scalar/group wrapper retains 512 bytes.
            // Reject insufficient capacity before canonical/subgroup decoding;
            // fixed arrays reserve their shape-dependent backing below.
            self.policy().output(512, usize::MAX).map_err(|_| Limit)?;
        }
        let value = match tag {
            64 => {
                let count = (width - 6) / 32;
                let retained = crate::field_array::bytes(count).map_err(|_| Limit)?;
                // Vec-to-Arc conversion temporarily retains both scalar buffers.
                // Account for the peak before either allocation. Rust allocator
                // failure itself is outside the typed runtime failure contract.
                let peak = retained
                    .checked_add(count.checked_mul(32).ok_or(Limit)?)
                    .ok_or(Limit)?;
                self.policy().output(peak, usize::MAX).map_err(|_| Limit)?;
                self.policy().vector(count).map_err(|_| Limit)?;
                let mut elements = Vec::new();
                elements.try_reserve_exact(count).map_err(|_| Limit)?;
                for element in bytes[6..].as_chunks::<32>().0 {
                    elements.push(
                        zkc_arkworks::decode_scalar(element)
                            .map_err(|_| Invalid(DecodeReason::Scalar))?,
                    );
                }
                Value::FieldArray(
                    crate::FieldArray::new(ty.logical(), elements.into())
                        .map_err(NativeWireError::Backend)?,
                )
            }
            31 => Value::Index(u64::from_le_bytes(
                bytes[6..14].try_into().expect("checked index width"),
            )),
            5 => Value::Bool(super::decode_bool(&bytes[6..]).map_err(Invalid)?),
            // These checked helpers already normalize upstream decoding and
            // canonical re-encoding errors. No lost provenance is reconstructed.
            1 => Value::Field(
                zkc_arkworks::decode_scalar(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            9 => Value::Curve(
                crate::GroupPoint::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            50 => Value::Bn254Gt(
                crate::Bn254Gt::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            40 => Value::Bn254Field(
                zkc_arkworks::bn254::decode_scalar(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            46 => Value::Bn254G1(
                crate::Bn254G1::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            48 => Value::Bn254G2(
                crate::Bn254G2::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            19 => Value::KoalaBearField(
                crate::plonky3::decode_scalar(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            26 => Value::KoalaBearExt8Field(
                crate::plonky3::decode_extension(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            13 => Value::RistrettoField(
                Option::from(crate::RistrettoScalar::from_canonical_bytes(
                    bytes[6..].try_into().expect("checked scalar width"),
                ))
                .ok_or(Invalid(DecodeReason::Scalar))?,
            ),
            16 => {
                let compressed = curve25519_dalek::ristretto::CompressedRistretto(
                    bytes[6..].try_into().expect("checked group width"),
                );
                let point = compressed
                    .decompress()
                    .ok_or(Invalid(DecodeReason::Group))?;
                if point.compress() != compressed {
                    return Err(Invalid(DecodeReason::Group));
                }
                Value::RistrettoGroup(point)
            }
            _ => unreachable!("closed native frame"),
        };
        self.policy()
            .output(value.retained_bytes(), usize::MAX)
            .map_err(|_| Limit)?;
        Ok(value)
    }
}

fn decode_table(policy: &Policy, bytes: &[u8]) -> Result<Value, NativeWireError> {
    use NativeWireError::{Invalid, Limit};
    if bytes.len() < 10 {
        return Err(Invalid(DecodeReason::Length));
    }
    if &bytes[..5] != super::MAGIC || bytes[5] != 2 {
        return Err(Invalid(DecodeReason::Header));
    }
    policy.wire(bytes.len()).map_err(|_| Limit)?;
    let arity = u32::from_le_bytes(bytes[6..10].try_into().expect("checked arity")) as usize;
    // Arity and the derived allocation bound precede shifts or allocation.
    let count = policy.table_len(arity).map_err(|_| Limit)?;
    let width = count
        .checked_mul(32)
        .and_then(|n| n.checked_add(10))
        .ok_or(Limit)?;
    if bytes.len() != width {
        return Err(Invalid(DecodeReason::Length));
    }
    policy
        .output(width.checked_add(512).ok_or(Limit)?, usize::MAX)
        .map_err(|_| Limit)?;
    let mut values = Vec::new();
    values.try_reserve_exact(count).map_err(|_| Limit)?;
    for element in bytes[10..].as_chunks::<32>().0 {
        values
            .push(zkc_arkworks::decode_scalar(element).map_err(|_| Invalid(DecodeReason::Scalar))?);
    }
    let table = zkc_arkworks::Table::from_logical_vec(values, &policy.ark_bounds())
        .map_err(|e| NativeWireError::Backend(crate::ark(e)))?;
    let value = Value::Table(std::sync::Arc::new(table));
    policy
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| Limit)?;
    Ok(value)
}
