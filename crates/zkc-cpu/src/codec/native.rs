//! Closed native wire profile. Errors are classified where they occur; opaque
//! BackendError strings are never parsed into receive failures.
mod bn254;
mod bulk;
mod domains;
mod input;
pub use input::NativeInputSize;
mod pcs;
mod readable;
mod structured;
use crate::{CpuBackend, Policy, Value};
pub use readable::readable_wire;
use zkc_runtime::vm::{BackendError, DecodeReason, PhysicalType, Type, Value as RuntimeValue};

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
    if crate::fields::contains(ty.logical().identity()) && ty.kind() == Type::Field {
        if PhysicalType::default_for(ty.logical().clone())
            .ok()
            .as_ref()
            != Some(ty)
        {
            return None;
        }
        return Some((
            crate::fields::tags(ty.logical().identity()).ok()?[0],
            6 + crate::fields::element_width(ty.logical().identity()).ok()?,
        ));
    }
    // Positive selected codec inventory. Canonical ZKCV tags are unchanged.
    if crate::operations::halo2curves::is_resident(ty) {
        return match (ty.kind(), ty.logical().identity()) {
            (Type::Field, zkc_runtime::vm::Identity::Bn254Fr) => Some((40, 38)),
            (Type::Group, zkc_runtime::vm::Identity::Bn254G1) => Some((46, 38)),
            (Type::Group, zkc_runtime::vm::Identity::Bn254G2) => Some((48, 70)),
            _ => None,
        };
    }
    if crate::operations::blst::is_resident(ty) {
        return match (ty.kind(), ty.logical().identity()) {
            (Type::Field, zkc_runtime::vm::Identity::Bls12381Fr) => Some((1, 38)),
            (Type::Group, zkc_runtime::vm::Identity::Bls12381G1) => Some((9, 54)),
            (Type::Group, zkc_runtime::vm::Identity::Bls12381G2) => Some((51, 102)),
            _ => None,
        };
    }
    // Exact physical identities, including storage. Other providers never fall
    // through merely because their coarse kind is Field or Group.
    if *ty == Value::Bool(false).physical_type() {
        Some((5, 7))
    } else if *ty == Value::Field(crate::Scalar::from(0)).physical_type() {
        Some((1, 38))
    } else if *ty == Value::Curve(crate::G1::identity()).physical_type() {
        Some((9, 54))
    } else if *ty == Value::Index(0).physical_type() {
        Some((31, 14))
    } else if crate::field_array::supports_type(ty) {
        let (field, length) = ty.logical().field_array_parts()?;
        if field != zkc_runtime::vm::Identity::Bls12381Fr {
            return None;
        }
        Some((
            64,
            usize::try_from(length)
                .ok()?
                .checked_mul(32)?
                .checked_add(6)?,
        ))
    } else if PhysicalType::default_for(ty.logical().clone())
        .ok()
        .as_ref()
        == Some(ty)
    {
        use zkc_runtime::vm::{Identity::*, Type::*};
        match (ty.kind(), ty.logical().identity()) {
            (Field, Bn254Fr) => Some((40, 38)),
            (Group, Bn254G1) => Some((46, 38)),
            (Group, Bn254Gt) => Some((50, 390)),
            (Group, Bn254G2) => Some((48, 70)),
            (Group, Bls12381G2) => Some((51, 102)),
            (Group, Bls12381Gt) => Some((53, 582)),
            (Field, Binary64) => Some((73, 14)),
            (Field, Binary64Ext3) => Some((76, 30)),
            (Field, Ristretto255Scalar) => Some((13, 38)),
            (Group, Ristretto255Group) => Some((16, 38)),
            (Group, Edwards25519Prime) => Some((68, 38)),
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
// Fixed leaves preserve framing errors before capacity checks. Share this
// nonallocating check with Host measurement so preflight cannot mask Decode.
fn fixed_header(ty: &PhysicalType, bytes: &[u8]) -> Result<(u8, usize), NativeWireError> {
    let (tag, width) = frame(ty).ok_or_else(unsupported)?;
    if bytes.len() != width {
        return Err(NativeWireError::Invalid(DecodeReason::Length));
    }
    if &bytes[..5] != super::MAGIC || bytes[5] != tag {
        return Err(NativeWireError::Invalid(DecodeReason::Header));
    }
    Ok((tag, width))
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
    ty.representation() == zkc_runtime::vm::Representation::TableLsb
        && ty.logical().spelling() == "table:bls12-381.fr"
}

/// Shared by proof-message production and transcript observation.
pub(crate) fn encode(
    value: &Value,
    policy: &Policy,
    key: &crate::SetupRegistry,
) -> Result<Vec<u8>, NativeWireError> {
    if bulk::format(&value.physical_type()).is_some() {
        return bulk::encode(value, policy);
    }
    if structured::tag(&value.physical_type()).is_some() {
        return structured::encode(value, policy, key);
    }
    if pcs::tag(&value.physical_type()).is_some() {
        pcs::encoded_width(value, key)?;
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
            .vector(array.len())
            .map_err(|_| NativeWireError::Limit)?;
    }
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(width)
        .map_err(|_| NativeWireError::Limit)?;
    bytes.extend_from_slice(super::MAGIC);
    bytes.push(tag);
    let encoding = |e| NativeWireError::Backend(crate::ark(e));
    if crate::fields::contains(value.physical_type().logical().identity()) {
        crate::fields::encode_scalar(value, &mut bytes).map_err(NativeWireError::Backend)?;
        return Ok(bytes);
    }

    match value {
        Value::FieldArray(array) => {
            array.validate().map_err(NativeWireError::Backend)?;
            if let Some(elements) = array.resident_elements() {
                let offset = bytes.len();
                bytes.resize(width, 0);
                elements
                    .write_bytes(&mut bytes[offset..])
                    .map_err(|e| NativeWireError::Backend(crate::operations::blst::failure(e)))?;
            } else {
                for element in array.ark_elements().ok_or_else(unsupported)? {
                    bytes.extend_from_slice(
                        &zkc_kernels::arkworks::bls12_381::encode_scalar(element)
                            .map_err(encoding)?,
                    );
                }
            }
        }
        Value::Index(v) => bytes.extend_from_slice(&v.to_le_bytes()),
        Value::Bool(v) => bytes.push(u8::from(*v)),
        Value::BlstField(v) => bytes.extend_from_slice(&v.to_bytes_le()),
        Value::HaloField(v) => bytes.extend_from_slice(&v.to_bytes_le()),
        Value::BlstG1(v) => bytes.extend_from_slice(&v.to_bytes()),
        Value::HaloG1(v) => bytes.extend_from_slice(&v.to_bytes()),
        Value::BlstG2(v) => bytes.extend_from_slice(&v.to_bytes()),
        Value::HaloG2(v) => bytes.extend_from_slice(&v.to_bytes()),
        Value::Field(v) => bytes.extend_from_slice(
            &zkc_kernels::arkworks::bls12_381::encode_scalar(v).map_err(encoding)?,
        ),
        Value::Curve(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bn254Field(v) => bytes
            .extend_from_slice(&zkc_kernels::arkworks::bn254::encode_scalar(v).map_err(encoding)?),
        Value::Bn254G1(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bn254Gt(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bn254G2(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bls12381G2(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Bls12381Gt(v) => bytes.extend_from_slice(&v.to_bytes().map_err(encoding)?),
        Value::Binary64Field(v) => {
            bytes.extend_from_slice(&zkc_kernels::plonky3::binary::encode(*v))
        }
        Value::Binary64Ext3Field(v) => {
            bytes.extend_from_slice(&zkc_kernels::plonky3::binary::encode_ext3(*v))
        }
        Value::RistrettoField(v) => bytes.extend_from_slice(&v.to_bytes()),
        Value::RistrettoGroup(v) => bytes.extend_from_slice(&v.compress().to_bytes()),
        Value::EdwardsGroup(v) => bytes.extend_from_slice(&v.to_bytes()),
        _ => return Err(unsupported()),
    }
    if bytes.len() != width {
        return Err(NativeWireError::Backend(BackendError::new(
            "native-wire-width",
        )));
    }
    Ok(bytes)
}
impl CpuBackend {
    /// Check supported immutable host data without encoding it. Backend policy,
    /// setup authorization and aggregate collection limits apply; wire buffers
    /// and decode-only temporary allocations are absent from this path.
    /// Native elements must satisfy their upstream library invariants; this
    /// method does not repair values created with unchecked scalar constructors.
    pub fn validate_native_input(&self, value: &Value) -> Result<(), NativeWireError> {
        let ty = value.physical_type();
        self.installation()
            .check_type(&ty)
            .map_err(NativeWireError::Backend)?;
        if matches!(ty.kind(), Type::ProverKey | Type::VerifierKey)
            || !ty.is_duplicable()
            || !has_native_wire(&ty)
        {
            return Err(unsupported());
        }
        if structured::tag(&ty).is_some() {
            structured::value_counts(value, self.policy())?;
        } else if bulk::format(&ty).is_some() {
            bulk::value_counts(value, self.policy())?;
        }
        zkc_runtime::vm::Backend::validate_value(self, value).map_err(NativeWireError::Backend)
    }
    /// Bound native input retention before expensive payload decoding. This
    /// uses byte lengths and, for recursive/bulk encodings, shape scans;
    /// complete-value collection limits also apply to the measured counts.
    /// Callers must still decode and check complete framing and values.
    pub fn native_input_retained_bytes(
        &self,
        ty: &PhysicalType,
        bytes: &[u8],
    ) -> Result<usize, NativeWireError> {
        Ok(self.measure_native_wire(ty, bytes)?.retained_bytes())
    }
    /// Raw Bytes transport borrows its payload without a tag, length prefix or
    /// deployment header. The transport checks its buffer limit before copying.
    pub fn encode_raw_bytes<'a>(&self, value: &'a Value) -> Result<&'a [u8], NativeWireError> {
        let Value::Bytes(bytes) = value else {
            return Err(unsupported());
        };
        self.policy()
            .bytes(bytes.len())
            .map_err(|_| NativeWireError::Limit)?;
        Ok(bytes)
    }
    /// The expected type comes from the admitted receive action.
    pub fn decode_raw_bytes(
        &self,
        ty: &PhysicalType,
        bytes: &[u8],
    ) -> Result<Value, NativeWireError> {
        self.installation()
            .check_type(ty)
            .map_err(NativeWireError::Backend)?;
        if ty.kind() != Type::Bytes
            || PhysicalType::default_for(ty.logical().clone())
                .ok()
                .as_ref()
                != Some(ty)
        {
            return Err(unsupported());
        }
        self.policy()
            .bytes(bytes.len())
            .map_err(|_| NativeWireError::Limit)?;
        Ok(Value::Bytes(bytes.into()))
    }
    pub fn encode_native_value(&self, value: &Value) -> Result<Vec<u8>, NativeWireError> {
        self.installation()
            .check_type(&value.physical_type())
            .map_err(NativeWireError::Backend)?;
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
        self.installation()
            .check_type(ty)
            .map_err(NativeWireError::Backend)?;
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
        let (tag, width) = fixed_header(ty, bytes)?;
        self.policy().wire(width).map_err(|_| Limit)?;
        if tag != 64 {
            // Installed fixed scalar/group wrappers retain 512 bytes, except the
            // 1024-byte BLS12-381 target. Reject insufficient capacity before
            // canonical/subgroup decoding; fixed arrays reserve their
            // shape-dependent backing below.
            let retained = if tag == 53 { 1024 } else { 512 };
            self.policy()
                .output(retained, usize::MAX)
                .map_err(|_| Limit)?;
        }
        if crate::operations::halo2curves::is_resident(ty) {
            use zkc_kernels::halo2curves::bn254 as kernel;
            return match tag {
                40 => kernel::decode_scalar(&bytes[6..])
                    .map(Value::HaloField)
                    .map_err(|_| Invalid(DecodeReason::Scalar)),
                46 => kernel::G1::from_bytes(&bytes[6..])
                    .map(Value::HaloG1)
                    .map_err(|_| Invalid(DecodeReason::Group)),
                48 => kernel::G2::from_bytes(&bytes[6..])
                    .map(|p| Value::HaloG2(std::sync::Arc::new(p)))
                    .map_err(|_| Invalid(DecodeReason::Group)),
                _ => Err(unsupported()),
            };
        }
        if crate::operations::blst::is_resident(ty) {
            use zkc_kernels::blst::bls12_381 as kernel;
            return match tag {
                1 => kernel::decode_scalar(&bytes[6..])
                    .map(Value::BlstField)
                    .map_err(|_| Invalid(DecodeReason::Scalar)),
                9 => kernel::G1::from_bytes(&bytes[6..])
                    .map(Value::BlstG1)
                    .map_err(|_| Invalid(DecodeReason::Group)),
                51 => kernel::G2::from_bytes(&bytes[6..])
                    .map(|p| Value::BlstG2(std::sync::Arc::new(p)))
                    .map_err(|_| Invalid(DecodeReason::Group)),
                _ => Err(unsupported()),
            };
        }
        if crate::fields::contains(ty.logical().identity()) {
            return crate::fields::decode_scalar(ty.logical().identity(), &bytes[6..])
                .map_err(|_| Invalid(DecodeReason::Scalar));
        }
        let value = match tag {
            64 => {
                let count = (width - 6) / 32;
                let retained = crate::field_array::bytes(count)
                    .map_err(|_| Limit)?
                    .checked_add(ty.descriptor_bytes())
                    .ok_or(Limit)?;
                // Vec-to-Arc conversion temporarily retains both scalar buffers.
                // Account for the peak before either allocation. Rust allocator
                // failure itself is outside the typed runtime failure contract.
                let peak = retained
                    .checked_add(count.checked_mul(32).ok_or(Limit)?)
                    .ok_or(Limit)?;
                self.policy().output(peak, usize::MAX).map_err(|_| Limit)?;
                self.policy().vector(count).map_err(|_| Limit)?;
                if ty.representation().name() == "blst/field-array" {
                    let elements =
                        zkc_kernels::blst::bls12_381::ScalarVector::from_bytes(&bytes[6..])
                            .map_err(|e| match e {
                                zkc_kernels::blst::bls12_381::Error::InvalidEncoding => {
                                    Invalid(DecodeReason::Scalar)
                                }
                                _ => NativeWireError::Backend(crate::operations::blst::failure(e)),
                            })?;
                    Value::FieldArray(
                        crate::FieldArray::from_resident(ty.clone(), std::sync::Arc::new(elements))
                            .map_err(NativeWireError::Backend)?,
                    )
                } else {
                    let mut elements = Vec::new();
                    elements.try_reserve_exact(count).map_err(|_| Limit)?;
                    for element in bytes[6..].as_chunks::<32>().0 {
                        elements.push(
                            zkc_kernels::arkworks::bls12_381::decode_scalar(element)
                                .map_err(|_| Invalid(DecodeReason::Scalar))?,
                        );
                    }
                    Value::FieldArray(
                        crate::FieldArray::new(ty.clone(), elements.into())
                            .map_err(NativeWireError::Backend)?,
                    )
                }
            }
            31 => Value::Index(u64::from_le_bytes(
                bytes[6..14].try_into().expect("checked index width"),
            )),
            5 => Value::Bool(super::decode_bool(&bytes[6..]).map_err(Invalid)?),
            // These checked helpers already normalize upstream decoding and
            // canonical re-encoding errors. No lost provenance is reconstructed.
            1 => Value::Field(
                zkc_kernels::arkworks::bls12_381::decode_scalar(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            9 => Value::Curve(
                crate::G1::from_bytes(&bytes[6..]).map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            50 => Value::Bn254Gt(
                crate::Bn254Gt::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            40 => Value::Bn254Field(
                zkc_kernels::arkworks::bn254::decode_scalar(&bytes[6..])
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
            51 => Value::Bls12381G2(
                crate::Bls12381G2::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            ),
            53 => Value::Bls12381Gt(std::sync::Arc::new(
                crate::Bls12381Gt::from_bytes(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Group))?,
            )),
            // Every bit pattern of the exact width is an element.
            73 => Value::Binary64Field(
                zkc_kernels::plonky3::binary::decode(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            76 => Value::Binary64Ext3Field(
                zkc_kernels::plonky3::binary::decode_ext3(&bytes[6..])
                    .map_err(|_| Invalid(DecodeReason::Scalar))?,
            ),
            13 => Value::RistrettoField(
                Option::from(crate::RistrettoScalar::from_canonical_bytes(
                    bytes[6..].try_into().expect("checked scalar width"),
                ))
                .ok_or(Invalid(DecodeReason::Scalar))?,
            ),
            68 => Value::EdwardsGroup(
                crate::EdwardsPrime::from_bytes(&bytes[6..]).ok_or(Invalid(DecodeReason::Group))?,
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

fn table_header(policy: &Policy, bytes: &[u8]) -> Result<(usize, usize), NativeWireError> {
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
    Ok((count, width))
}
fn decode_table(policy: &Policy, bytes: &[u8]) -> Result<Value, NativeWireError> {
    use NativeWireError::{Invalid, Limit};
    let (count, width) = table_header(policy, bytes)?;
    policy
        .output(width.checked_add(512).ok_or(Limit)?, usize::MAX)
        .map_err(|_| Limit)?;
    let mut values = Vec::new();
    values.try_reserve_exact(count).map_err(|_| Limit)?;
    for element in bytes[10..].as_chunks::<32>().0 {
        values.push(
            zkc_kernels::arkworks::bls12_381::decode_scalar(element)
                .map_err(|_| Invalid(DecodeReason::Scalar))?,
        );
    }
    let table =
        zkc_kernels::arkworks::bls12_381::Table::from_logical_vec(values, &policy.ark_bounds())
            .map_err(|e| NativeWireError::Backend(crate::ark(e)))?;
    let value = Value::Table(std::sync::Arc::new(table));
    policy
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| Limit)?;
    Ok(value)
}

#[cfg(test)]
mod tag_tests {
    use super::*;
    use zkc_runtime::vm::{Identity, LogicalType};

    /// The frame tag of every default physical type over the listed identities.
    fn tag(ty: &PhysicalType) -> Option<u8> {
        frame(ty)
            .map(|(tag, _)| tag)
            .or_else(|| bulk::format(ty).map(|(tag, _, _)| tag))
            .or_else(|| pcs::tag(ty))
            .or_else(|| structured::tag(ty))
            .or_else(|| table_type(ty).then_some(2))
    }

    #[test]
    fn binary_field_frame_tags_are_unique() {
        let identities = [
            "",
            "bn254.fr",
            "bn254.g1",
            "bn254.g2",
            "bn254.gt",
            "bls12-381.fr",
            "bls12-381.g1",
            "bls12-381.g2",
            "bls12-381.gt",
            "multilinear.kzg.bls12-381/0",
            "rows.merkle-keccak256.koala-bear/0",
            "rows.merkle-keccak256.koala-bear.ext8-binomial3/0",
            "rows.merkle-poseidon2-16.koala-bear/0",
            "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0",
            "merlin3.koala-bear.ext8-binomial3.rejection31le/0",
            "merlin3.bls12-381.fr64be/0",
            "merlin3.ristretto255.scalar64le/0",
            "spongefish0.8.0.keccak.bls12-381.fr64be/0",
            "hash-chain.keccak256.bls12-381.fr64be/0",
            "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0",
            "ristretto255.scalar",
            "ristretto255.group",
            "edwards25519.prime",
            "koala-bear",
            "koala-bear.ext8-binomial3",
            "koala-bear.ext4-binomial3",
            "gf2-64.pentanomial-4-3-1",
            "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
        ];
        let kinds = [
            "bool",
            "index",
            "indices",
            "bytes",
            "shake128_state",
            "field",
            "vector",
            "polynomial",
            "round",
            "matrix",
            "table",
            "point",
            "rng",
            "nonce",
            "group",
            "groups",
            "transcript",
            "commitment",
            "proof",
            "opening_state",
            "commitments",
            "opening_states",
            "prover_key",
            "verifier_key",
        ];
        let mut owners: std::collections::BTreeMap<u8, Vec<String>> = Default::default();
        for identity in identities {
            for kind in kinds {
                let spelling = if identity.is_empty() {
                    kind.to_string()
                } else {
                    format!("{kind}:{identity}")
                };
                let Ok(logical) = LogicalType::parse(&spelling) else {
                    continue;
                };
                let ty = PhysicalType::default_for(logical).unwrap();
                if let Some(tag) = tag(&ty) {
                    owners.entry(tag).or_default().push(spelling);
                }
            }
        }
        let expected = [
            (73, "field:gf2-64.pentanomial-4-3-1"),
            (74, "vector:gf2-64.pentanomial-4-3-1"),
            (75, "matrix:gf2-64.pentanomial-4-3-1"),
            (76, "field:gf2-64.pentanomial-4-3-1.ext3-trinomial1"),
            (77, "vector:gf2-64.pentanomial-4-3-1.ext3-trinomial1"),
            (78, "matrix:gf2-64.pentanomial-4-3-1.ext3-trinomial1"),
        ];
        for (tag, spelling) in expected {
            assert_eq!(owners[&tag], vec![spelling.to_string()], "tag {tag}");
        }
        // Appended after every earlier tag, so no earlier frame can collide.
        let earlier = owners.keys().copied().filter(|t| *t < 73).max();
        assert_eq!(earlier, Some(72));
        assert!(owners.keys().all(|t| *t <= 78));
        assert!(Identity::Binary64.bit_pattern_width().is_some());
    }
}
