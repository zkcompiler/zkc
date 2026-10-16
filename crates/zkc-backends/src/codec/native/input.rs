//! Whole-value admission for immutable native data. Counts share the native
//! codec; callers reserve invocation-wide retention before loading.
use super::{NativeWireError as Error, structured, unsupported};
use crate::{NativeBackend, Value, Variant};
use zkc_runtime::vm::{PhysicalType, Value as RuntimeValue};

type Result<T> = std::result::Result<T, Error>;

/// Opaque physical-profile measurements, not authority to construct a value.
#[derive(Debug)]
pub struct NativeInputSize {
    ty: PhysicalType,
    retained: usize,
    wire: usize,
    counts: structured::Counts,
}
impl NativeInputSize {
    pub fn retained_bytes(&self) -> usize {
        self.retained
    }
}
impl NativeBackend {
    /// Measure the shape of recursive native data without an encoded frame.
    /// Complete backend/setup validation remains the loader's obligation.
    pub fn measure_native_input(&self, value: &Value) -> Result<NativeInputSize> {
        let ty = value.physical_type();
        if !ty.is_duplicable() || !super::has_native_wire(&ty) {
            return Err(unsupported());
        }
        self.policy()
            .output(value.retained_bytes(), usize::MAX)
            .map_err(|_| Error::Limit)?;
        Ok(NativeInputSize {
            ty,
            retained: value.retained_bytes(),
            wire: 0,
            counts: structured::value_counts(value, self.policy())?,
        })
    }
    /// Measure one native frame without decoding its cryptographic elements.
    /// Fixed leaves and tables use length bounds; recursive and bulk frames
    /// require shape scans. Complete framing and value checks remain with loading.
    pub fn measure_native_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<NativeInputSize> {
        let mut counts = structured::Counts::default();
        let retained = if super::table_type(ty)
            || super::frame(ty).is_some() && !ty.has_native_array_frame()
        {
            // Match the ordinary leaf decoder's retention contract. Recursive
            // framing may need a more conservative estimate for nested leaves.
            counts.nodes = 1;
            let (elements, groups) = if super::table_type(ty) {
                // This profile is BLS12-381 Fr: 32-byte elements after a
                // 10-byte header, so division bounds the decoded element count.
                (bytes.len() / 32, 0)
            } else {
                structured::fixed_counts(ty, super::frame(ty).unwrap().1)
            };
            counts.add(elements, groups)?;
            Value::typed_wire_retained_bytes_bound(ty.clone(), bytes.len(), self.policy())
                .map_err(|_| Error::Limit)?
        } else {
            let retained = structured::scan(ty, bytes, self.policy(), self.setups(), &mut counts)?;
            structured::peak(self.policy(), retained, bytes.len())?;
            retained
        };
        counts.admit(self.policy())?;
        Ok(NativeInputSize {
            ty: ty.clone(),
            retained,
            wire: bytes.len(),
            counts,
        })
    }
    /// Check a complete active arm before assembling any of its payload values.
    /// Inactive arms allocate no values, but the complete descriptor is charged.
    pub fn measure_native_variant(
        &self,
        ty: &PhysicalType,
        alternative: usize,
        payload: &[NativeInputSize],
    ) -> Result<NativeInputSize> {
        if structured::tag(ty) != Some(65) || !ty.is_duplicable() {
            return Err(unsupported());
        }
        let logical = ty.logical();
        let descriptor = logical.variant_descriptor().ok_or_else(unsupported)?;
        let arm = descriptor
            .alternatives()
            .get(alternative)
            .ok_or_else(unsupported)?;
        if arm.payload().len() != payload.len() {
            return Err(unsupported());
        }
        let mut counts = structured::Counts {
            nodes: 1,
            ..Default::default()
        };
        let mut bytes = 0;
        let mut wire = 0;
        for (expected, child) in arm.payload().iter().zip(payload) {
            if PhysicalType::default_for(expected.clone()).ok().as_ref() != Some(&child.ty) {
                return Err(unsupported());
            }
            counts.nodes = structured::add(counts.nodes, child.counts.nodes)?;
            counts.add(child.counts.elements, child.counts.groups)?;
            counts.admit(self.policy())?;
            bytes = structured::add(bytes, child.retained)?;
            wire = structured::add(wire, child.wire)?;
        }
        counts.admit(self.policy())?;
        let retained =
            Variant::storage_bytes(descriptor, payload.len(), bytes).ok_or(Error::Limit)?;
        // Retained siblings coexist with wire/decode buffers. Native-only
        // requests need only the Vec-to-Arc construction peak.
        structured::peak(self.policy(), retained, wire)?;
        Ok(NativeInputSize {
            ty: ty.clone(),
            retained,
            wire,
            counts,
        })
    }
}
