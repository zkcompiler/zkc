//! Whole-value admission for host-assembled immutable sums. Counts share the
//! native wire scanner; callers reserve invocation-wide retention before loading.
use super::{NativeWireError as Error, structured, unsupported};
use crate::{NativeBackend, Value, Variant};
use zkc_runtime::interactive::{PhysicalType, Value as RuntimeValue};

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
            ty: value.physical_type(),
            retained: value.retained_bytes(),
            wire: 0,
            counts: structured::value_counts(value, self.policy())?,
        })
    }
    /// Scan one payload frame without decoding its cryptographic elements.
    pub fn measure_native_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<NativeInputSize> {
        let mut counts = structured::Counts::default();
        let retained = structured::scan(ty, bytes, self.policy(), self.setups(), &mut counts)?;
        counts.admit(self.policy())?;
        structured::peak(self.policy(), retained, bytes.len())?;
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
