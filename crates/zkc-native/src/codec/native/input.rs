//! Whole-value admission for immutable native data. Counts share the native
//! codec; callers reserve invocation-wide retention before loading.
use super::{NativeWireError as Error, structured, unsupported};
use crate::{NativeBackend, Value, Variant};
use zkc_runtime::vm::{PhysicalType, Value as RuntimeValue};

type Result<T> = std::result::Result<T, Error>;

fn admitted_type(ty: &PhysicalType) -> bool {
    crate::native_contracts()
        .physical_type(&ty.spelling())
        .is_ok_and(|admitted| admitted == *ty)
}

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
        self.measure_native_value(value)
    }
    /// Measure immutable runtime-owned data, including internal mathematical
    /// values without wire codecs. This grants neither ingress nor setup or
    /// constructor authority; the owning backend must already validate values.
    /// Counts retain owner collection units, including opaque handle counts.
    /// Callers must charge repeated walks before measurement, using the value's
    /// conservative retained-byte bound without recursively scanning it first.
    pub fn measure_native_value(&self, value: &Value) -> Result<NativeInputSize> {
        let ty = value.physical_type();
        if !ty.is_duplicable() || !value.is_resource_free() || !admitted_type(&ty) {
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
    /// require shape scans. Preserve each decoder's framing/setup checks before
    /// its policy checks. Canonical element and value checks remain with loading.
    pub fn measure_native_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<NativeInputSize> {
        if !super::has_native_wire(ty) {
            return Err(unsupported());
        }
        if super::frame(ty).is_some() {
            super::fixed_header(ty, bytes)?;
        } else if super::table_type(ty) {
            let (_, width) = super::table_header(self.policy(), bytes)?;
            // Match the table decoder's allocation allowance after framing.
            self.policy()
                .output(width.checked_add(512).ok_or(Error::Limit)?, usize::MAX)
                .map_err(|_| Error::Limit)?;
        } else if let Some(tag) = super::pcs::tag(ty) {
            super::pcs::preflight(self.setups(), tag, bytes)?;
        }
        let mut counts = structured::Counts::default();
        let fixed_leaf =
            super::frame(ty).is_some() && ty.kind() != zkc_runtime::vm::Type::FieldArray;
        let retained = if super::table_type(ty) || fixed_leaf {
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
        } else if super::bulk::format(ty).is_some() {
            // Root bulk decoders scan framing before whole-value counts. A
            // recursive wrapper's earlier node allowance must not mask that.
            let (retained, elements, groups) = super::bulk::scan(ty, bytes, self.policy())?;
            counts.nodes = 1;
            counts.add(elements, groups)?;
            structured::peak(self.policy(), retained, bytes.len())?;
            retained
        } else {
            let retained = structured::scan(ty, bytes, self.policy(), self.setups(), &mut counts)?;
            structured::peak(self.policy(), retained, bytes.len())?;
            counts.admit(self.policy())?;
            retained
        };
        // Standalone leaves, tables and bulk collections follow their own
        // decoder limits. Keep their counts for later aggregate construction,
        // without imposing recursive node or unrelated collection ceilings here.
        Ok(NativeInputSize {
            ty: ty.clone(),
            retained,
            wire: bytes.len(),
            counts,
        })
    }
    /// Check a complete active arm before assembling any of its payload values.
    /// Inactive arms allocate no values, but the complete descriptor is charged.
    /// Internal data need no wire codec; complete type and resource restrictions
    /// still apply. This measurement does not authorize external construction.
    pub fn measure_native_variant(
        &self,
        ty: &PhysicalType,
        alternative: usize,
        payload: &[NativeInputSize],
    ) -> Result<NativeInputSize> {
        if ty.kind() != zkc_runtime::vm::Type::Variant
            || ty.representation() != zkc_runtime::vm::Representation::Variant
            || !ty.is_duplicable()
            || !admitted_type(ty)
        {
            return Err(unsupported());
        }
        let arm = ty.variant_payload(alternative).ok_or_else(unsupported)?;
        if arm.len() != payload.len() {
            return Err(unsupported());
        }
        let mut counts = structured::Counts {
            nodes: 1,
            ..Default::default()
        };
        let mut bytes = 0;
        let mut wire = 0;
        for (expected, child) in arm.iter().zip(payload) {
            if *expected != child.ty {
                return Err(unsupported());
            }
            counts.nodes = structured::add(counts.nodes, child.counts.nodes)?;
            counts.add(child.counts.elements, child.counts.groups)?;
            counts.admit(self.policy())?;
            bytes = structured::add(bytes, child.retained)?;
            wire = structured::add(wire, child.wire)?;
        }
        counts.admit(self.policy())?;
        let retained = Variant::storage_bytes(ty, payload.len(), bytes).ok_or(Error::Limit)?;
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
