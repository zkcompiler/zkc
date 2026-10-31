//! Checked active-only local values. Capability payloads are handles; packing
//! never issues authority and frame admission still authenticates every leaf.
use crate::{Result, VALUE_SLOT_BYTES, Value, refused};
use std::sync::Arc;
use zkc_runtime::vm::{Backing, PhysicalType, Value as RuntimeValue, VariantDescriptor};

#[derive(Clone, Debug)]
pub struct Variant {
    physical_type: PhysicalType,
    descriptor: Arc<VariantDescriptor>,
    alternative: usize,
    payload: Arc<[Value]>,
    /// Charge of the payload allocation: header, payload slots and
    /// storage the payload keeps inline. Payload allocations are separate.
    spine: usize,
    /// Expanded physical-profile charge, counting every active occurrence.
    /// Immutable payloads keep this bound available before recursive work.
    retained: usize,
    /// No active leaf carries a capability.
    resource_free: bool,
}
impl Variant {
    pub fn new(
        physical_type: PhysicalType,
        alternative: usize,
        payload: Vec<Value>,
    ) -> Result<Self> {
        if physical_type.representation() != zkc_runtime::vm::Representation::Variant {
            return Err(refused("variant-payload-representation"));
        }
        let logical = physical_type.logical();
        let descriptor = logical
            .variant_descriptor()
            .ok_or_else(|| refused("variant-type"))?
            .clone();
        let inline = payload.iter().try_fold(0usize, |sum, value| {
            sum.checked_add(value.retained_parts(&mut |_| false))
        });
        let spine = inline
            .and_then(|bytes| Self::payload_bytes(payload.len(), bytes))
            .unwrap_or(usize::MAX);
        let retained = payload
            .iter()
            .try_fold(0usize, |sum, value| sum.checked_add(value.retained_bytes()))
            .and_then(|bytes| Self::storage_bytes(&physical_type, payload.len(), bytes))
            .unwrap_or(usize::MAX);
        let resource_free = payload.iter().all(Value::is_resource_free);
        let value = Self {
            physical_type,
            descriptor,
            alternative,
            payload: payload.into(),
            spine,
            retained,
            resource_free,
        };
        value.validate()?;
        Ok(value)
    }
    /// Report the payload allocation and, when it is newly retained, the
    /// payload's own allocations.
    pub(crate) fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        if shared(self.spine()) {
            self.physical_type.visit_descriptor_backings(shared);
            for value in self.payload.iter() {
                value.retained_parts(shared);
            }
        }
        0
    }
    fn spine(&self) -> Backing {
        Backing::of(&self.payload, self.spine)
    }
    /// Contents fix validation only when no capability can be retired later.
    pub(crate) fn validation_backing(&self) -> Option<Backing> {
        self.resource_free.then(|| self.spine())
    }
    pub(crate) fn is_resource_free(&self) -> bool {
        self.resource_free
    }
    pub(crate) fn physical_type(&self) -> &PhysicalType {
        &self.physical_type
    }
    pub fn descriptor(&self) -> &Arc<VariantDescriptor> {
        &self.descriptor
    }
    pub fn alternative(&self) -> usize {
        self.alternative
    }
    pub fn payload(&self) -> &[Value] {
        &self.payload
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let arm = self
            .physical_type
            .variant_payload(self.alternative)
            .ok_or_else(|| refused("variant-alternative"))?;
        if self.payload.len() != arm.len()
            || self
                .payload
                .iter()
                .zip(arm)
                .any(|(v, t)| v.physical_type() != *t)
        {
            return Err(refused("variant-payload"));
        }
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> usize {
        // Stable physical-profile charge: descriptor, active storage, leaves.
        // Arc payload storage has exact length; no inactive value is allocated.
        const {
            assert!(std::mem::size_of::<Self>() <= 256);
        }
        self.retained
    }
    pub(crate) fn storage_bytes(
        physical_type: &PhysicalType,
        length: usize,
        payload_bytes: usize,
    ) -> Option<usize> {
        physical_type
            .descriptor_bytes()
            .checked_add(Self::payload_bytes(length, payload_bytes)?)
    }
    fn payload_bytes(length: usize, payload_bytes: usize) -> Option<usize> {
        256usize
            .checked_add(length.checked_mul(VALUE_SLOT_BYTES)?)?
            .checked_add(payload_bytes)
    }
}
