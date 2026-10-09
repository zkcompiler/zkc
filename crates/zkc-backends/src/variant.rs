//! Checked active-only local values. Capability payloads are handles; packing
//! never issues authority and frame admission still authenticates every leaf.
use crate::{Result, Value, refused};
use std::sync::Arc;
use zkc_runtime::interactive::{Backing, PhysicalType, Value as RuntimeValue, VariantDescriptor};

#[derive(Clone, Debug)]
pub struct Variant {
    physical_type: PhysicalType,
    descriptor: Arc<VariantDescriptor>,
    alternative: usize,
    payload: Arc<[Value]>,
    /// Charge of the payload allocation: descriptor, header, payload slots and
    /// storage the payload keeps inline. Payload allocations are separate.
    spine: usize,
    /// No active leaf carries a capability.
    resource_free: bool,
}
impl Variant {
    pub fn new(
        descriptor: Arc<VariantDescriptor>,
        alternative: usize,
        payload: Vec<Value>,
    ) -> Result<Self> {
        let physical_type = PhysicalType::default_for(
            zkc_runtime::interactive::LogicalType::variant(descriptor.clone()),
        )
        .map_err(|_| refused("variant-payload-representation"))?;
        let inline = payload.iter().try_fold(0usize, |sum, value| {
            sum.checked_add(value.retained_parts(&mut |_| false))
        });
        let spine = inline
            .and_then(|bytes| Self::storage_bytes(&descriptor, payload.len(), bytes))
            .unwrap_or(usize::MAX);
        let resource_free = payload.iter().all(Value::is_resource_free);
        let value = Self {
            physical_type,
            descriptor,
            alternative,
            payload: payload.into(),
            spine,
            resource_free,
        };
        value.validate()?;
        Ok(value)
    }
    /// Report the payload allocation and, when it is newly retained, the
    /// payload's own allocations.
    pub(crate) fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        if shared(self.spine()) {
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
            .descriptor
            .alternatives()
            .get(self.alternative)
            .ok_or_else(|| refused("variant-alternative"))?;
        if self.payload.len() != arm.payload().len()
            || self.payload.iter().zip(arm.payload()).any(|(v, t)| {
                !PhysicalType::default_for(t.clone()).is_ok_and(|ty| v.physical_type() == ty)
            })
        {
            return Err(refused("variant-payload"));
        }
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> usize {
        // Stable physical-profile charge: descriptor, active storage, leaves.
        // Arc payload storage has exact length; no inactive value is allocated.
        const {
            assert!(std::mem::size_of::<Value>() <= 512);
        }
        const {
            assert!(std::mem::size_of::<Self>() <= 256);
        }
        let payload = self
            .payload
            .iter()
            .try_fold(0usize, |sum, value| sum.checked_add(value.retained_bytes()));
        payload
            .and_then(|bytes| Self::storage_bytes(&self.descriptor, self.payload.len(), bytes))
            .unwrap_or(usize::MAX)
    }
    pub(crate) fn storage_bytes(
        descriptor: &VariantDescriptor,
        length: usize,
        payload_bytes: usize,
    ) -> Option<usize> {
        descriptor
            .retained_bytes()
            .checked_add(256)?
            .checked_add(length.checked_mul(512)?)?
            .checked_add(payload_bytes)
    }
}
