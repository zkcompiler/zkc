//! Checked active-only local values. Capability payloads are handles; packing
//! never issues authority and frame admission still authenticates every leaf.
use crate::{Result, Value, refused};
use std::sync::Arc;
use zkc_runtime::interactive::{PhysicalType, Value as RuntimeValue, VariantDescriptor};

#[derive(Clone, Debug)]
pub struct Variant {
    physical_type: PhysicalType,
    descriptor: Arc<VariantDescriptor>,
    alternative: usize,
    payload: Arc<[Value]>,
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
        let value = Self {
            physical_type,
            descriptor,
            alternative,
            payload: payload.into(),
        };
        value.validate()?;
        Ok(value)
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
        let bytes = (|| {
            let mut bytes = self.descriptor.retained_bytes().checked_add(256)?;
            bytes = bytes.checked_add(self.payload.len().checked_mul(512)?)?;
            for value in self.payload.iter() {
                bytes = bytes.checked_add(value.retained_bytes())?;
            }
            Some(bytes)
        })();
        bytes.unwrap_or(usize::MAX)
    }
}
