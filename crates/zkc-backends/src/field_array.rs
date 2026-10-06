//! Immutable BLS12-381 field arrays. The complete logical shape is retained.
use crate::{Policy, Result, Scalar, Value, exhausted, refused};
use std::sync::Arc;
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, Invocation, KernelSignature, LogicalType,
    OperationBinding, PhysicalType, Representation, Type,
};

#[derive(Clone, Debug)]
pub struct FieldArray {
    physical_type: PhysicalType,
    elements: Arc<[Scalar]>,
}
impl FieldArray {
    pub fn new(logical: LogicalType, elements: Arc<[Scalar]>) -> Result<Self> {
        let physical_type = PhysicalType::new(logical, Representation::FieldArray)
            .map_err(|_| refused("field-array-representation"))?;
        let value = Self {
            physical_type,
            elements,
        };
        value.validate()?;
        Ok(value)
    }
    pub fn physical_type(&self) -> &PhysicalType {
        &self.physical_type
    }
    pub fn elements(&self) -> &[Scalar] {
        &self.elements
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let (field, length) = self
            .physical_type
            .logical()
            .field_array_parts()
            .ok_or_else(|| refused("field-array-type"))?;
        if field != Identity::Bls12381Fr || self.elements.len() as u64 != length {
            return Err(refused("field-array-length"));
        }
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> Result<usize> {
        bytes(self.elements.len())
    }
}
pub(crate) fn bytes(length: usize) -> Result<usize> {
    crate::value::size(length, 32)?
        .checked_add(1024)
        .ok_or_else(|| exhausted("output-bytes"))
}

/// Independent advertisement. It does not call the runtime contract resolver.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, length] = binding.arguments.as_slice() else {
        return None;
    };
    if field != "bls12-381.fr" || binding.implementation != format!("arkworks/{}", binding.contract)
    {
        return None;
    }
    let length = zkc_runtime::logical::natural_index(length).ok()?;
    let scalar =
        PhysicalType::default_for(LogicalType::new(Type::Field, Identity::Bls12381Fr).ok()?)
            .ok()?;
    let vector =
        PhysicalType::default_for(LogicalType::new(Type::Vector, Identity::Bls12381Fr).ok()?)
            .ok()?;
    let array =
        PhysicalType::default_for(LogicalType::field_array(Identity::Bls12381Fr, length).ok()?)
            .ok()?;
    let (inputs, outputs, attributes) = match binding.contract.as_str() {
        "field_array.from_vector" => (vec![vector], vec![array], AttributeRule::None),
        "field_array.at" => (vec![array], vec![scalar], AttributeRule::Unsigned64),
        _ => return None,
    };
    Some(KernelSignature {
        inputs,
        outputs,
        attributes,
    })
}
pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let value = match (name, args) {
        ("field_array.from_vector", [Value::Vector(elements)]) => {
            policy.output(bytes(elements.len())?, invocation.max_output_bytes)?;
            Value::FieldArray(FieldArray::new(
                invocation.binding.signature().outputs[0].logical(),
                elements.clone(),
            )?)
        }
        ("field_array.at", [Value::FieldArray(array)]) => {
            array.validate()?;
            let [index] = invocation.attributes else {
                return Err(refused("field-array-index"));
            };
            let index = zkc_runtime::logical::natural_index(index)
                .map_err(|_| refused("field-array-index"))?;
            let index = usize::try_from(index).map_err(|_| refused("field-array-index"))?;
            policy.output(512, invocation.max_output_bytes)?;
            Value::Field(
                *array
                    .elements()
                    .get(index)
                    .ok_or_else(|| refused("field-array-index"))?,
            )
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![value])
}
pub(crate) const OPERATIONS: &[&str] = &["field_array.from_vector", "field_array.at"];
