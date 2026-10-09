//! Private immutable KoalaBear bulk values with a retained logical length.
use crate::{KoalaBear, Policy, Result, Value, exhausted, refused};
use std::sync::Arc;
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, Invocation, KernelSignature, LogicalType,
    OperationBinding, PhysicalType, Representation, Type,
};

#[derive(Clone, Debug)]
pub struct FixedVector {
    physical_type: PhysicalType,
    elements: Arc<[KoalaBear]>,
}
impl FixedVector {
    /// Admission and exact length precede construction. There is no wire codec.
    pub fn new(logical: LogicalType, elements: Arc<[KoalaBear]>) -> Result<Self> {
        let physical_type = PhysicalType::new(logical, Representation::FixedVector)
            .map_err(|_| refused("fixed-vector-representation"))?;
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
    pub fn elements(&self) -> &[KoalaBear] {
        &self.elements
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let logical = self.physical_type.logical();
        let (_, length) = logical
            .fixed_vector_parts()
            .ok_or_else(|| refused("fixed-vector-type"))?;
        if self.elements.len() as u64 != length {
            return Err(refused("fixed-vector-length"));
        }
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> Result<usize> {
        // Includes the small, fixed-shape field/N descriptor and shared storage.
        bytes(self.elements.len())
    }
}

fn bytes(length: usize) -> Result<usize> {
    crate::value::size(length, 4)?
        .checked_add(1024)
        .ok_or_else(|| exhausted("output-bytes"))
}

/// Independent native advertisement; never call the runtime operation resolver.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, length] = binding.arguments.as_slice() else {
        return None;
    };
    if field != "koala-bear" || binding.implementation != format!("plonky3/{}", binding.contract) {
        return None;
    }
    let length = zkc_runtime::logical::natural_index(length).ok()?;
    if length > 1_048_576 {
        return None;
    }
    let scalar = crate::domains::KOALA_BEAR.physical(Type::Field)?;
    let vector = crate::domains::KOALA_BEAR.physical(Type::Vector)?;
    let fixed = PhysicalType::new(
        LogicalType::fixed_vector(
            LogicalType::new(Type::Field, Identity::KoalaBear).ok()?,
            length,
        )
        .ok()?,
        Representation::FixedVector,
    )
    .ok()?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "fixed_vector.from_vector" => (vec![vector], vec![fixed]),
        "fixed_vector.to_vector" => (vec![fixed], vec![vector]),
        "fixed_vector.dot" => (vec![fixed.clone(), fixed], vec![scalar]),
        _ => return None,
    };
    Some(KernelSignature {
        inputs,
        outputs,
        attributes: AttributeRule::None,
    })
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let value = match (name, args) {
        ("fixed_vector.from_vector", [Value::KoalaBearVector(elements)]) => {
            policy.output(bytes(elements.len())?, invocation.max_output_bytes)?;
            Value::FixedVector(FixedVector::new(
                invocation.binding.signature().outputs[0].logical(),
                elements.clone(),
            )?)
        }
        ("fixed_vector.to_vector", [Value::FixedVector(value)]) => {
            value.validate()?;
            policy.output(
                crate::value::size(value.elements.len(), 4)?,
                invocation.max_output_bytes,
            )?;
            Value::KoalaBearVector(value.elements.clone())
        }
        ("fixed_vector.dot", [Value::FixedVector(a), Value::FixedVector(b)]) => {
            a.validate()?;
            b.validate()?;
            if a.physical_type != b.physical_type {
                return Err(refused("fixed-vector-type"));
            }
            policy.output(512, invocation.max_output_bytes)?;
            // Existing backend field operations own arithmetic and reduction.
            Value::KoalaBearField(crate::plonky3::dot(a.elements(), b.elements())?)
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![value])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    (
        "plonky3/fixed_vector.from_vector",
        "fixed_vector.from_vector",
    ),
    ("plonky3/fixed_vector.to_vector", "fixed_vector.to_vector"),
    ("plonky3/fixed_vector.dot", "fixed_vector.dot"),
];
