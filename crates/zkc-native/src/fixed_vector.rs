//! Local immutable dense vectors with complete selected element layouts.
use crate::{KoalaBear, Policy, Result, Value, exhausted, refused};
use std::sync::Arc;
use zkc_runtime::vm::{
    AttributeRule, Backing, BoundSignature, Identity, Invocation, LogicalType, OperationBinding,
    OperationSignature, PhysicalType, Representation, Type,
};

#[derive(Clone, Debug)]
pub struct FixedVector {
    physical_type: PhysicalType,
    storage: Storage,
}
#[derive(Clone, Debug)]
enum Storage {
    KoalaBear(Arc<[KoalaBear]>),
    Blst(Arc<zkc_kernels::blst::bls12_381::ScalarVector>),
}
impl FixedVector {
    /// Admission and exact length precede construction. There is no wire codec.
    pub fn new(physical_type: PhysicalType, elements: Arc<[KoalaBear]>) -> Result<Self> {
        let value = Self {
            physical_type,
            storage: Storage::KoalaBear(elements),
        };
        value.validate()?;
        Ok(value)
    }
    pub fn from_resident(
        physical_type: PhysicalType,
        elements: Arc<zkc_kernels::blst::bls12_381::ScalarVector>,
    ) -> Result<Self> {
        let value = Self {
            physical_type,
            storage: Storage::Blst(elements),
        };
        value.validate()?;
        Ok(value)
    }
    pub fn physical_type(&self) -> &PhysicalType {
        &self.physical_type
    }
    pub fn len(&self) -> usize {
        match &self.storage {
            Storage::KoalaBear(v) => v.len(),
            Storage::Blst(v) => v.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn element_width(&self) -> usize {
        match self.storage {
            Storage::KoalaBear(_) => 4,
            Storage::Blst(_) => 32,
        }
    }
    pub fn koala_bear_elements(&self) -> Option<&[KoalaBear]> {
        match &self.storage {
            Storage::KoalaBear(v) => Some(v),
            _ => None,
        }
    }
    pub fn resident_elements(&self) -> Option<&Arc<zkc_kernels::blst::bls12_381::ScalarVector>> {
        match &self.storage {
            Storage::Blst(v) => Some(v),
            _ => None,
        }
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let logical = self.physical_type.logical();
        let (element, length) = logical
            .fixed_vector_parts()
            .ok_or_else(|| refused("fixed-vector-type"))?;
        if self.len() as u64 != length {
            return Err(refused("fixed-vector-length"));
        }
        let (expected, storage) = match self.storage {
            Storage::KoalaBear(_) => (
                crate::domains::KOALA_BEAR.physical(Type::Field),
                "plonky3.fixed-vector/0",
            ),
            Storage::Blst(_) => (
                crate::operations::blst::physical(Type::Field, Identity::Bls12381Fr),
                "blst/fixed-vector",
            ),
        };
        if expected.as_ref() != self.physical_type.fixed_vector_element()
            || expected.as_ref().map(PhysicalType::logical).as_ref() != Some(element)
            || self.physical_type.representation().name() != storage
            || matches!(self.storage, Storage::Blst(_))
                && Some(self.physical_type.representation())
                    != crate::contracts::dense_representation(Type::FixedVector)
        {
            return Err(refused("fixed-vector-representation"));
        }
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> Result<usize> {
        self.owned_bytes()
            .checked_add(self.backing()?.bytes())
            .ok_or_else(|| exhausted("output-bytes"))
    }
    pub(crate) fn owned_bytes(&self) -> usize {
        DESCRIPTOR_BYTES.saturating_add(self.physical_type.descriptor_bytes())
    }
    pub(crate) fn backing(&self) -> Result<Backing> {
        Ok(match &self.storage {
            Storage::KoalaBear(v) => Backing::of(v, crate::value::size(v.len(), 4)?),
            Storage::Blst(v) => Backing::of(
                v,
                v.storage_bytes()
                    .checked_add(256)
                    .ok_or_else(|| exhausted("output-bytes"))?,
            ),
        })
    }
}

const DESCRIPTOR_BYTES: usize = 1024;
pub(crate) fn supports_type(ty: &PhysicalType) -> bool {
    let logical = ty.logical();
    let Some((element, length)) = logical.fixed_vector_parts() else {
        return false;
    };
    if length > 1_048_576 {
        return false;
    }
    let expected = match ty.representation() {
        Representation::FixedVector => crate::domains::KOALA_BEAR.physical(Type::Field),
        representation
            if Some(representation)
                == crate::contracts::dense_representation(Type::FixedVector) =>
        {
            crate::operations::blst::physical(Type::Field, Identity::Bls12381Fr)
        }
        _ => None,
    };
    expected
        .as_ref()
        .is_some_and(|scalar| scalar.logical() == *element)
        && expected.as_ref() == ty.fixed_vector_element()
}
/// Independent native advertisement; never call the runtime operation resolver.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, length] = binding.arguments.as_slice() else {
        return None;
    };
    let length = zkc_runtime::logical::natural_index(length).ok()?;
    let fixed = match binding.physical_arguments.as_slice() {
        [] => PhysicalType::default_for(
            LogicalType::fixed_vector(LogicalType::parse(&format!("field:{field}")).ok()?, length)
                .ok()?,
        )
        .ok()?,
        [selected] => crate::native_contracts().physical_type(selected).ok()?,
        _ => return None,
    };
    let (scalar, vector) = if field == "koala-bear"
        && binding.implementation == format!("plonky3/{}", binding.contract)
    {
        if fixed.representation() != Representation::FixedVector {
            return None;
        }
        (
            crate::domains::KOALA_BEAR.physical(Type::Field)?,
            crate::domains::KOALA_BEAR.physical(Type::Vector)?,
        )
    } else if field == "bls12-381.fr"
        && binding.implementation == format!("blst/resident/{}", binding.contract)
    {
        if fixed.representation().name() != "blst/fixed-vector" {
            return None;
        }
        (
            crate::operations::blst::physical(Type::Field, Identity::Bls12381Fr)?,
            crate::operations::blst::physical(Type::Vector, Identity::Bls12381Fr)?,
        )
    } else {
        return None;
    };
    if fixed.logical() != LogicalType::fixed_vector(scalar.logical(), length).ok()?
        || fixed.fixed_vector_element() != Some(&scalar)
    {
        return None;
    }
    let (inputs, outputs) = match binding.contract.as_str() {
        "fixed_vector.from_vector" => (vec![vector], vec![fixed]),
        "fixed_vector.to_vector" => (vec![fixed], vec![vector]),
        "fixed_vector.dot" => (vec![fixed.clone(), fixed], vec![scalar]),
        _ => return None,
    };
    Some(OperationSignature {
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
            let ty = invocation.binding.signature().outputs[0].clone();
            let owned = DESCRIPTOR_BYTES.saturating_add(ty.descriptor_bytes());
            policy.output(
                crate::value::size(elements.len(), 4)?.saturating_add(owned),
                usize::MAX,
            )?;
            policy.output(owned, invocation.max_output_bytes)?;
            Value::FixedVector(FixedVector::new(ty, elements.clone())?)
        }
        ("fixed_vector.from_vector", [Value::BlstVector(elements)]) => {
            let ty = invocation.binding.signature().outputs[0].clone();
            let owned = DESCRIPTOR_BYTES.saturating_add(ty.descriptor_bytes());
            policy.output(
                elements
                    .storage_bytes()
                    .saturating_add(256)
                    .saturating_add(owned),
                usize::MAX,
            )?;
            policy.output(owned, invocation.max_output_bytes)?;
            Value::FixedVector(FixedVector::from_resident(ty, elements.clone())?)
        }
        ("fixed_vector.to_vector", [Value::FixedVector(value)]) => {
            value.validate()?;
            match &value.storage {
                Storage::KoalaBear(v) => Value::KoalaBearVector(v.clone()),
                Storage::Blst(v) => Value::BlstVector(v.clone()),
            }
        }
        ("fixed_vector.dot", [Value::FixedVector(a), Value::FixedVector(b)]) => {
            a.validate()?;
            b.validate()?;
            if a.physical_type != b.physical_type {
                return Err(refused("fixed-vector-type"));
            }
            policy.output(512, invocation.max_output_bytes)?;
            let call = crate::numerical::Call::new(policy, invocation.max_output_bytes);
            match (&a.storage, &b.storage) {
                (Storage::KoalaBear(a), Storage::KoalaBear(b)) => {
                    crate::operations::arithmetic::dot(a, b, &call)?
                }
                (Storage::Blst(a), Storage::Blst(b)) => {
                    crate::operations::arithmetic::dot(a.as_elements(), b.as_elements(), &call)?
                }
                _ => return Err(refused("fixed-vector-type")),
            }
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![value])
}

pub(crate) const RESIDENT_IMPLEMENTATIONS: &[(&str, &str)] = &[
    (
        "blst/resident/fixed_vector.from_vector",
        "fixed_vector.from_vector",
    ),
    (
        "blst/resident/fixed_vector.to_vector",
        "fixed_vector.to_vector",
    ),
    ("blst/resident/fixed_vector.dot", "fixed_vector.dot"),
];
pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    (
        "plonky3/fixed_vector.from_vector",
        "fixed_vector.from_vector",
    ),
    ("plonky3/fixed_vector.to_vector", "fixed_vector.to_vector"),
    ("plonky3/fixed_vector.dot", "fixed_vector.dot"),
];
