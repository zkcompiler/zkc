//! Immutable BLS12-381 field arrays with complete selected element layouts.
use crate::{Policy, Result, Scalar, Value, exhausted, refused};
use std::sync::Arc;
use zkc_runtime::vm::{
    AttributeRule, Backing, BoundSignature, Identity, Invocation, LogicalType, OperationBinding,
    OperationSignature, PhysicalType, Representation, Type,
};

#[derive(Clone, Debug)]
pub struct FieldArray {
    physical_type: PhysicalType,
    storage: Storage,
}
#[derive(Clone, Debug)]
enum Storage {
    Ark(Arc<[Scalar]>),
    Blst(Arc<zkc_kernels::blst::bls12_381::ScalarVector>),
}
impl FieldArray {
    pub fn new(physical_type: PhysicalType, elements: Arc<[Scalar]>) -> Result<Self> {
        let value = Self {
            physical_type,
            storage: Storage::Ark(elements),
        };
        value.validate()?;
        Ok(value)
    }
    /// Share an existing typed resident carrier after checking its exact extent.
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
            Storage::Ark(v) => v.len(),
            Storage::Blst(v) => v.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn ark_elements(&self) -> Option<&[Scalar]> {
        match &self.storage {
            Storage::Ark(v) => Some(v),
            _ => None,
        }
    }
    pub fn resident_elements(&self) -> Option<&Arc<zkc_kernels::blst::bls12_381::ScalarVector>> {
        match &self.storage {
            Storage::Blst(v) => Some(v),
            _ => None,
        }
    }
    pub(crate) fn get(&self, index: usize) -> Option<Value> {
        match &self.storage {
            Storage::Ark(v) => v.get(index).copied().map(Value::Field),
            Storage::Blst(v) => v.get(index).map(Value::BlstField),
        }
    }
    pub(crate) fn validate(&self) -> Result<()> {
        let (field, length) = self
            .physical_type
            .logical()
            .field_array_parts()
            .ok_or_else(|| refused("field-array-type"))?;
        if field != Identity::Bls12381Fr || self.len() as u64 != length {
            return Err(refused("field-array-length"));
        }
        let expected = match self.storage {
            Storage::Ark(_) => PhysicalType::default_for(
                LogicalType::new(Type::Field, field).map_err(|_| refused("field-array-type"))?,
            )
            .ok(),
            Storage::Blst(_) => crate::operations::blst::physical(Type::Field, field),
        };
        let storage = match self.storage {
            Storage::Ark(_) => "arkworks.field-array/0",
            Storage::Blst(_) => "blst/field-array",
        };
        if expected.as_ref() != self.physical_type.field_array_element()
            || self.physical_type.representation().name() != storage
            || matches!(self.storage, Storage::Blst(_))
                && Some(self.physical_type.representation())
                    != crate::contracts::dense_representation(Type::FieldArray)
        {
            return Err(refused("field-array-representation"));
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
    /// The identity and charge match the dynamic vector's shared carrier.
    pub(crate) fn backing(&self) -> Result<Backing> {
        Ok(match &self.storage {
            Storage::Ark(v) => Backing::of(v, crate::value::size(v.len(), 32)?),
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
pub(crate) fn bytes(length: usize) -> Result<usize> {
    crate::value::size(length, 32)?
        .checked_add(DESCRIPTOR_BYTES)
        .ok_or_else(|| exhausted("output-bytes"))
}

/// Exact storage/child pairing supported by the local typed carrier and frame.
pub(crate) fn supports_type(ty: &PhysicalType) -> bool {
    if !matches!(
        ty.logical().field_array_parts(),
        Some((Identity::Bls12381Fr, 0..=1_048_576))
    ) {
        return false;
    }
    let expected = match ty.representation() {
        Representation::FieldArray => PhysicalType::default_for(
            LogicalType::new(Type::Field, Identity::Bls12381Fr).expect("native scalar"),
        )
        .ok(),
        _ if Some(ty.representation())
            == crate::contracts::dense_representation(Type::FieldArray) =>
        {
            crate::operations::blst::physical(Type::Field, Identity::Bls12381Fr)
        }
        _ => None,
    };
    expected.is_some() && expected.as_ref() == ty.field_array_element()
}

/// Independent advertisement. It does not call the runtime contract resolver.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, length] = binding.arguments.as_slice() else {
        return None;
    };
    if field != "bls12-381.fr" {
        return None;
    }
    let length = zkc_runtime::logical::natural_index(length).ok()?;
    let array = match binding.physical_arguments.as_slice() {
        [] => {
            PhysicalType::default_for(LogicalType::field_array(Identity::Bls12381Fr, length).ok()?)
                .ok()?
        }
        [selected] => crate::native_contracts().physical_type(selected).ok()?,
        _ => return None,
    };
    if array.logical() != LogicalType::field_array(Identity::Bls12381Fr, length).ok()? {
        return None;
    }
    let scalar = array.field_array_element()?.clone();
    let vector = if binding.implementation == format!("arkworks/{}", binding.contract) {
        if array.representation() != Representation::FieldArray
            || scalar
                != PhysicalType::default_for(
                    LogicalType::new(Type::Field, Identity::Bls12381Fr).ok()?,
                )
                .ok()?
        {
            return None;
        }
        PhysicalType::default_for(LogicalType::new(Type::Vector, Identity::Bls12381Fr).ok()?)
            .ok()?
    } else if binding.implementation == format!("blst/resident/{}", binding.contract) {
        if array.representation().name() != "blst/field-array"
            || scalar != crate::operations::blst::physical(Type::Field, Identity::Bls12381Fr)?
        {
            return None;
        }
        crate::operations::blst::physical(Type::Vector, Identity::Bls12381Fr)?
    } else {
        return None;
    };
    let (inputs, outputs, attributes) = match binding.contract.as_str() {
        "field_array.from_vector" => (vec![vector], vec![array], AttributeRule::None),
        "field_array.at" => (vec![array], vec![scalar], AttributeRule::Unsigned64),
        "field_array.get" => (
            vec![
                array,
                PhysicalType::default_for(LogicalType::new(Type::Index, Identity::None).ok()?)
                    .ok()?,
            ],
            vec![scalar],
            AttributeRule::None,
        ),
        _ => return None,
    };
    Some(OperationSignature {
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
            let ty = invocation.binding.signature().outputs[0].clone();
            policy.output(
                bytes(elements.len())?.saturating_add(ty.descriptor_bytes()),
                usize::MAX,
            )?;
            policy.output(
                DESCRIPTOR_BYTES.saturating_add(ty.descriptor_bytes()),
                invocation.max_output_bytes,
            )?;
            Value::FieldArray(FieldArray::new(ty, elements.clone())?)
        }
        ("field_array.from_vector", [Value::BlstVector(elements)]) => {
            let ty = invocation.binding.signature().outputs[0].clone();
            policy.output(
                elements
                    .storage_bytes()
                    .saturating_add(256)
                    .saturating_add(DESCRIPTOR_BYTES)
                    .saturating_add(ty.descriptor_bytes()),
                usize::MAX,
            )?;
            policy.output(
                DESCRIPTOR_BYTES.saturating_add(ty.descriptor_bytes()),
                invocation.max_output_bytes,
            )?;
            Value::FieldArray(FieldArray::from_resident(ty, elements.clone())?)
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
            array
                .get(index)
                .ok_or_else(|| refused("field-array-index"))?
        }
        ("field_array.get", [Value::FieldArray(array), Value::Index(index)]) => {
            array.validate()?;
            let index = usize::try_from(*index).map_err(|_| refused("field-array-index"))?;
            policy.output(512, invocation.max_output_bytes)?;
            array
                .get(index)
                .ok_or_else(|| refused("field-array-index"))?
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![value])
}
pub(crate) const RESIDENT_IMPLEMENTATIONS: &[(&str, &str)] = &[
    (
        "blst/resident/field_array.from_vector",
        "field_array.from_vector",
    ),
    ("blst/resident/field_array.at", "field_array.at"),
    ("blst/resident/field_array.get", "field_array.get"),
];
pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    (
        "arkworks/field_array.from_vector",
        "field_array.from_vector",
    ),
    ("arkworks/field_array.at", "field_array.at"),
    ("arkworks/field_array.get", "field_array.get"),
];
