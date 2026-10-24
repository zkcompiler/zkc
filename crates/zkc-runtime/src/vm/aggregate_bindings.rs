//! Bounded trusted signature rules in the existing implementation inventory.
use super::{
    AdmissionError, BoundSignature, ErrorCode, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Representation, Type,
};
type Result<T> = std::result::Result<T, AdmissionError>;

/// A finite storage-owner rule, never an artifact-provided signature.
#[derive(Clone, Debug)]
pub enum AggregateImplementationFamily {
    Sequence,
    FieldArray {
        representation: Representation,
        scalar: PhysicalType,
        vector: PhysicalType,
    },
    FixedVector {
        representation: Representation,
        scalar: PhysicalType,
        vector: PhysicalType,
    },
}
impl AggregateImplementationFamily {
    pub(super) fn kind(&self) -> Type {
        match self {
            Self::Sequence => Type::Sequence,
            Self::FieldArray { .. } => Type::FieldArray,
            Self::FixedVector { .. } => Type::FixedVector,
        }
    }
    pub(super) fn supports(&self, contract: &str) -> bool {
        match self {
            Self::Sequence => matches!(
                contract,
                "sequence.empty" | "sequence.append" | "sequence.length" | "sequence.at"
            ),
            Self::FieldArray { .. } => matches!(
                contract,
                "field_array.from_vector" | "field_array.at" | "field_array.get"
            ),
            Self::FixedVector { .. } => matches!(
                contract,
                "fixed_vector.from_vector" | "fixed_vector.to_vector" | "fixed_vector.dot"
            ),
        }
    }
    pub(super) fn check_logical(
        &self,
        binding: &OperationBinding,
        logical: &OperationSignature<LogicalType>,
    ) -> Result<()> {
        let container = logical
            .inputs
            .iter()
            .chain(&logical.outputs)
            .find(|ty| ty.kind() == self.kind())
            .ok_or_else(|| AdmissionError::new(ErrorCode::Signature, "aggregate-specialization"))?;
        if !self.supports(&binding.contract) {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "aggregate-specialization",
            ));
        }
        // Logical implementation constraints describe mathematical domains. They
        // cannot require any default layout for a complete aggregate child.
        match self {
            Self::Sequence => Ok(()),
            Self::FieldArray { scalar, .. } | Self::FixedVector { scalar, .. } => {
                let children = PhysicalType::logical_children(container)?;
                if children.as_deref() == Some(std::slice::from_ref(scalar.logical())) {
                    Ok(())
                } else {
                    Err(AdmissionError::new(
                        ErrorCode::Signature,
                        "aggregate-specialization",
                    ))
                }
            }
        }
    }
    pub(super) fn signature(
        &self,
        binding: &OperationBinding,
        logical: &OperationSignature<LogicalType>,
        physical: &[PhysicalType],
    ) -> Result<BoundSignature> {
        let fail = || AdmissionError::new(ErrorCode::Signature, "aggregate-specialization");
        if !self.supports(&binding.contract) {
            return Err(fail());
        }
        let container = selected_container(binding, logical, physical, self.kind())?;
        let element = container
            .children()
            .and_then(|c| c.first())
            .ok_or_else(fail)?;
        let vector = match self {
            Self::Sequence if container.representation() == Representation::Sequence => None,
            Self::Sequence => return Err(fail()),
            Self::FieldArray {
                representation,
                scalar,
                vector,
            }
            | Self::FixedVector {
                representation,
                scalar,
                vector,
            } => {
                if container.representation() != *representation || element != scalar {
                    return Err(fail());
                }
                Some(vector)
            }
        };
        physical_signature(logical, &container, vector)
    }
}

fn selected_container(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    physical: &[PhysicalType],
    kind: Type,
) -> Result<PhysicalType> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "aggregate-specialization");
    let logical_container = logical
        .inputs
        .iter()
        .chain(&logical.outputs)
        .find(|ty| ty.kind() == kind)
        .ok_or_else(fail)?;
    let container = match physical {
        [] if binding.physical_arguments.is_empty() => {
            PhysicalType::default_for(logical_container.clone())?
        }
        [selected] => selected.clone(),
        _ => return Err(fail()),
    };
    if container.logical() != logical_container {
        return Err(fail());
    }
    Ok(container)
}

fn physical_signature(
    logical: &OperationSignature<LogicalType>,
    container: &PhysicalType,
    vector: Option<&PhysicalType>,
) -> Result<BoundSignature> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "aggregate-specialization");
    let element = container
        .children()
        .and_then(|children| children.first())
        .ok_or_else(fail)?;
    let port = |ty: &LogicalType| -> Result<PhysicalType> {
        if ty == container.logical() {
            Ok(container.clone())
        } else if ty == element.logical() {
            Ok(element.clone())
        } else if let Some(vector) = vector
            && ty == vector.logical()
        {
            Ok(vector.clone())
        } else if ty.kind() == Type::Index {
            PhysicalType::default_for(ty.clone())
        } else {
            Err(fail())
        }
    };
    Ok(OperationSignature {
        inputs: logical.inputs.iter().map(port).collect::<Result<_>>()?,
        outputs: logical.outputs.iter().map(port).collect::<Result<_>>()?,
        attributes: logical.attributes,
    })
}

/// Exact trusted contributions select their container and child layouts. Their
/// vector adapter, when present, is an independently admitted port; standard
/// provider restrictions belong only to the standard implementation families.
pub(super) fn exact_signature(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    physical: &[PhysicalType],
    signature: &BoundSignature,
) -> Option<Result<BoundSignature>> {
    let kind = match binding.contract.as_str() {
        "sequence.empty" | "sequence.append" | "sequence.length" | "sequence.at" => Type::Sequence,
        "field_array.from_vector" | "field_array.at" | "field_array.get" => Type::FieldArray,
        "fixed_vector.from_vector" | "fixed_vector.to_vector" | "fixed_vector.dot" => {
            Type::FixedVector
        }
        _ => return None,
    };
    Some(
        selected_container(binding, logical, physical, kind).and_then(|container| {
            let vector = signature
                .inputs
                .iter()
                .chain(&signature.outputs)
                .find(|ty| ty.kind() == Type::Vector);
            physical_signature(logical, &container, vector)
        }),
    )
}

fn standard_family(binding: &OperationBinding) -> Option<AggregateImplementationFamily> {
    let family = if binding.contract.starts_with("sequence.") {
        AggregateImplementationFamily::Sequence
    } else if binding.contract.starts_with("field_array.") {
        AggregateImplementationFamily::FieldArray {
            representation: Representation::FieldArray,
            scalar: PhysicalType::parse("field:bls12-381.fr@arkworks.fr/0")
                .expect("standard scalar"),
            vector: PhysicalType::parse("vector:bls12-381.fr@arkworks.fr-vector/0")
                .expect("standard vector"),
        }
    } else if binding.contract.starts_with("fixed_vector.") {
        AggregateImplementationFamily::FixedVector {
            representation: Representation::FixedVector,
            scalar: PhysicalType::parse("field:koala-bear@plonky3.koala-bear/0")
                .expect("standard scalar"),
            vector: PhysicalType::parse("vector:koala-bear@plonky3.koala-bear-vector/0")
                .expect("standard vector"),
        }
    } else {
        return None;
    };
    Some(family)
}

pub(super) fn standard_logical(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
) -> Option<Result<()>> {
    Some(standard_family(binding)?.check_logical(binding, logical))
}

pub(super) fn standard_signature(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
    physical: &[PhysicalType],
) -> Option<Result<BoundSignature>> {
    Some(standard_family(binding)?.signature(binding, logical, physical))
}
