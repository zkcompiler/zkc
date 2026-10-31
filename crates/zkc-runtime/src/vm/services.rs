//! Closed service-port profile, separate from the ordinary data type lattice.
use super::{AdmissionError, ErrorCode, PhysicalType};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServiceContract {
    RandomBls12381Field,
    RandomBn254Field,
    RandomRistrettoField,
    RandomExtensionField,
    RandomKoalaBearExt4,
    RandomBabyBearExt4,
    RandomGoldilocksExt2,
}
impl ServiceContract {
    pub fn parse(value: &str) -> Result<Self, AdmissionError> {
        match value {
            "random.bls12-381.fr/0" => Ok(Self::RandomBls12381Field),
            "random.bn254.fr/0" => Ok(Self::RandomBn254Field),
            "random.ristretto255.scalar/0" => Ok(Self::RandomRistrettoField),
            "random.baby-bear.ext4-binomial11/0" => Ok(Self::RandomBabyBearExt4),
            "random.goldilocks.ext2-binomial7/0" => Ok(Self::RandomGoldilocksExt2),
            "random.koala-bear.ext8-binomial3/0" => Ok(Self::RandomExtensionField),
            "random.koala-bear.ext4-binomial3/0" => Ok(Self::RandomKoalaBearExt4),
            _ => Err(AdmissionError::new(
                ErrorCode::Type,
                "unsupported service contract",
            )),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::RandomBls12381Field => "random.bls12-381.fr/0",
            Self::RandomBn254Field => "random.bn254.fr/0",
            Self::RandomRistrettoField => "random.ristretto255.scalar/0",
            Self::RandomExtensionField => "random.koala-bear.ext8-binomial3/0",
            Self::RandomKoalaBearExt4 => "random.koala-bear.ext4-binomial3/0",
            Self::RandomBabyBearExt4 => "random.baby-bear.ext4-binomial11/0",
            Self::RandomGoldilocksExt2 => "random.goldilocks.ext2-binomial7/0",
        }
    }
    pub fn field(self) -> super::Identity {
        use super::Identity;
        match self {
            Self::RandomBls12381Field => Identity::Bls12381Fr,
            Self::RandomBn254Field => Identity::Bn254Fr,
            Self::RandomRistrettoField => Identity::Ristretto255Scalar,
            Self::RandomExtensionField => Identity::KoalaBearExt8,
            Self::RandomKoalaBearExt4 => Identity::KoalaBearExt4,
            Self::RandomBabyBearExt4 => Identity::BabyBearExt4,
            Self::RandomGoldilocksExt2 => Identity::GoldilocksExt2,
        }
    }
    pub fn for_field(field: super::Identity) -> Option<Self> {
        [
            Self::RandomBls12381Field,
            Self::RandomBn254Field,
            Self::RandomRistrettoField,
            Self::RandomExtensionField,
            Self::RandomKoalaBearExt4,
            Self::RandomBabyBearExt4,
            Self::RandomGoldilocksExt2,
        ]
        .into_iter()
        .find(|contract| contract.field() == field)
    }
    pub fn signature(self, method: &str) -> Option<ServiceSignature> {
        let physical = |kind, identity| {
            PhysicalType::default_for(
                super::LogicalType::new(kind, identity).expect("installed type"),
            )
            .expect("installed representation")
        };
        match method {
            // This describes a block distribution; provider installation is a
            // separate check and cannot follow from the scalar method.
            "indices"
                if matches!(
                    self,
                    Self::RandomExtensionField
                        | Self::RandomKoalaBearExt4
                        | Self::RandomBabyBearExt4
                        | Self::RandomGoldilocksExt2
                ) =>
            {
                Some(ServiceSignature {
                    inputs: vec![physical(super::Type::Index, super::Identity::None); 2],
                    outputs: vec![physical(super::Type::Indices, super::Identity::None)],
                })
            }
            "draw" => Some(ServiceSignature {
                inputs: vec![],
                outputs: vec![physical(super::Type::Field, self.field())],
            }),
            // UniformIndex(bound) masks one uniform 64-bit word to a
            // power-of-two bound. Only explicitly installed roots offer it.
            "index"
                if matches!(
                    self,
                    Self::RandomExtensionField
                        | Self::RandomKoalaBearExt4
                        | Self::RandomBabyBearExt4
                        | Self::RandomGoldilocksExt2
                ) =>
            {
                Some(ServiceSignature {
                    inputs: vec![physical(super::Type::Index, super::Identity::None)],
                    outputs: vec![physical(super::Type::Index, super::Identity::None)],
                })
            }
            _ => None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceSignature {
    pub inputs: Vec<PhysicalType>,
    pub outputs: Vec<PhysicalType>,
}
/// Independently authored installation facts for one service method.
/// This description grants no authority to a particular service root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceSupport {
    pub signature: ServiceSignature,
    /// Conservative aggregate retained-byte charge for the entire reply tuple.
    /// Count shared backing in full, as Value::retained_bytes does. This is not
    /// a wire-size bound or a reservation of provider scratch space.
    pub max_retained_bytes: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServicePort {
    pub name: String,
    pub contract: ServiceContract,
    /// Index in the projected MLIR participant's complete input interface.
    pub input_index: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn index_blocks_have_a_distinct_two_parameter_service_signature() {
        for (contract, supported) in [
            (ServiceContract::RandomKoalaBearExt4, true),
            (ServiceContract::RandomExtensionField, true),
            (ServiceContract::RandomBabyBearExt4, true),
            (ServiceContract::RandomGoldilocksExt2, true),
            (ServiceContract::RandomBls12381Field, false),
            (ServiceContract::RandomBn254Field, false),
            (ServiceContract::RandomRistrettoField, false),
        ] {
            let signature = contract.signature("indices");
            assert_eq!(signature.is_some(), supported);
            if let Some(signature) = signature {
                assert_eq!(
                    signature
                        .inputs
                        .iter()
                        .map(PhysicalType::kind)
                        .collect::<Vec<_>>(),
                    vec![super::super::Type::Index; 2]
                );
                assert_eq!(
                    signature
                        .outputs
                        .iter()
                        .map(PhysicalType::kind)
                        .collect::<Vec<_>>(),
                    vec![super::super::Type::Indices]
                );
            }
            assert!(contract.signature("unknown").is_none());
            assert!(contract.signature("draw").is_some());
        }
    }
}
