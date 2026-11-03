//! Closed service-port profile, separate from the ordinary data type lattice.
use super::{AdmissionError, ErrorCode, PhysicalType};

// The presentation names of the installed random services. A variant names
// the catalog row of its field; the contract identity, membership and method
// gates come from the catalog.
macro_rules! services {
    ($($variant:ident => $field:ident),* $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum ServiceContract {
            $($variant,)*
        }
        impl ServiceContract {
            pub const ALL: &[Self] = &[$(Self::$variant,)*];
            /// The installed field the service draws from.
            pub fn field(self) -> super::Identity {
                match self {
                    $(Self::$variant => super::Identity::$field,)*
                }
            }
        }
    };
}
services! {
    RandomBls12381Field => Bls12381Fr,
    RandomBn254Field => Bn254Fr,
    RandomRistrettoField => Ristretto255Scalar,
    RandomExtensionField => KoalaBearExt8,
    RandomKoalaBearExt4 => KoalaBearExt4,
    RandomBabyBearExt4 => BabyBearExt4,
    RandomGoldilocksExt2 => GoldilocksExt2,
}
impl ServiceContract {
    fn row(self) -> Option<&'static zkc_catalog::RandomService> {
        let field = self.field().catalog()?;
        zkc_catalog::CATALOG
            .random_services
            .iter()
            .find(|row| row.field == field)
    }
    pub fn parse(value: &str) -> Result<Self, AdmissionError> {
        Self::ALL
            .iter()
            .copied()
            .find(|contract| contract.row().is_some_and(|row| row.contract == value))
            .ok_or_else(|| {
                AdmissionError::new(ErrorCode::Type, "unsupported service contract")
                    .with_class(super::RefusalClass::UnsupportedProfile)
            })
    }
    /// The installed contract identity of the service.
    pub fn name(self) -> &'static str {
        self.row().map_or("", |row| row.contract)
    }
    pub fn for_field(field: super::Identity) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|contract| contract.field() == field && contract.row().is_some())
    }
    /// The declared service method's request signature, when the field holds
    /// the method's capability. Provider installation is a separate check and
    /// never follows from the method.
    pub fn signature(self, method: &str) -> Option<ServiceSignature> {
        use super::{Identity, LogicalType, Type};
        use zkc_catalog::ServiceSignature as Rule;
        // This adapter consumes the nominal Random constructor's methods.
        let declared = zkc_catalog::CATALOG
            .service_methods
            .iter()
            .find(|row| row.constructor == "service.random" && row.name == method)?;
        let field = self.row().map(|_| self.field())?;
        if !declared.capability.is_empty() && !field.holds(declared.capability) {
            return None;
        }
        let physical = |kind, identity| {
            PhysicalType::default_for(LogicalType::new(kind, identity).expect("installed type"))
                .expect("installed representation")
        };
        Some(match declared.signature {
            Rule::RandomDraw => ServiceSignature {
                inputs: vec![],
                outputs: vec![physical(Type::Field, field)],
            },
            // UniformIndex(bound) masks one uniform 64-bit word to a
            // power-of-two bound.
            Rule::RandomIndex => ServiceSignature {
                inputs: vec![physical(Type::Index, Identity::None)],
                outputs: vec![physical(Type::Index, Identity::None)],
            },
            // A block distribution with its own two parameters.
            Rule::RandomIndices => ServiceSignature {
                inputs: vec![physical(Type::Index, Identity::None); 2],
                outputs: vec![physical(Type::Indices, Identity::None)],
            },
        })
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
