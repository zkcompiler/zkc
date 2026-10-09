//! Closed service-port profile, separate from the ordinary data type lattice.
use super::{AdmissionError, ErrorCode, PhysicalType};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ServiceContract {
    RandomBls12381Field,
    RandomBn254Field,
    RandomRistrettoField,
    RandomExtensionField,
}
impl ServiceContract {
    pub fn parse(value: &str) -> Result<Self, AdmissionError> {
        match value {
            "random.bls12-381.fr/1" => Ok(Self::RandomBls12381Field),
            "random.bn254.fr/1" => Ok(Self::RandomBn254Field),
            "random.ristretto255.scalar/1" => Ok(Self::RandomRistrettoField),
            "random.koala-bear.ext8-binomial3/1" => Ok(Self::RandomExtensionField),
            _ => Err(AdmissionError::new(
                ErrorCode::Type,
                "unsupported service contract",
            )),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::RandomBls12381Field => "random.bls12-381.fr/1",
            Self::RandomBn254Field => "random.bn254.fr/1",
            Self::RandomRistrettoField => "random.ristretto255.scalar/1",
            Self::RandomExtensionField => "random.koala-bear.ext8-binomial3/1",
        }
    }
    pub fn field(self) -> super::Identity {
        use super::Identity;
        match self {
            Self::RandomBls12381Field => Identity::Bls12381Fr,
            Self::RandomBn254Field => Identity::Bn254Fr,
            Self::RandomRistrettoField => Identity::Ristretto255Scalar,
            Self::RandomExtensionField => Identity::KoalaBearExt8,
        }
    }
    pub fn for_field(field: super::Identity) -> Option<Self> {
        [
            Self::RandomBls12381Field,
            Self::RandomBn254Field,
            Self::RandomRistrettoField,
            Self::RandomExtensionField,
        ]
        .into_iter()
        .find(|contract| contract.field() == field)
    }
    pub fn signature(self, method: &str) -> Option<ServiceSignature> {
        (method == "draw").then(|| ServiceSignature {
            inputs: vec![],
            outputs: vec![
                PhysicalType::default_for(
                    super::LogicalType::new(super::Type::Field, self.field())
                        .expect("installed field"),
                )
                .expect("installed representation"),
            ],
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
