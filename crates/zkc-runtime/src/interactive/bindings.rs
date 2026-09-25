//! Closed nominal contracts shared by admission and execution. Installed
//! backends independently advertise implementations of these contracts.

use super::{AdmissionError, AttributeRule, ErrorCode, KernelSignature, Type};

type Result<T> = std::result::Result<T, AdmissionError>;
fn error(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Type, detail)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArtifactFormat {
    ExplicitBindings,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Identity {
    None,
    Bn254Fr,
    Bn254G1,
    Bn254G2,
    Bls12381Fr,
    Bls12381G1,
    MultilinearKzgBls12381,
    MerkleKoalaBear,
    MerkleKoalaBearExt8,
    Merlin3KoalaBearExt8,
    Merlin3Fr64Be,
    Spongefish074KeccakFr64Be,
    Ristretto255Scalar,
    KoalaBear,
    KoalaBearExt8,
    Ristretto255Group,
    Merlin3Ristretto64Le,
}
impl Identity {
    /// Closed installation fact for operations that divide by two. Unknown
    /// identities and non-field identities acquire no algebraic capability.
    pub fn has_characteristic_not_two(self) -> bool {
        matches!(
            self,
            Self::Bn254Fr
                | Self::Bls12381Fr
                | Self::Ristretto255Scalar
                | Self::KoalaBear
                | Self::KoalaBearExt8
        )
    }
    /// Installed associations, independent of the value kind.
    pub fn scalar_field(self) -> Option<Self> {
        match self {
            Self::Bn254Fr | Self::Bn254G1 | Self::Bn254G2 => Some(Self::Bn254Fr),
            Self::Bls12381Fr
            | Self::Bls12381G1
            | Self::Spongefish074KeccakFr64Be
            | Self::Merlin3Fr64Be
            | Self::MultilinearKzgBls12381 => Some(Self::Bls12381Fr),
            Self::Ristretto255Scalar | Self::Ristretto255Group | Self::Merlin3Ristretto64Le => {
                Some(Self::Ristretto255Scalar)
            }
            Self::KoalaBear | Self::MerkleKoalaBear => Some(Self::KoalaBear),
            Self::KoalaBearExt8 | Self::MerkleKoalaBearExt8 | Self::Merlin3KoalaBearExt8 => {
                Some(Self::KoalaBearExt8)
            }
            _ => None,
        }
    }
    /// A row commitment has no polynomial opening capability.
    pub fn is_row_commitment(self) -> bool {
        matches!(self, Self::MerkleKoalaBear | Self::MerkleKoalaBearExt8)
    }
    /// A nominal extension has an explicit base; other fields have no embedding contract.
    pub fn base_field(self) -> Option<Self> {
        match self {
            Self::KoalaBearExt8 => Some(Self::KoalaBear),
            _ => None,
        }
    }
    pub fn group(self) -> Option<Self> {
        if matches!(self, Self::Bn254G1 | Self::Bn254G2) {
            return Some(self);
        }
        match self.scalar_field()? {
            Self::Bls12381Fr => Some(Self::Bls12381G1),
            Self::Ristretto255Scalar => Some(Self::Ristretto255Group),
            _ => None,
        }
    }
    /// A transcript is selected nominally, never inferred from its field.
    pub fn transcript(self) -> Option<Self> {
        match self {
            Self::Merlin3Fr64Be
            | Self::Merlin3Ristretto64Le
            | Self::Spongefish074KeccakFr64Be
            | Self::Merlin3KoalaBearExt8 => Some(self),
            _ => None,
        }
    }
    pub fn provider(self) -> Option<&'static str> {
        if self == Self::Spongefish074KeccakFr64Be {
            return Some("spongefish");
        }
        match self.scalar_field()? {
            Self::Bls12381Fr | Self::Bn254Fr => Some("arkworks"),
            Self::Ristretto255Scalar => Some("dalek"),
            Self::KoalaBear | Self::KoalaBearExt8 => Some("plonky3"),
            _ => None,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::None => "",
            Self::Bn254Fr => "bn254.fr",
            Self::Bn254G1 => "bn254.g1",
            Self::Bn254G2 => "bn254.g2",

            Self::KoalaBear => "koala-bear",
            Self::KoalaBearExt8 => "koala-bear.ext8-binomial3",
            Self::Bls12381Fr => "bls12-381.fr",
            Self::Bls12381G1 => "bls12-381.g1",
            Self::MultilinearKzgBls12381 => "multilinear.kzg.bls12-381/1",
            Self::MerkleKoalaBear => "rows.merkle-keccak256.koala-bear/1",
            Self::MerkleKoalaBearExt8 => "rows.merkle-keccak256.koala-bear.ext8-binomial3/1",
            Self::Ristretto255Scalar => "ristretto255.scalar",
            Self::Ristretto255Group => "ristretto255.group",
            Self::Merlin3Ristretto64Le => "merlin3.ristretto255.scalar64le/1",
            Self::Merlin3KoalaBearExt8 => "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            Self::Merlin3Fr64Be => "merlin3.bls12-381.fr64be/1",
            Self::Spongefish074KeccakFr64Be => "spongefish0.7.4.keccak.bls12-381.fr64be/1",
        }
    }
    pub fn parse(name: &str) -> Result<Self> {
        [
            Self::None,
            Self::Bn254Fr,
            Self::Bn254G1,
            Self::Bn254G2,
            Self::Bls12381Fr,
            Self::Bls12381G1,
            Self::MultilinearKzgBls12381,
            Self::MerkleKoalaBear,
            Self::MerkleKoalaBearExt8,
            Self::Merlin3KoalaBearExt8,
            Self::Merlin3Fr64Be,
            Self::Spongefish074KeccakFr64Be,
            Self::Ristretto255Scalar,
            Self::KoalaBear,
            Self::KoalaBearExt8,
            Self::Ristretto255Group,
            Self::Merlin3Ristretto64Le,
        ]
        .into_iter()
        .find(|i| i.name() == name)
        .ok_or_else(|| error("uninstalled nominal identity"))
    }
}

pub(crate) fn valid_static_identity(name: &str) -> bool {
    if matches!(Identity::parse(name), Ok(i) if i != Identity::None) {
        return true;
    }
    let Some(body) = name
        .strip_prefix("zkcv.")
        .and_then(|s| s.strip_suffix("/1"))
    else {
        return false;
    };
    if matches!(body, "bool" | "index" | "indices") {
        return true;
    }
    let Some((kind, nominal)) = body.split_once('.') else {
        return false;
    };
    let nominal = if nominal == "multilinear-kzg.bls12-381" {
        Identity::MultilinearKzgBls12381.name()
    } else if nominal == "rows-merkle-keccak256.koala-bear" {
        Identity::MerkleKoalaBear.name()
    } else if nominal == "rows-merkle-keccak256.koala-bear.ext8-binomial3" {
        Identity::MerkleKoalaBearExt8.name()
    } else {
        nominal
    };
    LogicalType::parse(&format!("{kind}:{nominal}")).is_ok_and(|t| t.kind.is_serializable())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LogicalType {
    kind: Type,
    identity: Identity,
    resource_domain: Option<super::ResourceDomain>,
    variant: Option<std::sync::Arc<super::VariantDescriptor>>,
}
impl LogicalType {
    pub fn resource_unit(domain: super::ResourceDomain) -> Self {
        Self {
            kind: Type::ResourceUnit,
            identity: Identity::None,
            resource_domain: Some(domain),
            variant: None,
        }
    }
    pub fn resource_domain(&self) -> Option<super::ResourceDomain> {
        self.resource_domain
    }
    pub fn new(kind: Type, identity: Identity) -> Result<Self> {
        use Identity::*;
        let valid = match kind {
            Type::ResourceUnit | Type::Variant => false,
            Type::Bool | Type::Index | Type::Indices => identity == None,
            Type::Field | Type::Matrix | Type::Vector | Type::Polynomial | Type::Round => {
                matches!(
                    identity,
                    Bn254Fr | Bls12381Fr | Ristretto255Scalar | KoalaBear | KoalaBearExt8
                )
            }
            Type::Rng => matches!(
                identity,
                Bn254Fr | Bls12381Fr | Ristretto255Scalar | KoalaBearExt8
            ),
            Type::Nonce => matches!(identity, Bls12381Fr | Ristretto255Scalar),
            Type::Table | Type::Point => identity == Bls12381Fr,
            Type::Group => matches!(identity, Bn254G1 | Bn254G2 | Bls12381G1 | Ristretto255Group),
            Type::Groups => matches!(identity, Bn254G1 | Bn254G2 | Bls12381G1 | Ristretto255Group),
            Type::Transcript => matches!(
                identity,
                Merlin3Fr64Be
                    | Merlin3Ristretto64Le
                    | Spongefish074KeccakFr64Be
                    | Merlin3KoalaBearExt8
            ),
            Type::Commitments | Type::OpeningStates => identity.is_row_commitment(),
            Type::Commitment | Type::Proof | Type::OpeningState => {
                identity == MultilinearKzgBls12381 || identity.is_row_commitment()
            }
            Type::ProverKey | Type::VerifierKey => identity == MultilinearKzgBls12381,
        };
        if !valid {
            return Err(error("nominal identity has wrong type sort"));
        }
        Ok(Self {
            kind,
            identity,
            resource_domain: std::option::Option::None,
            variant: std::option::Option::None,
        })
    }
    pub fn kind(&self) -> Type {
        self.kind
    }
    pub fn identity(&self) -> Identity {
        self.identity
    }
    pub fn codec(&self) -> Option<String> {
        if !self.kind.is_serializable() {
            return None;
        }
        let suffix = match self.identity {
            Identity::None => String::new(),
            Identity::MultilinearKzgBls12381 => ".multilinear-kzg.bls12-381".into(),
            Identity::MerkleKoalaBear => ".rows-merkle-keccak256.koala-bear".into(),
            Identity::MerkleKoalaBearExt8 => {
                ".rows-merkle-keccak256.koala-bear.ext8-binomial3".into()
            }
            _ => format!(".{}", self.identity.name()),
        };
        Some(format!("zkcv.{}{suffix}/1", self.kind.name()))
    }
    pub fn spelling(&self) -> String {
        if let Some(d) = &self.variant {
            return d.spelling().to_owned();
        }
        if let Some(domain) = self.resource_domain {
            return format!("resource_unit:{}", domain.name());
        }
        if matches!(self.kind, Type::Bool | Type::Index | Type::Indices) {
            return self.kind.name().into();
        }
        format!("{}:{}", self.kind.name(), self.identity.name())
    }
    pub fn variant(descriptor: std::sync::Arc<super::VariantDescriptor>) -> Self {
        Self {
            kind: Type::Variant,
            identity: Identity::None,
            resource_domain: None,
            variant: Some(descriptor),
        }
    }
    pub fn variant_descriptor(&self) -> Option<&std::sync::Arc<super::VariantDescriptor>> {
        self.variant.as_ref()
    }
    pub fn is_duplicable(&self) -> bool {
        self.variant
            .as_ref()
            .map_or_else(|| self.kind.is_duplicable(), |d| d.is_duplicable())
    }
    pub fn is_discardable(&self) -> bool {
        self.variant
            .as_ref()
            .map_or_else(|| self.kind.is_discardable(), |d| d.is_discardable())
    }
    pub fn parse(spelling: &str) -> Result<Self> {
        Self::parse_nested(spelling, 0)
    }
    pub(super) fn parse_nested(spelling: &str, depth: usize) -> Result<Self> {
        if spelling.starts_with("variant:") {
            return Ok(Self::variant(super::VariantDescriptor::parse(
                spelling, depth,
            )?));
        }
        let (kind, identity) = spelling.split_once(':').unwrap_or((spelling, ""));
        if matches!(kind, "bool" | "index" | "indices") != identity.is_empty() {
            return Err(error("explicit nominal identity required"));
        }
        // The current kind grammar requires complete nominal identity.
        let kind = Type::parse_kind(kind)?;
        let parsed = if kind == Type::ResourceUnit {
            Self::resource_unit(super::ResourceDomain::parse(identity)?)
        } else {
            Self::new(kind, Identity::parse(identity)?)?
        };
        // One logical type has one spelling. `bool:` names the same type as
        // `bool`, and admitting both would let a producer mint a second nominal
        // identity for one payload, because a variant descriptor keeps the text
        // it was given. Readers do not silently normalize a different identity
        // to an admitted spelling: docs/spec/profiles/compiler/local-variants.md.
        if parsed.spelling() != spelling {
            return Err(error("noncanonical nominal spelling"));
        }
        Ok(parsed)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Representation {
    Variant,
    ResourceUnit,
    Bn254Fr,
    Bn254FrVector,
    Bn254Polynomial,
    Bn254Round,
    Bn254SparseCoo,
    Bn254G1,
    Bn254G1Vector,
    Bn254G2,
    Bn254G2Vector,

    FrSparseCoo,
    DalekSparseCoo,
    KoalaBearExt8SparseCoo,
    KoalaBearExt8Vector,
    KoalaBearExt8Polynomial,
    KoalaBearExt8Round,
    KoalaBearSparseCoo,
    KoalaBear,
    KoalaBearExt8,
    KoalaBearVector,
    KoalaBearPolynomial,
    KoalaBearRound,
    FrVector,
    Polynomial,
    DalekScalar,
    DalekVector,
    DalekPolynomial,
    DalekRound,
    Ristretto,
    RistrettoVector,
    FrDiagonal,
    RistrettoDiagonal,

    Bool,
    Index,
    Indices,
    Fr,
    TableLsb,
    TableMsb,
    Point,
    Round,
    G1,
    Groups,
    Resource,
    Pcs,
    MerkleRoot,
    MerklePath,
    MerkleState,
    MerkleRoots,
    MerkleStates,
}
impl Representation {
    pub fn name(self) -> &'static str {
        match self {
            Self::Variant => "logical.variant/1",
            Self::Bn254Fr => "arkworks.bn254-fr/1",
            Self::Bn254FrVector => "arkworks.bn254-fr-vector/1",
            Self::Bn254Polynomial => "arkworks.bn254-fr-polynomial/1",
            Self::Bn254Round => "arkworks.bn254-fr-round/1",
            Self::Bn254SparseCoo => "arkworks.bn254-fr-sparse-coo/1",
            Self::Bn254G1 => "arkworks.bn254-g1/1",
            Self::Bn254G1Vector => "arkworks.bn254-g1-vector/1",
            Self::Bn254G2 => "arkworks.bn254-g2/1",
            Self::Bn254G2Vector => "arkworks.bn254-g2-vector/1",
            Self::FrSparseCoo => "arkworks.fr-sparse-coo/1",
            Self::DalekSparseCoo => "dalek.scalar-sparse-coo/1",
            Self::KoalaBearSparseCoo => "plonky3.koala-bear-sparse-coo/1",
            Self::KoalaBearExt8 => "plonky3.koala-bear.ext8-binomial3/1",
            Self::KoalaBearExt8Vector => "plonky3.koala-bear.ext8-binomial3-vector/1",
            Self::KoalaBearExt8Polynomial => "plonky3.koala-bear.ext8-binomial3-polynomial/1",
            Self::KoalaBearExt8Round => "plonky3.koala-bear.ext8-binomial3-quadratic/1",
            Self::KoalaBearExt8SparseCoo => "plonky3.koala-bear.ext8-binomial3-sparse-coo/1",
            Self::KoalaBear => "plonky3.koala-bear/1",
            Self::KoalaBearVector => "plonky3.koala-bear-vector/1",
            Self::KoalaBearPolynomial => "plonky3.koala-bear-polynomial/1",
            Self::KoalaBearRound => "plonky3.koala-bear-quadratic/1",
            Self::FrVector => "arkworks.fr-vector/1",
            Self::Polynomial => "arkworks.polynomial/1",
            Self::DalekScalar => "dalek.scalar/1",
            Self::DalekVector => "dalek.scalar-vector/1",
            Self::DalekPolynomial => "dalek.polynomial/1",
            Self::DalekRound => "dalek.quadratic/1",
            Self::Ristretto => "dalek.ristretto/1",
            Self::RistrettoVector => "dalek.ristretto-vector/1",
            Self::FrDiagonal => "arkworks.fr-diagonal/1",
            Self::RistrettoDiagonal => "dalek.ristretto-diagonal/1",

            Self::Bool => "native.bool/1",
            Self::Index => "native.index/1",
            Self::Indices => "native.indices/1",
            Self::Fr => "arkworks.fr/1",
            Self::TableLsb => "arkworks.mle-lsb/1",
            Self::TableMsb => "arkworks.mle-msb/1",
            Self::Point => "arkworks.point/1",
            Self::Round => "arkworks.quadratic/1",
            Self::G1 => "arkworks.g1/1",
            Self::Groups => "arkworks.g1-vector/1",
            Self::ResourceUnit => "logical.resource_unit/1",
            Self::Resource => "host.resource/1",
            Self::Pcs => "arkworks.multilinear-pcs/1",
            Self::MerkleRoot => "plonky3.merkle-root/1",
            Self::MerklePath => "plonky3.merkle-path/1",
            Self::MerkleState => "plonky3.merkle-state/1",
            Self::MerkleRoots => "plonky3.merkle-roots/1",
            Self::MerkleStates => "plonky3.merkle-states/1",
        }
    }
    fn parse(name: &str) -> Result<Self> {
        [
            Self::Variant,
            Self::Bn254Fr,
            Self::Bn254FrVector,
            Self::Bn254Polynomial,
            Self::Bn254Round,
            Self::Bn254SparseCoo,
            Self::Bn254G1,
            Self::Bn254G1Vector,
            Self::Bn254G2,
            Self::Bn254G2Vector,
            Self::FrSparseCoo,
            Self::DalekSparseCoo,
            Self::KoalaBearExt8SparseCoo,
            Self::KoalaBearExt8Vector,
            Self::KoalaBearExt8Polynomial,
            Self::KoalaBearExt8Round,
            Self::KoalaBearSparseCoo,
            Self::KoalaBear,
            Self::KoalaBearExt8,
            Self::KoalaBearVector,
            Self::KoalaBearPolynomial,
            Self::KoalaBearRound,
            Self::FrVector,
            Self::Polynomial,
            Self::DalekScalar,
            Self::DalekVector,
            Self::DalekPolynomial,
            Self::DalekRound,
            Self::Ristretto,
            Self::RistrettoVector,
            Self::FrDiagonal,
            Self::RistrettoDiagonal,
            Self::Bool,
            Self::Index,
            Self::Indices,
            Self::Fr,
            Self::TableLsb,
            Self::TableMsb,
            Self::Point,
            Self::Round,
            Self::G1,
            Self::Groups,
            Self::ResourceUnit,
            Self::Resource,
            Self::Pcs,
            Self::MerkleRoot,
            Self::MerklePath,
            Self::MerkleState,
            Self::MerkleRoots,
            Self::MerkleStates,
        ]
        .into_iter()
        .find(|r| r.name() == name)
        .ok_or_else(|| error("uninstalled representation"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PhysicalType {
    logical: LogicalType,
    representation: Representation,
}
impl PhysicalType {
    pub fn new(logical: LogicalType, representation: Representation) -> Result<Self> {
        let default = Self::default_for(logical.clone());
        if representation != default.representation
            && !matches!(
                (logical.kind, logical.identity, representation),
                (Type::Table, Identity::Bls12381Fr, Representation::TableMsb)
                    | (
                        Type::Vector,
                        Identity::Bls12381Fr,
                        Representation::FrDiagonal
                    )
                    | (
                        Type::Groups,
                        Identity::Ristretto255Group,
                        Representation::RistrettoDiagonal
                    )
            )
        {
            return Err(error("representation does not implement logical type"));
        }
        Ok(Self {
            logical,
            representation,
        })
    }
    pub fn default_for(logical: LogicalType) -> Self {
        use Identity as I;
        use Representation as R;
        use Type as T;
        // LogicalType construction has already checked the finite sort/identity pairs.
        let representation = match (logical.kind, logical.identity) {
            (T::Variant, I::None) => R::Variant,
            (T::ResourceUnit, I::None) => R::ResourceUnit,
            (T::Field, I::Bn254Fr) => R::Bn254Fr,
            (T::Vector, I::Bn254Fr) => R::Bn254FrVector,
            (T::Polynomial, I::Bn254Fr) => R::Bn254Polynomial,
            (T::Round, I::Bn254Fr) => R::Bn254Round,
            (T::Matrix, I::Bn254Fr) => R::Bn254SparseCoo,
            (T::Group, I::Bn254G1) => R::Bn254G1,
            (T::Groups, I::Bn254G1) => R::Bn254G1Vector,
            (T::Group, I::Bn254G2) => R::Bn254G2,
            (T::Groups, I::Bn254G2) => R::Bn254G2Vector,
            (T::Matrix, I::Bls12381Fr) => R::FrSparseCoo,
            (T::Matrix, I::Ristretto255Scalar) => R::DalekSparseCoo,
            (T::Matrix, I::KoalaBear) => R::KoalaBearSparseCoo,
            (T::Field, I::KoalaBearExt8) => R::KoalaBearExt8,
            (T::Vector, I::KoalaBearExt8) => R::KoalaBearExt8Vector,
            (T::Polynomial, I::KoalaBearExt8) => R::KoalaBearExt8Polynomial,
            (T::Round, I::KoalaBearExt8) => R::KoalaBearExt8Round,
            (T::Matrix, I::KoalaBearExt8) => R::KoalaBearExt8SparseCoo,
            (T::Field, I::KoalaBear) => R::KoalaBear,
            (T::Vector, I::KoalaBear) => R::KoalaBearVector,
            (T::Polynomial, I::KoalaBear) => R::KoalaBearPolynomial,
            (T::Round, I::KoalaBear) => R::KoalaBearRound,
            (T::Field, I::Ristretto255Scalar) => R::DalekScalar,
            (T::Vector, I::Ristretto255Scalar) => R::DalekVector,
            (T::Polynomial, I::Ristretto255Scalar) => R::DalekPolynomial,
            (T::Round, I::Ristretto255Scalar) => R::DalekRound,
            (T::Group, I::Ristretto255Group) => R::Ristretto,
            (T::Groups, I::Ristretto255Group) => R::RistrettoVector,
            (T::Vector, I::Bls12381Fr) => R::FrVector,
            (T::Polynomial, I::Bls12381Fr) => R::Polynomial,
            (T::Bool, I::None) => R::Bool,
            (T::Index, I::None) => R::Index,
            (T::Indices, I::None) => R::Indices,
            (T::Field, I::Bls12381Fr) => R::Fr,
            (T::Table, I::Bls12381Fr) => R::TableLsb,
            (T::Point, I::Bls12381Fr) => R::Point,
            (T::Round, I::Bls12381Fr) => R::Round,
            (T::Group, I::Bls12381G1) => R::G1,
            (T::Groups, I::Bls12381G1) => R::Groups,
            (T::Rng | T::Nonce | T::Transcript, _) => R::Resource,
            (_, I::MultilinearKzgBls12381) => R::Pcs,
            (kind, I::MerkleKoalaBear | I::MerkleKoalaBearExt8) => match kind {
                T::Commitment => R::MerkleRoot,
                T::Proof => R::MerklePath,
                T::OpeningState => R::MerkleState,
                T::Commitments => R::MerkleRoots,
                T::OpeningStates => R::MerkleStates,
                _ => unreachable!("validated row commitment kind"),
            },
            _ => unreachable!("validated logical sort and identity"),
        };
        Self {
            logical,
            representation,
        }
    }
    pub fn logical(&self) -> LogicalType {
        self.logical.clone()
    }
    pub fn kind(&self) -> Type {
        self.logical.kind
    }
    pub fn representation(&self) -> Representation {
        self.representation
    }
    pub fn is_affine(&self) -> bool {
        !self.logical.is_duplicable()
    }
    pub fn is_duplicable(&self) -> bool {
        self.logical.is_duplicable()
    }
    pub fn is_discardable(&self) -> bool {
        self.logical.is_discardable()
    }
    pub fn is_serializable(&self) -> bool {
        self.kind().is_serializable()
            && !matches!(
                self.representation,
                Representation::FrDiagonal | Representation::RistrettoDiagonal
            )
    }
    pub fn spelling(&self) -> String {
        format!("{}@{}", self.logical.spelling(), self.representation.name())
    }
    pub fn parse(spelling: &str) -> Result<Self> {
        if spelling.len()
            > if spelling.starts_with("variant:") {
                256 * 1024 + 18
            } else {
                super::Limits::STRING_BYTES
            }
        {
            return Err(error("physical type spelling limit"));
        }
        let (logical, representation) = spelling
            .split_once('@')
            .ok_or_else(|| error("physical representation required"))?;
        Self::new(
            LogicalType::parse(logical)?,
            Representation::parse(representation)?,
        )
    }
}

/// Declaration selected by the compiler. Resolution below checks its contents;
/// constructing this record does not install a new contract or implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperationBinding {
    pub contract: String,
    pub arguments: Vec<String>,
    pub implementation: String,
}

pub type BoundSignature = KernelSignature<PhysicalType>;

/// Immutable admission result. Every invocation retains its independently
/// checked semantic and implementation binding.
#[derive(Clone, Debug)]
pub struct ResolvedBinding {
    pub(crate) declaration: OperationBinding,
    pub(crate) signature: BoundSignature,
    pub(crate) implementation: String,
}
impl ResolvedBinding {
    pub fn declaration(&self) -> &OperationBinding {
        &self.declaration
    }
    pub fn signature(&self) -> &BoundSignature {
        &self.signature
    }
    pub fn implementation(&self) -> &str {
        &self.implementation
    }
    pub(crate) fn explicit(binding: OperationBinding) -> Result<Self> {
        Ok(Self {
            signature: binding.signature()?,
            implementation: binding.implementation.clone(),
            declaration: binding,
        })
    }
}

impl OperationBinding {
    /// Resolve the finite source contract independently of backend advertisement.
    pub fn signature(&self) -> Result<BoundSignature> {
        let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
        if matches!(
            self.contract.as_str(),
            "resource_unit.create" | "resource_unit.pass" | "resource_unit.consume"
        ) {
            if self.arguments.len() != 1 {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "binding-resource-unit-domain",
                ));
            }
            let domain = super::ResourceDomain::parse(&self.arguments[0]).map_err(|_| {
                AdmissionError::new(ErrorCode::Type, "binding-resource-unit-domain")
            })?;
            if self.implementation != format!("logical/{}", self.contract) {
                return Err(AdmissionError::new(
                    ErrorCode::Signature,
                    "binding-implementation",
                ));
            }
            let ty = PhysicalType::default_for(LogicalType::resource_unit(domain));
            return Ok(KernelSignature {
                inputs: if self.contract == "resource_unit.create" {
                    vec![]
                } else {
                    vec![ty.clone()]
                },
                outputs: if self.contract == "resource_unit.consume" {
                    vec![]
                } else {
                    vec![ty.clone()]
                },
                attributes: AttributeRule::None,
            });
        }
        if self.contract == "table.relayout" {
            if self.implementation != "arkworks/table.relayout"
                || self.arguments.len() != 3
                || self.arguments[0] != Identity::Bls12381Fr.name()
            {
                return Err(fail());
            }
            let logical = LogicalType::new(Type::Table, Identity::Bls12381Fr)?;
            let from =
                PhysicalType::new(logical.clone(), Representation::parse(&self.arguments[1])?)?;
            let to = PhysicalType::new(logical, Representation::parse(&self.arguments[2])?)?;
            if from == to {
                return Err(fail());
            }
            return Ok(KernelSignature {
                inputs: vec![from],
                outputs: vec![to],
                attributes: AttributeRule::None,
            });
        }
        super::domain_bindings::signature(self)
    }
}
