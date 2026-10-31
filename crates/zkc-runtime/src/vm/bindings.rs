//! Standard nominal contracts shared by admission and execution. Installed
//! backends independently advertise implementations of these contracts.

use super::{AdmissionError, ErrorCode, OperationSignature, Type};

type Result<T> = std::result::Result<T, AdmissionError>;
fn error(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Type, detail)
}
fn representation_error(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Representation, detail)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Identity {
    None,
    Bn254Fr,
    Bn254G1,
    Bn254G2,
    Bn254Gt,
    Bls12381Fr,
    Bls12381G1,
    MultilinearKzgBls12381,
    MerkleKoalaBear,
    MerkleKoalaBearExt8,
    MerkleKoalaBearExt4,
    MerklePoseidon2KoalaBear,
    MerklePoseidon2KoalaBearExt4,
    MerklePoseidon2BabyBear,
    MerklePoseidon2BabyBearExt4,
    MerklePoseidon2Goldilocks,
    MerklePoseidon2GoldilocksExt2,

    Merlin3KoalaBearExt8,
    Merlin3Fr64Be,
    Spongefish080KeccakFr64Be,
    Ristretto255Scalar,
    KoalaBear,
    KoalaBearExt8,
    KoalaBearExt4,
    BabyBear,
    BabyBearExt4,
    Goldilocks,
    GoldilocksExt2,
    Merlin3BabyBearExt4,
    Merlin3GoldilocksExt2,
    Ristretto255Group,
    Edwards25519Prime,
    Merlin3Ristretto64Le,
    Bls12381G2,
    Bls12381Gt,
    HashChainKeccak256Fr64Be,
    HashChainKeccak256KoalaBearExt8,
    HashChainKeccak256KoalaBearExt4,
    Binary64,
    Binary64Ext3,
}
impl Identity {
    /// Characteristic of an installed field, including nominal extensions.
    /// A group or service with an associated scalar field is not itself a field.
    pub(crate) fn field_characteristic(self) -> Option<&'static str> {
        match self {
            Self::KoalaBear | Self::KoalaBearExt8 | Self::KoalaBearExt4 => Some("2130706433"),
            Self::BabyBear | Self::BabyBearExt4 => Some("2013265921"),
            Self::Goldilocks | Self::GoldilocksExt2 => Some("18446744069414584321"),
            Self::Binary64 | Self::Binary64Ext3 => Some("2"),
            Self::Bls12381Fr => Some(
                "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            ),
            Self::Bn254Fr => Some(
                "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            ),
            Self::Ristretto255Scalar => {
                Some("7237005577332262213973186563042994240857116359379907606001950938285454250989")
            }
            _ => None,
        }
    }
    /// A prime field with an integer residue representation. A binary field has
    /// characteristic two but is not a prime field.
    pub fn is_prime_field(self) -> bool {
        matches!(
            self,
            Self::Bn254Fr
                | Self::Bls12381Fr
                | Self::Ristretto255Scalar
                | Self::KoalaBear
                | Self::BabyBear
                | Self::Goldilocks
        )
    }
    /// A prime field or a nominal extension of one: every coordinate is an
    /// integer residue below the characteristic. Relation bundles and ring
    /// arenas use this presentation; binary fields do not have it.
    pub fn has_residue_coordinates(self) -> bool {
        self.is_prime_field() || self.base_field().is_some_and(Self::is_prime_field)
    }
    /// Closed installation of residue arithmetic, base-subgroup cosets and Ring.
    pub fn is_plonky3_residue(self) -> bool {
        matches!(
            self,
            Self::KoalaBear
                | Self::KoalaBearExt4
                | Self::KoalaBearExt8
                | Self::BabyBear
                | Self::BabyBearExt4
                | Self::Goldilocks
                | Self::GoldilocksExt2
        )
    }
    pub fn has_montgomery_words(self) -> bool {
        matches!(
            self,
            Self::KoalaBear
                | Self::KoalaBearExt4
                | Self::KoalaBearExt8
                | Self::BabyBear
                | Self::BabyBearExt4
        )
    }
    /// Width in bits of a binary field's bit-pattern presentation: the number
    /// of its coordinates over GF(2) (docs/spec/domains/values.md).
    pub fn bit_pattern_width(self) -> Option<u32> {
        match self {
            Self::Binary64 => Some(64),
            Self::Binary64Ext3 => Some(192),
            _ => None,
        }
    }
    /// Canonical constant attribute: a natural literal below the characteristic
    /// or, for a binary field, a canonical bit-pattern literal of at least two.
    pub(crate) fn canonical_constant_literal(self, text: &str) -> bool {
        self.canonical_field_literal(text)
            || self
                .bit_pattern_width()
                .is_some_and(|width| bit_pattern_literal(text, width).is_some())
    }
    /// Canonical prime-subfield natural literal; never reduces modulo the field.
    pub(crate) fn canonical_field_literal(self, text: &str) -> bool {
        let Some(modulus) = self.field_characteristic() else {
            return false;
        };
        !text.is_empty()
            && text.len() <= modulus.len()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text.len() == 1 || !text.starts_with('0'))
            && (text.len() < modulus.len() || (text.len() == modulus.len() && text < modulus))
    }
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
                | Self::KoalaBearExt4
                | Self::BabyBear
                | Self::BabyBearExt4
                | Self::Goldilocks
                | Self::GoldilocksExt2
        )
    }
    /// Installed associations, independent of the value kind.
    pub fn scalar_field(self) -> Option<Self> {
        match self {
            Self::Bn254Fr | Self::Bn254G1 | Self::Bn254G2 | Self::Bn254Gt => Some(Self::Bn254Fr),
            Self::Bls12381Fr
            | Self::Bls12381G1
            | Self::Bls12381G2
            | Self::Bls12381Gt
            | Self::Spongefish080KeccakFr64Be
            | Self::Merlin3Fr64Be
            | Self::HashChainKeccak256Fr64Be
            | Self::MultilinearKzgBls12381 => Some(Self::Bls12381Fr),
            Self::Ristretto255Scalar
            | Self::Ristretto255Group
            | Self::Edwards25519Prime
            | Self::Merlin3Ristretto64Le => Some(Self::Ristretto255Scalar),
            Self::KoalaBear | Self::MerkleKoalaBear | Self::MerklePoseidon2KoalaBear => {
                Some(Self::KoalaBear)
            }
            Self::KoalaBearExt8
            | Self::MerkleKoalaBearExt8
            | Self::Merlin3KoalaBearExt8
            | Self::HashChainKeccak256KoalaBearExt8 => Some(Self::KoalaBearExt8),
            Self::KoalaBearExt4
            | Self::MerkleKoalaBearExt4
            | Self::HashChainKeccak256KoalaBearExt4
            | Self::MerklePoseidon2KoalaBearExt4 => Some(Self::KoalaBearExt4),
            Self::Binary64 => Some(Self::Binary64),
            Self::Binary64Ext3 => Some(Self::Binary64Ext3),
            Self::BabyBear | Self::MerklePoseidon2BabyBear => Some(Self::BabyBear),
            Self::BabyBearExt4 | Self::Merlin3BabyBearExt4 | Self::MerklePoseidon2BabyBearExt4 => {
                Some(Self::BabyBearExt4)
            }
            Self::Goldilocks | Self::MerklePoseidon2Goldilocks => Some(Self::Goldilocks),
            Self::GoldilocksExt2
            | Self::Merlin3GoldilocksExt2
            | Self::MerklePoseidon2GoldilocksExt2 => Some(Self::GoldilocksExt2),
            Self::None => None,
        }
    }
    /// A row commitment has no polynomial opening capability.
    pub fn is_row_commitment(self) -> bool {
        matches!(
            self,
            Self::MerkleKoalaBear
                | Self::MerkleKoalaBearExt8
                | Self::MerkleKoalaBearExt4
                | Self::MerklePoseidon2KoalaBear
                | Self::MerklePoseidon2KoalaBearExt4
                | Self::MerklePoseidon2BabyBear
                | Self::MerklePoseidon2BabyBearExt4
                | Self::MerklePoseidon2Goldilocks
                | Self::MerklePoseidon2GoldilocksExt2
        )
    }
    /// A row commitment whose installed scheme opens several positions with
    /// one pruned proof.
    pub fn has_multi_opening(self) -> bool {
        matches!(
            self,
            Self::MerklePoseidon2KoalaBear
                | Self::MerklePoseidon2KoalaBearExt4
                | Self::MerklePoseidon2BabyBear
                | Self::MerklePoseidon2BabyBearExt4
                | Self::MerklePoseidon2Goldilocks
                | Self::MerklePoseidon2GoldilocksExt2
        )
    }
    /// A nominal extension has an explicit base; other fields have no embedding contract.
    pub fn base_field(self) -> Option<Self> {
        match self {
            Self::KoalaBearExt8 | Self::KoalaBearExt4 => Some(Self::KoalaBear),
            Self::BabyBearExt4 => Some(Self::BabyBear),
            Self::GoldilocksExt2 => Some(Self::Goldilocks),
            Self::Binary64Ext3 => Some(Self::Binary64),
            _ => None,
        }
    }
    pub fn group(self) -> Option<Self> {
        if matches!(
            self,
            Self::Bn254G1
                | Self::Bn254G2
                | Self::Bn254Gt
                | Self::Bls12381G2
                | Self::Bls12381Gt
                | Self::Edwards25519Prime
        ) {
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
            | Self::Spongefish080KeccakFr64Be
            | Self::Merlin3KoalaBearExt8
            | Self::Merlin3BabyBearExt4
            | Self::Merlin3GoldilocksExt2
            | Self::HashChainKeccak256Fr64Be
            | Self::HashChainKeccak256KoalaBearExt8
            | Self::HashChainKeccak256KoalaBearExt4 => Some(self),
            _ => None,
        }
    }
    /// The installed transcript suites with a UniformIndex byte sampler. Other
    /// suites keep field challenges only.
    pub fn has_index_transcript(self) -> bool {
        matches!(
            self,
            Self::Merlin3KoalaBearExt8
                | Self::Merlin3BabyBearExt4
                | Self::Merlin3GoldilocksExt2
                | Self::HashChainKeccak256KoalaBearExt8
                | Self::HashChainKeccak256KoalaBearExt4
        )
    }
    /// Explicit block installation, independent of scalar index sampling.
    pub fn has_index_block_transcript(self) -> bool {
        matches!(
            self,
            Self::HashChainKeccak256KoalaBearExt8 | Self::HashChainKeccak256KoalaBearExt4
        ) && self.has_index_transcript()
    }
    pub fn provider(self) -> Option<&'static str> {
        if self == Self::Spongefish080KeccakFr64Be {
            return Some("spongefish");
        }
        match self.scalar_field()? {
            Self::Bls12381Fr | Self::Bn254Fr => Some("arkworks"),
            Self::Ristretto255Scalar => Some("dalek"),
            Self::KoalaBear | Self::KoalaBearExt8 | Self::KoalaBearExt4 => Some("plonky3"),
            Self::Binary64
            | Self::Binary64Ext3
            | Self::BabyBear
            | Self::BabyBearExt4
            | Self::Goldilocks
            | Self::GoldilocksExt2 => Some("plonky3"),
            _ => None,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::None => "",
            Self::Bn254Fr => "bn254.fr",
            Self::Bn254G1 => "bn254.g1",
            Self::Bn254G2 => "bn254.g2",
            Self::Bn254Gt => "bn254.gt",

            Self::BabyBear => "baby-bear",
            Self::BabyBearExt4 => "baby-bear.ext4-binomial11",
            Self::Goldilocks => "goldilocks",
            Self::GoldilocksExt2 => "goldilocks.ext2-binomial7",
            Self::Merlin3BabyBearExt4 => "merlin3.baby-bear.ext4-binomial11.rejection31le/0",
            Self::Merlin3GoldilocksExt2 => "merlin3.goldilocks.ext2-binomial7.rejection64le/0",
            Self::KoalaBear => "koala-bear",
            Self::KoalaBearExt8 => "koala-bear.ext8-binomial3",
            Self::KoalaBearExt4 => "koala-bear.ext4-binomial3",
            Self::Binary64 => "gf2-64.pentanomial-4-3-1",
            Self::Binary64Ext3 => "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
            Self::Bls12381Fr => "bls12-381.fr",
            Self::Bls12381G1 => "bls12-381.g1",
            Self::Bls12381G2 => "bls12-381.g2",
            Self::Bls12381Gt => "bls12-381.gt",
            Self::MultilinearKzgBls12381 => "multilinear.kzg.bls12-381/0",
            Self::MerkleKoalaBear => "rows.merkle-keccak256.koala-bear/0",
            Self::MerkleKoalaBearExt8 => "rows.merkle-keccak256.koala-bear.ext8-binomial3/0",
            Self::MerkleKoalaBearExt4 => "rows.merkle-keccak256.koala-bear.ext4-binomial3/0",
            Self::MerklePoseidon2KoalaBear => "rows.merkle-poseidon2-16.koala-bear/0",
            Self::MerklePoseidon2KoalaBearExt4 => {
                "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0"
            }
            Self::MerklePoseidon2BabyBear => "rows.merkle-poseidon2-16.baby-bear/0",
            Self::MerklePoseidon2BabyBearExt4 => {
                "rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0"
            }
            Self::MerklePoseidon2Goldilocks => "rows.merkle-poseidon2-8.goldilocks/0",
            Self::MerklePoseidon2GoldilocksExt2 => {
                "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0"
            }
            Self::Ristretto255Scalar => "ristretto255.scalar",
            Self::Ristretto255Group => "ristretto255.group",
            Self::Edwards25519Prime => "edwards25519.prime",
            Self::Merlin3Ristretto64Le => "merlin3.ristretto255.scalar64le/0",
            Self::Merlin3KoalaBearExt8 => "merlin3.koala-bear.ext8-binomial3.rejection31le/0",
            Self::Merlin3Fr64Be => "merlin3.bls12-381.fr64be/0",
            Self::Spongefish080KeccakFr64Be => "spongefish0.8.0.keccak.bls12-381.fr64be/0",
            Self::HashChainKeccak256Fr64Be => "hash-chain.keccak256.bls12-381.fr64be/0",
            Self::HashChainKeccak256KoalaBearExt8 => {
                "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0"
            }
            Self::HashChainKeccak256KoalaBearExt4 => {
                "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0"
            }
        }
    }
    pub fn parse(name: &str) -> Result<Self> {
        [
            Self::None,
            Self::Bn254Fr,
            Self::Bn254G1,
            Self::Bn254G2,
            Self::Bn254Gt,
            Self::Bls12381Fr,
            Self::Bls12381G1,
            Self::MultilinearKzgBls12381,
            Self::MerkleKoalaBear,
            Self::MerkleKoalaBearExt8,
            Self::MerkleKoalaBearExt4,
            Self::MerklePoseidon2KoalaBear,
            Self::MerklePoseidon2KoalaBearExt4,
            Self::MerklePoseidon2BabyBear,
            Self::MerklePoseidon2BabyBearExt4,
            Self::MerklePoseidon2Goldilocks,
            Self::MerklePoseidon2GoldilocksExt2,
            Self::Merlin3KoalaBearExt8,
            Self::Merlin3Fr64Be,
            Self::Spongefish080KeccakFr64Be,
            Self::Ristretto255Scalar,
            Self::KoalaBear,
            Self::KoalaBearExt8,
            Self::KoalaBearExt4,
            Self::BabyBear,
            Self::BabyBearExt4,
            Self::Goldilocks,
            Self::GoldilocksExt2,
            Self::Merlin3BabyBearExt4,
            Self::Merlin3GoldilocksExt2,
            Self::Ristretto255Group,
            Self::Edwards25519Prime,
            Self::Merlin3Ristretto64Le,
            Self::Bls12381G2,
            Self::Bls12381Gt,
            Self::HashChainKeccak256Fr64Be,
            Self::HashChainKeccak256KoalaBearExt8,
            Self::HashChainKeccak256KoalaBearExt4,
            Self::Binary64,
            Self::Binary64Ext3,
        ]
        .into_iter()
        .find(|i| i.name() == name)
        .ok_or_else(|| error("uninstalled nominal identity"))
    }
}

/// Canonical bit-pattern literal of a binary field with `width` coordinates
/// over GF(2): `0x` followed by lowercase hexadecimal digits without leading
/// zeros, read as an unsigned integer whose bit `i` is coordinate `i`. Zero and
/// one keep their natural spellings `0` and `1`, so the value is at least two
/// and below `2^width`. Returns the value as little-endian 64-bit words.
pub fn bit_pattern_literal(text: &str, width: u32) -> Option<[u64; 3]> {
    let digits = text.strip_prefix("0x")?;
    let width = usize::try_from(width)
        .ok()
        .filter(|w| *w <= 192 && w % 4 == 0)?;
    if digits.is_empty()
        || digits.len() > width / 4
        || digits.starts_with('0')
        || !digits
            .bytes()
            .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
    {
        return None;
    }
    let mut words = [0u64; 3];
    for (position, digit) in digits.bytes().rev().enumerate() {
        let nibble = u64::from(match digit {
            b'0'..=b'9' => digit - b'0',
            _ => digit - b'a' + 10,
        });
        words[position / 16] |= nibble << (4 * (position % 16));
    }
    (words != [0, 0, 0] && words != [1, 0, 0]).then_some(words)
}

/// Ground origin arguments retain canonical Domain, Type, Nat, and existing
/// codec identities. Origins record construction identity; they install no
/// declarations and grant no executable permission.
pub(crate) fn valid_static_argument(name: &str) -> bool {
    if super::structural::natural(name).is_ok() || LogicalType::parse(name).is_ok() {
        return true;
    }
    if matches!(Identity::parse(name), Ok(i) if i != Identity::None) {
        return true;
    }
    let Some(body) = name
        .strip_prefix("zkcv.")
        .and_then(|s| s.strip_suffix("/0"))
    else {
        return false;
    };
    if matches!(
        body,
        "bool" | "index" | "indices" | "bytes" | "shake128_state" | "quotient_matrix"
    ) {
        return true;
    }
    let Some((kind, nominal)) = body.split_once('.') else {
        return false;
    };
    let nominal = if nominal == "multilinear-kzg.bls12-381" {
        Identity::MultilinearKzgBls12381.name()
    } else if nominal == "rows-merkle-keccak256.koala-bear" {
        Identity::MerkleKoalaBear.name()
    } else if nominal == "rows-merkle-keccak256.koala-bear.ext4-binomial3" {
        Identity::MerkleKoalaBearExt4.name()
    } else if nominal == "rows-merkle-keccak256.koala-bear.ext8-binomial3" {
        Identity::MerkleKoalaBearExt8.name()
    } else if nominal == "rows-merkle-poseidon2-16.koala-bear" {
        Identity::MerklePoseidon2KoalaBear.name()
    } else if nominal == "rows-merkle-poseidon2-16.koala-bear.ext4-binomial3" {
        Identity::MerklePoseidon2KoalaBearExt4.name()
    } else if nominal == "rows-merkle-poseidon2-16.baby-bear" {
        Identity::MerklePoseidon2BabyBear.name()
    } else if nominal == "rows-merkle-poseidon2-16.baby-bear.ext4-binomial11" {
        Identity::MerklePoseidon2BabyBearExt4.name()
    } else if nominal == "rows-merkle-poseidon2-8.goldilocks" {
        Identity::MerklePoseidon2Goldilocks.name()
    } else if nominal == "rows-merkle-poseidon2-8.goldilocks.ext2-binomial7" {
        Identity::MerklePoseidon2GoldilocksExt2.name()
    } else {
        nominal
    };
    LogicalType::parse(&format!("{kind}:{nominal}")).is_ok_and(|t| t.kind.is_serializable())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LogicalType {
    kind: Type,
    identity: Identity,
    resource_domain: Option<std::sync::Arc<super::ResourceDomain>>,
    variant: Option<std::sync::Arc<super::VariantDescriptor>>,
    structural: Option<std::sync::Arc<super::StructuralType>>,
}
impl LogicalType {
    pub(super) fn from_structure(structural: std::sync::Arc<super::StructuralType>) -> Self {
        Self {
            kind: structural.kind(),
            identity: Identity::None,
            resource_domain: None,
            variant: None,
            structural: Some(structural),
        }
    }
    pub(super) fn spelling_len(&self) -> usize {
        if let Some(structure) = &self.structural {
            return structure.spelling_len();
        }
        if let Some(variant) = &self.variant {
            return variant.spelling().len();
        }
        if let Some(slot) = &self.resource_domain {
            return "resource_unit:".len() + slot.name().len();
        }
        self.kind.name().len()
            + if self.identity == Identity::None {
                0
            } else {
                1 + self.identity.name().len()
            }
    }
    pub fn resource_unit(domain: super::ResourceDomain) -> Self {
        Self {
            kind: Type::ResourceUnit,
            identity: Identity::None,
            resource_domain: Some(std::sync::Arc::new(domain)),
            variant: None,
            structural: None,
        }
    }
    pub fn resource_domain(&self) -> Option<super::ResourceDomain> {
        self.resource_domain.as_deref().copied()
    }
    pub fn new(kind: Type, identity: Identity) -> Result<Self> {
        use Identity::*;
        let valid = match kind {
            Type::Sequence
            | Type::FieldArray
            | Type::FixedVector
            | Type::ResourceUnit
            | Type::Variant => false,
            Type::Bool
            | Type::Index
            | Type::Indices
            | Type::Bytes
            | Type::Shake128State
            | Type::QuotientMatrix => identity == None,
            Type::Field | Type::Matrix | Type::Vector | Type::Polynomial | Type::Round => {
                matches!(
                    identity,
                    Bn254Fr
                        | Bls12381Fr
                        | Ristretto255Scalar
                        | KoalaBear
                        | KoalaBearExt8
                        | KoalaBearExt4
                        | BabyBear
                        | BabyBearExt4
                        | Goldilocks
                        | GoldilocksExt2
                        | Binary64
                        | Binary64Ext3
                )
            }
            Type::Rng => matches!(
                identity,
                Bn254Fr
                    | Bls12381Fr
                    | Ristretto255Scalar
                    | KoalaBearExt8
                    | KoalaBearExt4
                    | BabyBearExt4
                    | GoldilocksExt2
            ),
            Type::Nonce => matches!(identity, Bls12381Fr | Ristretto255Scalar),
            Type::Table | Type::Point => identity == Bls12381Fr,
            Type::Group => matches!(
                identity,
                Bn254Gt
                    | Bn254G1
                    | Bn254G2
                    | Bls12381G1
                    | Bls12381G2
                    | Bls12381Gt
                    | Ristretto255Group
                    | Edwards25519Prime
            ),
            Type::Groups => matches!(
                identity,
                Bn254G1 | Bn254G2 | Bls12381G1 | Bls12381G2 | Ristretto255Group | Edwards25519Prime
            ),
            Type::Transcript => matches!(
                identity,
                Merlin3Fr64Be
                    | Merlin3Ristretto64Le
                    | Spongefish080KeccakFr64Be
                    | Merlin3KoalaBearExt8
                    | Merlin3BabyBearExt4
                    | Merlin3GoldilocksExt2
                    | HashChainKeccak256Fr64Be
                    | HashChainKeccak256KoalaBearExt8
                    | HashChainKeccak256KoalaBearExt4
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
            structural: std::option::Option::None,
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
            Identity::MerklePoseidon2KoalaBear => ".rows-merkle-poseidon2-16.koala-bear".into(),
            Identity::MerklePoseidon2KoalaBearExt4 => {
                ".rows-merkle-poseidon2-16.koala-bear.ext4-binomial3".into()
            }
            Identity::MerklePoseidon2BabyBear => ".rows-merkle-poseidon2-16.baby-bear".into(),
            Identity::MerklePoseidon2BabyBearExt4 => {
                ".rows-merkle-poseidon2-16.baby-bear.ext4-binomial11".into()
            }
            Identity::MerklePoseidon2Goldilocks => ".rows-merkle-poseidon2-8.goldilocks".into(),
            Identity::MerklePoseidon2GoldilocksExt2 => {
                ".rows-merkle-poseidon2-8.goldilocks.ext2-binomial7".into()
            }
            Identity::MerkleKoalaBearExt4 => {
                ".rows-merkle-keccak256.koala-bear.ext4-binomial3".into()
            }
            Identity::MerkleKoalaBearExt8 => {
                ".rows-merkle-keccak256.koala-bear.ext8-binomial3".into()
            }
            _ => format!(".{}", self.identity.name()),
        };
        Some(format!("zkcv.{}{suffix}/0", self.kind.name()))
    }
    pub fn spelling(&self) -> String {
        if let Some(t) = &self.structural {
            return t.spelling();
        }
        if let Some(d) = &self.variant {
            return d.spelling().to_owned();
        }
        if let Some(domain) = &self.resource_domain {
            return format!("resource_unit:{}", domain.name());
        }
        if matches!(
            self.kind,
            Type::Bool
                | Type::Index
                | Type::Indices
                | Type::Bytes
                | Type::Shake128State
                | Type::QuotientMatrix
        ) {
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
            structural: None,
        }
    }
    pub fn variant_descriptor(&self) -> Option<&std::sync::Arc<super::VariantDescriptor>> {
        self.variant.as_ref()
    }
    /// Closed structured-message data profile. Permission covers every possible
    /// payload, including inactive alternatives; it never follows from Copy alone.
    pub fn is_native_message_data(&self) -> bool {
        if let Some(element) = self.sequence_element() {
            return element.is_native_message_data();
        }
        if let Some(descriptor) = self.variant_descriptor() {
            return descriptor.is_native_message_data();
        }
        (self.kind() == Type::Group
            && matches!(self.identity(), Identity::Bn254Gt | Identity::Bls12381Gt))
            || self
                .field_array_parts()
                .is_some_and(|(f, n)| f == Identity::Bls12381Fr && n <= 1_048_576)
            || matches!(
                (self.kind(), self.identity()),
                (
                    Type::Bool | Type::Index | Type::Indices | Type::Bytes,
                    Identity::None
                ) | (
                    Type::Field | Type::Vector | Type::Matrix,
                    Identity::Bn254Fr
                        | Identity::Ristretto255Scalar
                        | Identity::KoalaBear
                        | Identity::KoalaBearExt8
                        | Identity::KoalaBearExt4
                        | Identity::BabyBear
                        | Identity::BabyBearExt4
                        | Identity::Goldilocks
                        | Identity::GoldilocksExt2
                        | Identity::Binary64
                        | Identity::Binary64Ext3
                ) | (
                    Type::Group | Type::Groups,
                    Identity::Bn254G1
                        | Identity::Bn254G2
                        | Identity::Ristretto255Group
                        | Identity::Edwards25519Prime
                ) | (
                    Type::Field | Type::Vector | Type::Matrix,
                    Identity::Bls12381Fr
                ) | (
                    Type::Group | Type::Groups,
                    Identity::Bls12381G1 | Identity::Bls12381G2
                ) | (
                    Type::Commitment | Type::Proof,
                    Identity::MultilinearKzgBls12381
                        | Identity::MerkleKoalaBear
                        | Identity::MerkleKoalaBearExt8
                        | Identity::MerkleKoalaBearExt4
                        | Identity::MerklePoseidon2KoalaBear
                        | Identity::MerklePoseidon2KoalaBearExt4
                        | Identity::MerklePoseidon2BabyBear
                        | Identity::MerklePoseidon2BabyBearExt4
                        | Identity::MerklePoseidon2Goldilocks
                        | Identity::MerklePoseidon2GoldilocksExt2
                )
            )
    }
    /// Logical program-port permission, independent of codec and target support.
    /// Copyable aggregates preserve the permission of every possible payload.
    pub(super) fn is_program_port(&self) -> bool {
        self.variant
            .as_ref()
            .is_none_or(|descriptor| descriptor.is_program_port())
            && self.structural.as_ref().is_none_or(|structure| {
                structure.arguments().iter().all(|argument| match argument {
                    super::TypeArgument::Type(ty) => ty.is_program_port(),
                    _ => true,
                })
            })
    }
    /// Copy permission for the complete type, including structural arguments and
    /// every variant payload. The constructor head alone cannot grant it.
    pub fn is_duplicable(&self) -> bool {
        if let Some(t) = &self.structural {
            return t.is_duplicable();
        }
        self.variant
            .as_ref()
            .map_or_else(|| self.kind.is_duplicable(), |d| d.is_duplicable())
    }
    /// Drop permission for the complete type, including structural arguments and
    /// every variant payload, independently of codec or representation support.
    pub fn is_discardable(&self) -> bool {
        if let Some(t) = &self.structural {
            return t.is_discardable();
        }
        self.variant
            .as_ref()
            .map_or_else(|| self.kind.is_discardable(), |d| d.is_discardable())
    }
    pub fn parse(spelling: &str) -> Result<Self> {
        Self::parse_nested(spelling, 0, &mut super::structural::ParseBudget::new())
    }
    pub fn structural(&self) -> Option<&super::StructuralType> {
        self.structural.as_deref()
    }
    /// Conservative retained charge for immutable structural type metadata.
    pub fn descriptor_bytes(&self) -> usize {
        self.variant
            .as_ref()
            .map_or(0, |v| v.retained_bytes())
            .saturating_add(self.structural.as_ref().map_or(0, |s| s.retained_bytes()))
    }
    pub(super) fn parse_nested(
        spelling: &str,
        depth: usize,
        budget: &mut super::structural::ParseBudget,
    ) -> Result<Self> {
        // Only compound types own descriptors worth sharing. Flat types still
        // consume their ordinary node budget, without allocating a cache key.
        if !spelling.starts_with("variant:") && !spelling.contains('<') {
            return Self::parse_uncached(spelling, depth, budget);
        }
        if let Some(ty) = budget.cached(spelling, depth, true)? {
            return Ok(ty);
        }
        let before = budget.remaining();
        let ty = Self::parse_uncached(spelling, depth, budget)?;
        budget.remember(
            spelling,
            depth,
            ty.clone(),
            before - budget.remaining(),
            true,
        );
        Ok(ty)
    }
    fn parse_uncached(
        spelling: &str,
        depth: usize,
        budget: &mut super::structural::ParseBudget,
    ) -> Result<Self> {
        if spelling.starts_with("variant:") {
            return Ok(Self::variant(super::VariantDescriptor::parse(
                spelling, depth, budget,
            )?));
        }
        budget.node(depth)?;
        if spelling.len() > super::STRUCTURAL_SPELLING_LIMIT {
            return Err(error("logical-type-limit"));
        }
        if spelling.contains('<') {
            let structural = super::structural::parse(spelling, depth, budget)?;
            return Ok(Self::from_structure(structural));
        }
        let (kind, identity) = spelling.split_once(':').unwrap_or((spelling, ""));
        if matches!(
            kind,
            "bool" | "index" | "indices" | "bytes" | "shake128_state" | "quotient_matrix"
        ) != identity.is_empty()
        {
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
        // to an admitted spelling: docs/spec/ir/variants.md.
        let canonical = if let Some(domain) = parsed.resource_domain() {
            spelling.split_once(':') == Some((parsed.kind.name(), domain.name()))
        } else if parsed.identity == Identity::None {
            spelling == parsed.kind.name()
        } else {
            spelling.split_once(':') == Some((parsed.kind.name(), parsed.identity.name()))
        };
        if !canonical {
            return Err(error("noncanonical nominal spelling"));
        }
        Ok(parsed)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Representation {
    /// Contributed explicitly by a trusted immutable admission catalog.
    Extension(super::ExtensionRepresentation),
    Sequence,
    FieldArray,
    FixedVector,
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
    Bn254Gt,
    Bn254G2Vector,

    FrSparseCoo,
    DalekSparseCoo,
    KoalaBearExt8SparseCoo,
    KoalaBearExt8Vector,
    KoalaBearExt8Polynomial,
    KoalaBearExt8Round,
    BabyBear,
    BabyBearVector,
    BabyBearPolynomial,
    BabyBearRound,
    BabyBearSparseCoo,
    BabyBearExt4,
    BabyBearExt4Vector,
    BabyBearExt4Polynomial,
    BabyBearExt4Round,
    BabyBearExt4SparseCoo,
    Goldilocks,
    GoldilocksVector,
    GoldilocksPolynomial,
    GoldilocksRound,
    GoldilocksSparseCoo,
    GoldilocksExt2,
    GoldilocksExt2Vector,
    GoldilocksExt2Polynomial,
    GoldilocksExt2Round,
    GoldilocksExt2SparseCoo,
    KoalaBearExt4SparseCoo,
    KoalaBearExt4Vector,
    KoalaBearExt4Polynomial,
    KoalaBearExt4Round,
    KoalaBearExt4,
    Binary64,
    Binary64Vector,
    Binary64Polynomial,
    Binary64Round,
    Binary64SparseCoo,
    Binary64Ext3,
    Binary64Ext3Vector,
    Binary64Ext3Polynomial,
    Binary64Ext3Round,
    Binary64Ext3SparseCoo,
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
    EdwardsPrime,
    EdwardsPrimeVector,
    FrDiagonal,
    RistrettoDiagonal,

    Bool,
    Index,
    Indices,
    Bytes,
    Shake128State,
    QuotientMatrix,
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
    Bls12381G2,
    Bls12381G2Vector,
    Bls12381Gt,
    MerkleDigest,
    MerkleProof,
    MerkleTree,
    MerkleDigests,
    MerkleTrees,
}
// One canonical name table defines both directions without constructing an
// array of the larger, catalog-capable enum on every lookup.
macro_rules! representation_names {
    ($($variant:ident => $name:literal),* $(,)?) => {
        pub fn name(self) -> &'static str {
            match self {
                Self::Extension(id) => id.name(),
                $(Self::$variant => $name,)*
            }
        }
        pub(super) fn parse(name: &str) -> Result<Self> {
            if name.is_empty() || name.contains('@') {
                return Err(error("uninstalled representation"));
            }
            match name {
                $($name => Ok(Self::$variant),)*
                _ => Err(representation_error("uninstalled representation")),
            }
        }
    };
}
impl Representation {
    representation_names! {
        Sequence => "logical.sequence/0",
        FieldArray => "arkworks.field-array/0",
        FixedVector => "plonky3.fixed-vector/0",
        Variant => "logical.variant/0",
        Bn254Fr => "arkworks.bn254-fr/0",
        Bn254FrVector => "arkworks.bn254-fr-vector/0",
        Bn254Polynomial => "arkworks.bn254-fr-polynomial/0",
        Bn254Round => "arkworks.bn254-fr-round/0",
        Bn254SparseCoo => "arkworks.bn254-fr-sparse-coo/0",
        Bn254G1 => "arkworks.bn254-g1/0",
        Bn254G1Vector => "arkworks.bn254-g1-vector/0",
        Bn254G2 => "arkworks.bn254-g2/0",
        Bn254Gt => "arkworks.bn254-gt/0",
        Bn254G2Vector => "arkworks.bn254-g2-vector/0",
        FrSparseCoo => "arkworks.fr-sparse-coo/0",
        DalekSparseCoo => "dalek.scalar-sparse-coo/0",
        KoalaBearSparseCoo => "plonky3.koala-bear-sparse-coo/0",
        KoalaBearExt8 => "plonky3.koala-bear.ext8-binomial3/0",
        KoalaBearExt8Vector => "plonky3.koala-bear.ext8-binomial3-vector/0",
        KoalaBearExt8Polynomial => "plonky3.koala-bear.ext8-binomial3-polynomial/0",
        KoalaBearExt8Round => "plonky3.koala-bear.ext8-binomial3-quadratic/0",
        KoalaBearExt8SparseCoo => "plonky3.koala-bear.ext8-binomial3-sparse-coo/0",
        BabyBear => "plonky3.baby-bear/0",
        BabyBearVector => "plonky3.baby-bear-vector/0",
        BabyBearPolynomial => "plonky3.baby-bear-polynomial/0",
        BabyBearRound => "plonky3.baby-bear-quadratic/0",
        BabyBearSparseCoo => "plonky3.baby-bear-sparse-coo/0",
        BabyBearExt4 => "plonky3.baby-bear.ext4-binomial11/0",
        BabyBearExt4Vector => "plonky3.baby-bear.ext4-binomial11-vector/0",
        BabyBearExt4Polynomial => "plonky3.baby-bear.ext4-binomial11-polynomial/0",
        BabyBearExt4Round => "plonky3.baby-bear.ext4-binomial11-quadratic/0",
        BabyBearExt4SparseCoo => "plonky3.baby-bear.ext4-binomial11-sparse-coo/0",
        Goldilocks => "plonky3.goldilocks/0",
        GoldilocksVector => "plonky3.goldilocks-vector/0",
        GoldilocksPolynomial => "plonky3.goldilocks-polynomial/0",
        GoldilocksRound => "plonky3.goldilocks-quadratic/0",
        GoldilocksSparseCoo => "plonky3.goldilocks-sparse-coo/0",
        GoldilocksExt2 => "plonky3.goldilocks.ext2-binomial7/0",
        GoldilocksExt2Vector => "plonky3.goldilocks.ext2-binomial7-vector/0",
        GoldilocksExt2Polynomial => "plonky3.goldilocks.ext2-binomial7-polynomial/0",
        GoldilocksExt2Round => "plonky3.goldilocks.ext2-binomial7-quadratic/0",
        GoldilocksExt2SparseCoo => "plonky3.goldilocks.ext2-binomial7-sparse-coo/0",
        KoalaBearExt4 => "plonky3.koala-bear.ext4-binomial3/0",
        KoalaBearExt4Vector => "plonky3.koala-bear.ext4-binomial3-vector/0",
        KoalaBearExt4Polynomial => "plonky3.koala-bear.ext4-binomial3-polynomial/0",
        KoalaBearExt4Round => "plonky3.koala-bear.ext4-binomial3-quadratic/0",
        KoalaBearExt4SparseCoo => "plonky3.koala-bear.ext4-binomial3-sparse-coo/0",
        Binary64 => "plonky3.gf2-64.pentanomial-4-3-1/0",
        Binary64Vector => "plonky3.gf2-64.pentanomial-4-3-1-vector/0",
        Binary64Polynomial => "plonky3.gf2-64.pentanomial-4-3-1-polynomial/0",
        Binary64Round => "plonky3.gf2-64.pentanomial-4-3-1-quadratic/0",
        Binary64SparseCoo => "plonky3.gf2-64.pentanomial-4-3-1-sparse-coo/0",
        Binary64Ext3 => "plonky3.gf2-64.pentanomial-4-3-1.ext3-trinomial1/0",
        Binary64Ext3Vector => "plonky3.gf2-64.pentanomial-4-3-1.ext3-trinomial1-vector/0",
        Binary64Ext3Polynomial => "plonky3.gf2-64.pentanomial-4-3-1.ext3-trinomial1-polynomial/0",
        Binary64Ext3Round => "plonky3.gf2-64.pentanomial-4-3-1.ext3-trinomial1-quadratic/0",
        Binary64Ext3SparseCoo => "plonky3.gf2-64.pentanomial-4-3-1.ext3-trinomial1-sparse-coo/0",
        KoalaBear => "plonky3.koala-bear/0",
        KoalaBearVector => "plonky3.koala-bear-vector/0",
        KoalaBearPolynomial => "plonky3.koala-bear-polynomial/0",
        KoalaBearRound => "plonky3.koala-bear-quadratic/0",
        FrVector => "arkworks.fr-vector/0",
        Polynomial => "arkworks.polynomial/0",
        DalekScalar => "dalek.scalar/0",
        DalekVector => "dalek.scalar-vector/0",
        DalekPolynomial => "dalek.polynomial/0",
        DalekRound => "dalek.quadratic/0",
        Ristretto => "dalek.ristretto/0",
        RistrettoVector => "dalek.ristretto-vector/0",
        EdwardsPrime => "dalek.edwards-prime/0",
        EdwardsPrimeVector => "dalek.edwards-prime-vector/0",
        FrDiagonal => "arkworks.fr-diagonal/0",
        RistrettoDiagonal => "dalek.ristretto-diagonal/0",
        Bool => "native.bool/0",
        Index => "native.index/0",
        Indices => "native.indices/0",
        Bytes => "native.bytes/0",
        Shake128State => "native.shake128/0",
        QuotientMatrix => "native.quotient_matrix/0",
        Fr => "arkworks.fr/0",
        TableLsb => "arkworks.mle-lsb/0",
        TableMsb => "arkworks.mle-msb/0",
        Point => "arkworks.point/0",
        Round => "arkworks.quadratic/0",
        G1 => "arkworks.g1/0",
        Groups => "arkworks.g1-vector/0",
        ResourceUnit => "logical.resource_unit/0",
        Resource => "host.resource/0",
        Pcs => "arkworks.multilinear-pcs/0",
        MerkleRoot => "plonky3.merkle-root/0",
        MerklePath => "plonky3.merkle-path/0",
        MerkleState => "plonky3.merkle-state/0",
        MerkleRoots => "plonky3.merkle-roots/0",
        MerkleStates => "plonky3.merkle-states/0",
        Bls12381G2 => "arkworks.bls12-381-g2/0",
        Bls12381G2Vector => "arkworks.bls12-381-g2-vector/0",
        Bls12381Gt => "arkworks.bls12-381-gt/0",
        MerkleDigest => "plonky3.merkle-digest/0",
        MerkleProof => "plonky3.merkle-proof/0",
        MerkleTree => "plonky3.merkle-tree/0",
        MerkleDigests => "plonky3.merkle-digests/0",
        MerkleTrees => "plonky3.merkle-trees/0",
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PhysicalType {
    pub(super) logical: LogicalType,
    pub(super) representation: Representation,
    pub(super) children: Option<std::sync::Arc<[PhysicalType]>>,
}
impl PhysicalType {
    pub(crate) fn extension(
        logical: LogicalType,
        representation: super::ExtensionRepresentation,
    ) -> Self {
        Self {
            logical,
            representation: Representation::Extension(representation),
            children: None,
        }
    }
    pub fn new(logical: LogicalType, representation: Representation) -> Result<Self> {
        if matches!(representation, Representation::Extension(_)) {
            return Err(representation_error("extension requires trusted catalog"));
        }
        let default = Self::default_for(logical.clone())?;
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
            return Err(representation_error(
                "representation does not implement logical type",
            ));
        }
        Ok(Self {
            children: default.children,
            logical,
            representation,
        })
    }
    pub(super) fn default_representation(logical: &LogicalType) -> Result<Representation> {
        use Identity as I;
        use Representation as R;
        use Type as T;
        // LogicalType construction has already checked the finite sort/identity pairs.
        let representation = match (logical.kind, logical.identity) {
            (T::Sequence, I::None) => R::Sequence,
            (T::FieldArray, I::None) => {
                let (field, _) = logical
                    .field_array_parts()
                    .ok_or_else(|| representation_error("unrepresented logical type"))?;
                if field != I::Bls12381Fr {
                    return Err(representation_error("unrepresented logical type"));
                }
                R::FieldArray
            }
            (T::FixedVector, I::None) => {
                let (element, _) = logical
                    .fixed_vector_parts()
                    .ok_or_else(|| representation_error("unrepresented logical type"))?;
                if element.kind() != T::Field || element.identity() != I::KoalaBear {
                    return Err(representation_error("unrepresented logical type"));
                }
                R::FixedVector
            }
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
            (T::Group, I::Bn254Gt) => R::Bn254Gt,
            (T::Groups, I::Bn254G2) => R::Bn254G2Vector,
            (T::Matrix, I::Bls12381Fr) => R::FrSparseCoo,
            (T::Matrix, I::Ristretto255Scalar) => R::DalekSparseCoo,
            (T::Matrix, I::KoalaBear) => R::KoalaBearSparseCoo,
            (T::Field, I::KoalaBearExt8) => R::KoalaBearExt8,
            (T::Vector, I::KoalaBearExt8) => R::KoalaBearExt8Vector,
            (T::Polynomial, I::KoalaBearExt8) => R::KoalaBearExt8Polynomial,
            (T::Round, I::KoalaBearExt8) => R::KoalaBearExt8Round,
            (T::Matrix, I::KoalaBearExt8) => R::KoalaBearExt8SparseCoo,
            (T::Field, I::BabyBear) => R::BabyBear,
            (T::Vector, I::BabyBear) => R::BabyBearVector,
            (T::Polynomial, I::BabyBear) => R::BabyBearPolynomial,
            (T::Round, I::BabyBear) => R::BabyBearRound,
            (T::Matrix, I::BabyBear) => R::BabyBearSparseCoo,
            (T::Field, I::BabyBearExt4) => R::BabyBearExt4,
            (T::Vector, I::BabyBearExt4) => R::BabyBearExt4Vector,
            (T::Polynomial, I::BabyBearExt4) => R::BabyBearExt4Polynomial,
            (T::Round, I::BabyBearExt4) => R::BabyBearExt4Round,
            (T::Matrix, I::BabyBearExt4) => R::BabyBearExt4SparseCoo,
            (T::Field, I::Goldilocks) => R::Goldilocks,
            (T::Vector, I::Goldilocks) => R::GoldilocksVector,
            (T::Polynomial, I::Goldilocks) => R::GoldilocksPolynomial,
            (T::Round, I::Goldilocks) => R::GoldilocksRound,
            (T::Matrix, I::Goldilocks) => R::GoldilocksSparseCoo,
            (T::Field, I::GoldilocksExt2) => R::GoldilocksExt2,
            (T::Vector, I::GoldilocksExt2) => R::GoldilocksExt2Vector,
            (T::Polynomial, I::GoldilocksExt2) => R::GoldilocksExt2Polynomial,
            (T::Round, I::GoldilocksExt2) => R::GoldilocksExt2Round,
            (T::Matrix, I::GoldilocksExt2) => R::GoldilocksExt2SparseCoo,
            (T::Field, I::KoalaBearExt4) => R::KoalaBearExt4,
            (T::Vector, I::KoalaBearExt4) => R::KoalaBearExt4Vector,
            (T::Polynomial, I::KoalaBearExt4) => R::KoalaBearExt4Polynomial,
            (T::Round, I::KoalaBearExt4) => R::KoalaBearExt4Round,
            (T::Matrix, I::KoalaBearExt4) => R::KoalaBearExt4SparseCoo,
            (T::Field, I::Binary64) => R::Binary64,
            (T::Vector, I::Binary64) => R::Binary64Vector,
            (T::Polynomial, I::Binary64) => R::Binary64Polynomial,
            (T::Round, I::Binary64) => R::Binary64Round,
            (T::Matrix, I::Binary64) => R::Binary64SparseCoo,
            (T::Field, I::Binary64Ext3) => R::Binary64Ext3,
            (T::Vector, I::Binary64Ext3) => R::Binary64Ext3Vector,
            (T::Polynomial, I::Binary64Ext3) => R::Binary64Ext3Polynomial,
            (T::Round, I::Binary64Ext3) => R::Binary64Ext3Round,
            (T::Matrix, I::Binary64Ext3) => R::Binary64Ext3SparseCoo,
            (T::Field, I::KoalaBear) => R::KoalaBear,
            (T::Vector, I::KoalaBear) => R::KoalaBearVector,
            (T::Polynomial, I::KoalaBear) => R::KoalaBearPolynomial,
            (T::Round, I::KoalaBear) => R::KoalaBearRound,
            (T::Field, I::Ristretto255Scalar) => R::DalekScalar,
            (T::Vector, I::Ristretto255Scalar) => R::DalekVector,
            (T::Polynomial, I::Ristretto255Scalar) => R::DalekPolynomial,
            (T::Round, I::Ristretto255Scalar) => R::DalekRound,
            (T::Group, I::Edwards25519Prime) => R::EdwardsPrime,
            (T::Groups, I::Edwards25519Prime) => R::EdwardsPrimeVector,
            (T::Group, I::Ristretto255Group) => R::Ristretto,
            (T::Groups, I::Ristretto255Group) => R::RistrettoVector,
            (T::Vector, I::Bls12381Fr) => R::FrVector,
            (T::Polynomial, I::Bls12381Fr) => R::Polynomial,
            (T::Bool, I::None) => R::Bool,
            (T::Index, I::None) => R::Index,
            (T::Indices, I::None) => R::Indices,
            (T::Bytes, I::None) => R::Bytes,
            (T::Shake128State, I::None) => R::Shake128State,
            (T::QuotientMatrix, I::None) => R::QuotientMatrix,
            (T::Field, I::Bls12381Fr) => R::Fr,
            (T::Table, I::Bls12381Fr) => R::TableLsb,
            (T::Point, I::Bls12381Fr) => R::Point,
            (T::Round, I::Bls12381Fr) => R::Round,
            (T::Group, I::Bls12381G1) => R::G1,
            (T::Groups, I::Bls12381G1) => R::Groups,
            (T::Group, I::Bls12381G2) => R::Bls12381G2,
            (T::Groups, I::Bls12381G2) => R::Bls12381G2Vector,
            (T::Group, I::Bls12381Gt) => R::Bls12381Gt,
            (T::Rng | T::Nonce | T::Transcript, _) => R::Resource,
            (_, I::MultilinearKzgBls12381) => R::Pcs,
            (kind, I::MerkleKoalaBear | I::MerkleKoalaBearExt8 | I::MerkleKoalaBearExt4) => {
                match kind {
                    T::Commitment => R::MerkleRoot,
                    T::Proof => R::MerklePath,
                    T::OpeningState => R::MerkleState,
                    T::Commitments => R::MerkleRoots,
                    T::OpeningStates => R::MerkleStates,
                    _ => return Err(representation_error("unrepresented logical type")),
                }
            }
            // Digest-generic Merkle schemes: each digest is the scheme's
            // fixed-width byte encoding, whatever its hash.
            (
                kind,
                I::MerklePoseidon2KoalaBear
                | I::MerklePoseidon2KoalaBearExt4
                | I::MerklePoseidon2BabyBear
                | I::MerklePoseidon2BabyBearExt4
                | I::MerklePoseidon2Goldilocks
                | I::MerklePoseidon2GoldilocksExt2,
            ) => match kind {
                T::Commitment => R::MerkleDigest,
                T::Proof => R::MerkleProof,
                T::OpeningState => R::MerkleTree,
                T::Commitments => R::MerkleDigests,
                T::OpeningStates => R::MerkleTrees,
                _ => return Err(representation_error("unrepresented logical type")),
            },
            _ => return Err(representation_error("unrepresented logical type")),
        };
        Ok(representation)
    }
    pub fn default_for(logical: LogicalType) -> Result<Self> {
        Self::default_layout(logical)?.check_aggregate_layout()
    }
    fn default_layout(logical: LogicalType) -> Result<Self> {
        let representation = Self::default_representation(&logical)?;
        let children = Self::logical_children(&logical)?
            .map(|children| {
                children
                    .into_iter()
                    .map(Self::default_layout)
                    .collect::<Result<Vec<_>>>()
            })
            .transpose()?
            .map(Into::into);
        Ok(Self {
            logical,
            representation,
            children,
        })
    }
    /// Inspect the logical descriptor without copying structural or resource metadata.
    #[inline]
    pub fn logical(&self) -> &LogicalType {
        &self.logical
    }
    pub fn kind(&self) -> Type {
        self.logical.kind
    }
    pub fn representation(&self) -> Representation {
        self.representation
    }
    /// Exact equality with an unparameterized value representation. Structural
    /// and resource descriptors must be compared by their full physical type.
    #[inline]
    pub fn is_leaf(&self, kind: Type, identity: Identity, representation: Representation) -> bool {
        let Self {
            logical:
                LogicalType {
                    kind: actual_kind,
                    identity: actual_identity,
                    resource_domain,
                    variant,
                    structural,
                },
            representation: actual_representation,
            children,
        } = self;
        *actual_kind == kind
            && *actual_identity == identity
            && *actual_representation == representation
            && resource_domain.is_none()
            && variant.is_none()
            && structural.is_none()
            && children.is_none()
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
    /// Exact native-only array frame. This grants no common codec.
    pub fn has_native_array_frame(&self) -> bool {
        self.representation == Representation::FieldArray
            && matches!(
                self.logical.field_array_parts(),
                Some((Identity::Bls12381Fr, 0..=1_048_576))
            )
    }
    /// New expected-type native frames, independent of host profile authority.
    pub fn has_native_data_frame(&self) -> bool {
        matches!(
            self.kind(),
            Type::Sequence
                | Type::Variant
                | Type::Vector
                | Type::Groups
                | Type::Indices
                | Type::Bytes
                | Type::Matrix
        ) && self.logical.is_native_message_data()
            && Self::default_for(self.logical.clone()).ok().as_ref() == Some(self)
    }
    pub(crate) fn is_message_type(&self) -> bool {
        self.is_serializable() || self.has_native_array_frame() || self.has_native_data_frame()
    }
    pub fn is_serializable(&self) -> bool {
        self.kind().is_serializable()
            && !matches!(
                self.representation,
                Representation::FrDiagonal
                    | Representation::RistrettoDiagonal
                    | Representation::Extension(_)
            )
    }
}

/// Declaration selected by the compiler. Resolution below checks its contents;
/// constructing this record does not install a new contract or implementation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OperationBinding {
    pub contract: String,
    pub arguments: Vec<String>,
    pub implementation: String,
    pub physical_arguments: Vec<String>,
}

pub type BoundSignature = OperationSignature<PhysicalType>;

/// Immutable admission result. Every invocation retains its independently
/// checked semantic and implementation binding.
#[derive(Clone, Debug)]
pub struct ResolvedBinding {
    pub(crate) declaration: OperationBinding,
    pub(crate) signature: BoundSignature,
    pub(crate) implementation: String,
    history: bool,
    installation_id: Option<super::ImplementationId>,
    requirements: super::ImplementationRequirements,
    physical_arguments: Vec<PhysicalType>,
}
impl ResolvedBinding {
    pub fn physical_arguments(&self) -> &[PhysicalType] {
        &self.physical_arguments
    }
    pub fn declaration(&self) -> &OperationBinding {
        &self.declaration
    }
    pub fn signature(&self) -> &BoundSignature {
        &self.signature
    }
    pub fn implementation(&self) -> &str {
        &self.implementation
    }
    /// True when the installed contract advances observation or sampling history.
    pub fn observes_history(&self) -> bool {
        self.history
    }
    pub fn implementation_id(&self) -> Option<super::ImplementationId> {
        self.installation_id
    }
    pub fn requirements(&self) -> super::ImplementationRequirements {
        self.requirements
    }
    pub(crate) fn admitted(
        binding: OperationBinding,
        signature: BoundSignature,
        installation_id: Option<super::ImplementationId>,
        requirements: super::ImplementationRequirements,
        physical_arguments: Vec<PhysicalType>,
    ) -> Result<Self> {
        Ok(Self {
            signature,
            history: binding.observes_history()?,
            implementation: binding.implementation.clone(),
            declaration: binding,
            installation_id,
            requirements,
            physical_arguments,
        })
    }
}

impl OperationBinding {
    /// Query the fixed logical contract's history facet. Unknown contracts refuse.
    /// Like registry discovery, this does not admit the static arguments or
    /// implementation; use signature admission before interpreting a binding.
    pub fn observes_history(&self) -> Result<bool> {
        super::operations::observes_history(&self.contract)
    }

    /// Discover exact implementation and contract identities from the standard
    /// contribution. Rows may still refuse particular static arguments; discovery
    /// does not replace logical or physical signature admission.
    pub fn installed_implementations() -> Result<Vec<(String, &'static str)>> {
        super::operations::installed_implementations()
    }

    /// Instantiate standard logical ports without choosing a representation.
    /// Physical specialization is checked separately by physical admission.
    pub fn logical_signature(&self) -> Result<OperationSignature<LogicalType>> {
        let logical = self.instantiate_logical_signature()?;
        if !self.implementation.is_empty() {
            let mut selection = self.clone();
            selection.physical_arguments.clear();
            super::operations::select_signature(&selection, &logical)?;
        }
        Ok(logical)
    }

    // Shared by logical admission and the production physical decoder. Formation
    // must not depend on the current installation's realization coverage.
    fn instantiate_logical_signature(&self) -> Result<OperationSignature<LogicalType>> {
        super::operations::logical_signature(self)
    }

    /// Resolve a standard implementation independently of backend advertisement.
    /// Contributed implementations require an explicit `Contracts::resolve`.
    pub fn signature(&self) -> Result<BoundSignature> {
        super::operations::signature(self)
    }
}
