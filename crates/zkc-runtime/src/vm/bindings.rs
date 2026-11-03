//! Standard nominal contracts shared by admission and execution. Installed
//! backends independently advertise implementations of these contracts.

use super::{AdmissionError, ErrorCode, OperationSignature, Type};
use zkc_catalog::{
    CommitmentFacts, DomainFacts, DomainIdentity, ExtensionBase, FieldStructure, INSTALLATION,
    InstalledDomain,
};

type Result<T> = std::result::Result<T, AdmissionError>;
fn error(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Type, detail)
}
fn representation_error(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Representation, detail)
}

// The presentation names of the installed domains. A variant only names a
// catalog row: membership, spelling and every fact come from the row, and the
// exhaustive conversion from `DomainIdentity` makes a new catalog domain a
// build error here until it has a name.
macro_rules! identities {
    ($($variant:ident => $domain:ident),* $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum Identity {
            None,
            $($variant,)*
        }
        impl Identity {
            /// The installed domain this name presents; `None` for no identity.
            pub const fn catalog(self) -> Option<DomainIdentity> {
                match self {
                    Self::None => None,
                    $(Self::$variant => Some(DomainIdentity::$domain),)*
                }
            }
            pub fn from_catalog(identity: DomainIdentity) -> Self {
                match identity {
                    $(DomainIdentity::$domain => Self::$variant,)*
                }
            }
        }
    };
}
identities! {
    Bn254Fr => Bn254Fr,
    Bn254G1 => Bn254G1,
    Bn254G2 => Bn254G2,
    Bn254Gt => Bn254Gt,
    Bls12381Fr => Bls12381Fr,
    Bls12381G1 => Bls12381G1,
    MultilinearKzgBls12381 => MultilinearKzgBls123810,
    MerkleKoalaBear => RowsMerkleKeccak256KoalaBear0,
    MerkleKoalaBearExt8 => RowsMerkleKeccak256KoalaBearExt8Binomial30,
    MerkleKoalaBearExt4 => RowsMerkleKeccak256KoalaBearExt4Binomial30,
    MerklePoseidon2KoalaBear => RowsMerklePoseidon216KoalaBear0,
    MerklePoseidon2KoalaBearExt4 => RowsMerklePoseidon216KoalaBearExt4Binomial30,
    MerklePoseidon2BabyBear => RowsMerklePoseidon216BabyBear0,
    MerklePoseidon2BabyBearExt4 => RowsMerklePoseidon216BabyBearExt4Binomial110,
    MerklePoseidon2Goldilocks => RowsMerklePoseidon28Goldilocks0,
    MerklePoseidon2GoldilocksExt2 => RowsMerklePoseidon28GoldilocksExt2Binomial70,
    Merlin3KoalaBearExt8 => Merlin3KoalaBearExt8Binomial3Rejection31le0,
    Merlin3Fr64Be => Merlin3Bls12381Fr64be0,
    Spongefish080KeccakFr64Be => Spongefish080KeccakBls12381Fr64be0,
    Ristretto255Scalar => Ristretto255Scalar,
    KoalaBear => KoalaBear,
    KoalaBearExt8 => KoalaBearExt8Binomial3,
    KoalaBearExt4 => KoalaBearExt4Binomial3,
    BabyBear => BabyBear,
    BabyBearExt4 => BabyBearExt4Binomial11,
    Goldilocks => Goldilocks,
    GoldilocksExt2 => GoldilocksExt2Binomial7,
    Merlin3BabyBearExt4 => Merlin3BabyBearExt4Binomial11Rejection31le0,
    Merlin3GoldilocksExt2 => Merlin3GoldilocksExt2Binomial7Rejection64le0,
    Ristretto255Group => Ristretto255Group,
    Edwards25519Prime => Edwards25519Prime,
    Merlin3Ristretto64Le => Merlin3Ristretto255Scalar64le0,
    Bls12381G2 => Bls12381G2,
    Bls12381Gt => Bls12381Gt,
    HashChainKeccak256Fr64Be => HashChainKeccak256Bls12381Fr64be0,
    HashChainKeccak256KoalaBearExt8 => HashChainKeccak256KoalaBearExt8Binomial3Rejection31le0,
    HashChainKeccak256KoalaBearExt4 => HashChainKeccak256KoalaBearExt4Binomial3Rejection31le0,
    Binary64 => Gf264Pentanomial431,
    Binary64Ext3 => Gf264Pentanomial431Ext3Trinomial1,
}
impl Identity {
    /// The installed catalog row; `None` has none.
    pub fn row(self) -> Option<&'static InstalledDomain> {
        self.catalog().map(zkc_catalog::installed_domain)
    }
    /// The declared sort of the installed domain.
    pub fn sort(self) -> Option<&'static str> {
        self.row().map(|row| row.sort)
    }
    /// Whether the installed domain declares `capability`.
    pub fn holds(self, capability: &str) -> bool {
        self.row()
            .is_some_and(|row| row.capabilities.contains(&capability))
    }
    /// The installed association `member` of this domain.
    pub fn member(self, member: &str) -> Option<Self> {
        self.row()?
            .members
            .iter()
            .find(|(name, _)| *name == member)
            .map(|(_, identity)| Self::from_catalog(*identity))
    }
    fn field_facts(self) -> Option<zkc_catalog::FieldFacts> {
        match self.row()?.facts {
            DomainFacts::Field(facts) => Some(facts),
            _ => None,
        }
    }
    fn field_form(self) -> Option<&'static zkc_catalog::FieldForm> {
        let identity = self.catalog()?;
        INSTALLATION
            .field_forms
            .iter()
            .find(|row| row.field == identity)
    }
    /// Characteristic of an installed field, including nominal extensions.
    /// A group or service with an associated scalar field is not itself a field.
    pub(crate) fn field_characteristic(self) -> Option<&'static str> {
        self.field_facts().map(|facts| facts.characteristic)
    }
    /// A prime field with an integer residue representation. A binary field has
    /// characteristic two but is not a prime field.
    pub fn is_prime_field(self) -> bool {
        self.holds("PrimeField")
    }
    /// Integer residue coordinates per element over the prime subfield: one
    /// for a prime field, and the product of the degrees along a tower of
    /// `BaseField` extensions of one, each in the ascending basis
    /// (docs/spec/domains/values.md). A binary field has none.
    pub fn residue_degree(self) -> Option<usize> {
        match self.field_facts()?.structure {
            FieldStructure::Prime => Some(1),
            FieldStructure::Extension {
                over: ExtensionBase::BaseField,
                degree,
                ..
            } => degree.checked_mul(self.base_field()?.residue_degree()?),
            FieldStructure::Extension { .. } => None,
        }
    }
    /// A prime field or a nominal extension of one: every coordinate is an
    /// integer residue below the characteristic. Relation bundles and ring
    /// arenas use this presentation; binary fields do not have it.
    pub fn has_residue_coordinates(self) -> bool {
        self.residue_degree().is_some()
    }
    /// Installed residue arithmetic in the field's default representation,
    /// with base-subgroup cosets and Ring.
    pub fn is_plonky3_residue(self) -> bool {
        self.field_form()
            .is_some_and(|form| form.arithmetic.is_some())
    }
    /// Coordinates stored as 32-bit Montgomery words.
    pub fn has_montgomery_words(self) -> bool {
        self.field_form()
            .and_then(|form| form.montgomery)
            .is_some_and(|form| form.word_bytes == 4 && form.radix_bits == 32)
    }
    /// Width in bits of a binary field's bit-pattern presentation: the number
    /// of its coordinates over GF(2) (docs/spec/domains/values.md).
    pub fn bit_pattern_width(self) -> Option<u32> {
        let facts = self.field_facts()?;
        if facts.characteristic != "2" {
            return None;
        }
        match facts.structure {
            FieldStructure::Prime => Some(1),
            FieldStructure::Extension {
                over: ExtensionBase::PrimeSubfield,
                degree,
                ..
            } => u32::try_from(degree).ok(),
            FieldStructure::Extension { degree, .. } => u32::try_from(degree)
                .ok()?
                .checked_mul(self.base_field()?.bit_pattern_width()?),
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
    /// Installed fact for operations that divide by two. Unknown identities and
    /// non-field identities acquire no algebraic capability.
    pub fn has_characteristic_not_two(self) -> bool {
        self.holds("CharacteristicNotTwo")
    }
    /// The installed field associated with this domain: a field itself, a
    /// group's scalar field, a transcript's challenge field or a commitment's
    /// value field. Independent of the value kind.
    pub fn scalar_field(self) -> Option<Self> {
        match self.sort()? {
            "Field" => Some(self),
            "Group" => self.member("Scalar"),
            "Transcript" => self.member("ChallengeField"),
            "Commitment" => self.member("ValueField"),
            _ => None,
        }
    }
    fn commitment(self) -> Option<CommitmentFacts> {
        match self.row()?.facts {
            DomainFacts::Commitment(facts) => Some(facts),
            _ => None,
        }
    }
    /// A row commitment has no polynomial opening capability.
    pub fn is_row_commitment(self) -> bool {
        matches!(
            self.commitment(),
            Some(CommitmentFacts::Keccak256Rows { .. } | CommitmentFacts::Poseidon2Rows { .. })
        )
    }
    /// A row commitment whose installed scheme opens several positions with
    /// one pruned proof.
    pub fn has_multi_opening(self) -> bool {
        self.holds("MultiOpening")
    }
    /// A nominal extension has an explicit base; other fields have no embedding contract.
    pub fn base_field(self) -> Option<Self> {
        self.member("BaseField")
    }
    /// The identity itself when it is an installed group.
    pub fn group(self) -> Option<Self> {
        (self.sort() == Some("Group")).then_some(self)
    }
    /// A transcript is selected nominally, never inferred from its field.
    pub fn transcript(self) -> Option<Self> {
        (self.sort() == Some("Transcript")).then_some(self)
    }
    /// The installed transcript suites with a UniformIndex byte sampler. Other
    /// suites keep field challenges only.
    pub fn has_index_transcript(self) -> bool {
        self.holds("IndexTranscript")
    }
    /// Explicit block installation, independent of scalar index sampling.
    pub fn has_index_block_transcript(self) -> bool {
        self.holds("IndexBlockTranscript")
    }
    /// The installation's default provider of the domain.
    pub fn provider(self) -> Option<&'static str> {
        let identity = self.catalog()?;
        INSTALLATION
            .providers
            .iter()
            .find(|row| row.domain == identity)
            .map(|row| row.default.name())
    }
    pub fn name(self) -> &'static str {
        self.catalog().map_or("", DomainIdentity::name)
    }
    pub fn parse(name: &str) -> Result<Self> {
        if name.is_empty() {
            return Ok(Self::None);
        }
        DomainIdentity::parse(name)
            .map(Self::from_catalog)
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

/// Ground origin arguments retain canonical Domain, Type, Nat, and installed
/// codec identities. Origins record construction identity; they install no
/// declarations and grant no executable permission.
pub(crate) fn valid_static_argument(name: &str) -> bool {
    super::structural::natural(name).is_ok()
        || LogicalType::parse(name).is_ok()
        || matches!(Identity::parse(name), Ok(i) if i != Identity::None)
        || zkc_catalog::installed_codec(name).is_some()
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
        // The catalog's admitted instances of nominal constructors. Structural
        // constructors have their own formation and no instance rows.
        let valid = super::installed::logical_type(kind, identity);
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
    /// The installed codec identity of a nominal instance.
    pub fn codec(&self) -> Option<String> {
        if self.resource_domain.is_some() || self.variant.is_some() || self.structural.is_some() {
            return None;
        }
        super::installed::codec(self.kind, self.identity).map(|row| row.identity.to_owned())
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
        // A formed nominal instance has an identity exactly when its
        // constructor has a parameter.
        if self.identity == Identity::None {
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
    /// A nominal atom is an instance of a catalog message constructor whose
    /// installed codec has a frame; a field array needs the catalog's aggregate
    /// frame over its field.
    pub fn is_native_message_data(&self) -> bool {
        if let Some(element) = self.sequence_element() {
            return element.is_native_message_data();
        }
        if let Some(descriptor) = self.variant_descriptor() {
            return descriptor.is_native_message_data();
        }
        if let Some((field, size)) = self.field_array_parts() {
            return size <= super::NATURAL_ARGUMENT_LIMIT
                && zkc_catalog::CATALOG.aggregate_frames.iter().any(|row| {
                    row.constructor == Type::FieldArray.name() && row.domain == field.catalog()
                });
        }
        if self.resource_domain.is_some() || self.structural.is_some() {
            return false;
        }
        zkc_catalog::constructor(self.kind.name()).is_some_and(|row| row.message)
            && super::installed::codec(self.kind, self.identity)
                .is_some_and(|row| row.frame.is_some())
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
            .saturating_add(self.resource_domain.as_ref().map_or(0, |_| 256))
    }
    /// Actual immutable descriptor custody. Returning false skips descendants,
    /// as required by both retention and release of a shared allocation graph.
    /// These identities describe storage, never evidence for value validity.
    pub fn visit_descriptor_backings(&self, shared: &mut dyn FnMut(super::Backing) -> bool) {
        if let Some(node) = &self.structural
            && shared(super::Backing::of(node, node.own_retained_bytes()))
        {
            for argument in node.arguments() {
                if let super::TypeArgument::Type(child) = argument {
                    child.visit_descriptor_backings(shared);
                }
            }
        }
        if let Some(node) = &self.variant
            && shared(super::Backing::of(node, node.own_retained_bytes()))
        {
            for child in node.alternatives().iter().flat_map(|arm| arm.payload()) {
                child.visit_descriptor_backings(shared);
            }
        }
        if let Some(node) = &self.resource_domain {
            const {
                assert!(
                    std::mem::size_of::<super::ResourceDomain>() + 2 * std::mem::size_of::<usize>()
                        <= 256
                );
            }
            shared(super::Backing::of(node, 256));
        }
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
        let parameterless =
            zkc_catalog::constructor(kind).is_some_and(|row| row.parameters.is_empty());
        if parameterless != identity.is_empty() {
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
        /// Every built-in representation; contributed extensions are not listed.
        pub const BUILT_IN: &[Self] = &[$(Self::$variant,)*];
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

/// Whether a structural argument instantiates an installation argument pattern.
fn argument_matches(
    argument: &super::TypeArgument,
    pattern: &zkc_catalog::ArgumentPattern,
) -> bool {
    use super::TypeArgument as A;
    use zkc_catalog::ArgumentPattern as P;
    match (pattern, argument) {
        (P::Any, _) => true,
        (P::Domain(domain), A::Domain(identity)) => identity.catalog() == Some(*domain),
        (P::Type(instance), A::Type(ty)) => {
            ty.structural.is_none()
                && ty.variant.is_none()
                && ty.resource_domain.is_none()
                && ty.kind.name() == instance.kind
                && ty.identity.catalog() == instance.domain
        }
        (P::Naturals { minimum, maximum }, A::Nat(n)) => (*minimum..=*maximum).contains(n),
        _ => false,
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
        // Another installation row of the same nominal instance.
        let alternative = || {
            logical.structural.is_none()
                && logical.variant.is_none()
                && logical.resource_domain.is_none()
                && zkc_catalog::INSTALLATION.representations.iter().any(|row| {
                    row.kind == logical.kind.name()
                        && row.domain == logical.identity.catalog()
                        && row.identity == representation.name()
                })
        };
        if representation != default.representation && !alternative() {
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
    /// The installation's default representation: the default row of a
    /// nominal instance, or the default applied row whose argument patterns
    /// match a structural type.
    pub(super) fn default_representation(logical: &LogicalType) -> Result<Representation> {
        let unrepresented = || representation_error("unrepresented logical type");
        let identity = if logical.structural.is_some()
            || logical.variant.is_some()
            || logical.resource_domain.is_some()
        {
            let arguments = logical.structural.as_ref().map(|t| t.arguments());
            zkc_catalog::INSTALLATION
                .applied_representations
                .iter()
                .find(|row| {
                    row.default
                        && row.constructor == logical.kind.name()
                        && arguments.is_none_or(|arguments| {
                            arguments.len() == row.arguments.len()
                                && arguments
                                    .iter()
                                    .zip(row.arguments)
                                    .all(|(argument, pattern)| argument_matches(argument, pattern))
                        })
                })
                .map(|row| row.identity)
        } else {
            super::installed::default_representation(logical.kind, logical.identity)
        }
        .ok_or_else(unrepresented)?;
        Representation::parse(identity).map_err(|_| unrepresented())
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
    /// Exact native-only array frame: the canonical field-array representation
    /// of an array whose field has the catalog's aggregate frame. This grants
    /// no common codec.
    pub fn has_native_array_frame(&self) -> bool {
        self.representation == Representation::FieldArray
            && self.logical.field_array_parts().is_some()
            && self.logical.is_native_message_data()
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
    /// An encodable instance's codec reads its default representation and a
    /// nondefault one whose value bytes are the codec's frame, never another
    /// local layout. A contributed representation belongs to its provider,
    /// which owns its transport.
    pub fn is_serializable(&self) -> bool {
        self.kind().is_serializable()
            && !matches!(self.representation, Representation::Extension(_))
            && super::installed::codec_reads(
                self.kind(),
                self.logical.identity,
                self.representation.name(),
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
