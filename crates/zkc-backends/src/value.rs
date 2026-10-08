use crate::{Capability, Result, exhausted, refused};
use std::sync::Arc;
use zkc_arkworks::{
    Bounds, Commitment, CommittedTable, OpeningProof, ProverKey, Scalar, Table, VerifierKey,
};
use zkc_runtime::interactive::{
    Identity, LogicalType, PhysicalType, Representation, Type, Value as RuntimeValue,
};

/// Explicit per-value, transport and service-store execution ceilings.
/// PCS temporary allocation is bounded indirectly by rank, not reserved here.
#[derive(Clone, Copy, Debug)]
pub struct Policy {
    pub max_arity: usize,
    pub max_table_elements: usize,
    pub max_wire_bytes: usize,
    pub max_value_bytes: usize,
    pub max_setup_cells: usize,
    pub max_capabilities: usize,
    pub max_groups: usize,
}
impl Default for Policy {
    fn default() -> Self {
        Self {
            max_arity: 16,
            max_table_elements: 1 << 16,
            max_wire_bytes: 16 << 20,
            max_value_bytes: 64 << 20,
            max_setup_cells: 16 << 16,
            max_capabilities: 4096,
            max_groups: 4096,
        }
    }
}
impl Policy {
    pub(crate) fn vector(&self, n: usize) -> Result<()> {
        self.vector_width(n, 32)
    }
    pub(crate) fn vector_width(&self, n: usize, width: usize) -> Result<()> {
        if n > self.max_table_elements.min(1 << 20) {
            return Err(exhausted("element-limit"));
        }
        self.output(size(n, width)?, usize::MAX)
    }
    pub(crate) fn ristretto_groups(&self, n: usize) -> Result<()> {
        if n > self.max_groups.min(32_768) {
            return Err(exhausted("group-limit"));
        }
        self.output(
            size(n, std::mem::size_of::<crate::RistrettoPoint>())?,
            usize::MAX,
        )
    }
    pub(crate) fn bn254_groups<T>(&self, n: usize) -> Result<()> {
        if n > self.max_groups.min(32_768) {
            return Err(exhausted("group-limit"));
        }
        self.output(size(n, std::mem::size_of::<T>())?, usize::MAX)
    }
    pub(crate) fn groups(&self, n: usize) -> Result<()> {
        if n > self.max_groups.min(32_768) {
            return Err(exhausted("group-limit"));
        }
        self.output(size(n, 128)?, usize::MAX)
    }
    pub fn ark_bounds(&self) -> Bounds {
        Bounds::new(
            self.max_arity,
            self.max_table_elements,
            self.max_wire_bytes,
            self.max_setup_cells,
        )
    }
    pub(crate) fn arity(&self, n: usize) -> Result<()> {
        if n > self.max_arity {
            return Err(exhausted("arity-limit"));
        }
        Ok(())
    }
    pub(crate) fn table_len(&self, n: usize) -> Result<usize> {
        self.arity(n)?;
        let len = u32::try_from(n)
            .ok()
            .and_then(|s| 1usize.checked_shl(s))
            .ok_or_else(|| exhausted("size-overflow"))?;
        if len > self.max_table_elements {
            return Err(exhausted("element-limit"));
        }
        self.output(size(len, 32)?, usize::MAX)?;
        Ok(len)
    }
    pub(crate) fn output(&self, bytes: usize, available: usize) -> Result<()> {
        if bytes > self.max_value_bytes || bytes > available || bytes > isize::MAX as usize {
            return Err(exhausted("output-bytes"));
        }
        Ok(())
    }
    pub(crate) fn wire(&self, bytes: usize) -> Result<()> {
        if bytes > self.max_wire_bytes || bytes > isize::MAX as usize {
            return Err(exhausted("wire-bytes"));
        }
        Ok(())
    }
}
pub(crate) fn size(n: usize, width: usize) -> Result<usize> {
    n.checked_mul(width)
        .and_then(|s| s.checked_add(256))
        .ok_or_else(|| exhausted("size-overflow"))
}
// Keep the public typed sum and test coverage inventory in one declaration.
macro_rules! value_inventory {
    ($( $(#[$meta:meta])* $variant:ident ( $($payload:ty),+ $(,)? ), )*) => {
        /// Trusted variants; clones retain immutable backing. Public proof/commitment
        /// variants never carry private opening custody. No token deserializer exists.
        #[derive(Clone, Debug)]
        pub enum Value { $( $(#[$meta])* $variant($($payload),+), )* }
        #[cfg(test)]
        impl Value {
            pub(crate) const PAYLOAD_NAMES: &'static [&'static str] = &[$(stringify!($variant)),*];
            pub(crate) fn payload_name(&self) -> &'static str {
                match self { $(Self::$variant(..) => stringify!($variant)),* }
            }
        }
    };
}
value_inventory! {
    Sequence(crate::Sequence),

    FieldArray(crate::FieldArray),
    FixedVector(crate::FixedVector),
    Variant(crate::variant::Variant),
    /// Zero payload; nominal identity and live ownership stay in authenticated metadata.
    ResourceUnit(crate::resource::LogicalUnit),
    Bn254Field(crate::Bn254Scalar),
    Bn254Vector(Arc<[crate::Bn254Scalar]>),
    Bn254Polynomial(Arc<[crate::Bn254Scalar]>),
    Bn254Round([crate::Bn254Scalar; 3]),
    Bn254Matrix(crate::matrix::SparseCoo<crate::Bn254Scalar>),
    Bn254G1(crate::Bn254G1),
    Bn254G1Vector(Arc<[crate::Bn254G1]>),
    Bn254G2(crate::Bn254G2),
    Bn254Gt(crate::Bn254Gt),
    Bn254G2Vector(Arc<[crate::Bn254G2]>),

    OracleRoot(crate::oracle::Domain, crate::plonky3::oracle::Digest),
    OraclePath(crate::oracle::Domain, Arc<[crate::plonky3::oracle::Digest]>),
    OracleState(crate::oracle::State),
    OracleRoots(crate::oracle::Domain, Arc<[crate::plonky3::oracle::Digest]>),
    OracleStates(crate::oracle::Domain, Arc<[crate::oracle::State]>),
    Index(u64),
    Indices(Arc<[u64]>),
    Matrix(crate::matrix::SparseCoo<Scalar>),
    RistrettoMatrix(crate::matrix::SparseCoo<crate::RistrettoScalar>),
    KoalaBearMatrix(crate::matrix::SparseCoo<crate::KoalaBear>),
    KoalaBearExt8Matrix(crate::matrix::SparseCoo<crate::KoalaBearExt8>),
    KoalaBearExt8Field(crate::KoalaBearExt8),
    KoalaBearExt8Vector(Arc<[crate::KoalaBearExt8]>),
    KoalaBearExt8Polynomial(Arc<[crate::KoalaBearExt8]>),
    KoalaBearExt8Round([crate::KoalaBearExt8; 3]),
    KoalaBearField(crate::KoalaBear),
    KoalaBearVector(Arc<[crate::KoalaBear]>),
    KoalaBearPolynomial(Arc<[crate::KoalaBear]>),
    KoalaBearRound([crate::KoalaBear; 3]),
    Vector(Arc<[Scalar]>),
    Polynomial(Arc<[Scalar]>),
    RistrettoField(crate::RistrettoScalar),
    RistrettoVector(Arc<[crate::RistrettoScalar]>),
    RistrettoPolynomial(Arc<[crate::RistrettoScalar]>),
    RistrettoRound([crate::RistrettoScalar; 3]),
    RistrettoGroup(crate::RistrettoPoint),
    RistrettoGroups(Arc<[crate::RistrettoPoint]>),
    FrDiagonal(Arc<crate::diagonal::Diagonal<Scalar, Scalar>>),
    RistrettoDiagonal(
        Arc<crate::diagonal::Diagonal<crate::RistrettoScalar, crate::RistrettoPoint>>,
    ),
    Field(Scalar),
    Table(Arc<Table>),
    TableMsb(Arc<zkc_arkworks::MsbTable>),
    Point(Arc<[Scalar]>),
    Round([Scalar; 3]),
    Bool(bool),
    Rng(Capability),
    Commitment(Arc<Commitment>),
    /// Private immutable original, key and commitment issued by the Ark helper.
    /// Borrowable across calls and repeat queries; never reconstructible from wire.
    OpeningState(Arc<CommittedTable>),
    Proof(Arc<OpeningProof>),
    ProverKey(Arc<ProverKey>),
    VerifierKey(Arc<VerifierKey>),
    Nonce(Capability),
    Transcript(Capability),
    Curve(zkc_arkworks::GroupPoint),
    Groups(Arc<[zkc_arkworks::GroupPoint]>),
}

impl Value {
    /// Conservative retained charge for an RNG, nonce or transcript handle.
    /// Host planners use this before issuing a capability.
    pub const fn capability_retained_bytes() -> usize {
        512
    }

    /// Visit only active leaves, preserving their exact capability handles.
    pub(crate) fn active_leaves(&self) -> Vec<&Self> {
        fn visit<'a>(v: &'a Value, out: &mut Vec<&'a Value>) {
            if let Value::Sequence(v) = v {
                for p in v.elements() {
                    visit(p, out);
                }
            } else if let Value::Variant(v) = v {
                for p in v.payload() {
                    visit(p, out);
                }
            } else {
                out.push(v);
            }
        }
        let mut out = Vec::new();
        visit(self, &mut out);
        out
    }

    pub fn ty(&self) -> Type {
        self.type_identity().0
    }
    // Each payload supplies kind, nominal identity and representation together.
    // New variants must explicitly classify all three properties.
    fn type_identity(&self) -> (Type, Identity, Representation) {
        match self {
            Self::Sequence(_) => (Type::Sequence, Identity::None, Representation::Sequence),
            Self::FieldArray(_) => (Type::FieldArray, Identity::None, Representation::FieldArray),
            Self::FixedVector(_) => (
                Type::FixedVector,
                Identity::None,
                Representation::FixedVector,
            ),
            Self::Variant(_) => (Type::Variant, Identity::None, Representation::Variant),
            Self::ResourceUnit(_) => (
                Type::ResourceUnit,
                Identity::None,
                Representation::ResourceUnit,
            ),
            Self::Bn254Field(_) => (Type::Field, Identity::Bn254Fr, Representation::Bn254Fr),
            Self::Bn254Vector(_) => (
                Type::Vector,
                Identity::Bn254Fr,
                Representation::Bn254FrVector,
            ),
            Self::Bn254Polynomial(_) => (
                Type::Polynomial,
                Identity::Bn254Fr,
                Representation::Bn254Polynomial,
            ),
            Self::Bn254Round(_) => (Type::Round, Identity::Bn254Fr, Representation::Bn254Round),
            Self::Bn254Matrix(_) => (
                Type::Matrix,
                Identity::Bn254Fr,
                Representation::Bn254SparseCoo,
            ),
            Self::Bn254G1(_) => (Type::Group, Identity::Bn254G1, Representation::Bn254G1),
            Self::Bn254G1Vector(_) => (
                Type::Groups,
                Identity::Bn254G1,
                Representation::Bn254G1Vector,
            ),
            Self::Bn254Gt(_) => (Type::Group, Identity::Bn254Gt, Representation::Bn254Gt),
            Self::Bn254G2(_) => (Type::Group, Identity::Bn254G2, Representation::Bn254G2),
            Self::Bn254G2Vector(_) => (
                Type::Groups,
                Identity::Bn254G2,
                Representation::Bn254G2Vector,
            ),
            Self::OracleRoot(d, _) => (Type::Commitment, d.identity(), Representation::MerkleRoot),
            Self::OraclePath(d, _) => (Type::Proof, d.identity(), Representation::MerklePath),
            Self::OracleState(s) => (
                Type::OpeningState,
                s.domain().identity(),
                Representation::MerkleState,
            ),
            Self::OracleRoots(d, _) => {
                (Type::Commitments, d.identity(), Representation::MerkleRoots)
            }
            Self::OracleStates(d, _) => (
                Type::OpeningStates,
                d.identity(),
                Representation::MerkleStates,
            ),
            Self::KoalaBearExt8Matrix(_) => (
                Type::Matrix,
                Identity::KoalaBearExt8,
                Representation::KoalaBearExt8SparseCoo,
            ),
            Self::KoalaBearExt8Round(_) => (
                Type::Round,
                Identity::KoalaBearExt8,
                Representation::KoalaBearExt8Round,
            ),
            Self::KoalaBearExt8Polynomial(_) => (
                Type::Polynomial,
                Identity::KoalaBearExt8,
                Representation::KoalaBearExt8Polynomial,
            ),
            Self::KoalaBearExt8Vector(_) => (
                Type::Vector,
                Identity::KoalaBearExt8,
                Representation::KoalaBearExt8Vector,
            ),
            Self::KoalaBearExt8Field(_) => (
                Type::Field,
                Identity::KoalaBearExt8,
                Representation::KoalaBearExt8,
            ),
            Self::Matrix(_) => (
                Type::Matrix,
                Identity::Bls12381Fr,
                Representation::FrSparseCoo,
            ),
            Self::RistrettoMatrix(_) => (
                Type::Matrix,
                Identity::Ristretto255Scalar,
                Representation::DalekSparseCoo,
            ),
            Self::KoalaBearMatrix(_) => (
                Type::Matrix,
                Identity::KoalaBear,
                Representation::KoalaBearSparseCoo,
            ),
            Self::KoalaBearField(_) => {
                (Type::Field, Identity::KoalaBear, Representation::KoalaBear)
            }
            Self::KoalaBearVector(_) => (
                Type::Vector,
                Identity::KoalaBear,
                Representation::KoalaBearVector,
            ),
            Self::KoalaBearPolynomial(_) => (
                Type::Polynomial,
                Identity::KoalaBear,
                Representation::KoalaBearPolynomial,
            ),
            Self::KoalaBearRound(_) => (
                Type::Round,
                Identity::KoalaBear,
                Representation::KoalaBearRound,
            ),
            Self::Vector(_) => (Type::Vector, Identity::Bls12381Fr, Representation::FrVector),
            Self::RistrettoVector(_) => (
                Type::Vector,
                Identity::Ristretto255Scalar,
                Representation::DalekVector,
            ),
            Self::FrDiagonal(_) => (
                Type::Vector,
                Identity::Bls12381Fr,
                Representation::FrDiagonal,
            ),
            Self::Polynomial(_) => (
                Type::Polynomial,
                Identity::Bls12381Fr,
                Representation::Polynomial,
            ),
            Self::RistrettoPolynomial(_) => (
                Type::Polynomial,
                Identity::Ristretto255Scalar,
                Representation::DalekPolynomial,
            ),
            Self::RistrettoField(_) => (
                Type::Field,
                Identity::Ristretto255Scalar,
                Representation::DalekScalar,
            ),
            Self::RistrettoRound(_) => (
                Type::Round,
                Identity::Ristretto255Scalar,
                Representation::DalekRound,
            ),
            Self::RistrettoGroup(_) => (
                Type::Group,
                Identity::Ristretto255Group,
                Representation::Ristretto,
            ),
            Self::RistrettoGroups(_) => (
                Type::Groups,
                Identity::Ristretto255Group,
                Representation::RistrettoVector,
            ),
            Self::RistrettoDiagonal(_) => (
                Type::Groups,
                Identity::Ristretto255Group,
                Representation::RistrettoDiagonal,
            ),
            Self::Field(_) => (Type::Field, Identity::Bls12381Fr, Representation::Fr),
            Self::Table(_) => (Type::Table, Identity::Bls12381Fr, Representation::TableLsb),
            Self::TableMsb(_) => (Type::Table, Identity::Bls12381Fr, Representation::TableMsb),
            Self::Point(_) => (Type::Point, Identity::Bls12381Fr, Representation::Point),
            Self::Round(_) => (Type::Round, Identity::Bls12381Fr, Representation::Round),
            Self::Bool(_) => (Type::Bool, Identity::None, Representation::Bool),
            Self::Index(_) => (Type::Index, Identity::None, Representation::Index),
            Self::Indices(_) => (Type::Indices, Identity::None, Representation::Indices),
            Self::Rng(t) => (Type::Rng, t.identity(), Representation::Resource),
            Self::Commitment(_) => (
                Type::Commitment,
                Identity::MultilinearKzgBls12381,
                Representation::Pcs,
            ),
            Self::OpeningState(_) => (
                Type::OpeningState,
                Identity::MultilinearKzgBls12381,
                Representation::Pcs,
            ),
            Self::Proof(_) => (
                Type::Proof,
                Identity::MultilinearKzgBls12381,
                Representation::Pcs,
            ),
            Self::ProverKey(_) => (
                Type::ProverKey,
                Identity::MultilinearKzgBls12381,
                Representation::Pcs,
            ),
            Self::VerifierKey(_) => (
                Type::VerifierKey,
                Identity::MultilinearKzgBls12381,
                Representation::Pcs,
            ),
            Self::Nonce(t) => (Type::Nonce, t.identity(), Representation::Resource),
            Self::Transcript(t) => (Type::Transcript, t.identity(), Representation::Resource),
            Self::Curve(_) => (Type::Group, Identity::Bls12381G1, Representation::G1),
            Self::Groups(_) => (Type::Groups, Identity::Bls12381G1, Representation::Groups),
        }
    }
    /// Pre-import conservative charge for a key selected by an already validated
    /// application VK. Uses exactly the runtime's per-operand key accounting;
    /// immutable sharing never reduces this charge. This does not authenticate PKs.
    pub fn key_retained_bytes(ty: Type, verifier: &VerifierKey) -> Result<usize> {
        match ty {
            Type::ProverKey => prover_key_bytes(verifier.metadata().arity()),
            Type::VerifierKey => payload_bytes(ty, verifier.metadata().arity()),
            _ => Err(refused("key-type")),
        }
    }

    /// Upper bound for a successfully decoded canonical public wire value.
    /// No parsing or allocation occurs. Wire length includes the ZKCV envelope.
    /// This is not validation: callers must still decode and check the actual
    /// retained charge (notably storage capacity for tables). Invalid/truncated
    /// bytes need not describe any value. Private values have no wire estimate.
    pub fn wire_retained_bytes_bound(ty: Type, wire_len: usize, policy: &Policy) -> Result<usize> {
        policy.wire(wire_len)?;
        if !ty.is_serializable() {
            return Err(refused("nonserializable"));
        }
        if ty == Type::Matrix {
            // Kind-only conservative estimate uses the widest supported entry backing.
            let bytes = size(wire_len / 12, 40)?;
            policy.output(bytes, usize::MAX)?;
            return Ok(bytes);
        }
        // Canonical framing overhead is smaller than one payload element for
        // each variable-width variant. Division therefore bounds element count.
        let elements = match ty {
            Type::Table | Type::Point | Type::Vector | Type::Polynomial => wire_len / 32,
            Type::Indices => wire_len / 8,
            Type::Groups => wire_len / 48,
            Type::Proof => wire_len / 96,
            Type::Sequence
            | Type::FieldArray
            | Type::FixedVector
            | Type::Variant
            | Type::ResourceUnit
            | Type::Field
            | Type::Matrix
            | Type::Round
            | Type::Group
            | Type::Bool
            | Type::Index
            | Type::Rng
            | Type::Commitment
            | Type::OpeningState
            | Type::ProverKey
            | Type::VerifierKey
            | Type::Nonce
            | Type::Transcript
            | Type::Commitments
            | Type::OpeningStates => 0,
        };
        let bytes = payload_bytes(ty, elements)?;
        policy.output(bytes, usize::MAX)?;
        Ok(bytes)
    }

    /// Domain-aware bound for explicit-binding ingress; views have no codec.
    pub fn typed_wire_retained_bytes_bound(
        ty: PhysicalType,
        wire_len: usize,
        policy: &Policy,
    ) -> Result<usize> {
        if !ty.is_serializable() {
            return Err(refused("nonserializable"));
        }
        if ty.kind() == Type::Groups
            && matches!(
                ty.logical().identity(),
                Identity::Bn254G1 | Identity::Bn254G2
            )
        {
            policy.wire(wire_len)?;
            let (wire, memory) = if ty.logical().identity() == Identity::Bn254G1 {
                (32, std::mem::size_of::<crate::Bn254G1>())
            } else {
                (64, std::mem::size_of::<crate::Bn254G2>())
            };
            let bytes = size(wire_len / wire, memory)?;
            policy.output(bytes, usize::MAX)?;
            return Ok(bytes);
        }
        if ty.logical().identity().is_row_commitment() {
            policy.wire(wire_len)?;
            let bytes = 512usize
                .checked_add(wire_len)
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.output(bytes, usize::MAX)?;
            return Ok(bytes);
        }
        if ty.kind() == Type::Matrix {
            policy.wire(wire_len)?;
            let width = if ty.logical().identity() == Identity::KoalaBear {
                12
            } else {
                40
            };
            let bytes = size(wire_len / width, width)?;
            policy.output(bytes, usize::MAX)?;
            return Ok(bytes);
        }
        if ty.logical().identity() == Identity::KoalaBear {
            policy.wire(wire_len)?;
            let bytes = match ty.kind() {
                Type::Vector | Type::Polynomial => size(wire_len / 4, 4)?,
                Type::Sequence
                | Type::FieldArray
                | Type::FixedVector
                | Type::Variant
                | Type::ResourceUnit
                | Type::Field
                | Type::Matrix
                | Type::Round
                | Type::Table
                | Type::Point
                | Type::Group
                | Type::Groups
                | Type::Bool
                | Type::Index
                | Type::Indices
                | Type::Rng
                | Type::Commitment
                | Type::OpeningState
                | Type::Proof
                | Type::ProverKey
                | Type::VerifierKey
                | Type::Nonce
                | Type::Transcript
                | Type::Commitments
                | Type::OpeningStates => 512,
            };
            policy.output(bytes, usize::MAX)?;
            Ok(bytes)
        } else if ty.logical().identity() == Identity::Ristretto255Group
            && ty.kind() == Type::Groups
        {
            policy.wire(wire_len)?;
            let bytes = size(wire_len / 32, std::mem::size_of::<crate::RistrettoPoint>())?;
            policy.output(bytes, usize::MAX)?;
            Ok(bytes)
        } else {
            Self::wire_retained_bytes_bound(ty.kind(), wire_len, policy)
        }
    }
    pub(crate) fn capability(&self) -> Option<&Capability> {
        match self {
            Self::ResourceUnit(t) => Some(t.capability()),
            Self::Rng(t) | Self::Nonce(t) | Self::Transcript(t) => Some(t),
            // Variants carry resources through active leaves, not a wrapper token.
            Self::Variant(_) | Self::Sequence(_) => None,
            Self::FieldArray(..)
            | Self::FixedVector(..)
            | Self::Bn254Field(..)
            | Self::Bn254Vector(..)
            | Self::Bn254Polynomial(..)
            | Self::Bn254Round(..)
            | Self::Bn254Matrix(..)
            | Self::Bn254G1(..)
            | Self::Bn254G1Vector(..)
            | Self::Bn254Gt(..)
            | Self::Bn254G2(..)
            | Self::Bn254G2Vector(..)
            | Self::OracleRoot(..)
            | Self::OraclePath(..)
            | Self::OracleState(..)
            | Self::OracleRoots(..)
            | Self::OracleStates(..)
            | Self::Index(..)
            | Self::Indices(..)
            | Self::Matrix(..)
            | Self::RistrettoMatrix(..)
            | Self::KoalaBearMatrix(..)
            | Self::KoalaBearExt8Matrix(..)
            | Self::KoalaBearExt8Field(..)
            | Self::KoalaBearExt8Vector(..)
            | Self::KoalaBearExt8Polynomial(..)
            | Self::KoalaBearExt8Round(..)
            | Self::KoalaBearField(..)
            | Self::KoalaBearVector(..)
            | Self::KoalaBearPolynomial(..)
            | Self::KoalaBearRound(..)
            | Self::Vector(..)
            | Self::Polynomial(..)
            | Self::RistrettoField(..)
            | Self::RistrettoVector(..)
            | Self::RistrettoPolynomial(..)
            | Self::RistrettoRound(..)
            | Self::RistrettoGroup(..)
            | Self::RistrettoGroups(..)
            | Self::FrDiagonal(..)
            | Self::RistrettoDiagonal(..)
            | Self::Field(..)
            | Self::Table(..)
            | Self::TableMsb(..)
            | Self::Point(..)
            | Self::Round(..)
            | Self::Bool(..)
            | Self::Commitment(..)
            | Self::OpeningState(..)
            | Self::Proof(..)
            | Self::ProverKey(..)
            | Self::VerifierKey(..)
            | Self::Curve(..)
            | Self::Groups(..) => None,
        }
    }
    /// Bounded host constructor for real G1 public vectors.
    pub fn groups(values: &[zkc_arkworks::GroupPoint], policy: &Policy) -> Result<Self> {
        policy.groups(values.len())?;
        let mut points = Vec::new();
        points
            .try_reserve_exact(values.len())
            .map_err(|_| exhausted("allocation"))?;
        points.extend_from_slice(values);
        Ok(Self::Groups(points.into()))
    }
    pub fn table(values: &[Scalar], policy: &Policy) -> Result<Self> {
        if !values.len().is_power_of_two() {
            return Err(refused("invalid-table-length"));
        }
        policy.table_len(values.len().trailing_zeros() as usize)?;
        Ok(Self::Table(Arc::new(
            Table::from_logical(values, &policy.ark_bounds()).map_err(crate::ark)?,
        )))
    }
    pub fn point(values: Vec<Scalar>, policy: &Policy) -> Result<Self> {
        policy.arity(values.len())?;
        policy.output(size(values.len(), 32)?, usize::MAX)?;
        Ok(Self::Point(values.into()))
    }
}
impl RuntimeValue for Value {
    fn pack_variant(
        descriptor: Arc<zkc_runtime::interactive::VariantDescriptor>,
        alternative: usize,
        payload: Vec<Self>,
    ) -> Result<Self> {
        Ok(Self::Variant(crate::variant::Variant::new(
            descriptor,
            alternative,
            payload,
        )?))
    }
    fn unpack_variant(
        &self,
    ) -> Result<(
        Arc<zkc_runtime::interactive::VariantDescriptor>,
        usize,
        Vec<Self>,
    )> {
        match self {
            Self::Variant(v) => {
                v.validate()?;
                Ok((
                    v.descriptor().clone(),
                    v.alternative(),
                    v.payload().to_vec(),
                ))
            }
            _ => Err(refused("variant-type")),
        }
    }

    fn control_bool(&self) -> Result<bool> {
        match self {
            Self::Bool(v) => Ok(*v),
            _ => Err(refused("local-control-bool")),
        }
    }
    fn control_index(&self) -> Result<u64> {
        match self {
            Self::Index(v) => Ok(*v),
            _ => Err(refused("local-control-index")),
        }
    }
    fn from_control_bool(value: bool) -> Result<Self> {
        Ok(Self::Bool(value))
    }
    fn from_control_index(index: u64) -> Result<Self> {
        Ok(Self::Index(index))
    }

    fn type_name(&self) -> &str {
        self.ty().name()
    }
    fn physical_type(&self) -> PhysicalType {
        if let Self::Sequence(value) = self {
            return value.physical_type().clone();
        }
        // Structural families already retain their checked physical descriptor;
        // do not traverse every inactive variant payload on each invocation.
        if let Self::FieldArray(value) = self {
            return value.physical_type().clone();
        }
        if let Self::FixedVector(value) = self {
            return value.physical_type().clone();
        }
        if let Self::Variant(value) = self {
            return value.physical_type().clone();
        }
        // Public enum wrappers can be mismatched by a host. Classification must
        // remain total before validation; the private issued token owns its type.
        // Core::validate still checks the wrapper kind against the resource store.
        if let Some(token) = self.capability() {
            let logical = if let Some(domain) = token.resource_domain() {
                LogicalType::resource_unit(domain)
            } else {
                LogicalType::new(token.kind(), token.identity()).expect("issued capability type")
            };
            return PhysicalType::default_for(logical).expect("issued capability representation");
        }
        let (kind, identity, representation) = self.type_identity();
        let logical = LogicalType::new(kind, identity).expect("intrinsic payload type");
        PhysicalType::new(logical, representation).expect("intrinsic represented leaf value")
    }

    fn validate_serializable(&self) -> Result<()> {
        if !self.physical_type().is_serializable() {
            return Err(refused("nonserializable"));
        }
        Ok(())
    }
    fn retained_bytes(&self) -> usize {
        // Conservative retained Rust payload, counting shared backing in full.
        match self {
            Self::Rng(_) | Self::Nonce(_) | Self::Transcript(_) => {
                Ok(Self::capability_retained_bytes())
            }
            Self::Sequence(v) => Ok(v.retained_bytes()),
            Self::FieldArray(v) => v.retained_bytes(),
            Self::FixedVector(v) => v.retained_bytes(),
            Self::Variant(v) => Ok(v.retained_bytes()),
            Self::ResourceUnit(_) => Ok(512),
            Self::OracleRoot(..) => Ok(512),
            Self::OraclePath(_, p) | Self::OracleRoots(_, p) => size(p.len(), 32),
            Self::OracleState(s) => s.retained_bytes(),
            Self::OracleStates(_, states) => crate::oracle::states_bytes(states),
            Self::Bn254Matrix(m) => m.retained_bytes(),
            Self::Bn254Vector(v) | Self::Bn254Polynomial(v) => size(v.len(), 32),
            Self::Bn254G1Vector(v) => size(v.len(), std::mem::size_of::<crate::Bn254G1>()),
            Self::Bn254G2Vector(v) => size(v.len(), std::mem::size_of::<crate::Bn254G2>()),
            Self::Indices(v) => size(v.len(), 8),
            Self::Matrix(m) => m.retained_bytes(),
            Self::RistrettoMatrix(m) => m.retained_bytes(),
            Self::KoalaBearMatrix(m) => m.retained_bytes(),
            Self::KoalaBearExt8Matrix(m) => m.retained_bytes(),
            Self::KoalaBearExt8Vector(v) | Self::KoalaBearExt8Polynomial(v) => size(v.len(), 32),
            Self::KoalaBearVector(v) | Self::KoalaBearPolynomial(v) => size(v.len(), 4),
            Self::Vector(v) | Self::Polynomial(v) => size(v.len(), 32),
            Self::RistrettoVector(v) | Self::RistrettoPolynomial(v) => size(v.len(), 32),
            Self::RistrettoGroups(v) => size(v.len(), std::mem::size_of::<crate::RistrettoPoint>()),
            Self::FrDiagonal(d) => d.retained_bytes(),
            Self::RistrettoDiagonal(d) => d.retained_bytes(),
            Self::Table(t) => payload_bytes(Type::Table, t.storage_capacity()),
            Self::TableMsb(t) => payload_bytes(Type::Table, t.storage_capacity()),
            Self::OpeningState(s) => {
                opening_state_bytes(s.original(), s.commitment().metadata().arity())
            }
            Self::Point(p) => payload_bytes(Type::Point, p.len()),
            Self::Groups(p) => payload_bytes(Type::Groups, p.len()),
            Self::Proof(p) => payload_bytes(Type::Proof, p.metadata().arity()),
            Self::ProverKey(k) => prover_key_bytes(k.metadata().arity()),
            Self::VerifierKey(k) => payload_bytes(Type::VerifierKey, k.metadata().arity()),
            Self::Bn254Field(_)
            | Self::Bn254Round(_)
            | Self::Bn254G1(_)
            | Self::Bn254Gt(_)
            | Self::Bn254G2(_)
            | Self::KoalaBearExt8Round(_)
            | Self::KoalaBearExt8Field(_)
            | Self::KoalaBearField(_)
            | Self::KoalaBearRound(_)
            | Self::RistrettoField(_)
            | Self::RistrettoRound(_)
            | Self::RistrettoGroup(_)
            | Self::Field(_)
            | Self::Round(_)
            | Self::Bool(_)
            | Self::Index(_)
            | Self::Commitment(_)
            | Self::Curve(_) => Ok(512),
        }
        .unwrap_or(usize::MAX)
    }
}

// Central payload charge shared by runtime accounting and pre-import bounds.
fn payload_bytes(ty: Type, elements: usize) -> Result<usize> {
    match ty {
        Type::Table | Type::Point | Type::Vector | Type::Polynomial => size(elements, 32),
        Type::Indices => size(elements, 8),
        Type::Groups | Type::VerifierKey => size(elements, 128),
        Type::Proof => size(elements, 192),
        Type::Sequence
        | Type::FieldArray
        | Type::FixedVector
        | Type::Variant
        | Type::ResourceUnit
        | Type::Field
        | Type::Matrix
        | Type::Round
        | Type::Group
        | Type::Bool
        | Type::Index
        | Type::Rng
        | Type::Commitment
        | Type::OpeningState
        | Type::ProverKey
        | Type::Nonce
        | Type::Transcript
        | Type::Commitments
        | Type::OpeningStates => Ok(512),
    }
}

// For the pinned BLS12-381 helper, both basis families have 2^(n+1)-2
// affine points each. 640*2^n + 256 bounds their backing, vector headers,
// generators and key wrapper. Count shared key backing in full for every value.
fn prover_key_bytes(arity: usize) -> Result<usize> {
    u32::try_from(arity)
        .ok()
        .and_then(|n| 1usize.checked_shl(n))
        .ok_or_else(|| exhausted("size-overflow"))
        .and_then(|n| size(n, 640))
}

pub(crate) fn opening_state_bytes(original: &Table, arity: usize) -> Result<usize> {
    size(original.storage_capacity(), 32)?
        .checked_add(prover_key_bytes(arity)?)
        // Commitment, state wrapper and Arc headers. Also charged independently
        // for the public commitment returned by commit; double counting is safe.
        .and_then(|n| n.checked_add(512))
        .ok_or_else(|| exhausted("size-overflow"))
}

#[cfg(test)]
mod admission_size_tests {
    use super::*;
    use crate::{Domain, EntryPolicy, NativeBackend};
    use zkc_arkworks::Keys;

    #[test]
    fn key_estimates_equal_imported_runtime_charges_at_small_ranks() {
        let policy = Policy::default();
        for rank in 1..=3 {
            let keys = Keys::setup_for_development(rank, &policy.ark_bounds()).unwrap();
            let vk_bytes = keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap();
            let vk = VerifierKey::from_bytes(
                &vk_bytes,
                keys.verifier_key().metadata().key_id(),
                &policy.ark_bounds(),
            )
            .unwrap();
            let pk_bytes = keys.prover_key().to_bytes(&policy.ark_bounds()).unwrap();
            let pk = ProverKey::from_bytes(
                &pk_bytes,
                keys.prover_key().material_fingerprint(),
                &vk,
                &policy.ark_bounds(),
            )
            .unwrap();
            assert_eq!(
                Value::key_retained_bytes(Type::ProverKey, &vk).unwrap(),
                Value::ProverKey(Arc::new(pk)).retained_bytes()
            );
            assert_eq!(
                Value::key_retained_bytes(Type::VerifierKey, &vk).unwrap(),
                Value::VerifierKey(Arc::new(vk)).retained_bytes()
            );
        }
        assert!(prover_key_bytes(usize::MAX).is_err());
    }

    #[test]
    fn wire_bounds_cover_actual_decoded_values() {
        let policy = Policy::default();
        let keys = Keys::setup_for_development(2, &policy.ark_bounds()).unwrap();
        let backend = NativeBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "s", "main", None), Some(2)),
            crate::SetupRegistry::new(vec![keys.verifier_key().clone()], &crate::Policy::default())
                .unwrap(),
        )
        .unwrap();
        let mut values = vec![
            Value::Field(Scalar::from(1)),
            Value::Bool(true),
            Value::Curve(crate::GroupPoint::generator()),
            Value::Round([Scalar::from(1); 3]),
        ];
        for rank in 0..=3 {
            values.push(Value::table(&vec![Scalar::from(1); 1 << rank], &policy).unwrap());
            values.push(Value::point(vec![Scalar::from(1); rank], &policy).unwrap());
            values
                .push(Value::groups(&vec![crate::GroupPoint::generator(); rank], &policy).unwrap());
        }
        let t = Value::table(&[Scalar::from(1); 4], &policy).unwrap();
        let Value::Table(t) = t else { unreachable!() };
        let committed = keys.prover_key().commit(&t).unwrap();
        let (_, proof) = committed.open(&[Scalar::from(2); 2]).unwrap();
        values.push(Value::Commitment(Arc::new(committed.commitment().clone())));
        values.push(Value::Proof(Arc::new(proof)));
        for value in values {
            if !crate::has_native_wire(&value.physical_type()) {
                assert!(backend.encode_native_value(&value).is_err());
                continue;
            }
            let bytes = backend.encode_native_value(&value).unwrap();
            let decoded = backend
                .decode_native_value(&value.physical_type(), &bytes)
                .unwrap();
            assert_eq!(
                Value::wire_retained_bytes_bound(value.ty(), bytes.len(), &policy).unwrap(),
                decoded.retained_bytes(),
                "{:?}",
                value.ty()
            );
        }
        assert!(Value::wire_retained_bytes_bound(Type::ProverKey, 0, &policy).is_err());
        assert!(Value::wire_retained_bytes_bound(Type::Table, usize::MAX, &policy).is_err());
    }
}
