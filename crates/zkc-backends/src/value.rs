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
/// Trusted variants; clones retain immutable backing. Public proof/commitment
/// variants never carry private opening custody. No token deserializer exists.
#[derive(Clone, Debug)]
pub enum Value {
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
    /// Visit only active leaves, preserving their exact capability handles.
    pub(crate) fn active_leaves(&self) -> Vec<&Self> {
        fn visit<'a>(v: &'a Value, out: &mut Vec<&'a Value>) {
            if let Value::Variant(v) = v {
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
        match self {
            Self::Variant(_) => Type::Variant,
            Self::ResourceUnit(_) => Type::ResourceUnit,
            Self::Bn254Field(_) => Type::Field,
            Self::Bn254Vector(_) => Type::Vector,
            Self::Bn254Polynomial(_) => Type::Polynomial,
            Self::Bn254Round(_) => Type::Round,
            Self::Bn254Matrix(_) => Type::Matrix,
            Self::Bn254G1(_) => Type::Group,
            Self::Bn254G1Vector(_) => Type::Groups,
            Self::Bn254G2(_) => Type::Group,
            Self::Bn254G2Vector(_) => Type::Groups,
            Self::OracleRoot(..) => Type::Commitment,
            Self::OraclePath(..) => Type::Proof,
            Self::OracleState(_) => Type::OpeningState,
            Self::OracleRoots(..) => Type::Commitments,
            Self::OracleStates(..) => Type::OpeningStates,
            Self::KoalaBearExt8Matrix(_) => Type::Matrix,
            Self::KoalaBearExt8Round(_) => Type::Round,
            Self::KoalaBearExt8Polynomial(_) => Type::Polynomial,
            Self::KoalaBearExt8Vector(_) => Type::Vector,
            Self::KoalaBearExt8Field(_) => Type::Field,
            Self::Matrix(_) | Self::RistrettoMatrix(_) | Self::KoalaBearMatrix(_) => Type::Matrix,
            Self::KoalaBearField(_) => Type::Field,
            Self::KoalaBearVector(_) => Type::Vector,
            Self::KoalaBearPolynomial(_) => Type::Polynomial,
            Self::KoalaBearRound(_) => Type::Round,
            Self::Vector(_) | Self::RistrettoVector(_) | Self::FrDiagonal(_) => Type::Vector,
            Self::Polynomial(_) | Self::RistrettoPolynomial(_) => Type::Polynomial,
            Self::RistrettoField(_) => Type::Field,
            Self::RistrettoRound(_) => Type::Round,
            Self::RistrettoGroup(_) => Type::Group,
            Self::RistrettoGroups(_) | Self::RistrettoDiagonal(_) => Type::Groups,
            Self::Field(_) => Type::Field,
            Self::Table(_) | Self::TableMsb(_) => Type::Table,
            Self::Point(_) => Type::Point,
            Self::Round(_) => Type::Round,
            Self::Bool(_) => Type::Bool,
            Self::Index(_) => Type::Index,
            Self::Indices(_) => Type::Indices,
            Self::Rng(_) => Type::Rng,
            Self::Commitment(_) => Type::Commitment,
            Self::OpeningState(_) => Type::OpeningState,
            Self::Proof(_) => Type::Proof,
            Self::ProverKey(_) => Type::ProverKey,
            Self::VerifierKey(_) => Type::VerifierKey,
            Self::Nonce(_) => Type::Nonce,
            Self::Transcript(_) => Type::Transcript,
            Self::Curve(_) => Type::Group,
            Self::Groups(_) => Type::Groups,
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
            _ => 0,
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
                _ => 512,
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
            _ => None,
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
    fn from_control_index(index: u64) -> Result<Self> {
        Ok(Self::Index(index))
    }

    fn type_name(&self) -> &str {
        self.ty().name()
    }
    fn physical_type(&self) -> PhysicalType {
        if let Self::Variant(v) = self {
            return PhysicalType::default_for(LogicalType::variant(v.descriptor().clone()));
        }
        if let Self::ResourceUnit(token) = self {
            return PhysicalType::default_for(LogicalType::resource_unit(token.domain()));
        }
        let identity = match self {
            Self::Bn254Field(_)
            | Self::Bn254Vector(_)
            | Self::Bn254Polynomial(_)
            | Self::Bn254Round(_)
            | Self::Bn254Matrix(_) => Identity::Bn254Fr,
            Self::Bn254G1(_) | Self::Bn254G1Vector(_) => Identity::Bn254G1,
            Self::Bn254G2(_) | Self::Bn254G2Vector(_) => Identity::Bn254G2,
            Self::OracleRoot(d, _)
            | Self::OraclePath(d, _)
            | Self::OracleRoots(d, _)
            | Self::OracleStates(d, _) => d.identity(),
            Self::OracleState(s) => s.domain().identity(),
            Self::KoalaBearExt8Field(_)
            | Self::KoalaBearExt8Vector(_)
            | Self::KoalaBearExt8Polynomial(_)
            | Self::KoalaBearExt8Round(_)
            | Self::KoalaBearExt8Matrix(_) => Identity::KoalaBearExt8,
            Self::KoalaBearMatrix(_)
            | Self::KoalaBearField(_)
            | Self::KoalaBearVector(_)
            | Self::KoalaBearPolynomial(_)
            | Self::KoalaBearRound(_) => Identity::KoalaBear,
            Self::RistrettoMatrix(_)
            | Self::RistrettoField(_)
            | Self::RistrettoVector(_)
            | Self::RistrettoPolynomial(_)
            | Self::RistrettoRound(_) => Identity::Ristretto255Scalar,
            Self::RistrettoGroup(_) | Self::RistrettoGroups(_) | Self::RistrettoDiagonal(_) => {
                Identity::Ristretto255Group
            }
            Self::Rng(t) | Self::Nonce(t) | Self::Transcript(t) => t.identity(),
            Self::Bool(_) | Self::Index(_) | Self::Indices(_) => Identity::None,
            Self::Curve(_) | Self::Groups(_) => Identity::Bls12381G1,

            Self::Commitment(_)
            | Self::Proof(_)
            | Self::ProverKey(_)
            | Self::VerifierKey(_)
            | Self::OpeningState(_) => Identity::MultilinearKzgBls12381,
            _ => Identity::Bls12381Fr,
        };
        let logical = LogicalType::new(self.ty(), identity).expect("intrinsic payload type");
        if matches!(self, Self::FrDiagonal(_)) {
            PhysicalType::new(logical, Representation::FrDiagonal).expect("intrinsic diagonal")
        } else if matches!(self, Self::RistrettoDiagonal(_)) {
            PhysicalType::new(logical, Representation::RistrettoDiagonal)
                .expect("intrinsic diagonal")
        } else if matches!(self, Self::TableMsb(_)) {
            PhysicalType::new(logical, Representation::TableMsb).expect("MSB table representation")
        } else {
            PhysicalType::default_for(logical)
        }
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
            _ => payload_bytes(self.ty(), 0),
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
        _ => Ok(512),
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
    use crate::{Domain, EntryPolicy, NativeBackend, PublicInputs};
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
            EntryPolicy::new(
                Domain::new("P", "s", "main", None),
                Some(2),
                PublicInputs::LocalOnly,
            ),
            Some(keys.verifier_key().clone()),
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
            let bytes = backend.encode_value(&value).unwrap();
            let decoded = backend
                .decode_typed_value(value.physical_type(), &bytes)
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
