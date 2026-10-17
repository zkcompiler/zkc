//! Merkle row commitments generic over leaf hash, compression and digest word.
//!
//! An [`Instance`] supplies one leaf hash, one two-to-one compression, the
//! committed element type and the canonical byte encoding of its digests;
//! Plonky3 0.8.0's `Mmcs` implementation owns tree construction, single and
//! pruned multi-openings and verification. Every carrier above the instance
//! holds digests as fixed-width byte strings, so a byte hash (a Keccak, SHA-2
//! or BLAKE2 instance) installs a hash and compression pair and a nominal
//! identity, not new values, codecs or operations. Nothing here assumes a
//! field digest, a two-adic field or a characteristic other than two.
//!
//! This adapter owns admission: shape, positions, widths, digest encodings,
//! resource preflight and the custody of prover trees. The verifier's expected
//! shape and positions never come from a proof. Authentication says nothing
//! about degree, relation satisfaction, hiding or extraction. See
//! docs/spec/domains/oracles.md for the tree, proof layout and hash calls.
pub mod poseidon2;

use crate::plonky3::oracle::Shape;
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use p3_commit::Mmcs;
use p3_matrix::{Dimensions, dense::RowMajorMatrix};
use std::sync::Arc;
use zkc_runtime::interactive::{
    AttributeRule, Backing, BoundSignature, Identity, Invocation, KernelSignature, LogicalType,
    OperationBinding, PhysicalType, Type,
};

/// One word of a digest, with its canonical byte encoding.
pub trait DigestWord: Copy + Default + Eq + Send + Sync + std::fmt::Debug + 'static {
    const BYTES: usize;
    fn write(self, out: &mut Vec<u8>);
    /// `None` when the bytes are not the canonical encoding of a word.
    fn read(bytes: &[u8]) -> Option<Self>;
}
impl DigestWord for u8 {
    const BYTES: usize = 1;
    fn write(self, out: &mut Vec<u8>) {
        out.push(self);
    }
    fn read(bytes: &[u8]) -> Option<Self> {
        match bytes {
            [byte] => Some(*byte),
            _ => None,
        }
    }
}
impl DigestWord for crate::KoalaBear {
    const BYTES: usize = 4;
    fn write(self, out: &mut Vec<u8>) {
        use crate::plonky3::words;
        out.extend_from_slice(&words::encode_word(self, words::Form::Canonical));
    }
    fn read(bytes: &[u8]) -> Option<Self> {
        use crate::plonky3::words;
        words::decode_word(bytes.try_into().ok()?, words::Form::Canonical)
    }
}

/// Concatenated digests, each word in its canonical encoding.
pub fn encode_digests<W: DigestWord, const N: usize>(digests: &[[W; N]]) -> Vec<u8> {
    let mut out = Vec::with_capacity(digests.len() * N * W::BYTES);
    for word in digests.iter().flatten() {
        word.write(&mut out);
    }
    out
}
/// `None` unless the bytes are whole digests of canonical words.
pub fn decode_digests<W: DigestWord, const N: usize>(bytes: &[u8]) -> Option<Vec<[W; N]>> {
    let width = N * W::BYTES;
    if width == 0 || !bytes.len().is_multiple_of(width) {
        return None;
    }
    let mut digests = Vec::new();
    digests.try_reserve_exact(bytes.len() / width).ok()?;
    for digest in bytes.chunks_exact(width) {
        let mut words = [W::default(); N];
        for (word, encoded) in words.iter_mut().zip(digest.chunks_exact(W::BYTES)) {
            *word = W::read(encoded)?;
        }
        digests.push(words);
    }
    Some(digests)
}

type Commitment<I> = <<I as Instance>::Mmcs as Mmcs<<I as Instance>::Element>>::Commitment;
type MultiProof<I> = <<I as Instance>::Mmcs as Mmcs<<I as Instance>::Element>>::MultiProof;
type ProverData<I> = <<I as Instance>::Mmcs as Mmcs<<I as Instance>::Element>>::ProverData<
    RowMajorMatrix<<I as Instance>::Element>,
>;

/// One installed leaf hash and compression over one element type.
pub trait Instance: 'static {
    type Element: Copy + Default + PartialEq + Send + Sync + std::fmt::Debug + 'static;
    type Mmcs: Mmcs<Self::Element> + Sync + 'static;
    /// Bytes of one encoded digest; also its in-memory width.
    const DIGEST_BYTES: usize;
    fn mmcs() -> &'static Self::Mmcs;
    fn root(commitment: &Commitment<Self>) -> Vec<u8>;
    fn commitment(root: &[u8]) -> Option<Commitment<Self>>;
    fn proof_bytes(proof: &MultiProof<Self>) -> Vec<u8>;
    fn proof(bytes: &[u8]) -> Option<MultiProof<Self>>;
    /// Whether the bytes are whole canonical digests.
    fn valid_digests(bytes: &[u8]) -> bool;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// An empty position list: there is nothing to open or authenticate.
    Positions,
    Coordinate,
    ValueCount,
    ByteLimit,
}

/// Prover-private immutable tree custody. No deserializer or public-root
/// constructor exists; sharing an `Arc` to it does not copy the table.
pub struct Tree<I: Instance> {
    shape: Shape,
    data: ProverData<I>,
}
impl<I: Instance> std::fmt::Debug for Tree<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MerkleTree")
            .field("shape", &self.shape)
            .finish_non_exhaustive()
    }
}
impl<I: Instance> Tree<I> {
    pub fn shape(&self) -> Shape {
        self.shape
    }
}

/// Conservative live table/tree bytes, excluding caller-owned input copies.
pub fn retained_bytes<I: Instance>(shape: Shape) -> Option<usize> {
    shape
        .elements()
        .checked_mul(std::mem::size_of::<I::Element>())?
        .checked_add(
            shape
                .height()
                .checked_next_power_of_two()?
                .checked_mul(2)?
                .checked_sub(1)?
                .checked_mul(I::DIGEST_BYTES)?,
        )?
        .checked_add(256)
}

/// Positions are checked before the upstream prover, which asserts them.
fn positions(shape: Shape, positions: &[usize]) -> std::result::Result<(), Error> {
    if positions.is_empty() {
        return Err(Error::Positions);
    }
    if positions.iter().any(|p| *p >= shape.height()) {
        return Err(Error::Coordinate);
    }
    Ok(())
}

pub fn commit<I: Instance>(
    values: Vec<I::Element>,
    shape: Shape,
    max_bytes: usize,
) -> std::result::Result<(Vec<u8>, Tree<I>), Error> {
    if values.len() != shape.elements() {
        return Err(Error::ValueCount);
    }
    if retained_bytes::<I>(shape).is_none_or(|bytes| bytes > max_bytes) {
        return Err(Error::ByteLimit);
    }
    let (commitment, data) = I::mmcs().commit(vec![RowMajorMatrix::new(values, shape.width())]);
    Ok((I::root(&commitment), Tree { shape, data }))
}

/// The rows at `positions`, in position order with duplicates, and one pruned
/// proof for the distinct positions. One position gives its full path.
pub fn open<I: Instance>(
    tree: &Tree<I>,
    at: &[usize],
) -> std::result::Result<(Vec<I::Element>, Vec<u8>), Error> {
    positions(tree.shape, at)?;
    let (opened, proof) = I::mmcs().open_multi_batch(at, &tree.data);
    let mut rows = Vec::with_capacity(at.len() * tree.shape.width());
    for mut query in opened {
        rows.extend(query.pop().ok_or(Error::ValueCount)?);
    }
    Ok((rows, I::proof_bytes(&proof)))
}

/// `Err` only for an invalid verifier request; every malformed or false
/// opening, including a wrong row count or digest encoding, is `Ok(false)`.
pub fn verify<I: Instance>(
    root: &[u8],
    shape: Shape,
    at: &[usize],
    rows: &[I::Element],
    proof: &[u8],
) -> std::result::Result<bool, Error> {
    positions(shape, at)?;
    if at.len().checked_mul(shape.width()) != Some(rows.len()) {
        return Ok(false);
    }
    let (Some(commitment), Some(proof)) = (I::commitment(root), I::proof(proof)) else {
        return Ok(false);
    };
    let opened: Vec<Vec<Vec<I::Element>>> = rows
        .chunks_exact(shape.width())
        .map(|row| vec![row.to_vec()])
        .collect();
    let dimensions = [Dimensions {
        width: shape.width(),
        height: shape.height(),
    }];
    Ok(I::mmcs()
        .verify_multi_batch(&commitment, &dimensions, at, &opened, &proof)
        .is_ok())
}

/// Installed instances, each a nominal row-commitment scheme.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scheme {
    Poseidon2KoalaBear,
}
impl Scheme {
    pub fn identity(self) -> Identity {
        match self {
            Self::Poseidon2KoalaBear => Identity::MerklePoseidon2KoalaBear,
        }
    }
    pub fn from_identity(identity: Identity) -> Option<Self> {
        match identity {
            Identity::MerklePoseidon2KoalaBear => Some(Self::Poseidon2KoalaBear),
            _ => None,
        }
    }
    fn of_binding(binding: &OperationBinding) -> Option<Self> {
        match binding.arguments.as_slice() {
            [scheme] => Self::from_identity(Identity::parse(scheme).ok()?),
            _ => None,
        }
    }
    /// The committed value field.
    pub fn field(self) -> Identity {
        match self {
            Self::Poseidon2KoalaBear => Identity::KoalaBear,
        }
    }
    pub fn digest_bytes(self) -> usize {
        match self {
            Self::Poseidon2KoalaBear => poseidon2::Base::DIGEST_BYTES,
        }
    }
    fn element_bytes(self) -> usize {
        match self {
            Self::Poseidon2KoalaBear => std::mem::size_of::<crate::KoalaBear>(),
        }
    }
    /// Whether the bytes are whole digests in this scheme's canonical encoding.
    pub fn valid_digests(self, bytes: &[u8]) -> bool {
        match self {
            Self::Poseidon2KoalaBear => poseidon2::Base::valid_digests(bytes),
        }
    }
    fn physical(self, kind: Type) -> Option<PhysicalType> {
        let identity = match kind {
            Type::Index | Type::Indices | Type::Bool => Identity::None,
            Type::Vector => self.field(),
            _ => self.identity(),
        };
        PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok()
    }
}

#[derive(Clone, Debug)]
pub enum State {
    Poseidon2KoalaBear(Arc<Tree<poseidon2::Base>>),
}
impl State {
    pub fn scheme(&self) -> Scheme {
        match self {
            Self::Poseidon2KoalaBear(_) => Scheme::Poseidon2KoalaBear,
        }
    }
    pub fn shape(&self) -> Shape {
        match self {
            Self::Poseidon2KoalaBear(tree) => tree.shape(),
        }
    }
    pub fn retained_bytes(&self) -> Result<usize> {
        match self {
            Self::Poseidon2KoalaBear(tree) => retained_bytes::<poseidon2::Base>(tree.shape()),
        }
        .ok_or_else(|| exhausted("oracle-byte-limit"))
    }
    /// The committed table and tree, shared by every handle to this state.
    pub(crate) fn backing(&self) -> Result<Backing> {
        let bytes = self.retained_bytes()?;
        Ok(match self {
            Self::Poseidon2KoalaBear(tree) => Backing::of(tree, bytes),
        })
    }
    /// Bytes `count` openings read: their rows and at most their full paths.
    pub(crate) fn opening_bytes(&self, count: usize) -> Result<usize> {
        let scheme = self.scheme();
        let shape = self.shape();
        let row = shape
            .width()
            .checked_mul(scheme.element_bytes())
            .and_then(|row| row.checked_add(shape.depth().checked_mul(scheme.digest_bytes())?))
            .ok_or_else(|| exhausted("size-overflow"))?;
        size(count, row)
    }
}

fn failure(error: Error) -> zkc_runtime::interactive::BackendError {
    match error {
        Error::ByteLimit => exhausted("oracle-byte-limit"),
        Error::Positions => refused("oracle-positions"),
        Error::Coordinate => refused("oracle-coordinate"),
        Error::ValueCount => refused("oracle-value-count"),
    }
}

/// Independent native advertisement for the shared row-oracle contracts and
/// the multi-opening contracts, for this family's schemes only.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::*;
    let scheme = Scheme::of_binding(binding)?;
    if binding.implementation != format!("plonky3/{}", binding.contract) {
        return None;
    }
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "oracle.commit" => (&[Vector, Index], &[Commitment, OpeningState]),
        "oracle.open" => (&[OpeningState, Index], &[Vector, Proof]),
        "oracle.check" => (&[Commitment, Index, Index, Index, Vector, Proof], &[Bool]),
        "oracle.open_many" => (&[OpeningState, Indices], &[Vector, Proof]),
        "oracle.check_many" => (&[Commitment, Index, Index, Indices, Vector, Proof], &[Bool]),
        "commitments.empty" => (&[], &[Commitments]),
        "commitments.append" => (&[Commitments, Commitment], &[Commitments]),
        "commitments.at" => (&[Commitments, Index], &[Commitment]),
        "commitments.length" => (&[Commitments], &[Index]),
        "opening_states.empty" => (&[], &[OpeningStates]),
        "opening_states.append" => (&[OpeningStates, OpeningState], &[OpeningStates]),
        "opening_states.at" => (&[OpeningStates, Index], &[OpeningState]),
        "opening_states.length" => (&[OpeningStates], &[Index]),
        _ => return None,
    };
    Some(KernelSignature {
        inputs: inputs
            .iter()
            .map(|t| scheme.physical(*t))
            .collect::<Option<_>>()?,
        outputs: outputs
            .iter()
            .map(|t| scheme.physical(*t))
            .collect::<Option<_>>()?,
        attributes: AttributeRule::None,
    })
}

fn index(v: &Value) -> Result<usize> {
    if let Value::Index(n) = v {
        usize::try_from(*n).map_err(|_| refused("oracle-coordinate"))
    } else {
        Err(refused("oracle-operands"))
    }
}
fn indices(v: &Value) -> Result<Vec<usize>> {
    let Value::Indices(values) = v else {
        return Err(refused("oracle-operands"));
    };
    values
        .iter()
        .map(|n| usize::try_from(*n).map_err(|_| refused("oracle-coordinate")))
        .collect()
}
fn table_shape(width: usize, height: usize, policy: &Policy) -> Result<Shape> {
    Shape::new(width, height, policy.max_table_elements.min(1 << 20)).map_err(|error| {
        use crate::plonky3::oracle::Error as E;
        match error {
            E::ElementLimit => exhausted("oracle-element-limit"),
            _ => refused("oracle-shape"),
        }
    })
}
fn digest(scheme: Scheme, value: &Value) -> Option<Arc<[u8]>> {
    match value {
        Value::MerkleDigest(s, root) if *s == scheme => Some(root.clone()),
        _ => None,
    }
}

/// Opening several positions allocates their rows and at most one full path
/// per distinct position; the actual pruned proof is never larger.
fn open_outputs(state: &State, count: usize, policy: &Policy, available: usize) -> Result<()> {
    let scheme = state.scheme();
    let shape = state.shape();
    let elements = count
        .checked_mul(shape.width())
        .ok_or_else(|| exhausted("size-overflow"))?;
    policy.vector_width(elements, scheme.element_bytes())?;
    let proof = count
        .checked_mul(shape.depth())
        .ok_or_else(|| exhausted("size-overflow"))?;
    policy.vector_width(proof, scheme.digest_bytes())?;
    policy.output(
        size(elements, scheme.element_bytes())?
            .checked_add(size(proof, scheme.digest_bytes())?)
            .ok_or_else(|| exhausted("size-overflow"))?,
        available,
    )
}

fn open_state(
    state: &State,
    at: &[usize],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    open_outputs(state, at.len(), policy, available)?;
    let scheme = state.scheme();
    Ok(match state {
        State::Poseidon2KoalaBear(tree) => {
            let (rows, proof) = open(tree, at).map_err(failure)?;
            vec![
                Value::KoalaBearVector(rows.into()),
                Value::MerkleProof(scheme, proof.into()),
            ]
        }
    })
}

#[allow(clippy::too_many_arguments)]
fn check_state(
    scheme: Scheme,
    root: &[u8],
    width: usize,
    height: usize,
    at: &[usize],
    rows: &Value,
    proof: &[u8],
    policy: &Policy,
) -> Result<bool> {
    let shape = table_shape(width, height, policy)?;
    let result = match (scheme, rows) {
        (Scheme::Poseidon2KoalaBear, Value::KoalaBearVector(rows)) => {
            verify::<poseidon2::Base>(root, shape, at, rows, proof)
        }
        _ => return Err(refused("oracle-operands")),
    };
    result.map_err(failure)
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let scheme = invocation
        .binding
        .declaration()
        .arguments
        .first()
        .and_then(|s| Identity::parse(s).ok())
        .and_then(Scheme::from_identity)
        .ok_or_else(|| refused("oracle-domain"))?;
    let available = invocation.max_output_bytes;
    let digest_bytes = scheme.digest_bytes();
    let outputs = match (name, args) {
        ("oracle.commit", [Value::KoalaBearVector(values), width])
            if scheme == Scheme::Poseidon2KoalaBear =>
        {
            let width = index(width)?;
            if width == 0 || !values.len().is_multiple_of(width) {
                return Err(refused("oracle-shape"));
            }
            let shape = table_shape(width, values.len() / width, policy)?;
            let bytes = retained_bytes::<poseidon2::Base>(shape)
                .ok_or_else(|| exhausted("oracle-byte-limit"))?;
            policy.output(
                bytes
                    .checked_add(size(1, digest_bytes)?)
                    .ok_or_else(|| exhausted("size-overflow"))?,
                available,
            )?;
            let (root, tree) =
                commit::<poseidon2::Base>(values.to_vec(), shape, policy.max_value_bytes)
                    .map_err(failure)?;
            vec![
                Value::MerkleDigest(scheme, root.into()),
                Value::MerkleTree(State::Poseidon2KoalaBear(Arc::new(tree))),
            ]
        }
        ("oracle.open", [Value::MerkleTree(state), at]) if state.scheme() == scheme => {
            open_state(state, &[index(at)?], policy, available)?
        }
        ("oracle.open_many", [Value::MerkleTree(state), at]) if state.scheme() == scheme => {
            open_state(state, &indices(at)?, policy, available)?
        }
        (
            "oracle.check" | "oracle.check_many",
            [root, width, height, at, rows, Value::MerkleProof(p, proof)],
        ) if *p == scheme => {
            policy.output(512, available)?;
            let root = digest(scheme, root).ok_or_else(|| refused("oracle-operands"))?;
            let at = if name == "oracle.check" {
                vec![index(at)?]
            } else {
                indices(at)?
            };
            let (width, height) = (index(width)?, index(height)?);
            vec![Value::Bool(check_state(
                scheme, &root, width, height, &at, rows, proof, policy,
            )?)]
        }
        ("commitments.empty", []) => {
            policy.output(256, available)?;
            vec![Value::MerkleDigests(scheme, Arc::from([]))]
        }
        ("commitments.append", [Value::MerkleDigests(s, roots), Value::MerkleDigest(r, root)])
            if *s == scheme && *r == scheme =>
        {
            let length = roots
                .len()
                .checked_add(root.len())
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.vector_width(length / digest_bytes, digest_bytes)?;
            policy.output(size(length, 1)?, available)?;
            let mut result = crate::kernels::arithmetic::reserve(length)?;
            result.extend_from_slice(roots);
            result.extend_from_slice(root);
            vec![Value::MerkleDigests(scheme, result.into())]
        }
        ("commitments.at", [Value::MerkleDigests(s, roots), at]) if *s == scheme => {
            policy.output(512, available)?;
            let at = index(at)?;
            let root = at
                .checked_mul(digest_bytes)
                .and_then(|start| roots.get(start..start.checked_add(digest_bytes)?))
                .ok_or_else(|| refused("oracle-coordinate"))?;
            vec![Value::MerkleDigest(scheme, root.into())]
        }
        ("commitments.length", [Value::MerkleDigests(s, roots)]) if *s == scheme => {
            vec![Value::Index((roots.len() / digest_bytes) as u64)]
        }
        ("opening_states.empty", []) => {
            policy.output(256, available)?;
            vec![Value::MerkleTrees(scheme, Arc::from([]))]
        }
        ("opening_states.append", [Value::MerkleTrees(s, states), Value::MerkleTree(state)])
            if *s == scheme && state.scheme() == scheme =>
        {
            let length = states
                .len()
                .checked_add(1)
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.vector_width(length, std::mem::size_of::<State>())?;
            let bytes = states_bytes(states)?
                .checked_add(state.retained_bytes()?)
                .and_then(|n| n.checked_add(std::mem::size_of::<State>()))
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.output(bytes, usize::MAX)?;
            // Existing trees are shared; only the new list of handles is allocated.
            policy.output(size(length, std::mem::size_of::<State>())?, available)?;
            let mut result = crate::kernels::arithmetic::reserve(length)?;
            result.extend_from_slice(states);
            result.push(state.clone());
            vec![Value::MerkleTrees(scheme, result.into())]
        }
        ("opening_states.at", [Value::MerkleTrees(s, states), at]) if *s == scheme => {
            let state = states
                .get(index(at)?)
                .ok_or_else(|| refused("oracle-coordinate"))?;
            policy.output(state.retained_bytes()?, usize::MAX)?;
            vec![Value::MerkleTree(state.clone())]
        }
        ("opening_states.length", [Value::MerkleTrees(s, states)]) if *s == scheme => {
            vec![Value::Index(states.len() as u64)]
        }
        _ => return Err(refused("oracle-operands")),
    };
    Ok(outputs)
}

pub(crate) fn states_bytes(states: &[State]) -> Result<usize> {
    states.iter().try_fold(
        size(states.len(), std::mem::size_of::<State>())?,
        |sum, state| {
            sum.checked_add(state.retained_bytes()?)
                .ok_or_else(|| exhausted("size-overflow"))
        },
    )
}
/// The list's handle slots, which hold no table data.
pub(crate) fn states_list(states: &Arc<[State]>) -> Result<Backing> {
    Ok(Backing::of(
        states,
        size(states.len(), std::mem::size_of::<State>())?,
    ))
}
/// Report the list and, when it is newly retained, each distinct tree.
pub(crate) fn states_parts(
    states: &Arc<[State]>,
    shared: &mut dyn FnMut(Backing) -> bool,
) -> Result<usize> {
    if shared(states_list(states)?) {
        for state in states.iter() {
            shared(state.backing()?);
        }
    }
    Ok(0)
}

/// Digest bytes of a public value, or `None` when the value is not this
/// family's root or proof.
pub(crate) fn wire_digests(value: &Value) -> Option<(Scheme, &[u8])> {
    match value {
        Value::MerkleDigest(scheme, bytes) | Value::MerkleProof(scheme, bytes) => {
            Some((*scheme, bytes))
        }
        _ => None,
    }
}

/// The ZKCV frame of a root (`tag, digest`) or proof (`tag, count:u32,
/// digests`); the bulk codec checks limits and stamps the final tag.
pub(crate) fn encode(value: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (scheme, bytes) = wire_digests(value)?;
    let root = matches!(value, Value::MerkleDigest(..));
    Some((|| {
        validate(value, policy)?;
        let length = bytes
            .len()
            .checked_add(if root { 6 } else { 10 })
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(length)?;
        let mut out = crate::kernels::arithmetic::reserve(length)?;
        out.extend_from_slice(b"ZKCV\x00");
        out.push(if root { 71 } else { 72 });
        if !root {
            let count = u32::try_from(bytes.len() / scheme.digest_bytes())
                .map_err(|_| exhausted("element-limit"))?;
            out.extend(count.to_le_bytes());
        }
        out.extend_from_slice(bytes);
        Ok(out)
    })())
}

/// Validate a carrier's digest bytes: whole canonical digests, and exactly one
/// for a root.
pub(crate) fn validate(value: &Value, policy: &Policy) -> Result<()> {
    let (scheme, bytes, root) = match value {
        Value::MerkleDigest(scheme, bytes) => (*scheme, bytes, true),
        Value::MerkleProof(scheme, bytes) | Value::MerkleDigests(scheme, bytes) => {
            (*scheme, bytes, false)
        }
        _ => return Ok(()),
    };
    let digest_bytes = scheme.digest_bytes();
    if !bytes.len().is_multiple_of(digest_bytes) || (root && bytes.len() != digest_bytes) {
        return Err(refused("oracle-digest"));
    }
    policy.vector_width(bytes.len() / digest_bytes, digest_bytes)?;
    if !scheme.valid_digests(bytes) {
        return Err(refused("oracle-digest"));
    }
    Ok(())
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("plonky3/oracle.open_many", "oracle.open_many"),
    ("plonky3/oracle.check_many", "oracle.check_many"),
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KoalaBear;
    use p3_field::PrimeCharacteristicRing;

    fn table(width: usize, height: usize) -> Vec<KoalaBear> {
        (0..width * height)
            .map(|i| KoalaBear::from_usize(1 + i * 7))
            .collect()
    }

    #[test]
    fn single_and_multiple_openings_verify_against_the_expected_shape() {
        for height in [1, 2, 3, 5, 8, 13, 32] {
            for width in [1, 3, 8, 9] {
                let shape = Shape::new(width, height, 1 << 12).unwrap();
                let values = table(width, height);
                let (root, tree) =
                    commit::<poseidon2::Base>(values.clone(), shape, 1 << 24).unwrap();
                assert_eq!(root.len(), 32);
                let row = |i: usize| values[i * width..(i + 1) * width].to_vec();
                for i in 0..height {
                    let (rows, proof) = open(&tree, &[i]).unwrap();
                    assert_eq!(rows, row(i));
                    assert_eq!(proof.len(), 32 * shape.depth());
                    assert_eq!(
                        verify::<poseidon2::Base>(&root, shape, &[i], &rows, &proof),
                        Ok(true)
                    );
                }
                let at: Vec<usize> = (0..height).rev().chain([0, height - 1]).collect();
                let (rows, proof) = open(&tree, &at).unwrap();
                let expected: Vec<KoalaBear> = at.iter().flat_map(|&i| row(i)).collect();
                assert_eq!(rows, expected);
                // Every leaf is queried, so only padding digests are sent; a
                // power-of-two height has none.
                if height.is_power_of_two() {
                    assert!(proof.is_empty());
                }
                assert_eq!(
                    verify::<poseidon2::Base>(&root, shape, &at, &rows, &proof),
                    Ok(true)
                );
            }
        }
    }

    #[test]
    fn malformed_openings_are_false_and_invalid_requests_refuse() {
        let shape = Shape::new(2, 16, 1 << 12).unwrap();
        let values = table(2, 16);
        let (root, tree) = commit::<poseidon2::Base>(values, shape, 1 << 24).unwrap();
        let at = [1, 6, 6, 11];
        let (rows, proof) = open(&tree, &at).unwrap();
        let check = |root: &[u8], at: &[usize], rows: &[KoalaBear], proof: &[u8]| {
            verify::<poseidon2::Base>(root, shape, at, rows, proof)
        };
        assert_eq!(check(&root, &at, &rows, &proof), Ok(true));
        // A changed row, a different position, a short or long proof, a
        // changed digest, a changed root, inconsistent duplicates and a wrong
        // row count are all authentication failures.
        let mut changed = rows.clone();
        changed[0] += KoalaBear::ONE;
        assert_eq!(check(&root, &at, &changed, &proof), Ok(false));
        assert_eq!(check(&root, &[2, 6, 6, 11], &rows, &proof), Ok(false));
        assert_eq!(
            check(&root, &at, &rows, &proof[..proof.len() - 32]),
            Ok(false)
        );
        let mut longer = proof.clone();
        longer.extend_from_slice(&proof[..32]);
        assert_eq!(check(&root, &at, &rows, &longer), Ok(false));
        let mut digest = proof.clone();
        digest[0] ^= 1;
        assert_eq!(check(&root, &at, &rows, &digest), Ok(false));
        let mut other = root.clone();
        other[4] ^= 1;
        assert_eq!(check(&other, &at, &rows, &proof), Ok(false));
        let mut duplicate = rows.clone();
        duplicate[4] += KoalaBear::ONE;
        assert_eq!(check(&root, &at, &duplicate, &proof), Ok(false));
        assert_eq!(check(&root, &at, &rows[..6], &proof), Ok(false));
        // A digest word at the modulus is not a canonical encoding.
        let mut noncanonical = proof.clone();
        noncanonical[..4].copy_from_slice(&crate::plonky3::MODULUS.to_le_bytes());
        assert_eq!(check(&root, &at, &rows, &noncanonical), Ok(false));
        assert_eq!(check(&root, &[], &[], &[]), Err(Error::Positions));
        assert_eq!(
            check(&root, &[16], &rows[..2], &proof),
            Err(Error::Coordinate)
        );
        assert_eq!(open(&tree, &[]).unwrap_err(), Error::Positions);
        assert_eq!(open(&tree, &[16]).unwrap_err(), Error::Coordinate);
        // The expected height selects the tree geometry, not the proof. The
        // root does not encode the height: heights with the same depth give
        // the same paths below the smaller height, as in Plonky3.
        for (height, accepted) in [(15, true), (9, true), (8, false), (17, false)] {
            let expected = Shape::new(2, height, 1 << 12).unwrap();
            let at: Vec<usize> = at.iter().map(|p| p % 8).collect();
            let (rows, proof) = open(&tree, &at).unwrap();
            assert_eq!(
                verify::<poseidon2::Base>(&root, expected, &at, &rows, &proof),
                Ok(accepted),
                "{height}"
            );
        }
    }

    #[test]
    fn digests_round_trip_only_in_canonical_form() {
        let digests = [[KoalaBear::from_u32(5); 8], [KoalaBear::NEG_ONE; 8]];
        let bytes = encode_digests(&digests);
        assert_eq!(bytes.len(), 64);
        assert_eq!(decode_digests::<KoalaBear, 8>(&bytes).unwrap(), digests);
        assert!(decode_digests::<KoalaBear, 8>(&bytes[..63]).is_none());
        let mut high = bytes.clone();
        high[60..].copy_from_slice(&crate::plonky3::MODULUS.to_le_bytes());
        assert!(decode_digests::<KoalaBear, 8>(&high).is_none());
        assert!(!Scheme::Poseidon2KoalaBear.valid_digests(&high));
        // A byte-word digest has no canonicality condition beyond its width.
        assert_eq!(decode_digests::<u8, 32>(&[7; 64]).unwrap(), [[7; 32]; 2]);
        assert!(decode_digests::<u8, 32>(&[7; 63]).is_none());
    }
}
