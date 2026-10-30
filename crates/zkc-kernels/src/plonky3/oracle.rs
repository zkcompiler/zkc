//! Shape-bound vector commitments using Plonky3's binary Merkle tree.
//!
//! This adapter owns admission, canonical leaf encoding and leaf/node domain
//! separation. Plonky3 owns tree construction and path hashing. Verification
//! receives the expected shape from its caller, never from the opening proof.
//! Authentication says nothing about degree, relation satisfaction or hiding.

use super::KoalaBearExt4;
use p3_commit::{BatchOpeningRef, Mmcs};
use p3_field::{ExtensionField, PrimeField32, extension::BinomialExtensionField};
use p3_keccak::Keccak256Hash;
use p3_koala_bear::KoalaBear;
use p3_matrix::{Dimensions, dense::RowMajorMatrix};
use p3_merkle_tree::{MerkleCap, MerkleTreeMmcs};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use std::marker::PhantomData;

pub type Digest = [u8; 32];
pub type Octic = BinomialExtensionField<KoalaBear, 8>;

const HASH_LANES: usize = <Keccak256Hash as CryptographicHasher<u8, Digest>>::LANES;
// Optional provider staging, per task, not retained table/tree storage. Wide
// rows and failed optional reservations keep the allocation-free scalar path.
const HASH_BATCH_BYTES: usize = 32 * 1024;
const NODE_TAG: &[u8] = b"zkc.oracle.keccak256.node/0\0";

fn batch_buffer(message_bytes: usize, count: usize) -> Option<(usize, Vec<u8>)> {
    let rows = HASH_LANES.min(count);
    let bytes = message_bytes.checked_mul(rows)?;
    if rows < 2 || bytes > HASH_BATCH_BYTES {
        return None;
    }
    let mut buffer = Vec::new();
    buffer.try_reserve_exact(bytes).ok()?;
    Some((rows, buffer))
}

fn leaf_message_bytes<E: Element>(header: usize, width: usize) -> Option<usize> {
    width.checked_mul(4 * E::DIMENSION)?.checked_add(header)
}
mod sealed {
    pub trait Sealed {}
    impl Sealed for p3_koala_bear::KoalaBear {}
    impl Sealed for super::KoalaBearExt4 {}
    impl Sealed for super::Octic {}
}
/// The leaf codec fixes the field, defining polynomial and ordered basis.
/// It intentionally does not use Plonky3's internal Montgomery serialization.
pub trait Element:
    ExtensionField<KoalaBear> + super::residue::Residue<Base = KoalaBear> + sealed::Sealed
{
    const CODEC: &'static str;
}
impl Element for KoalaBear {
    const CODEC: &'static str = "koala-bear.canonical-u32le/0";
}
impl Element for KoalaBearExt4 {
    const CODEC: &'static str = "koala-bear.ext4-binomial3.ascending-u32le/0";
}
impl Element for Octic {
    const CODEC: &'static str = "koala-bear.ext8-binomial3.ascending-u32le/0";
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Shape,
    ElementLimit,
    ByteLimit,
    ValueCount,
    Coordinate,
    RowWidth,
    PathLength,
    Authentication,
}

/// A nonempty rectangular table; no polynomial domain is implied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    width: usize,
    height: usize,
}
impl Shape {
    pub fn new(width: usize, height: usize, max_elements: usize) -> Result<Self, Error> {
        if width == 0 || height == 0 || height > (1 << 24) {
            return Err(Error::Shape);
        }
        let count = width.checked_mul(height).ok_or(Error::ElementLimit)?;
        if count > max_elements {
            return Err(Error::ElementLimit);
        }
        Ok(Self { width, height })
    }
    pub fn width(&self) -> usize {
        self.width
    }
    pub fn height(&self) -> usize {
        self.height
    }
    pub fn elements(&self) -> usize {
        self.width * self.height
    }
    pub fn depth(&self) -> usize {
        (usize::BITS - (self.height - 1).leading_zeros()) as usize
    }
    /// Conservative live table/tree bytes, excluding caller-owned input copies.
    pub fn retained_bytes<E: Element>(&self) -> Result<usize, Error> {
        self.elements()
            .checked_mul(std::mem::size_of::<E>())
            .and_then(|n| n.checked_add((2 * self.height.next_power_of_two() - 1) * 32))
            .and_then(|n| n.checked_add(256))
            .ok_or(Error::ByteLimit)
    }
}

#[derive(Clone, Debug)]
struct LeafHash<E, const BATCH: bool = true> {
    header: Vec<u8>,
    element: PhantomData<E>,
}
impl<E: Element, const BATCH: bool> LeafHash<E, BATCH> {
    fn new(shape: Shape) -> Self {
        let mut header = b"zkc.oracle.keccak256.leaf/0\0".to_vec();
        header.extend((E::CODEC.len() as u64).to_le_bytes());
        header.extend(E::CODEC.as_bytes());
        header.extend((shape.width as u64).to_le_bytes());
        header.extend((shape.height as u64).to_le_bytes());
        Self {
            header,
            element: PhantomData,
        }
    }
}
impl<E: Element, const BATCH: bool> CryptographicHasher<E, Digest> for LeafHash<E, BATCH> {
    const LANES: usize = if BATCH { HASH_LANES } else { 1 };

    fn hash_iter<I: IntoIterator<Item = E>>(&self, input: I) -> Digest {
        // No leaf-sized allocation: each element yields at most eight words.
        Keccak256Hash.hash_iter(
            self.header
                .iter()
                .copied()
                .chain(input.into_iter().flat_map(|value| {
                    let mut bytes = [0u8; 32];
                    for (chunk, coordinate) in bytes
                        .as_chunks_mut::<4>()
                        .0
                        .iter_mut()
                        .zip(value.as_basis_coefficients_slice())
                    {
                        chunk.copy_from_slice(&coordinate.as_canonical_u32().to_le_bytes());
                    }
                    bytes.into_iter().take(4 * E::DIMENSION)
                })),
        )
    }

    fn hash_many(&self, input: &[E], out: &mut [Digest]) {
        if out.is_empty() {
            return;
        }
        assert!(input.len().is_multiple_of(out.len()), "ragged leaf batch");
        let width = input.len() / out.len();
        let staging = (BATCH && width != 0)
            .then(|| leaf_message_bytes::<E>(self.header.len(), width))
            .flatten()
            .and_then(|bytes| batch_buffer(bytes, out.len()));
        let Some((rows, mut buffer)) = staging else {
            for (index, digest) in out.iter_mut().enumerate() {
                *digest = self.hash_slice(&input[index * width..(index + 1) * width]);
            }
            return;
        };
        for (values, digests) in input.chunks(rows * width).zip(out.chunks_mut(rows)) {
            buffer.clear();
            for row in values.chunks_exact(width) {
                buffer.extend_from_slice(&self.header);
                for value in row {
                    for coordinate in value.as_basis_coefficients_slice() {
                        buffer.extend_from_slice(&coordinate.as_canonical_u32().to_le_bytes());
                    }
                }
            }
            Keccak256Hash.hash_many(&buffer, digests);
        }
    }
}
#[derive(Clone, Debug)]
struct NodeHash;
impl PseudoCompressionFunction<Digest, 2> for NodeHash {
    const LANES: usize = HASH_LANES;

    fn compress(&self, input: [Digest; 2]) -> Digest {
        Keccak256Hash.hash_iter(NODE_TAG.iter().copied().chain(input.into_iter().flatten()))
    }

    fn compress_many(&self, input: &[[Digest; 2]], out: &mut [Digest]) {
        assert_eq!(input.len(), out.len(), "ragged node batch");
        let Some((rows, mut buffer)) = batch_buffer(NODE_TAG.len() + 64, out.len()) else {
            for (pair, digest) in input.iter().zip(out) {
                *digest = self.compress(*pair);
            }
            return;
        };
        for (pairs, digests) in input.chunks(rows).zip(out.chunks_mut(rows)) {
            buffer.clear();
            for pair in pairs {
                buffer.extend_from_slice(NODE_TAG);
                buffer.extend_from_slice(&pair[0]);
                buffer.extend_from_slice(&pair[1]);
            }
            Keccak256Hash.hash_many(&buffer, digests);
        }
    }
}
type Tree<E> = MerkleTreeMmcs<E, u8, LeafHash<E>, NodeHash, 2, 32>;
fn tree<E: Element>(shape: Shape) -> Tree<E> {
    Tree::new(LeafHash::new(shape), NodeHash, 0)
}

/// Prover-private immutable opening custody. No deserializer or public-root
/// constructor exists. Sharing an Arc to this value does not copy the table.
pub struct State<E: Element> {
    shape: Shape,
    tree: <Tree<E> as Mmcs<E>>::ProverData<RowMajorMatrix<E>>,
}
impl<E: Element> std::fmt::Debug for State<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OracleState")
            .field("shape", &self.shape)
            .finish_non_exhaustive()
    }
}
impl<E: Element> State<E> {
    pub fn shape(&self) -> Shape {
        self.shape
    }
    pub fn open(&self, index: usize) -> Result<(Vec<E>, Vec<Digest>), Error> {
        if index >= self.shape.height {
            return Err(Error::Coordinate);
        }
        let opening = tree::<E>(self.shape).open_batch(index, &self.tree);
        let mut rows = opening.opened_values;
        Ok((rows.pop().unwrap(), opening.opening_proof))
    }
}

pub fn commit<E: Element>(
    values: Vec<E>,
    shape: Shape,
    max_bytes: usize,
) -> Result<(Digest, State<E>), Error> {
    if values.len() != shape.elements() {
        return Err(Error::ValueCount);
    }
    if shape.retained_bytes::<E>()? > max_bytes {
        return Err(Error::ByteLimit);
    }
    let (root, state) = crate::cpu::install(|| {
        let leaf = LeafHash::<E>::new(shape);
        let batching_fits = leaf_message_bytes::<E>(leaf.header.len(), shape.width)
            .and_then(|bytes| bytes.checked_mul(HASH_LANES))
            .is_some_and(|bytes| bytes <= HASH_BATCH_BYTES);
        let matrix = vec![RowMajorMatrix::new(values, shape.width)];
        if batching_fits {
            Tree::<E>::new(leaf, NodeHash, 0).commit(matrix)
        } else {
            // Choose scalar leaves before Plonky3 allocates its row-copy tile.
            // Parent-node batching remains independent of the leaf width.
            MerkleTreeMmcs::<E, u8, LeafHash<E, false>, NodeHash, 2, 32>::new(
                LeafHash::new(shape),
                NodeHash,
                0,
            )
            .commit(matrix)
        }
    });
    Ok((root.roots()[0], State { shape, tree: state }))
}

/// Validate the declared row width, coordinate and height-derived path length
/// before calling the upstream verifier. These are this adapter's admission
/// obligations regardless of the upstream verifier's own shape checks.
pub fn verify<E: Element>(
    root: Digest,
    shape: Shape,
    index: usize,
    row: &[E],
    path: &[Digest],
) -> Result<(), Error> {
    if index >= shape.height {
        return Err(Error::Coordinate);
    }
    if row.len() != shape.width {
        return Err(Error::RowWidth);
    }
    if path.len() != shape.depth() {
        return Err(Error::PathLength);
    }
    tree::<E>(shape)
        .verify_batch(
            &MerkleCap::new(vec![root]),
            &[Dimensions {
                width: shape.width,
                height: shape.height,
            }],
            index,
            BatchOpeningRef::new(&[row.to_vec()], &path.to_vec()),
        )
        .map_err(|_| Error::Authentication)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    fn exercise<E: Element>() {
        for height in [1, 2, 3, 4, 7, 8, 16, 31, 64] {
            for width in [1, 2, 7, 16] {
                let shape = Shape::new(width, height, 4096).unwrap();
                let data: Vec<E> = (0..shape.elements())
                    .map(|i| {
                        E::from_basis_coefficients_fn(|j| KoalaBear::from_usize(1 + i * 17 + j * 3))
                    })
                    .collect();
                let (root, state) = commit(data.clone(), shape, 1 << 20).unwrap();
                for index in 0..height {
                    let (row, path) = state.open(index).unwrap();
                    assert_eq!(&row, &data[index * width..(index + 1) * width]);
                    assert_eq!(verify(root, shape, index, &row, &path), Ok(()));
                    let mut changed = row.clone();
                    changed[0] += E::ONE;
                    assert_eq!(
                        verify(root, shape, index, &changed, &path),
                        Err(Error::Authentication)
                    );
                    let mut changed = root;
                    changed[0] ^= 1;
                    assert_eq!(
                        verify(changed, shape, index, &row, &path),
                        Err(Error::Authentication)
                    );
                    assert_eq!(
                        verify(root, shape, height, &row, &path),
                        Err(Error::Coordinate)
                    );
                    assert_eq!(
                        verify::<E>(root, shape, index, &[], &path),
                        Err(Error::RowWidth)
                    );
                    let mut longer = path.clone();
                    longer.push([0; 32]);
                    assert_eq!(
                        verify(root, shape, index, &row, &longer),
                        Err(Error::PathLength)
                    );
                    if height > 1 {
                        assert_eq!(
                            verify(root, shape, (index + 1) % height, &row, &path),
                            Err(Error::Authentication)
                        );
                        let mut changed = path.clone();
                        changed[0][0] ^= 1;
                        assert_eq!(
                            verify(root, shape, index, &row, &changed),
                            Err(Error::Authentication)
                        );
                    }
                }
                assert_eq!(state.open(height), Err(Error::Coordinate));
            }
        }
    }
    #[test]
    fn base_and_extension_authentication() {
        exercise::<KoalaBear>();
        exercise::<KoalaBearExt4>();
        exercise::<Octic>();
    }
    #[test]
    fn shape_codec_and_resource_binding() {
        let shape = Shape::new(1, 4, 16).unwrap();
        let (root, state) = commit(vec![KoalaBear::ONE; 4], shape, 4096).unwrap();
        let (row, path) = state.open(0).unwrap();
        // Same path depth, different expected height must still fail.
        assert_eq!(
            verify(root, Shape::new(1, 3, 16).unwrap(), 0, &row, &path),
            Err(Error::Authentication)
        );
        let (_, s) = commit(vec![Octic::ONE; 4], shape, 4096).unwrap();
        let (row, path) = s.open(0).unwrap();
        assert_eq!(
            verify(root, shape, 0, &row, &path),
            Err(Error::Authentication)
        );
        assert_eq!(Shape::new(0, 1, 16), Err(Error::Shape));
        assert_eq!(Shape::new(1, 0, 16), Err(Error::Shape));
        assert_eq!(Shape::new(1, (1 << 24) + 1, usize::MAX), Err(Error::Shape));
        assert_eq!(
            Shape::new(usize::MAX, 2, usize::MAX),
            Err(Error::ElementLimit)
        );
        assert_eq!(Shape::new(4, 4, 15), Err(Error::ElementLimit));
        assert!(matches!(
            commit(vec![KoalaBear::ONE; 3], shape, 4096),
            Err(Error::ValueCount)
        ));
        assert!(matches!(
            commit(vec![KoalaBear::ONE; 4], shape, 0),
            Err(Error::ByteLimit)
        ));
    }

    fn batch_digests<E: Element>() {
        let leaf = LeafHash::<E>::new(Shape::new(1, 7, 7).unwrap());
        // Cross rate boundaries, partial SIMD groups and the staging ceiling.
        for width in (0..72).chain([HASH_BATCH_BYTES / (4 * E::DIMENSION) + 1]) {
            for count in [0, 1, 2, 3, HASH_LANES + 1, 2 * HASH_LANES + 1] {
                let values: Vec<E> = (0..width * count)
                    .map(|i| E::from_basis_coefficients_fn(|j| KoalaBear::from_usize(i * 17 + j)))
                    .collect();
                let mut digests = vec![[0; 32]; count];
                leaf.hash_many(&values, &mut digests);
                for (index, digest) in digests.iter().enumerate() {
                    assert_eq!(
                        *digest,
                        leaf.hash_slice(&values[index * width..(index + 1) * width])
                    );
                }
            }
        }
    }

    #[test]
    fn batch_hashes_preserve_canonical_leaf_and_node_bytes() {
        batch_digests::<KoalaBear>();
        batch_digests::<KoalaBearExt4>();
        batch_digests::<Octic>();
        for count in [0, 1, 2, 3, HASH_LANES + 1, 2 * HASH_LANES + 1] {
            let pairs: Vec<_> = (0..count)
                .map(|i| [[i as u8; 32], [(i + 1) as u8; 32]])
                .collect();
            let mut digests = vec![[0; 32]; count];
            NodeHash.compress_many(&pairs, &mut digests);
            for (pair, digest) in pairs.iter().zip(digests) {
                assert_eq!(digest, NodeHash.compress(*pair));
            }
        }
        assert!(batch_buffer(usize::MAX, usize::MAX).is_none());
        assert!(batch_buffer(HASH_BATCH_BYTES + 1, 2).is_none());
    }

    #[derive(Clone)]
    struct ScalarLeaf<E>(LeafHash<E>);
    impl<E: Element> CryptographicHasher<E, Digest> for ScalarLeaf<E> {
        fn hash_iter<I: IntoIterator<Item = E>>(&self, values: I) -> Digest {
            self.0.hash_iter(values)
        }
    }
    #[derive(Clone)]
    struct ScalarNode;
    impl PseudoCompressionFunction<Digest, 2> for ScalarNode {
        fn compress(&self, pair: [Digest; 2]) -> Digest {
            NodeHash.compress(pair)
        }
    }

    fn scalar_tree_agreement<E: Element>() {
        type ScalarTree<E> = MerkleTreeMmcs<E, u8, ScalarLeaf<E>, ScalarNode, 2, 32>;
        for height in [1, 2, 3, 7, 31, 1024, 4096] {
            for width in [1, 7, 32]
                .into_iter()
                .chain((height <= 3).then_some(HASH_BATCH_BYTES / (4 * E::DIMENSION) + 1))
            {
                let shape = Shape::new(width, height, 1 << 20).unwrap();
                let values: Vec<E> = (0..shape.elements())
                    .map(|i| E::from_basis_coefficients_fn(|j| KoalaBear::from_usize(i * 17 + j)))
                    .collect();
                let scalar = ScalarTree::<E>::new(ScalarLeaf(LeafHash::new(shape)), ScalarNode, 0);
                let (expected, data) =
                    scalar.commit(vec![RowMajorMatrix::new(values.clone(), width)]);
                let (root, state) = commit(values.clone(), shape, 1 << 25).unwrap();
                assert_eq!(root, expected.roots()[0]);
                for index in [0, height / 2, height - 1] {
                    let expected = scalar.open_batch(index, &data);
                    let (row, path) = state.open(index).unwrap();
                    assert_eq!(row, expected.opened_values[0]);
                    assert_eq!(path, expected.opening_proof);
                    assert_eq!(verify(root, shape, index, &row, &path), Ok(()));
                }
                assert!(matches!(
                    commit(values, shape, shape.retained_bytes::<E>().unwrap() - 1),
                    Err(Error::ByteLimit)
                ));
            }
        }
    }

    #[test]
    fn batched_trees_match_scalar_roots_paths_and_resource_refusals() {
        crate::cpu::CpuExecution::new(if cfg!(feature = "parallel") { 2 } else { 1 })
            .unwrap()
            .execute(|| {
                scalar_tree_agreement::<KoalaBear>();
                scalar_tree_agreement::<KoalaBearExt4>();
                scalar_tree_agreement::<Octic>();
            });
    }

    #[test]
    #[should_panic(expected = "ragged leaf batch")]
    fn ragged_leaf_batch_is_an_internal_contract_error() {
        LeafHash::<KoalaBear>::new(Shape::new(1, 1, 1).unwrap())
            .hash_many(&[KoalaBear::ONE], &mut [[0; 32]; 2]);
    }

    #[test]
    #[should_panic(expected = "ragged node batch")]
    fn ragged_node_batch_is_an_internal_contract_error() {
        NodeHash.compress_many(&[], &mut [[0; 32]; 1]);
    }
}

#[cfg(test)]
mod quartic_tests;
