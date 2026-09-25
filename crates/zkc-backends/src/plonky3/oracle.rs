//! Shape-bound vector commitments using Plonky3's binary Merkle tree.
//!
//! This adapter owns admission, canonical leaf encoding and leaf/node domain
//! separation. Plonky3 owns tree construction and path hashing. Verification
//! receives the expected shape from its caller, never from the opening proof.
//! Authentication says nothing about degree, relation satisfaction or hiding.

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
mod sealed {
    pub trait Sealed {}
    impl Sealed for p3_koala_bear::KoalaBear {}
    impl Sealed for super::Octic {}
}
/// The leaf codec fixes the field, defining polynomial and ordered basis.
/// It intentionally does not use Plonky3's internal Montgomery serialization.
pub trait Element: ExtensionField<KoalaBear> + sealed::Sealed {
    const CODEC: &'static str;
}
impl Element for KoalaBear {
    const CODEC: &'static str = "koala-bear.canonical-u32le/1";
}
impl Element for Octic {
    const CODEC: &'static str = "koala-bear.ext8-binomial3.ascending-u32le/1";
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
struct LeafHash<E> {
    header: Vec<u8>,
    element: PhantomData<E>,
}
impl<E: Element> LeafHash<E> {
    fn new(shape: Shape) -> Self {
        let mut header = b"zkc.oracle.keccak256.leaf/1\0".to_vec();
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
impl<E: Element> CryptographicHasher<E, Digest> for LeafHash<E> {
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
}
#[derive(Clone, Debug)]
struct NodeHash;
impl PseudoCompressionFunction<Digest, 2> for NodeHash {
    fn compress(&self, input: [Digest; 2]) -> Digest {
        Keccak256Hash.hash_iter(
            b"zkc.oracle.keccak256.node/1\0"
                .iter()
                .copied()
                .chain(input.into_iter().flatten()),
        )
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
    let (root, state) = tree::<E>(shape).commit(vec![RowMajorMatrix::new(values, shape.width)]);
    Ok((root.roots()[0], State { shape, tree: state }))
}

/// All shape checks precede the pinned upstream verifier. In 0.5.1 the
/// upstream verifier does not itself require the declared row width or derive
/// path length from the expected height; those are this adapter's obligations.
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
}
