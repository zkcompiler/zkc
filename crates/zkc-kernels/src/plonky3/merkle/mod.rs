//! Merkle row commitments generic over leaf hash, compression and digest word.
//!
//! An [`Instance`] supplies the committed element type, hash/compression pair
//! and canonical digest encoding. Plonky3 0.8.0 owns immutable tree construction,
//! single and pruned multi-openings and verification. The caller supplies the
//! expected shape and positions; proofs never supply them. Authentication says
//! nothing about degree, relation satisfaction, hiding or extraction.
//!
//! These typed primitives own no VM values, operation bindings or runtime policy.
pub mod poseidon2;

use crate::plonky3::oracle::Shape;
use p3_commit::Mmcs;
use p3_matrix::{Dimensions, dense::RowMajorMatrix};

/// One word of a digest, with its canonical byte encoding.
pub trait DigestWord: Copy + Default + Eq + Send + Sync + std::fmt::Debug + 'static {
    /// Nonzero width of the canonical encoding written by [`Self::write`].
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
impl DigestWord for crate::plonky3::KoalaBear {
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
///
/// # Panics
/// Panics if the word width is zero or the encoded length exceeds `usize` or
/// the vector's capacity limit.
pub fn encode_digests<W: DigestWord, const N: usize>(digests: &[[W; N]]) -> Vec<u8> {
    assert!(W::BYTES > 0, "digest word width must be nonzero");
    let length = digests
        .len()
        .checked_mul(N)
        .and_then(|words| words.checked_mul(W::BYTES))
        .expect("digest byte length overflow");
    let mut out = Vec::with_capacity(length);
    for word in digests.iter().flatten() {
        word.write(&mut out);
    }
    out
}
/// A malformed digest is distinct from insufficient decoding storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    Invalid,
    Allocation,
}

/// Decode whole digests of canonical words, preserving allocation failures.
pub fn decode_digests<W: DigestWord, const N: usize>(
    bytes: &[u8],
) -> Result<Vec<[W; N]>, DecodeError> {
    let width = N.checked_mul(W::BYTES).ok_or(DecodeError::Invalid)?;
    if width == 0 || !bytes.len().is_multiple_of(width) {
        return Err(DecodeError::Invalid);
    }
    let mut digests =
        crate::allocation::reserve(bytes.len() / width).map_err(|_| DecodeError::Allocation)?;
    for digest in bytes.chunks_exact(width) {
        let mut words = [W::default(); N];
        for (word, encoded) in words.iter_mut().zip(digest.chunks_exact(W::BYTES)) {
            *word = W::read(encoded).ok_or(DecodeError::Invalid)?;
        }
        digests.push(words);
    }
    Ok(digests)
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
    fn commitment(root: &[u8]) -> Result<Commitment<Self>, DecodeError>;
    fn proof_bytes(proof: &MultiProof<Self>) -> Vec<u8>;
    fn proof(bytes: &[u8]) -> Result<MultiProof<Self>, DecodeError>;
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
    Allocation,
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
) -> std::result::Result<(Vec<u8>, Tree<I>), Error>
where
    Commitment<I>: Send,
    ProverData<I>: Send,
{
    if values.len() != shape.elements() {
        return Err(Error::ValueCount);
    }
    if retained_bytes::<I>(shape).is_none_or(|bytes| bytes > max_bytes) {
        return Err(Error::ByteLimit);
    }
    let (commitment, data) =
        crate::cpu::install(|| I::mmcs().commit(vec![RowMajorMatrix::new(values, shape.width())]));
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

/// `Err` for an invalid verifier request or insufficient decoding storage;
/// malformed or false openings, including a wrong row count or digest encoding,
/// are `Ok(false)` when decoding storage is available.
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
    let decoded =
        I::commitment(root).and_then(|commitment| I::proof(proof).map(|proof| (commitment, proof)));
    let (commitment, proof) = match decoded {
        Ok(decoded) => decoded,
        Err(DecodeError::Invalid) => return Ok(false),
        Err(DecodeError::Allocation) => return Err(Error::Allocation),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonky3::KoalaBear;
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
        assert!(decode_digests::<KoalaBear, 8>(&bytes[..63]).is_err());
        let mut high = bytes.clone();
        high[60..].copy_from_slice(&crate::plonky3::MODULUS.to_le_bytes());
        assert!(decode_digests::<KoalaBear, 8>(&high).is_err());
        assert!(!poseidon2::Base::valid_digests(&high));
        // A byte-word digest has no canonicality condition beyond its width.
        assert_eq!(decode_digests::<u8, 32>(&[7; 64]).unwrap(), [[7; 32]; 2]);
        assert!(decode_digests::<u8, 32>(&[7; 63]).is_err());
        assert_eq!(encode_digests::<u8, 32>(&[]), Vec::<u8>::new());
        assert_eq!(decode_digests::<u8, 32>(&[]), Ok(Vec::new()));
    }

    #[test]
    fn decoding_allocation_failures_do_not_reject_valid_openings() {
        let shape = Shape::new(2, 8, 16).unwrap();
        let (root, tree) = commit::<poseidon2::Base>(table(2, 8), shape, 1 << 20).unwrap();
        let (rows, proof) = open(&tree, &[1]).unwrap();
        for successful in [0, 1] {
            // The commitment digest and the proof digests are separate owned
            // decodes. Either reservation can fail without changing the claim.
            let guard = crate::allocation::failure::after(successful);
            assert_eq!(
                verify::<poseidon2::Base>(&root, shape, &[1], &rows, &proof),
                Err(Error::Allocation)
            );
            drop(guard);
        }
        assert_eq!(
            verify::<poseidon2::Base>(&root, shape, &[1], &rows, &proof),
            Ok(true)
        );
        assert_eq!(
            decode_digests::<KoalaBear, 8>(&proof[..proof.len() - 1]),
            Err(DecodeError::Invalid)
        );
        let guard = crate::allocation::failure::after(0);
        assert_eq!(
            decode_digests::<KoalaBear, 8>(&proof),
            Err(DecodeError::Allocation)
        );
        drop(guard);
    }

    // Zero-sized test words let width arithmetic be exercised without huge
    // allocations. Invalid widths must be rejected before invoking a codec.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct TestWord<const BYTES: usize>;

    impl<const BYTES: usize> DigestWord for TestWord<BYTES> {
        const BYTES: usize = BYTES;
        fn write(self, _: &mut Vec<u8>) {
            panic!("invalid digest width reached the word encoder");
        }
        fn read(_: &[u8]) -> Option<Self> {
            panic!("invalid digest width reached the word decoder");
        }
    }

    #[test]
    fn digest_decoding_rejects_zero_and_overflowing_widths() {
        assert!(decode_digests::<u8, 0>(&[]).is_err());
        assert!(decode_digests::<TestWord<0>, 1>(&[]).is_err());
        // Wrapping multiplication would turn this width into two bytes and
        // accept default words without decoding either of them.
        type OverflowWord = TestWord<{ usize::MAX / 2 + 2 }>;
        assert!(decode_digests::<OverflowWord, 2>(&[0, 0]).is_err());
        assert!(decode_digests::<OverflowWord, 2>(&[]).is_err());
    }

    #[test]
    #[should_panic(expected = "digest byte length overflow")]
    fn digest_encoding_rejects_overflowing_digest_width() {
        let _ = encode_digests(&[[TestWord::<{ usize::MAX / 2 + 2 }>; 2]]);
    }

    #[test]
    #[should_panic(expected = "digest byte length overflow")]
    fn digest_encoding_rejects_overflowing_total_length() {
        let _ = encode_digests(&[[TestWord::<{ usize::MAX / 2 + 1 }>]; 2]);
    }

    #[test]
    #[should_panic(expected = "digest word width must be nonzero")]
    fn digest_encoding_rejects_zero_word_width() {
        let _ = encode_digests(&[[TestWord::<0>]]);
    }
}
