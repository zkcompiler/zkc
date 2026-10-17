//! The Poseidon2 instances: the width-16 KoalaBear permutation of
//! `crate::plonky3::poseidon2`, padding-free overwrite sponge leaves with rate
//! eight and eight output elements, two-to-one truncated-permutation
//! compression, and digests of eight canonical KoalaBear words. This is
//! Plonky3 0.8.0's `PaddingFreeSponge<Perm16, 16, 8, 8>` and
//! `TruncatedPermutation<Perm16, 2, 8, 16>` over `MerkleTreeMmcs` with cap
//! height zero. Packed field types let the tree builder hash several rows per
//! call where the build enables SIMD packing.
use super::{Instance, decode_digests, encode_digests};
use crate::plonky3::{KoalaBear, poseidon2::permutation};
use p3_field::Field;
use p3_koala_bear::Poseidon2KoalaBear;
use p3_merkle_tree::{MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use std::sync::OnceLock;

type Permutation = Poseidon2KoalaBear<16>;
/// Leaf hash: overwrite the first eight state elements per absorbed block.
pub type Hash = PaddingFreeSponge<Permutation, 16, 8, 8>;
/// Node hash: the first eight elements of `P(left || right)`.
pub type Compress = TruncatedPermutation<Permutation, 2, 8, 16>;
type Packed = <KoalaBear as Field>::Packing;
pub type BaseMmcs = MerkleTreeMmcs<Packed, Packed, Hash, Compress, 2, 8>;
pub type Digest = [KoalaBear; 8];

pub fn base_mmcs() -> &'static BaseMmcs {
    static MMCS: OnceLock<BaseMmcs> = OnceLock::new();
    MMCS.get_or_init(|| {
        BaseMmcs::new(
            Hash::new(permutation().clone()),
            Compress::new(permutation().clone()),
            0,
        )
    })
}

/// Rows of `koala-bear` elements.
pub struct Base;
impl Instance for Base {
    type Element = KoalaBear;
    type Mmcs = BaseMmcs;
    const DIGEST_BYTES: usize = 32;
    fn mmcs() -> &'static BaseMmcs {
        base_mmcs()
    }
    fn root(commitment: &MerkleCap<KoalaBear, Digest>) -> Vec<u8> {
        encode_digests(commitment.roots())
    }
    fn commitment(root: &[u8]) -> Option<MerkleCap<KoalaBear, Digest>> {
        let digests = decode_digests::<KoalaBear, 8>(root)?;
        (digests.len() == 1).then(|| MerkleCap::new(digests))
    }
    fn proof_bytes(proof: &PrunedMerklePaths<KoalaBear, 8>) -> Vec<u8> {
        encode_digests(&proof.sibling_hashes)
    }
    fn proof(bytes: &[u8]) -> Option<PrunedMerklePaths<KoalaBear, 8>> {
        Some(PrunedMerklePaths {
            sibling_hashes: decode_digests::<KoalaBear, 8>(bytes)?,
        })
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        crate::plonky3::words::valid_elements::<KoalaBear>(bytes)
            && bytes.len().is_multiple_of(Self::DIGEST_BYTES)
    }
}
