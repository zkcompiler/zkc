//! The Poseidon2 instances: the width-16 KoalaBear permutation of
//! `crate::plonky3::poseidon2`, padding-free overwrite sponge leaves with rate
//! eight and eight output elements, two-to-one truncated-permutation
//! compression, and digests of eight canonical KoalaBear words. This is
//! Plonky3 0.8.0's `PaddingFreeSponge<Perm16, 16, 8, 8>` and
//! `TruncatedPermutation<Perm16, 2, 8, 16>` over `MerkleTreeMmcs` with cap
//! height zero. Packed field types let the tree builder hash several rows per
//! call where the build enables SIMD packing. Rows of the quartic extension are
//! flattened to their ascending base coordinates before hashing, as Plonky3's
//! `ExtensionMmcs` does, so both instances share one tree and digest form.
use super::{DecodeError, Instance, decode_digests, encode_digests};
use crate::plonky3::{KoalaBear, KoalaBearExt4, poseidon2::permutation};
use p3_commit::ExtensionMmcs;
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
pub type QuarticMmcs = ExtensionMmcs<KoalaBear, KoalaBearExt4, BaseMmcs>;
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

pub fn quartic_mmcs() -> &'static QuarticMmcs {
    static MMCS: OnceLock<QuarticMmcs> = OnceLock::new();
    MMCS.get_or_init(|| QuarticMmcs::new(base_mmcs().clone()))
}

fn root(commitment: &MerkleCap<KoalaBear, Digest>) -> Vec<u8> {
    encode_digests(commitment.roots())
}
fn commitment(root: &[u8]) -> Result<MerkleCap<KoalaBear, Digest>, DecodeError> {
    if root.len() != 32 {
        return Err(DecodeError::Invalid);
    }
    let digests = decode_digests::<KoalaBear, 8>(root)?;
    Ok(MerkleCap::new(digests))
}
fn proof_bytes(proof: &PrunedMerklePaths<KoalaBear, 8>) -> Vec<u8> {
    encode_digests(&proof.sibling_hashes)
}
fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<KoalaBear, 8>, DecodeError> {
    Ok(PrunedMerklePaths {
        sibling_hashes: decode_digests::<KoalaBear, 8>(bytes)?,
    })
}
fn valid_digests(bytes: &[u8]) -> bool {
    crate::plonky3::words::valid_elements::<KoalaBear>(bytes) && bytes.len().is_multiple_of(32)
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
    fn root(c: &MerkleCap<KoalaBear, Digest>) -> Vec<u8> {
        root(c)
    }
    fn commitment(bytes: &[u8]) -> Result<MerkleCap<KoalaBear, Digest>, DecodeError> {
        commitment(bytes)
    }
    fn proof_bytes(p: &PrunedMerklePaths<KoalaBear, 8>) -> Vec<u8> {
        proof_bytes(p)
    }
    fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<KoalaBear, 8>, DecodeError> {
        proof(bytes)
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        valid_digests(bytes)
    }
}

/// Rows of `koala-bear.ext4-binomial3` elements, hashed as base coordinates.
pub struct Quartic;
impl Instance for Quartic {
    type Element = KoalaBearExt4;
    type Mmcs = QuarticMmcs;
    const DIGEST_BYTES: usize = 32;
    fn mmcs() -> &'static QuarticMmcs {
        quartic_mmcs()
    }
    fn root(c: &MerkleCap<KoalaBear, Digest>) -> Vec<u8> {
        root(c)
    }
    fn commitment(bytes: &[u8]) -> Result<MerkleCap<KoalaBear, Digest>, DecodeError> {
        commitment(bytes)
    }
    fn proof_bytes(p: &PrunedMerklePaths<KoalaBear, 8>) -> Vec<u8> {
        proof_bytes(p)
    }
    fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<KoalaBear, 8>, DecodeError> {
        proof(bytes)
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        valid_digests(bytes)
    }
}
