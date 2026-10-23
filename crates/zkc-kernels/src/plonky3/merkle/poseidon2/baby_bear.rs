//! Explicit BabyBear Poseidon2 row commitments, pinned to Plonky3 0.8.0.
//!
//! `default_babybear_poseidon2_16` fixes the seventh-power S-box,
//! eight full rounds, 13 partial rounds, constants and linear layers.
//! Leaves use `PaddingFreeSponge<_, 16, 8, 8>`; binary nodes use
//! `TruncatedPermutation<_, 2, 8, 16>`. Cap height is zero. Each digest
//! is 8 canonical 32-bit little-endian base words, exactly 32 bytes.
//! Extension leaves flatten to ascending base coordinates via `ExtensionMmcs`.
//! The protocol must bind the scheme, row width and height independently.
//! This profile makes no whole-proof-system interoperability claim.
//!
//! Source: <https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/baby-bear/src/poseidon2.rs>.
use super::super::{DecodeError, Instance, decode_digests, encode_digests};
use crate::plonky3::{BabyBear, BabyBearExt4};
use p3_baby_bear::{Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_commit::ExtensionMmcs;
use p3_field::Field;
use p3_merkle_tree::{MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use std::sync::OnceLock;

type Permutation = Poseidon2BabyBear<16>;
/// Overwrite sponge for protocol-fixed row widths.
pub type Hash = PaddingFreeSponge<Permutation, 16, 8, 8>;
/// The first 8 words of `P(left || right)`.
pub type Compress = TruncatedPermutation<Permutation, 2, 8, 16>;
type Packed = <BabyBear as Field>::Packing;
pub type BaseMmcs = MerkleTreeMmcs<Packed, Packed, Hash, Compress, 2, 8>;
pub type QuarticMmcs = ExtensionMmcs<BabyBear, BabyBearExt4, BaseMmcs>;
pub type Digest = [BabyBear; 8];

/// Construct the architecture's scalar/packed permutation from pinned defaults.
pub fn permutation() -> &'static Poseidon2BabyBear<16> {
    static PERMUTATION: OnceLock<Permutation> = OnceLock::new();
    PERMUTATION.get_or_init(default_babybear_poseidon2_16)
}

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

fn root(commitment: &MerkleCap<BabyBear, Digest>) -> Vec<u8> {
    encode_digests(commitment.roots())
}
fn commitment(root: &[u8]) -> Result<MerkleCap<BabyBear, Digest>, DecodeError> {
    if root.len() != 32 {
        return Err(DecodeError::Invalid);
    }
    Ok(MerkleCap::new(decode_digests::<BabyBear, 8>(root)?))
}
fn proof_bytes(proof: &PrunedMerklePaths<BabyBear, 8>) -> Vec<u8> {
    encode_digests(&proof.sibling_hashes)
}
fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<BabyBear, 8>, DecodeError> {
    Ok(PrunedMerklePaths {
        sibling_hashes: decode_digests::<BabyBear, 8>(bytes)?,
    })
}
fn valid_digests(bytes: &[u8]) -> bool {
    bytes.len().is_multiple_of(32) && crate::plonky3::words::valid_elements::<BabyBear>(bytes)
}

/// Rows of `baby-bear` elements.
pub struct Base;
impl Instance for Base {
    type Element = BabyBear;
    type Mmcs = BaseMmcs;
    const DIGEST_BYTES: usize = 32;
    fn mmcs() -> &'static BaseMmcs {
        base_mmcs()
    }
    fn root(c: &MerkleCap<BabyBear, Digest>) -> Vec<u8> {
        root(c)
    }
    fn commitment(bytes: &[u8]) -> Result<MerkleCap<BabyBear, Digest>, DecodeError> {
        commitment(bytes)
    }
    fn proof_bytes(p: &PrunedMerklePaths<BabyBear, 8>) -> Vec<u8> {
        proof_bytes(p)
    }
    fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<BabyBear, 8>, DecodeError> {
        proof(bytes)
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        valid_digests(bytes)
    }
}

/// Rows of `baby-bear.ext4-binomial11`, hashed as ascending base coordinates.
pub struct Quartic;
impl Instance for Quartic {
    type Element = BabyBearExt4;
    type Mmcs = QuarticMmcs;
    const DIGEST_BYTES: usize = 32;
    fn mmcs() -> &'static QuarticMmcs {
        quartic_mmcs()
    }
    fn root(c: &MerkleCap<BabyBear, Digest>) -> Vec<u8> {
        root(c)
    }
    fn commitment(bytes: &[u8]) -> Result<MerkleCap<BabyBear, Digest>, DecodeError> {
        commitment(bytes)
    }
    fn proof_bytes(p: &PrunedMerklePaths<BabyBear, 8>) -> Vec<u8> {
        proof_bytes(p)
    }
    fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<BabyBear, 8>, DecodeError> {
        proof(bytes)
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        valid_digests(bytes)
    }
}
