//! Explicit Goldilocks Poseidon2 row commitments, pinned to Plonky3 0.8.0.
//!
//! `default_goldilocks_poseidon2_8` fixes the seventh-power S-box,
//! eight full rounds, 22 partial rounds, constants and linear layers.
//! Leaves use `PaddingFreeSponge<_, 8, 4, 4>`; binary nodes use
//! `TruncatedPermutation<_, 2, 4, 8>`. Cap height is zero. Each digest
//! is 4 canonical 64-bit little-endian base words, exactly 32 bytes.
//! Extension leaves flatten to ascending base coordinates via `ExtensionMmcs`.
//! The protocol must bind the scheme, row width and height independently.
//! This profile makes no whole-proof-system interoperability claim.
//!
//! Source: <https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/goldilocks/src/poseidon2.rs>.
use super::super::{DecodeError, Instance, decode_digests, encode_digests};
use crate::plonky3::{Goldilocks, GoldilocksExt2};
use p3_commit::ExtensionMmcs;
use p3_field::Field;
use p3_goldilocks::{Poseidon2Goldilocks, default_goldilocks_poseidon2_8};
use p3_merkle_tree::{MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use std::sync::OnceLock;

type Permutation = Poseidon2Goldilocks<8>;
/// Overwrite sponge for protocol-fixed row widths.
pub type Hash = PaddingFreeSponge<Permutation, 8, 4, 4>;
/// The first 4 words of `P(left || right)`.
pub type Compress = TruncatedPermutation<Permutation, 2, 4, 8>;
type Packed = <Goldilocks as Field>::Packing;
pub type BaseMmcs = MerkleTreeMmcs<Packed, Packed, Hash, Compress, 2, 4>;
pub type QuadraticMmcs = ExtensionMmcs<Goldilocks, GoldilocksExt2, BaseMmcs>;
pub type Digest = [Goldilocks; 4];

/// Construct the architecture's scalar/packed permutation from pinned defaults.
pub fn permutation() -> &'static Poseidon2Goldilocks<8> {
    static PERMUTATION: OnceLock<Permutation> = OnceLock::new();
    PERMUTATION.get_or_init(default_goldilocks_poseidon2_8)
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

pub fn quadratic_mmcs() -> &'static QuadraticMmcs {
    static MMCS: OnceLock<QuadraticMmcs> = OnceLock::new();
    MMCS.get_or_init(|| QuadraticMmcs::new(base_mmcs().clone()))
}

fn root(commitment: &MerkleCap<Goldilocks, Digest>) -> Vec<u8> {
    encode_digests(commitment.roots())
}
fn commitment(root: &[u8]) -> Result<MerkleCap<Goldilocks, Digest>, DecodeError> {
    if root.len() != 32 {
        return Err(DecodeError::Invalid);
    }
    Ok(MerkleCap::new(decode_digests::<Goldilocks, 4>(root)?))
}
fn proof_bytes(proof: &PrunedMerklePaths<Goldilocks, 4>) -> Vec<u8> {
    encode_digests(&proof.sibling_hashes)
}
fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<Goldilocks, 4>, DecodeError> {
    Ok(PrunedMerklePaths {
        sibling_hashes: decode_digests::<Goldilocks, 4>(bytes)?,
    })
}
fn valid_digests(bytes: &[u8]) -> bool {
    bytes.len().is_multiple_of(32) && crate::plonky3::words::valid_elements::<Goldilocks>(bytes)
}

/// Rows of `goldilocks` elements.
pub struct Base;
impl Instance for Base {
    type Element = Goldilocks;
    type Mmcs = BaseMmcs;
    const DIGEST_BYTES: usize = 32;
    fn mmcs() -> &'static BaseMmcs {
        base_mmcs()
    }
    fn root(c: &MerkleCap<Goldilocks, Digest>) -> Vec<u8> {
        root(c)
    }
    fn commitment(bytes: &[u8]) -> Result<MerkleCap<Goldilocks, Digest>, DecodeError> {
        commitment(bytes)
    }
    fn proof_bytes(p: &PrunedMerklePaths<Goldilocks, 4>) -> Vec<u8> {
        proof_bytes(p)
    }
    fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<Goldilocks, 4>, DecodeError> {
        proof(bytes)
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        valid_digests(bytes)
    }
}

/// Rows of `goldilocks.ext2-binomial7`, hashed as ascending base coordinates.
pub struct Quadratic;
impl Instance for Quadratic {
    type Element = GoldilocksExt2;
    type Mmcs = QuadraticMmcs;
    const DIGEST_BYTES: usize = 32;
    fn mmcs() -> &'static QuadraticMmcs {
        quadratic_mmcs()
    }
    fn root(c: &MerkleCap<Goldilocks, Digest>) -> Vec<u8> {
        root(c)
    }
    fn commitment(bytes: &[u8]) -> Result<MerkleCap<Goldilocks, Digest>, DecodeError> {
        commitment(bytes)
    }
    fn proof_bytes(p: &PrunedMerklePaths<Goldilocks, 4>) -> Vec<u8> {
        proof_bytes(p)
    }
    fn proof(bytes: &[u8]) -> Result<PrunedMerklePaths<Goldilocks, 4>, DecodeError> {
        proof(bytes)
    }
    fn valid_digests(bytes: &[u8]) -> bool {
        valid_digests(bytes)
    }
}
