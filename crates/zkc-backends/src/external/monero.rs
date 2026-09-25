//! Monero v0.18.5.1, revision 4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5.
//! Source: src/ringct/bulletproofs_plus.cc (transcript_update, lines 481-499;
//! initial transcript lines 152-156), src/ringct/rctOps.cpp (hash_to_scalar),
//! src/crypto/hash.c (cn_fast_hash). See provenance.json for source hashes.
//!
//! Keccak-256 (NOT SHA3-256), then little-endian reduction modulo the Edwards
//! scalar order. Crypto is delegated to RustCrypto and curve25519-dalek.
use super::{Error, Result, Work};
use curve25519_dalek::scalar::Scalar;
use sha3::{Digest, Keccak256};

pub type Word = [u8; 32];

/// Saved encoded hash-to-point initial value from the pinned upstream harness.
/// This is a protocol constant, not a scalar, nor a zkc prefix. This module does
/// not implement Monero hash-to-point; its derivation remains an external premise.
pub const BP_PLUS_INITIAL: Word = [
    0x4a, 0x67, 0x7c, 0x90, 0xeb, 0x73, 0x05, 0x1e, 0x79, 0x0d, 0xa4, 0x55, 0x91, 0x10, 0x7f, 0x6e,
    0xe1, 0x05, 0x90, 0x4d, 0x91, 0x87, 0xc5, 0xd3, 0x54, 0x71, 0x09, 0x6c, 0x44, 0x5a, 0x22, 0x75,
];

/// Independent conversion of a hash digest to the native scalar encoding.
/// Zero is returned unchanged; the protocol owns its retry/reject policy.
pub fn reduce_digest(digest: Word) -> Word {
    Scalar::from_bytes_mod_order(digest).to_bytes()
}

/// Stateless Hs(items[0] || ...). Empty input still invokes Keccak.
/// Encoded points are hashed as supplied, without decoding/cofactor clearing.
pub fn hash_to_scalar(items: &[Word]) -> Word {
    let mut hash = Keccak256::new();
    for item in items {
        hash.update(item);
    }
    reduce_digest(hash.finalize().into())
}

pub fn hash_work(item_count: usize, include_state: bool) -> Result<Work> {
    let words = item_count
        .checked_add(usize::from(include_state))
        .ok_or(Error::SizeOverflow)?;
    let bytes = words.checked_mul(32).ok_or(Error::SizeOverflow)?;
    Ok(Work {
        hash_calls: 1,
        hash_bytes: u64::try_from(bytes).map_err(|_| Error::SizeOverflow)?,
        ..Work::default()
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HashChain {
    state: Word,
}
impl HashChain {
    /// No implicit hashing, initial point derivation, or prefix.
    pub fn new(initial: Word) -> Self {
        Self { state: initial }
    }
    pub fn state(&self) -> Word {
        self.state
    }
    /// Hs(state || items[0] || ...), including Hs(state) for an empty update.
    /// A call boundary matters: update([a,b]) differs from update([a]);update([b]).
    pub fn update(&mut self, items: &[Word]) -> Word {
        let mut hash = Keccak256::new();
        hash.update(self.state);
        for item in items {
            hash.update(item);
        }
        self.state = reduce_digest(hash.finalize().into());
        self.state
    }
}
