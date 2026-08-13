//! The toy supplier set, as concrete types: an SHA-256 chaining duplex
//! with per-call framing tags, big-endian 8-byte codecs, and the
//! safe-prime group moduli (p = 2q + 1, g of order q). The reference
//! semantics are `lib/Interpreter/ToyProfile.cpp` and
//! `reference/oracle/exec.py`; the golden vectors those two agree on are
//! the conformance contract this implementation replays.

use sha2::{Digest, Sha256};

/// The safe prime p = 2q + 1.
pub const P: u64 = 4611686018427394499;
/// The subgroup order q.
pub const Q: u64 = 2305843009213697249;

/// The toy duplex: SHA-256 chaining with framing tags. Byte 0x00 prefixes
/// an absorbed value and 0x01 prefixes a squeeze domain, so no absorb
/// input can collide with a squeeze input (the a-injectivity framing rule,
/// kernel.md §13(e)).
pub struct ToyDuplex {
    state: [u8; 32],
}

impl ToyDuplex {
    /// The iv policy `artifact-id`: the state seeds from the source
    /// protocol identity string, committing the transcript to the sealed
    /// protocol before any event.
    pub fn new(source_identity: &str) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(source_identity.as_bytes());
        ToyDuplex {
            state: hasher.finalize().into(),
        }
    }

    pub fn absorb(&mut self, framed: &[u8]) {
        let mut hasher = Sha256::new();
        hasher.update(self.state);
        hasher.update([0x00]);
        hasher.update(framed);
        self.state = hasher.finalize().into();
    }

    /// One 32-byte digest regardless of symbol count; the codec derives
    /// its scalar from the leading bytes.
    pub fn squeeze(&mut self, domain: &str) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(self.state);
        hasher.update([0x01]);
        hasher.update(domain.as_bytes());
        self.state = hasher.finalize().into();
        self.state
    }
}

/// The toy codec's wire and framing form: eight big-endian bytes.
pub fn frame_be8(value: u64) -> [u8; 8] {
    value.to_be_bytes()
}

/// Wire bytes to a value (the codec's decode; canonicality against the
/// class modulus is the emitted caller's gate, exactly as the
/// interpreter sequences it).
pub fn decode_be8(bytes: &[u8]) -> u64 {
    let mut value = 0u64;
    for &byte in bytes {
        value = (value << 8) | byte as u64;
    }
    value
}

/// Squeeze derivation: the first eight digest bytes reduced into the
/// declared sample space.
pub fn derive_be8(digest: &[u8; 32], space: u64) -> u64 {
    let mut value = 0u64;
    for &byte in &digest[..8] {
        value = (value << 8) | byte as u64;
    }
    value % space
}

/// Modular multiplication in a 64-bit modulus via u128 widening.
pub fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

/// Modular exponentiation.
pub fn powmod(mut base: u64, mut exponent: u64, m: u64) -> u64 {
    let mut result = 1 % m;
    base %= m;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result = mulmod(result, base, m);
        }
        base = mulmod(base, base, m);
        exponent >>= 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The honest Schnorr vector from the committed golden file
    /// (`test/Oir/Inputs/schnorr-exec-vectors.json`): the toy duplex must
    /// reproduce the recorded challenge from the recorded transcript.
    #[test]
    fn schnorr_honest_vector_challenge() {
        let source = "sha256:ecb02fdfc351e4df1a340f5c1ee5c90cf8cf96e1d1af7fa69368b5b49d32751c";
        let mut sponge = ToyDuplex::new(source);
        sponge.absorb(&frame_be8(3133908059330535738));
        sponge.absorb(&frame_be8(0x1cd59301fb10753e));
        let digest = sponge.squeeze("schnorr.c");
        assert_eq!(
            derive_be8(&digest, 2305843009213693952),
            1193094727132841256
        );
    }
}
