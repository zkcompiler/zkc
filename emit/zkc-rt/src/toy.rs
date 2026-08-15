//! The toy supplier set, as concrete types: an SHA-256 chaining duplex
//! with per-call framing tags, big-endian 8-byte codecs, and the
//! safe-prime group moduli (p = 2q + 1, g of order q). The reference
//! semantics are `lib/Interpreter/ToyProfile.cpp` and
//! `reference/oracle/exec.py`; the golden vectors those two agree on are
//! the conformance contract this implementation replays.

use crate::Payload;
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

/// Modular addition in a 64-bit modulus, with each operand reduced
/// first — the reference's own sequencing (`Interpreter.cpp`'s `f_add`).
/// The sum is taken at double width because two reduced operands can
/// still exceed `u64` when the modulus does not fit in 63 bits.
pub fn addmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 % m as u128 + b as u128 % m as u128) % m as u128) as u64
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

//===-- hole fills ------------------------------------------------------===//
//
// The prover-side suppliers, ported from `ToyProfile.cpp`. Each is a
// plain typed function: the emitter checks the hole row's operand and
// result shapes against the signature at emit time and then calls it
// monomorphically, so there is no dispatch table and no "no supplier"
// arm at run time. Test-grade arithmetic — variable-time throughout, as
// the emitted README states.

/// The sigma witness payload convention shared with the reference twin
/// and the C++ toy profile: sixteen bytes, x then k, each eight
/// big-endian. Parsing is the supplier's, never the emitted crate's.
fn parse_sigma_witness(witness: &Payload) -> Result<(u64, u64), String> {
    let bytes = witness.as_bytes();
    if bytes.len() != 16 {
        return Err("sigma witness payload must be sixteen bytes (x, k big-endian)".to_owned());
    }
    Ok((decode_be8(&bytes[..8]), decode_be8(&bytes[8..])))
}

/// The honest fill for the sigma commit: a = g^k, with the witness
/// threaded on to the response hole that consumes it.
pub fn sigma_commit(generator: u64, witness: Payload) -> Result<(u64, Payload), String> {
    let (_x, k) = parse_sigma_witness(&witness)?;
    Ok((powmod(generator, k, P), witness))
}

/// The honest fill for the sigma response: z = k + c*x mod q. The
/// witness is consumed here — the handle chain ends at the last hole
/// that needs it, which is what makes the payload's move the linearity.
pub fn sigma_response(challenge: u64, witness: Payload) -> Result<u64, String> {
    let (x, k) = parse_sigma_witness(&witness)?;
    let c = challenge % Q;
    Ok((k % Q + mulmod(c, x % Q, Q)) % Q)
}

/// The wrong algebra behind the same boundary: z+1 is in range and
/// canonical, so it survives every emission gate and dies exactly where
/// it must — at the verifier's equation. This exists to make that
/// boundary observable, and no honest binding names it.
pub fn sigma_response_cheat(challenge: u64, witness: Payload) -> Result<u64, String> {
    Ok((sigma_response(challenge, witness)? + 1) % Q)
}

#[cfg(test)]
mod fills {
    use super::*;

    /// The round-trip fixture (`test/Oir/prover-round-trip.test`):
    /// x = 5, k = 7 over the toy group, generator 4.
    fn fixture() -> Payload {
        Payload::new([5u64.to_be_bytes(), 7u64.to_be_bytes()].concat().to_vec())
    }

    #[test]
    fn commit_is_the_generator_raised_to_the_nonce() {
        let (commitment, witness) = sigma_commit(4, fixture()).expect("a sixteen-byte payload");
        assert_eq!(commitment, powmod(4, 7, P));
        // 4^7 = 16384 is below p, so the pinned proof's first eight
        // bytes read as that integer.
        assert_eq!(commitment, 16384);
        assert_eq!(witness.len(), 16, "the witness threads through unchanged");
    }

    #[test]
    fn response_satisfies_the_verification_equation() {
        let challenge = 1405996128736189831u64;
        let z = sigma_response(challenge, fixture()).expect("a sixteen-byte payload");
        // g^z == a * y^c, the equation the derived verifier asserts.
        let y = powmod(4, 5, P);
        assert_eq!(
            powmod(4, z, P),
            mulmod(powmod(4, 7, P), powmod(y, challenge % Q, P), P)
        );
    }

    #[test]
    fn the_cheat_stays_inside_the_boundary_and_breaks_the_equation() {
        let challenge = 1405996128736189831u64;
        let honest = sigma_response(challenge, fixture()).expect("a sixteen-byte payload");
        let cheat = sigma_response_cheat(challenge, fixture()).expect("a sixteen-byte payload");
        assert_ne!(honest, cheat);
        assert!(
            cheat < Q,
            "a cheat that failed the range gate would prove nothing"
        );
    }

    #[test]
    fn a_short_payload_is_the_supplier_s_own_defect() {
        let short = Payload::new(vec![0; 8]);
        assert_eq!(
            sigma_commit(4, short).unwrap_err(),
            "sigma witness payload must be sixteen bytes (x, k big-endian)"
        );
    }
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
