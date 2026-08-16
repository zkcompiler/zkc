//! The plonky3 supplier set, as concrete types. The permutation is the
//! borrowed kernel — the pinned upstream Poseidon2-16 over BabyBear, at
//! exactly the replay harness's revision — while the duplex framing
//! around it is zkc's spec-anchored lenpad contract
//! (`lib/Interpreter/Plonky3Profile.cpp` is the C++ sibling): width 16,
//! rate 8, buffered absorbs invalidate outputs, an absorb is made
//! prefix-free by zeroing the untouched rate slots and binding the
//! absorbed length into the first capacity element, samples pop LIFO.
//! The pinned construction hashes no domain strings — domain separation
//! lives in the event schedule, not the sponge.

use p3_baby_bear::{default_babybear_poseidon2_16, Poseidon2BabyBear};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_symmetric::Permutation;

/// The BabyBear prime, 2^31 - 2^27 + 1.
pub const BB: u32 = 2013265921;

/// The lenpad duplex over the pinned upstream permutation. `Clone` is
/// the transcript peek's mechanism: a `pow_search` trial runs on a
/// copy, never on the live state.
#[derive(Clone)]
pub struct P3Duplex {
    permutation: Poseidon2BabyBear<16>,
    state: [u32; 16],
    input_buffer: Vec<u32>,
    output_buffer: Vec<u32>,
}

impl P3Duplex {
    /// The iv policy `artifact-id`: the source identity string is
    /// absorbed before any event, as rate-many elements derived from its
    /// bytes (4-byte big-endian chunks, reduced canonically). An empty
    /// identity absorbs nothing — the `zero` iv policy, exactly the
    /// counterpart upstream verifier's own start.
    pub fn new(source_identity: &str) -> Self {
        let mut duplex = P3Duplex {
            permutation: default_babybear_poseidon2_16(),
            state: [0; 16],
            input_buffer: Vec::with_capacity(8),
            output_buffer: Vec::with_capacity(8),
        };
        let bytes = source_identity.as_bytes();
        let mut words = Vec::with_capacity(bytes.len().div_ceil(4));
        for chunk in bytes.chunks(4) {
            let mut word: u64 = 0;
            for &byte in chunk {
                word = (word << 8) | byte as u64;
            }
            words.push((word % BB as u64) as u32);
        }
        duplex.absorb(&words);
        duplex
    }

    /// Absorb canonical field elements: buffered, invalidating any
    /// pending output; a full rate buffer duplexes.
    pub fn absorb(&mut self, words: &[u32]) {
        for &word in words {
            self.output_buffer.clear();
            self.input_buffer.push(word % BB);
            if self.input_buffer.len() == 8 {
                self.duplexing();
            }
        }
    }

    /// One squeezed field element (LIFO over the rate slots).
    pub fn squeeze_element(&mut self) -> u32 {
        if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
            self.duplexing();
        }
        self.output_buffer
            .pop()
            .expect("duplexing refills the output buffer")
    }

    fn duplexing(&mut self) {
        let len = self.input_buffer.len();
        self.state[..len].copy_from_slice(&self.input_buffer);
        self.input_buffer.clear();
        if len > 0 {
            // Prefix-free absorb: zero the rate slots the inputs did not
            // overwrite and bind the absorbed length into the first
            // capacity element — length and zero-padding cannot collide.
            // An empty buffer is a squeeze: the rate stays untouched.
            for slot in &mut self.state[len..8] {
                *slot = 0;
            }
            self.state[8] = ((self.state[8] as u64 + len as u64) % BB as u64) as u32;
        }
        let mut field_state = self.state.map(p3_baby_bear::BabyBear::from_u32);
        self.permutation.permute_mut(&mut field_state);
        for (slot, element) in self.state.iter_mut().zip(field_state.iter()) {
            *slot = element.as_canonical_u32();
        }
        self.output_buffer.clear();
        self.output_buffer.extend_from_slice(&self.state[..8]);
    }
}

/// Parse `N` big-endian 32-bit words from an exact-width wire slice.
pub fn decode_words<const N: usize>(bytes: &[u8]) -> [u32; N] {
    let mut words = [0u32; N];
    for (index, word) in words.iter_mut().enumerate() {
        let base = index * 4;
        *word = u32::from_be_bytes([
            bytes[base],
            bytes[base + 1],
            bytes[base + 2],
            bytes[base + 3],
        ]);
    }
    words
}

/// The write direction of the same codecs: each canonical word as four
/// big-endian bytes, appended to the proof under construction. The
/// caller gates canonicality first, exactly as the reference sequences
/// it — an out-of-range word is the fill's defect, not a wire fact.
pub fn encode_words(words: &[u32], out: &mut Vec<u8>) {
    for &word in words {
        out.extend_from_slice(&word.to_be_bytes());
    }
}

/// The wire-canonicality rule shared by every BabyBear codec: each
/// 32-bit word must be a canonical field element.
pub fn words_canonical(words: &[u32]) -> bool {
    words.iter().all(|&word| word < BB)
}

/// Squeeze an extension element: four coordinates, least-significant
/// first, one squeezed element per coordinate (the tuple bijection —
/// exact over |F|^4, no reduction).
pub fn squeeze_ext4(duplex: &mut P3Duplex) -> [u32; 4] {
    let mut coords = [0u32; 4];
    for coord in coords.iter_mut() {
        *coord = duplex.squeeze_element();
    }
    coords
}

/// The challenge-log spelling of an extension element: the coordinates
/// packed least-significant-first into one integer, in decimal — the
/// same spelling the reference executor logs for the packed value.
pub fn ext4_decimal(coords: &[u32; 4]) -> String {
    let mut packed: u128 = 0;
    for (index, &coord) in coords.iter().enumerate() {
        packed |= (coord as u128) << (32 * index);
    }
    packed.to_string()
}

/// Squeeze one element reduced into a declared sample space (the
/// low-bits rule: the space is a power of two, so mask and modulus
/// agree).
pub fn squeeze_low_bits(duplex: &mut P3Duplex, space: u64) -> u32 {
    (duplex.squeeze_element() as u64 % space) as u32
}

/// The proof-of-work search (`docs/spec/endpoints.md` §6.2): enumerate
/// canonical field values ascending from zero and return the least one
/// whose trial derivation is zero — the normative order, so every
/// conforming implementation emits the same nonce. The trial is an
/// oracle built by the caller over a cloned duplex; this function never
/// sees the transcript. An exhausted domain is the fill's own defect,
/// reported rather than panicked (the upstream kernel vendor panics
/// here, and over a 31-bit field with a deep target the no-witness
/// probability is real).
pub fn pow_search(domain_end: u32, mut trial: impl FnMut(u32) -> u32) -> Result<u32, String> {
    for nonce in 0..domain_end {
        if trial(nonce) == 0 {
            return Ok(nonce);
        }
    }
    Err(format!(
        "no nonce below {domain_end} satisfies the proof-of-work condition"
    ))
}

/// The pinned known-answer test (upstream
/// `test_default_babybear_poseidon2_width_16`): a build whose permutation
/// cannot reproduce it must not derive challenges. Emitted conformance
/// suites call this before replaying vectors.
pub fn permutation_self_check() {
    let mut state: [u32; 16] = [
        894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
        19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
    ];
    const EXPECTED: [u32; 16] = [
        516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906, 563338433,
        319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758, 1052633829,
        1344246938,
    ];
    let permutation = default_babybear_poseidon2_16();
    let mut field_state = state.map(p3_baby_bear::BabyBear::from_u32);
    permutation.permute_mut(&mut field_state);
    for (slot, element) in state.iter_mut().zip(field_state.iter()) {
        *slot = element.as_canonical_u32();
    }
    assert_eq!(
        state, EXPECTED,
        "pinned Poseidon2-16 known-answer test failed"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_answer_test() {
        permutation_self_check();
    }

    /// The peek discipline end to end: the trial clones, the live
    /// duplex is untouched, and the returned nonce is the least one —
    /// checked by rescanning every earlier candidate.
    #[test]
    fn pow_search_returns_the_least_witness_and_leaves_the_state() {
        let mut sponge = P3Duplex::new("sha256:test");
        sponge.absorb(&[7, 11]);
        let before = sponge.clone();
        let found = pow_search(1 << 20, |nonce| {
            let mut trial = sponge.clone();
            trial.absorb(&[nonce]);
            squeeze_low_bits(&mut trial, 16)
        })
        .expect("a 4-bit target in 2^20 draws");
        for earlier in 0..found {
            let mut trial = before.clone();
            trial.absorb(&[earlier]);
            assert_ne!(squeeze_low_bits(&mut trial, 16), 0);
        }
        let mut check = before.clone();
        check.absorb(&[found]);
        assert_eq!(squeeze_low_bits(&mut check, 16), 0);
        assert_eq!(sponge.state, before.state, "the live state never moves");
    }

    #[test]
    fn an_exhausted_domain_is_an_error_not_a_panic() {
        assert_eq!(
            pow_search(8, |_| 1).unwrap_err(),
            "no nonce below 8 satisfies the proof-of-work condition"
        );
    }

    /// The upstream `empty_squeeze` observation
    /// (`evaluation/upstream/plonky3-replay/fixtures/duplex_babybear.json`,
    /// generated by the trace binary): after observing eight elements, the
    /// first eight samples drain the rate in the challenger's native order,
    /// and the ninth triggers the *empty* duplexing — a squeeze that leaves
    /// the rate untouched rather than zero-padding it.
    #[test]
    fn upstream_empty_squeeze_observation() {
        const FIRST_RATE: [u32; 8] = [
            1638090453, 408318230, 292540408, 524907186, 768508945, 195580818, 1827061661,
            754191363,
        ];
        let mut duplex = P3Duplex::new("");
        duplex.absorb(&[1, 2, 3, 4, 5, 6, 7, 8]);
        for expected in FIRST_RATE {
            assert_eq!(duplex.squeeze_element(), expected);
        }
        assert_eq!(duplex.squeeze_element(), 1304064941);
    }

    /// The upstream `full_absorb_ext4` observation: eight observed
    /// elements duplex once, and an extension sample pops four
    /// coefficients in the challenger's native order.
    #[test]
    fn upstream_full_absorb_ext4_observation() {
        let mut duplex = P3Duplex::new("");
        duplex.absorb(&[1, 2, 3, 4, 5, 6, 7, 8]);
        let coefficients = squeeze_ext4(&mut duplex);
        assert_eq!(coefficients, [1638090453, 408318230, 292540408, 524907186]);
    }
}
