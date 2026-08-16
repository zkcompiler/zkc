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

//===-- FRI leaf fills --------------------------------------------------===//
//
// The prover-side fills for the value-faithful FRI family, assembled
// from the pinned upstream kernels. The reference semantics are the
// replay runner (`evaluation/upstream/plonky3-replay`), whose
// whole-pipeline wire the emitted crate's conformance suite reproduces
// byte for byte. Fills are pure: every challenge arrives as a spine-squeezed
// value, and results reach the transcript only through spine rows.
// The `Codeword` handle is supplier state moved fill to fill — the
// carrier's exactly-once handle rule as Rust ownership.

use core::marker::PhantomData;

use p3_commit::{ExtensionMmcs, Mmcs};
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{batch_multiplicative_inverse, dot_product, BasedVectorSpace, Field};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::interpolation::{compute_adjusted_weights, Interpolate};
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_util::reverse_slice_index_bits;

use crate::Payload;

type Val = p3_baby_bear::BabyBear;
type Challenge = BinomialExtensionField<Val, 4>;
type Perm = Poseidon2BabyBear<16>;
type FieldHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, FieldHash, Compress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type ChallengeProverData =
    <ChallengeMmcs as Mmcs<Challenge>>::ProverData<RowMajorMatrix<Challenge>>;

/// The extension element for four spine-squeezed words, coefficient
/// order 0..3 — the same monomial order the upstream challenger
/// observes and samples.
fn ext_from_words(words: [u32; 4]) -> Challenge {
    Challenge::from_basis_coefficients_fn(|i| Val::from_u32(words[i]))
}

fn words_from_ext(value: Challenge) -> [u32; 4] {
    let coefficients: &[Val] = value.as_basis_coefficients_slice();
    let mut words = [0u32; 4];
    for (word, coefficient) in words.iter_mut().zip(coefficients) {
        *word = coefficient.as_canonical_u32();
    }
    words
}

fn challenge_mmcs() -> ChallengeMmcs {
    let permutation = default_babybear_poseidon2_16();
    ExtensionMmcs::new(MerkleTreeMmcs::new(
        FieldHash::new(permutation.clone()),
        Compress::new(permutation),
        0,
    ))
}

/// The codeword handle: supplier state, staged by which fill produced
/// it. Its content is exactly what the next fill needs and the spine's
/// operands do not carry.
pub enum Codeword {
    /// After the opening fill: the bit-reversed low-degree extension,
    /// the inverse denominators at zeta over its full height, and the
    /// opened value.
    Opened {
        lde: RowMajorMatrix<Val>,
        inv_denoms: Vec<Challenge>,
        opened: Challenge,
    },
    /// Between reduce or fold and the next commit: the current
    /// bit-reversed extension codeword.
    Ext(Vec<Challenge>),
    /// Between a commit and its fold: the Merkle prover data owns the
    /// reshaped codeword, and the fold reads the leaves as a view —
    /// the upstream commit phase's own no-copy dataflow.
    Committed(Box<ChallengeProverData>),
}

impl core::fmt::Debug for Codeword {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Codeword::Opened { lde, .. } => {
                write!(f, "Codeword::Opened(height {})", lde.height())
            }
            Codeword::Ext(evals) => write!(f, "Codeword::Ext(len {})", evals.len()),
            Codeword::Committed(_) => f.write_str("Codeword::Committed"),
        }
    }
}

/// The opening fill: parse the witness trace, rebuild the committed
/// bit-reversed LDE exactly as the upstream commit does, and evaluate
/// it at zeta by barycentric interpolation over the low coset. The
/// inverse denominators are computed once over the full height and
/// ride the handle: the reduce fill shares them, upstream's own
/// point-level reuse.
pub fn fri_openval(zeta: [u32; 4], witness: Payload) -> Result<([u32; 4], Codeword), String> {
    let bytes = witness.as_bytes();
    if bytes.is_empty() || !bytes.len().is_multiple_of(4) {
        return Err("fri witness payload must be big-endian 4-byte base-field words".to_owned());
    }
    let mut trace = Vec::with_capacity(bytes.len() / 4);
    for chunk in bytes.chunks(4) {
        let word = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        if word >= BB {
            return Err("fri witness payload word is outside the canonical field range".to_owned());
        }
        trace.push(Val::from_u32(word));
    }
    let height = trace.len();
    if !height.is_power_of_two() || height < 2 {
        return Err(
            "fri witness payload must hold a power-of-two number of rows, at least two".to_owned(),
        );
    }
    let log_height = height.trailing_zeros() as usize;
    // The committed input: coset LDE at the family's blowup over
    // GENERATOR·K, bit-reversed — byte for byte the upstream commit's
    // own construction.
    let dft = Radix2DitParallel::<Val>::default();
    let lde = dft
        .coset_lde_batch(RowMajorMatrix::new(trace, 1), 1, Val::GENERATOR)
        .bit_reverse_rows()
        .to_row_major_matrix();
    let zeta = ext_from_words(zeta);
    let coset = TwoAdicMultiplicativeCoset::new(Val::GENERATOR, log_height + 1)
        .expect("the trace height fits the field's two-adicity");
    let mut points: Vec<Val> = coset.iter().collect();
    reverse_slice_index_bits(&mut points);
    let differences: Vec<Challenge> = points.iter().map(|&x| zeta - x).collect();
    let inv_denoms = batch_multiplicative_inverse(&differences);
    let weights = compute_adjusted_weights(zeta, &inv_denoms[..height]);
    let (low_coset, _) = lde.split_rows(height);
    let opened = low_coset.interpolate_coset_with_precomputation(Val::GENERATOR, zeta, &weights)[0];
    Ok((
        words_from_ext(opened),
        Codeword::Opened {
            lde,
            inv_denoms,
            opened,
        },
    ))
}

/// The reduce fill: the alpha-batched reduced opening that seeds FRI.
/// For the current family's shape — one width-one matrix opened at one
/// point — the loop is `(opened − p(x)) / (zeta − x)` over the
/// bit-reversed LDE; the width gate keeps that scope honest rather
/// than pretending generality the subject does not exercise.
pub fn fri_reduce(alpha: [u32; 4], codeword: Codeword) -> Result<Codeword, String> {
    let Codeword::Opened {
        lde,
        inv_denoms,
        opened,
    } = codeword
    else {
        return Err("the reduce fill consumes the opening fill's handle".to_owned());
    };
    if lde.width() != 1 {
        return Err(
            "the reduce fill covers width-one inputs; wider batches arrive with their subject"
                .to_owned(),
        );
    }
    let alpha = ext_from_words(alpha);
    // Upstream's alpha combination, at this width: the row compression
    // and the opening combination are both single-term dot products.
    let combined_opening: Challenge = dot_product(alpha.powers(), core::iter::once(opened));
    let reduced: Vec<Challenge> = lde
        .values
        .iter()
        .zip(&inv_denoms)
        .map(|(&value, &inv_denom)| (combined_opening - Challenge::from(value)) * inv_denom)
        .collect();
    Ok(Codeword::Ext(reduced))
}

/// The commit fill: reshape the bit-reversed codeword as adjacent
/// conjugate pairs and commit through the extension Merkle scheme —
/// one root at cap height zero. The prover data keeps ownership of the
/// leaves so the following fold reads them as a view, copy-free.
pub fn fri_commit(codeword: Codeword) -> Result<([u32; 8], Codeword), String> {
    let Codeword::Ext(folded) = codeword else {
        return Err("the commit fill consumes an extension codeword".to_owned());
    };
    if folded.len() < 4 || !folded.len().is_power_of_two() {
        return Err(
            "the commit fill expects a power-of-two codeword with at least four evaluations"
                .to_owned(),
        );
    }
    let leaves = RowMajorMatrix::new(folded, 2);
    let (cap, prover_data) = challenge_mmcs().commit_matrix(leaves);
    let root = cap.roots()[0];
    let mut words = [0u32; 8];
    for (word, element) in words.iter_mut().zip(root) {
        *word = element.as_canonical_u32();
    }
    Ok((words, Codeword::Committed(Box::new(prover_data))))
}

/// The fold fill: the upstream arity-two fold over the committed
/// leaves, beta on the odd part.
pub fn fri_fold(beta: [u32; 4], codeword: Codeword) -> Result<Codeword, String> {
    let Codeword::Committed(prover_data) = codeword else {
        return Err("the fold fill consumes the commit fill's handle".to_owned());
    };
    let mmcs = challenge_mmcs();
    let leaves = *mmcs
        .get_matrices(&prover_data)
        .first()
        .expect("the commit fill stored exactly one matrix");
    let folding = TwoAdicFriFolding::<(), ()>(PhantomData);
    let folded = <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Val, Challenge>>::fold_matrix(
        &folding,
        ext_from_words(beta),
        1,
        leaves.as_view(),
    );
    Ok(Codeword::Ext(folded))
}

/// The final fill: with the family's final polynomial length of one,
/// the fully folded codeword holds one evaluation per blowup copy;
/// truncation to length one, the bit reversal, and the length-one
/// inverse DFT are all identities, so the coefficient is the first
/// entry.
pub fn fri_final(codeword: Codeword) -> Result<[u32; 4], String> {
    let Codeword::Ext(folded) = codeword else {
        return Err("the final fill consumes the folded codeword".to_owned());
    };
    if folded.len() != 2 {
        return Err(format!(
            "the final fill expects the fully folded codeword (two evaluations at blowup one); \
             got {}",
            folded.len()
        ));
    }
    Ok(words_from_ext(folded[0]))
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

    /// The fill chain over the runner's fixture trace: stage gates
    /// refuse the wrong handle by name, and the honest chain halves the
    /// codeword 16 → 8 → 4 → 2 down to the final coefficient.
    #[test]
    fn fri_fill_stages_gate_and_halve() {
        let trace: Vec<u8> = (1u32..=8).flat_map(|w| w.to_be_bytes()).collect();
        let zeta = [7, 11, 13, 17];
        let (opened, cw) =
            fri_openval(zeta, Payload::new(trace.clone())).expect("the fixture trace opens");
        assert!(words_canonical(&opened));
        assert_eq!(
            fri_fold([1, 0, 0, 0], cw).unwrap_err(),
            "the fold fill consumes the commit fill's handle"
        );
        let (_, cw) = fri_openval(zeta, Payload::new(trace)).unwrap();
        let mut cw = fri_reduce([3, 1, 4, 1], cw).unwrap();
        for expected_len in [8usize, 4, 2] {
            let (root, committed) = fri_commit(cw).unwrap();
            assert!(words_canonical(&root));
            cw = fri_fold([2, 7, 1, 8], committed).unwrap();
            let Codeword::Ext(evals) = &cw else {
                panic!("a fold yields an extension codeword");
            };
            assert_eq!(evals.len(), expected_len);
        }
        assert!(words_canonical(&fri_final(cw).unwrap()));
    }

    #[test]
    fn fri_payload_defects_are_named() {
        assert_eq!(
            fri_openval([0; 4], Payload::new(vec![1, 2, 3])).unwrap_err(),
            "fri witness payload must be big-endian 4-byte base-field words"
        );
        assert_eq!(
            fri_openval([0; 4], Payload::new(vec![0, 0, 0, 1])).unwrap_err(),
            "fri witness payload must hold a power-of-two number of rows, at least two"
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
