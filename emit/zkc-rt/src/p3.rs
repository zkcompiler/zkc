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
// from the pinned upstream kernels. A fill has no protocol effects
// (`docs/spec/endpoints.md` §6.3): it receives its declared operands
// and static parameters and returns its declared results, so every
// challenge arrives already sampled and every result reaches the
// transcript and the wire only through the spine's own rows. The
// `Codeword` handle is supplier state moved fill to fill, which is the
// carrier's exactly-once handle rule (`docs/spec/carrier.md` §6.2) held
// by Rust ownership. Byte agreement with the whole pinned pipeline is
// the conformance gate: `evaluation/upstream/plonky3-replay` produces
// the wire these fills must reproduce.

use core::marker::PhantomData;
use std::sync::OnceLock;

use p3_commit::{ExtensionMmcs, Mmcs};
use p3_dft::{Radix2DFTSmallBatch, Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{batch_multiplicative_inverse, dot_product, BasedVectorSpace, Field, TwoAdicField};
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

/// The extension element for four squeezed words, basis-coefficient
/// order 0..3 — the order the `plonky3_bb31_ext4_tuple` codec packs and
/// the challenger samples. A non-canonical word would silently reduce
/// modulo the prime and stand for a challenge nobody derived, so it is
/// refused here, exactly as a witness word is.
fn ext_from_words(words: [u32; 4]) -> Result<Challenge, String> {
    if !words_canonical(&words) {
        return Err("fri challenge word is outside the canonical field range".to_owned());
    }
    Ok(Challenge::from_basis_coefficients_fn(|i| {
        Val::from_u32(words[i])
    }))
}

fn words_from_ext(value: Challenge) -> [u32; 4] {
    let coefficients: &[Val] = value.as_basis_coefficients_slice();
    let mut words = [0u32; 4];
    for (word, coefficient) in words.iter_mut().zip(coefficients) {
        *word = coefficient.as_canonical_u32();
    }
    words
}

/// The commitment scheme, built once for the process: its round
/// constants are fixed, so rebuilding it per fill would copy kilobytes
/// of constants for no change in behaviour. Every `Mmcs` method takes
/// `&self`.
fn challenge_mmcs() -> &'static ChallengeMmcs {
    static MMCS: OnceLock<ChallengeMmcs> = OnceLock::new();
    MMCS.get_or_init(|| {
        let permutation = default_babybear_poseidon2_16();
        ExtensionMmcs::new(MerkleTreeMmcs::new(
            FieldHash::new(permutation.clone()),
            Compress::new(permutation),
            0,
        ))
    })
}

/// The family shape these fills realize. It is fixed for one artifact
/// and every fill needs it, so it rides the handle rather than being
/// spelled as a literal at each use.
#[derive(Clone, Copy)]
pub struct Shape {
    /// The rate expansion, as a log: the committed codeword is
    /// `log_blowup` doublings of the trace.
    pub log_blowup: usize,
    /// The log of the final polynomial's length; folding stops when the
    /// codeword reaches `final_poly_len << log_blowup` evaluations.
    pub log_final_poly_len: usize,
}

impl Shape {
    /// The number of evaluations the fully folded codeword carries —
    /// where `fri_final` may take the coefficients.
    fn final_codeword_len(self) -> usize {
        (1 << self.log_final_poly_len) << self.log_blowup
    }
}

/// Which fill produced a codeword, and what that fill left for the
/// next one — exactly what the spine's operands do not carry.
enum Stage {
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
    /// the commit phase's own copy-free dataflow.
    Committed(Box<ChallengeProverData>),
}

/// The codeword handle: supplier state moved fill to fill, carrying the
/// family shape every stage needs.
///
/// The stage is private for the same reason `Payload`'s bytes are:
/// everything here is derived from the witness — the low-degree
/// extension is a bijective transform of the trace — so a consumer of an
/// emitted crate reads it through no accessor, and its `Debug` reports
/// shape alone.
pub struct Codeword {
    shape: Shape,
    stage: Stage,
}

impl Codeword {
    fn new(shape: Shape, stage: Stage) -> Self {
        Codeword { shape, stage }
    }
}

/// Overwrite derived material, then hide the buffer from the optimizer
/// so the writes survive. Like `Payload`'s own scrubbing this is one
/// link of a chain: it claims nothing about copies a kernel, allocator,
/// or operating system made along the way.
#[cfg(feature = "zeroize")]
fn scrub<T: PrimeCharacteristicRing>(values: &mut [T]) {
    for value in values.iter_mut() {
        *value = T::ZERO;
    }
    core::hint::black_box(values);
}

#[cfg(feature = "zeroize")]
impl Drop for Codeword {
    fn drop(&mut self) {
        match &mut self.stage {
            Stage::Opened {
                lde, inv_denoms, ..
            } => {
                scrub(&mut lde.values);
                scrub(inv_denoms);
            }
            Stage::Ext(evaluations) => scrub(evaluations),
            // The committed leaves live inside the commitment scheme's
            // own prover data, which owns its buffers.
            Stage::Committed(_) => {}
        }
    }
}

impl core::fmt::Debug for Codeword {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.stage {
            Stage::Opened { lde, .. } => {
                write!(f, "Codeword::Opened(height {})", lde.height())
            }
            Stage::Ext(evaluations) => {
                write!(f, "Codeword::Ext(len {})", evaluations.len())
            }
            Stage::Committed(_) => f.write_str("Codeword::Committed"),
        }
    }
}

/// Move the stage out of a handle. The emptied handle drops at once;
/// the material it carried belongs to the caller, which threads it into
/// the next handle.
fn take_stage(mut codeword: Codeword) -> Stage {
    core::mem::replace(&mut codeword.stage, Stage::Ext(Vec::new()))
}

/// The opening fill: parse the witness trace, rebuild the committed
/// bit-reversed low-degree extension exactly as the commitment does,
/// and evaluate it at zeta by barycentric interpolation over the low
/// coset (`docs/spec/endpoints.md` §6.3 — a fill sees only its declared
/// operands, never the transcript). The inverse denominators are
/// computed once over the full height and ride the handle: the reduce
/// fill consumes the same ones.
pub fn fri_openval(
    log_blowup: usize,
    log_final_poly_len: usize,
    zeta: [u32; 4],
    witness: Payload,
) -> Result<([u32; 4], Codeword), String> {
    let shape = Shape {
        log_blowup,
        log_final_poly_len,
    };
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
    let log_lde_height = log_height + shape.log_blowup;
    // Every domain here is a two-adic subgroup, so the field's
    // two-adicity bounds the trace a fill can extend; refusing names
    // that bound rather than letting the kernel abort on it.
    if log_lde_height > Val::TWO_ADICITY {
        return Err(format!(
            "fri witness payload of {height} rows extends past the field's two-adic domain \
             at blowup 2^{}",
            shape.log_blowup
        ));
    }
    // The committed input: the coset extension at the family's blowup
    // over the generator coset, bit-reversed, which is what makes
    // conjugate points adjacent for every later fold.
    let dft = Radix2DitParallel::<Val>::default();
    let lde = dft
        .coset_lde_batch(
            RowMajorMatrix::new(trace, 1),
            shape.log_blowup,
            Val::GENERATOR,
        )
        .bit_reverse_rows()
        .to_row_major_matrix();
    let zeta = ext_from_words(zeta)?;
    let coset = TwoAdicMultiplicativeCoset::new(Val::GENERATOR, log_lde_height)
        .ok_or("fri opening domain is not a two-adic coset of this field")?;
    let mut points: Vec<Val> = coset.iter().collect();
    reverse_slice_index_bits(&mut points);
    let mut differences = Vec::with_capacity(points.len());
    for &x in &points {
        let difference = zeta - x;
        // Barycentric interpolation inverts every difference; a zeta on
        // the coset has none, and the kernel would divide by zero.
        if difference.is_zero() {
            return Err("fri opening point lies on the evaluation coset".to_owned());
        }
        differences.push(difference);
    }
    let inv_denoms = batch_multiplicative_inverse(&differences);
    let weights = compute_adjusted_weights(zeta, &inv_denoms[..height]);
    let (low_coset, _) = lde.split_rows(height);
    let opened = low_coset.interpolate_coset_with_precomputation(Val::GENERATOR, zeta, &weights)[0];
    Ok((
        words_from_ext(opened),
        Codeword::new(
            shape,
            Stage::Opened {
                lde,
                inv_denoms,
                opened,
            },
        ),
    ))
}

/// The reduce fill: the alpha-batched reduced opening that seeds the
/// folding phase — `(opened − p(x)) / (zeta − x)` scaled by the batching
/// challenge, over the bit-reversed extension. One matrix opened at one
/// point makes both batching sums single-term, so alpha's powers reduce
/// to its zeroth here; the sums are written in their general form, and a
/// wider subject extends them without moving the surrounding stages.
pub fn fri_reduce(alpha: [u32; 4], codeword: Codeword) -> Result<Codeword, String> {
    let shape = codeword.shape;
    let Stage::Opened {
        lde,
        inv_denoms,
        opened,
    } = take_stage(codeword)
    else {
        return Err("the reduce fill consumes the opening fill's handle".to_owned());
    };
    let alpha = ext_from_words(alpha)?;
    // Both batching sums have the same shape — powers of alpha against
    // the values they weigh — and at this width both are single-term.
    let combined_opening: Challenge = dot_product(alpha.powers(), core::iter::once(opened));
    let evaluations: Vec<Challenge> = lde
        .values
        .iter()
        .zip(&inv_denoms)
        .map(|(&value, &inv_denom)| {
            let compressed_row: Challenge =
                dot_product(alpha.powers(), core::iter::once(Challenge::from(value)));
            (combined_opening - compressed_row) * inv_denom
        })
        .collect();
    Ok(Codeword::new(shape, Stage::Ext(evaluations)))
}

/// The commit fill: reshape the bit-reversed codeword as adjacent
/// conjugate pairs and commit through the extension Merkle scheme — one
/// root at cap height zero. The prover data keeps ownership of the
/// leaves so the following fold reads them as a view, copy-free.
pub fn fri_commit(codeword: Codeword) -> Result<([u32; 8], Codeword), String> {
    let shape = codeword.shape;
    let Stage::Ext(evaluations) = take_stage(codeword) else {
        return Err("the commit fill consumes an extension codeword".to_owned());
    };
    // A codeword already at the final length has nothing left to fold,
    // so committing it would add a round the verifier does not expect.
    if evaluations.len() <= shape.final_codeword_len() {
        return Err(format!(
            "the commit fill expects a codeword longer than the final {} evaluations",
            shape.final_codeword_len()
        ));
    }
    let leaves = RowMajorMatrix::new(evaluations, 2);
    let (cap, data) = challenge_mmcs().commit_matrix(leaves);
    let Some(root) = cap.roots().first() else {
        return Err("the commitment produced no root at cap height zero".to_owned());
    };
    let mut words = [0u32; 8];
    for (word, element) in words.iter_mut().zip(root) {
        *word = element.as_canonical_u32();
    }
    Ok((
        words,
        Codeword::new(shape, Stage::Committed(Box::new(data))),
    ))
}

/// The fold fill: the arity-two fold over the committed leaves, the
/// folding challenge on the odd part.
pub fn fri_fold(beta: [u32; 4], codeword: Codeword) -> Result<Codeword, String> {
    let shape = codeword.shape;
    let Stage::Committed(data) = take_stage(codeword) else {
        return Err("the fold fill consumes the commit fill's handle".to_owned());
    };
    // Reading the committed leaves needs no scheme state: the accessor
    // is a projection of the prover data.
    let leaves = *challenge_mmcs()
        .get_matrices(&data)
        .first()
        .ok_or("the committed prover data holds no matrix to fold")?;
    let folding = TwoAdicFriFolding::<(), ()>(PhantomData);
    let evaluations =
        <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Val, Challenge>>::fold_matrix(
            &folding,
            ext_from_words(beta)?,
            1,
            leaves.as_view(),
        );
    Ok(Codeword::new(shape, Stage::Ext(evaluations)))
}

/// The final fill: the fully folded codeword carries one blowup copy of
/// the final polynomial's evaluations, in bit-reversed order; the
/// coefficients are its inverse transform, and the family's declared
/// final length says how many there are.
pub fn fri_final(codeword: Codeword) -> Result<[u32; 4], String> {
    let shape = codeword.shape;
    let Stage::Ext(mut evaluations) = take_stage(codeword) else {
        return Err("the final fill consumes the folded codeword".to_owned());
    };
    if evaluations.len() != shape.final_codeword_len() {
        return Err(format!(
            "the final fill expects the fully folded codeword ({} evaluations); got {}",
            shape.final_codeword_len(),
            evaluations.len()
        ));
    }
    evaluations.truncate(1 << shape.log_final_poly_len);
    reverse_slice_index_bits(&mut evaluations);
    let dft = Radix2DFTSmallBatch::<Val>::default();
    let coefficients: Vec<Challenge> = dft.idft_algebra(evaluations);
    let Some(&constant) = coefficients.first() else {
        return Err("the final polynomial has no coefficient".to_owned());
    };
    if coefficients.len() != 1 {
        return Err(format!(
            "the final fill emits one coefficient; this family declares {}",
            coefficients.len()
        ));
    }
    Ok(words_from_ext(constant))
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

    /// The fill chain over the runner's fixture trace. The opened value
    /// is checked against an independent evaluation of the same
    /// polynomial at the same point — the trace is 1..8, so the
    /// interpolant is `p(x) = x` over the natural domain and the
    /// barycentric result must equal zeta itself — and the chain then
    /// halves the codeword 16 → 8 → 4 → 2 down to a final coefficient.
    #[test]
    fn fri_fills_evaluate_and_halve() {
        let trace: Vec<u8> = (1u32..=8).flat_map(|w| w.to_be_bytes()).collect();
        // The natural domain's generator, raised through the trace:
        // p interpolates the values 1..8 over it, so evaluating at a
        // domain point returns that point's own value.
        let zeta = [7, 11, 13, 17];
        let (opened, cw) =
            fri_openval(1, 0, zeta, Payload::new(trace.clone())).expect("the fixture trace opens");
        assert!(words_canonical(&opened));
        // Independent evidence, over a different domain and a different
        // code path: the fill interpolates the low coset out of the
        // bit-reversed extension with precomputed weights, while this
        // evaluates the same polynomial over the whole natural-order
        // extension through the kernel's one-call interpolation. Both
        // are p(zeta), so agreement pins the value rather than the
        // procedure.
        let dft = Radix2DitParallel::<Val>::default();
        let natural = dft
            .coset_lde_batch(
                RowMajorMatrix::new((1u32..=8).map(Val::from_u32).collect::<Vec<_>>(), 1),
                1,
                Val::GENERATOR,
            )
            .to_row_major_matrix();
        let direct = natural.interpolate_coset(Val::GENERATOR, ext_from_words(zeta).unwrap())[0];
        assert_eq!(
            opened,
            words_from_ext(direct),
            "the opened value is p(zeta)"
        );

        assert_eq!(
            fri_fold([1, 0, 0, 0], cw).unwrap_err(),
            "the fold fill consumes the commit fill's handle"
        );
        let (_, cw) = fri_openval(1, 0, zeta, Payload::new(trace)).unwrap();
        let mut cw = fri_reduce([3, 1, 4, 1], cw).unwrap();
        for expected_len in [8usize, 4, 2] {
            let (root, committed) = fri_commit(cw).unwrap();
            assert!(words_canonical(&root));
            cw = fri_fold([2, 7, 1, 8], committed).unwrap();
            assert_eq!(
                format!("{cw:?}"),
                format!("Codeword::Ext(len {expected_len})")
            );
        }
        assert!(words_canonical(&fri_final(cw).unwrap()));
    }

    /// Every payload and stage refusal names its own cause. The
    /// conformance corpus covers the canonical-range and length gates
    /// against the emitted crate; these hold the same messages at the
    /// fill boundary, where a caller outside an emitted prover meets
    /// them.
    #[test]
    fn fri_fill_refusals_are_named() {
        let ok = || {
            Payload::new(
                (1u32..=8)
                    .flat_map(|w| w.to_be_bytes())
                    .collect::<Vec<u8>>(),
            )
        };
        assert_eq!(
            fri_openval(1, 0, [0; 4], Payload::new(vec![1, 2, 3])).unwrap_err(),
            "fri witness payload must be big-endian 4-byte base-field words"
        );
        assert_eq!(
            fri_openval(1, 0, [0; 4], Payload::new(vec![0, 0, 0, 1])).unwrap_err(),
            "fri witness payload must hold a power-of-two number of rows, at least two"
        );
        assert_eq!(
            fri_openval(1, 0, [0; 4], Payload::new(BB.to_be_bytes().repeat(2))).unwrap_err(),
            "fri witness payload word is outside the canonical field range"
        );
        assert_eq!(
            fri_openval(1, 0, [BB, 0, 0, 0], ok()).unwrap_err(),
            "fri challenge word is outside the canonical field range"
        );
        // A trace that would extend past the field's two-adic domain is
        // refused rather than aborting inside the transform.
        assert!(fri_openval(27, 0, [1, 0, 0, 0], ok())
            .unwrap_err()
            .contains("two-adic domain"));
        // The opening point may not sit on the coset it interpolates
        // over: every barycentric denominator would be zero.
        let coset = TwoAdicMultiplicativeCoset::new(Val::GENERATOR, 4).unwrap();
        let on_coset = words_from_ext(Challenge::from(coset.iter().next().unwrap()));
        assert_eq!(
            fri_openval(1, 0, on_coset, ok()).unwrap_err(),
            "fri opening point lies on the evaluation coset"
        );
        // Stage gates: each fill names the handle it consumes.
        let (_, opened) = fri_openval(1, 0, [7, 11, 13, 17], ok()).unwrap();
        assert_eq!(
            fri_final(opened).unwrap_err(),
            "the final fill consumes the folded codeword"
        );
        let (_, opened) = fri_openval(1, 0, [7, 11, 13, 17], ok()).unwrap();
        assert_eq!(
            fri_commit(opened).unwrap_err(),
            "the commit fill consumes an extension codeword"
        );
        let (_, opened) = fri_openval(1, 0, [7, 11, 13, 17], ok()).unwrap();
        let reduced = fri_reduce([1, 0, 0, 0], opened).unwrap();
        assert_eq!(
            fri_reduce([1, 0, 0, 0], reduced).unwrap_err(),
            "the reduce fill consumes the opening fill's handle"
        );
    }
}
