//! Replay harness for one pinned Plonky3 FRI-shaped witness.
//!
//! This crate observes what the pinned upstream verifier consumes — exact
//! inputs, transcript events, proof bytes — and replays the verifier from a
//! captured fixture alone. It is an evaluation shim, not a zkc backend: no
//! code here is linked into the compiler or checker, and a positive replay
//! never claims universal implementation conformance.
//!
//! The design decisions (pin, witness shape, what "exact verifier input"
//! means, fixture format) are recorded in `evaluation/upstream/plonky3-replay/README.md`.

use std::sync::{Arc, Mutex};

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{
    CanObserve, CanSample, CanSampleBits, DuplexChallenger, FieldChallenger, GrindingChallenger,
};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub const PLONKY3_REPOSITORY: &str = "https://github.com/Plonky3/Plonky3";
pub const PLONKY3_REVISION: &str = "3da346791c813433b201299afc3d10bf42f8a078";
pub const FIXTURE_FORMAT: &str = "zkc.replay.fixture";

// The witness configuration fixed by the design gate: every transcript event
// kind the FRI spine names must occur, grinding included, in the smallest
// readable instance.
pub const LOG_BLOWUP: usize = 1;
pub const LOG_FINAL_POLY_LEN: usize = 0;
pub const MAX_LOG_ARITY: usize = 1;
pub const NUM_QUERIES: usize = 4;
pub const COMMIT_POW_BITS: usize = 0;
pub const QUERY_POW_BITS: usize = 8;
pub const TRACE_HEIGHT: usize = 8;

pub type Val = BabyBear;
pub type Perm = Poseidon2BabyBear<16>;
pub type FieldHash = PaddingFreeSponge<Perm, 16, 8, 8>;
pub type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
pub type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, FieldHash, Compress, 2, 8>;
pub type Challenge = BinomialExtensionField<Val, 4>;
pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
pub type Dft = Radix2DitParallel<Val>;
pub type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
pub type PlainChallenger = DuplexChallenger<Val, Perm, 16, 8>;
pub type PlainConfig = StarkConfig<Pcs, Challenge, PlainChallenger>;
pub type RecordingConfig = StarkConfig<Pcs, Challenge, RecordingChallenger>;

// ---------------------------------------------------------------------------
// Transcript events.
//
// Recorded at the granularity the verifier crosses the challenger trait
// boundary, with full values, so the log plus the pinned permutation
// reproduces challenge derivation exactly. An extension sample is one event
// carrying its basis coefficients; the inner duplex may or may not permute on
// any given call, which is exactly why the log records calls, not permutes.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "event", content = "value", deny_unknown_fields)]
pub enum Event {
    ObserveVal(u32),
    /// A Merkle-cap commitment: one event per observed cap, all roots.
    ObserveCap(Vec<[u32; 8]>),
    SampleVal(u32),
    SampleExt([u32; 4]),
    SampleBits {
        bits: usize,
        value: u64,
    },
    CheckWitness {
        bits: usize,
        witness: u32,
        ok: bool,
    },
    Grind {
        bits: usize,
        witness: u32,
    },
}

pub type EventLog = Arc<Mutex<Vec<Event>>>;

/// Wraps the plain duplex challenger and records every trait-boundary event.
///
/// Clones share one log sink: the config clones its stored challenger per
/// run, and the observation must escape that clone.
#[derive(Clone, Debug)]
pub struct RecordingChallenger {
    inner: PlainChallenger,
    log: EventLog,
}

impl RecordingChallenger {
    pub fn new(inner: PlainChallenger) -> (Self, EventLog) {
        let log: EventLog = Arc::new(Mutex::new(Vec::new()));
        (
            Self {
                inner,
                log: log.clone(),
            },
            log,
        )
    }

    fn push(&self, event: Event) {
        self.log.lock().unwrap().push(event);
    }
}

impl CanObserve<Val> for RecordingChallenger {
    fn observe(&mut self, value: Val) {
        self.push(Event::ObserveVal(value.as_canonical_u32()));
        self.inner.observe(value);
    }
}

impl CanObserve<MerkleCap<Val, [Val; 8]>> for RecordingChallenger {
    fn observe(&mut self, value: MerkleCap<Val, [Val; 8]>) {
        let roots: &[[Val; 8]] = value.as_ref();
        self.push(Event::ObserveCap(
            roots
                .iter()
                .map(|digest| digest.map(|v| v.as_canonical_u32()))
                .collect(),
        ));
        self.inner.observe(value);
    }
}

impl CanSample<Val> for RecordingChallenger {
    fn sample(&mut self) -> Val {
        let value: Val = self.inner.sample();
        self.push(Event::SampleVal(value.as_canonical_u32()));
        value
    }
}

// Required by the StarkConfig bound (Challenger: CanSample<Challenge>).
// The pinned uni-stark verifier reaches extension challenges through the
// FieldChallenger default `sample_algebra_element` — four base samples, so
// this route records nothing on the current witness; the delegation keeps
// it faithful if a future upstream path calls it directly.
impl CanSample<Challenge> for RecordingChallenger {
    fn sample(&mut self) -> Challenge {
        let value: Challenge = self.inner.sample();
        let coefficients: &[Val] = value.as_basis_coefficients_slice();
        let mut recorded = [0u32; 4];
        for (slot, coefficient) in recorded.iter_mut().zip(coefficients) {
            *slot = coefficient.as_canonical_u32();
        }
        self.push(Event::SampleExt(recorded));
        value
    }
}

impl CanSampleBits<usize> for RecordingChallenger {
    fn sample_bits(&mut self, bits: usize) -> usize {
        let value = self.inner.sample_bits(bits);
        self.push(Event::SampleBits {
            bits,
            value: value as u64,
        });
        value
    }
}

impl FieldChallenger<Val> for RecordingChallenger {}

impl GrindingChallenger for RecordingChallenger {
    type Witness = Val;

    fn grind(&mut self, bits: usize) -> Val {
        // Prover-side only. Delegating keeps the inner state identical to a
        // plain run; the found witness is recorded so the log stays a total
        // account of state-changing calls.
        let witness = self.inner.grind(bits);
        self.push(Event::Grind {
            bits,
            witness: witness.as_canonical_u32(),
        });
        witness
    }

    fn check_witness(&mut self, bits: usize, witness: Val) -> bool {
        // Spelled out (rather than the trait default) so the verifier-side
        // grinding check is one recorded event with its verdict, while the
        // inner state advances exactly as the default would advance it —
        // including the zero-bit early return, which touches no sponge
        // state at all. A spurious observe here shifts every later
        // challenge; the first draft of this method proved it.
        let ok = if bits == 0 {
            true
        } else {
            self.inner.observe(witness);
            self.inner.sample_bits(bits) == 0
        };
        self.push(Event::CheckWitness {
            bits,
            witness: witness.as_canonical_u32(),
            ok,
        });
        ok
    }
}

// ---------------------------------------------------------------------------
// The fibonacci-shaped AIR: two columns, three public values (a, b, x), the
// smallest shape that exercises public-value observation. Adapted from the
// pinned revision's own uni-stark test AIR so the constraint content is the
// upstream-exercised one.
// ---------------------------------------------------------------------------

pub const AIR_NAME: &str = "zkc.replay.fib_air";
pub const NUM_FIB_COLS: usize = 2;
pub const NUM_PUBLIC_VALUES: usize = 3;

pub struct FibAir;

impl<F> BaseAir<F> for FibAir {
    fn width(&self) -> usize {
        NUM_FIB_COLS
    }

    fn num_public_values(&self) -> usize {
        NUM_PUBLIC_VALUES
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}

impl<AB: AirBuilder> Air<AB> for FibAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let pis = builder.public_values();
        let (a, b, x) = (pis[0], pis[1], pis[2]);

        let local = main.current_slice();
        let (left, right) = (local[0], local[1]);
        let next = main.next_slice();
        let (next_left, next_right) = (next[0], next[1]);

        let mut when_first = builder.when_first_row();
        when_first.assert_eq(left, a);
        when_first.assert_eq(right, b);

        let mut when_transition = builder.when_transition();
        when_transition.assert_eq(right, next_left);
        when_transition.assert_eq(left + right, next_right);

        builder.when_last_row().assert_eq(right, x);
    }
}

pub fn generate_trace(a: u64, b: u64, rows: usize) -> RowMajorMatrix<Val> {
    assert!(rows.is_power_of_two());
    let mut values = Vec::with_capacity(rows * NUM_FIB_COLS);
    let (mut left, mut right) = (Val::from_u64(a), Val::from_u64(b));
    for _ in 0..rows {
        values.push(left);
        values.push(right);
        let next_right = left + right;
        left = right;
        right = next_right;
    }
    RowMajorMatrix::new(values, NUM_FIB_COLS)
}

pub fn public_values(a: u64, b: u64, rows: usize) -> Vec<Val> {
    let trace = generate_trace(a, b, rows);
    let x = trace.values[(rows - 1) * NUM_FIB_COLS + 1];
    vec![Val::from_u64(a), Val::from_u64(b), x]
}

// ---------------------------------------------------------------------------
// Configuration and identity.
// ---------------------------------------------------------------------------

/// The fixture's own parameter point, kept for the captured-transcript
/// replay legs whose event logs were recorded at it.
pub fn fri_parameters(mmcs: ChallengeMmcs) -> FriParameters<ChallengeMmcs> {
    fri_parameters_for(
        mmcs,
        NUM_QUERIES,
        QUERY_POW_BITS,
        LOG_BLOWUP,
        LOG_FINAL_POLY_LEN,
    )
}

/// The family instance's parameter point: the query count and the
/// grinding bits, rate, and final length come from the artifact's own
/// schedule (the runner and the judge derive them from the document);
/// the fold arity and commit grinding stay the value-faithful
/// template's shape.
pub fn fri_parameters_for(
    mmcs: ChallengeMmcs,
    num_queries: usize,
    query_pow_bits: usize,
    log_blowup: usize,
    log_final_poly_len: usize,
) -> FriParameters<ChallengeMmcs> {
    FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity: MAX_LOG_ARITY,
        num_queries,
        commit_proof_of_work_bits: COMMIT_POW_BITS,
        query_proof_of_work_bits: query_pow_bits,
        mmcs,
    }
}

fn pcs() -> Pcs {
    let perm = default_babybear_poseidon2_16();
    let hash = FieldHash::new(perm.clone());
    let compress = Compress::new(perm);
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    Pcs::new(Dft::default(), val_mmcs, fri_parameters(challenge_mmcs))
}

pub fn plain_config() -> PlainConfig {
    let perm = default_babybear_poseidon2_16();
    PlainConfig::new(pcs(), PlainChallenger::new(perm))
}

pub fn recording_config() -> (RecordingConfig, EventLog) {
    let perm = default_babybear_poseidon2_16();
    let (challenger, log) = RecordingChallenger::new(PlainChallenger::new(perm));
    (RecordingConfig::new(pcs(), challenger), log)
}

/// Behavioral content address of the pinned permutation: the digest of its
/// output on a fixed input vector. Round constants are verifier identity;
/// this pins them without depending on how the crate spells them.
pub fn permutation_behavior_digest() -> String {
    use p3_symmetric::Permutation;
    let perm = default_babybear_poseidon2_16();
    let mut state = [Val::ZERO; 16];
    for (index, slot) in state.iter_mut().enumerate() {
        *slot = Val::from_u64(index as u64);
    }
    perm.permute_mut(&mut state);
    let mut hasher = Sha256::new();
    for value in state {
        hasher.update(value.as_canonical_u32().to_le_bytes());
    }
    hex::encode(hasher.finalize())
}

/// Declared content address of the AIR: name, shape, and constraint version.
/// The upstream verifier does not absorb the AIR into the transcript (an
/// acknowledged upstream gap), so this binding is structural on the zkc side
/// and travels in the fixture as such.
pub fn air_content_digest() -> String {
    let description = format!(
        "{AIR_NAME}|width={NUM_FIB_COLS}|public_values={NUM_PUBLIC_VALUES}|constraints=fib:first(a,b),transition(shift,add),last(x)|degree=2"
    );
    hex::encode(Sha256::digest(description.as_bytes()))
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

// ---------------------------------------------------------------------------
// The fixture.
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fixture {
    /// Prototype format tag. Public schemas wait for the Binding Foundation;
    /// nothing outside this crate may depend on this shape.
    pub format: String,
    /// Explicit prototype marker inside the record itself.
    pub status: String,
    pub backend: BackendRecord,
    pub config: ConfigRecord,
    pub air: AirRecord,
    pub instance: InstanceRecord,
    pub proof: ProofRecord,
    /// The verifier-side transcript, one entry per challenger trait call.
    pub transcript: Vec<Event>,
    pub acceptance: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BackendRecord {
    pub repository: String,
    pub revision: String,
    /// The upstream crates this capture links, all at the pinned revision.
    pub crates: Vec<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
#[serde(deny_unknown_fields)]
pub struct ConfigRecord {
    pub field: String,
    pub extension_degree: usize,
    pub permutation: String,
    pub permutation_behavior_digest: String,
    pub sponge_width: usize,
    pub sponge_rate: usize,
    pub digest_elems: usize,
    pub mmcs: String,
    pub dft: String,
    pub pcs: String,
    pub challenger: String,
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_proof_of_work_bits: usize,
    pub query_proof_of_work_bits: usize,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AirRecord {
    pub name: String,
    /// Structural binding only: the upstream transcript does not carry it.
    pub content_digest: String,
    pub width: usize,
    pub num_public_values: usize,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstanceRecord {
    pub public_values: Vec<u32>,
    pub degree_bits: usize,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProofRecord {
    /// Proof-byte identity is the tuple (encoding, crate revision, proof type
    /// parameters); upstream defines no canonical byte encoding.
    pub encoding: String,
    pub bytes_hex: String,
    pub sha256: String,
}

pub fn config_record() -> ConfigRecord {
    ConfigRecord {
        field: "baby_bear".to_string(),
        extension_degree: 4,
        permutation: "default_babybear_poseidon2_16".to_string(),
        permutation_behavior_digest: permutation_behavior_digest(),
        sponge_width: 16,
        sponge_rate: 8,
        digest_elems: 8,
        mmcs: "merkle_tree".to_string(),
        dft: "radix2_dit_parallel".to_string(),
        pcs: "two_adic_fri".to_string(),
        challenger: "duplex".to_string(),
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: LOG_FINAL_POLY_LEN,
        max_log_arity: MAX_LOG_ARITY,
        num_queries: NUM_QUERIES,
        commit_proof_of_work_bits: COMMIT_POW_BITS,
        query_proof_of_work_bits: QUERY_POW_BITS,
    }
}
