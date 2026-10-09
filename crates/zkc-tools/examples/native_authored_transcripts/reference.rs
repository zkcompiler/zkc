//! Independent schedules, primitive-library comparisons and archived checkpoints.
use super::{codec, inputs, messages, unhex, words};
use p3_baby_bear_043::{BabyBear, default_babybear_poseidon2_16};
use p3_challenger_043::{CanObserve, CanSample, DuplexChallenger};
use p3_field_043::{PrimeCharacteristicRing, PrimeField32};
use serde_json::Value as Json;
use sha2::Digest;
use zkc_backends::{
    Policy, Sequence, Value,
    external::{monero, openvm},
};
use zkc_runtime::interactive::LogicalType;
use zkc_tools::proof::NativeDeployment;
fn packed(state: &openvm::Duplex) -> Value {
    let s = state.snapshot();
    words(
        [1514881876, 0, 2]
            .into_iter()
            .chain(s.state.map(u64::from))
            .chain([s.absorb_index as u64, s.sample_index as u64]),
    )
}
// Separate hash invocation and reduction, outside the installed adapter.
pub(super) fn hash_word(bytes: &[u8]) -> [u8; 32] {
    curve25519_dalek::Scalar::from_bytes_mod_order(sha3::Keccak256::digest(bytes).into()).to_bytes()
}
pub(super) fn monero_data(count: usize, snapshot: bool) -> (Vec<Value>, Vec<Value>, u64) {
    let seed = std::array::from_fn(|i| (i * 7 + 129) as u8);
    let prefix: Vec<monero::Word> = vec![[3; 32], [19; 32]];
    let mut state = monero::HashChain::new(seed);
    let mut reference = hash_word(&[seed.as_slice(), prefix.concat().as_slice()].concat());
    assert_eq!(state.update(&prefix), reference);
    let mut work = monero::hash_work(prefix.len(), true)
        .unwrap()
        .units()
        .unwrap();
    let mut expected = Vec::new();
    for i in 0..count {
        // Include empty updates and nonuniform lengths: boundaries affect hashing.
        let row: Vec<monero::Word> = (0..i % 3).map(|j| [((i + j) * 11 + 1) as u8; 32]).collect();
        reference = hash_word(&[reference.as_slice(), row.concat().as_slice()].concat());
        assert_eq!(state.update(&row), reference);
        work += monero::hash_work(row.len(), true).unwrap().units().unwrap();
        expected.push(words(row.iter().flatten().copied().map(u64::from)));
    }
    let batch = Value::Sequence(
        Sequence::new(
            LogicalType::parse("indices").unwrap(),
            expected.clone(),
            &Policy::default(),
        )
        .unwrap(),
    );
    let final_word = state.update(&[]);
    assert_eq!(final_word, hash_word(&reference));
    work += monero::hash_work(0, true).unwrap().units().unwrap();
    expected.push(words(final_word.map(u64::from)));
    let initial = if snapshot {
        words([1514881876, 0, 1].into_iter().chain(seed.map(u64::from)))
    } else {
        words(seed.map(u64::from))
    };
    (
        vec![
            initial,
            words(prefix.iter().flatten().copied().map(u64::from)),
            Value::Index(count as u64),
            batch,
            Value::Bool(true),
        ],
        expected,
        work,
    )
}
pub(super) fn openvm_data(
    count: usize,
    snapshot: bool,
    duplicate: bool,
    difficulty: u32,
    width: u32,
) -> (Vec<Value>, Vec<Value>, u64, u64) {
    let context: Vec<u32> = (0..count).map(|i| (i * 97 + 13) as u32).collect();
    let mut live = openvm::Duplex::new();
    let mut independent =
        DuplexChallenger::<BabyBear, _, 16, 8>::new(default_babybear_poseidon2_16());
    for &v in &context {
        independent.observe(BabyBear::from_u32(v));
    }
    let observed = live.observe(&context).unwrap().units().unwrap();
    let mut trials = 0;
    let mut candidates = Vec::new();
    let chosen = (0..10000)
        .find(|&w| {
            candidates.push(u64::from(w));
            let checked = live.trial_witness(difficulty, w).unwrap();
            let mut trial = independent.clone();
            let accepted = if difficulty == 0 {
                true
            } else {
                trial.observe(BabyBear::from_u32(w));
                let value: BabyBear = trial.sample();
                value.as_canonical_u32() & ((1 << difficulty) - 1) == 0
            };
            assert_eq!(checked.value, accepted);
            trials += checked.work.units().unwrap();
            checked.value
        })
        .unwrap();
    // A noncanonical unused candidate must never be checked after success.
    candidates.push(u64::MAX);
    let initial = if snapshot {
        packed(&live)
    } else {
        words(context.iter().copied().map(u64::from))
    };
    let mut work = if snapshot { 0 } else { observed };
    let checked = live.check_witness(difficulty, chosen).unwrap();
    assert!(checked.value);
    work += checked.work.units().unwrap();
    let ext = live.sample_ext();
    work += ext.work.units().unwrap();
    let bits = live.sample_bits(width).unwrap();
    work += bits.work.units().unwrap();
    let scalar = live.sample();
    work += scalar.work.units().unwrap();
    if difficulty != 0 {
        independent.observe(BabyBear::from_u32(chosen));
        let check: BabyBear = independent.sample();
        assert_eq!(check.as_canonical_u32() & ((1 << difficulty) - 1), 0);
    }
    let extension: [u32; 4] = std::array::from_fn(|_| {
        let x: BabyBear = independent.sample();
        x.as_canonical_u32()
    });
    assert_eq!(extension, ext.value);
    let bit_sample: BabyBear = independent.sample();
    assert_eq!(
        bit_sample.as_canonical_u32() & ((1 << width) - 1),
        bits.value
    );
    let scalar_sample: BabyBear = independent.sample();
    assert_eq!(scalar_sample.as_canonical_u32(), scalar.value);
    (
        vec![
            initial,
            Value::Index(difficulty.into()),
            Value::Index(width.into()),
            words(candidates),
        ],
        vec![
            Value::Index(chosen.into()),
            words(ext.value.map(u64::from)),
            Value::Index(bits.value.into()),
            Value::Index(scalar.value.into()),
        ],
        work + trials * if duplicate { 2 } else { 1 },
        work,
    )
}
pub(super) fn archived_answers(deployment: &NativeDeployment, envelope: &Json, family: &str) {
    // Embed the reference data so installed consumers do not need the build checkout.
    let (values, expected) = if family == "monero" {
        let saved: Json = serde_json::from_slice(
            include_bytes!("../../../zkc-test-support/fixtures/external-transcript/ordinary-monero-1.transcript.json"),
        )
        .unwrap();
        let proof = include_bytes!(
            "../../../zkc-test-support/fixtures/external-transcript/ordinary-monero-1.proof"
        );
        let public: Vec<u8> = saved["V"]
            .as_array()
            .unwrap()
            .iter()
            .flat_map(|v| unhex(v.as_str().unwrap()))
            .collect();
        let a = words(proof[..32].iter().copied().map(u64::from));
        let batch = Value::Sequence(
            Sequence::new(
                LogicalType::parse("indices").unwrap(),
                vec![a.clone()],
                &Policy::default(),
            )
            .unwrap(),
        );
        (
            vec![
                words(
                    unhex(saved["initial"].as_str().unwrap())
                        .into_iter()
                        .map(u64::from),
                ),
                words(hash_word(&public).map(u64::from)),
                Value::Index(1),
                batch,
                Value::Bool(true),
            ],
            vec![
                a,
                words(
                    unhex(saved["z"].as_str().unwrap())
                        .into_iter()
                        .map(u64::from),
                ),
            ],
        )
    } else {
        let saved: Json = serde_json::from_slice(
            include_bytes!("../../../zkc-test-support/fixtures/external-transcript/ordinary-openvm-0.transcript.json"),
        )
        .unwrap();
        let rows = saved.as_array().unwrap();
        let n = rows.iter().position(|v| v["sample"] == true).unwrap();
        assert!(rows[n..n + 6].iter().all(|v| v["sample"] == true));
        let sample = |i: usize| rows[n + i]["value"].as_u64().unwrap();
        (
            vec![
                words(rows[..n].iter().map(|v| v["value"].as_u64().unwrap())),
                Value::Index(0),
                Value::Index(30),
                words([5]),
            ],
            vec![
                Value::Index(5),
                words((0..4).map(sample)),
                Value::Index(sample(4) & ((1 << 30) - 1)),
                Value::Index(sample(5)),
            ],
        )
    };
    let produced = deployment
        .execute(&inputs(envelope, &values, true), None)
        .unwrap()
        .outcome
        .unwrap();
    let expected: Vec<_> = expected
        .iter()
        .map(|v| codec().encode_native_value(v).unwrap())
        .collect();
    assert_eq!(messages(&produced), expected);
    deployment
        .execute(&inputs(envelope, &values, false), Some(&produced))
        .unwrap()
        .outcome
        .unwrap();
}
