//! Independent primitive vectors and pinned upstream challenger comparisons.
use p3_baby_bear_043::{BabyBear, default_babybear_poseidon2_16};
use p3_challenger_043::{CanObserve, CanSample, DuplexChallenger};
use p3_field_043::{PrimeCharacteristicRing, PrimeField32};
use serde_json::Value;
use std::{fs, path::PathBuf};
use zkc_backends::external::{
    Error, Work,
    monero::{self, BP_PLUS_INITIAL, HashChain},
    openvm::{self, Duplex},
};

fn fixture(name: &str) -> PathBuf {
    zkc_test_support::source(&format!("external-transcript/{name}"))
}
fn read_json(name: &str) -> Value {
    serde_json::from_slice(&fs::read(fixture(name)).unwrap()).unwrap()
}

fn decode_word(s: &str) -> Result<[u8; 32], String> {
    zkc_test_support::unhex(s)
        .try_into()
        .map_err(|_| "word length".into())
}
fn encode_hex(b: &[u8]) -> String {
    zkc_test_support::hex(b)
}
#[test]
fn monero_stateless_hash_empty_update_and_zero_conversion_are_distinct() {
    let mut chain = HashChain::new(BP_PLUS_INITIAL);
    let saved = chain.state();
    let hash = monero::hash_to_scalar(&[[1; 32], [2; 32]]);
    assert_eq!(chain.state(), saved);
    assert_ne!(chain.update(&[]), saved);
    assert_eq!(chain.state(), monero::hash_to_scalar(&[saved]));
    assert_ne!(monero::hash_to_scalar(&[]), chain.state());
    assert_ne!(hash, chain.update(&[[1; 32], [2; 32]]));
    assert_eq!(monero::reduce_digest([0; 32]), [0; 32]);
    assert_eq!(monero::hash_work(2, true).unwrap().hash_bytes, 96);
    assert_eq!(
        monero::hash_work(usize::MAX, true),
        Err(Error::SizeOverflow)
    );
}

#[test]
fn duplex_matches_separate_pinned_challenger_across_partial_rate_boundaries() {
    let mut native = Duplex::new();
    let mut reference =
        DuplexChallenger::<BabyBear, _, 16, 8>::new(default_babybear_poseidon2_16());
    for round in 0..96u32 {
        let fields: Vec<_> = (0..(round % 19))
            .map(|i| (round * 131 + i * 17) % openvm::MODULUS)
            .collect();
        let predicted = native.observe_work(fields.len()).unwrap();
        assert_eq!(native.observe(&fields).unwrap(), predicted);
        for value in fields {
            reference.observe(BabyBear::from_u32(value));
        }
        let mut state = reference.sponge_state.map(|x| x.as_canonical_u32());
        for (i, x) in reference.input_buffer.iter().enumerate() {
            state[i] = x.as_canonical_u32();
        }
        assert_eq!(native.snapshot().state, state);
        assert_eq!(native.snapshot().absorb_index, reference.input_buffer.len());
        let count = (round as usize * 7) % 23;
        let predicted = native.sample_work(count).unwrap();
        let mut actual = Work::default();
        for _ in 0..count {
            let sample = native.sample();
            let expected: BabyBear = reference.sample();
            assert_eq!(sample.value, expected.as_canonical_u32());
            actual = actual.checked_add(sample.work).unwrap();
        }
        assert_eq!(actual, predicted);
        if native.snapshot().absorb_index == 0 {
            assert_eq!(
                native.snapshot().sample_index,
                reference.output_buffer.len()
            );
        }
    }
}

#[test]
fn conversion_grinding_and_failed_direct_checks_preserve_exact_effects() {
    let mut seed = Duplex::new();
    seed.observe(&[1, 2, 3, 4, 5]).unwrap();
    for bits in 0..=30 {
        let mut direct = seed.clone();
        let raw = direct.sample();
        let mut masked = seed.clone();
        let sample = masked.sample_bits(bits).unwrap();
        assert_eq!(sample.value, raw.value & ((1u32 << bits) - 1));
        assert_eq!(direct.snapshot(), masked.snapshot());
    }
    let mut coefficients = seed.clone();
    let expected = std::array::from_fn::<_, 4, _>(|_| coefficients.sample().value);
    let mut ext = seed.clone();
    assert_eq!(ext.sample_ext().value, expected);
    assert_eq!(ext.snapshot(), coefficients.snapshot());
    let original = seed.snapshot();
    let mut zero = seed.clone();
    assert!(zero.check_witness(0, 123).unwrap().value);
    assert_eq!(zero.snapshot(), original);
    let mut fail = None;
    let mut pass = None;
    for witness in 0..1000 {
        let trial = seed.trial_witness(3, witness).unwrap();
        assert_eq!(trial.work, seed.witness_work(3).unwrap());
        assert_eq!(seed.snapshot(), original);
        if trial.value {
            pass = Some(witness);
        } else {
            fail = Some(witness);
        }
        if pass.is_some() && fail.is_some() {
            break;
        }
    }
    let mut live = seed.clone();
    assert!(!live.check_witness(3, fail.unwrap()).unwrap().value);
    assert_ne!(live.snapshot(), original);
    let mut selected = seed.clone();
    assert!(selected.check_witness(3, pass.unwrap()).unwrap().value);
    assert_ne!(selected.snapshot(), original);
    let mut manual = seed.clone();
    manual.observe(&[pass.unwrap()]).unwrap();
    manual.sample_bits(3).unwrap();
    assert_eq!(manual.snapshot(), selected.snapshot());
    for count in 0..8 {
        let mut d = Duplex::new();
        d.observe(&vec![17; count]).unwrap();
        assert_eq!(
            d.check_witness(3, 2).unwrap().work,
            d.witness_work(3).unwrap()
        );
    }
}

#[test]
fn invalid_native_inputs_refuse_before_state_changes() {
    let mut d = Duplex::new();
    d.observe(&[42]).unwrap();
    let saved = d.snapshot();
    assert_eq!(
        d.observe(&[1, openvm::MODULUS]),
        Err(Error::NonCanonicalField)
    );
    assert_eq!(d.sample_bits(31), Err(Error::InvalidBitWidth));
    assert_eq!(d.check_witness(31, 0), Err(Error::InvalidBitWidth));
    assert_eq!(d.check_witness(0, u32::MAX), Err(Error::NonCanonicalField));
    assert_eq!(d.snapshot(), saved);
    assert_eq!(
        openvm::challenge_bits(openvm::MODULUS, 0),
        Err(Error::NonCanonicalField)
    );
    assert_eq!(d.observe_work(usize::MAX), Err(Error::SizeOverflow));
    assert_eq!(
        Work {
            hash_calls: u64::MAX,
            ..Work::default()
        }
        .checked_add(Work {
            hash_calls: 1,
            ..Work::default()
        }),
        Err(Error::SizeOverflow)
    );
}

#[test]
fn installed_keccak_and_scalar_reduction_match_pinned_native_primitive_vectors() {
    let vectors = read_json("monero-hash-vectors.json");
    assert_eq!(vectors["vectors"].as_array().unwrap().len(), 6);
    for vector in vectors["vectors"].as_array().unwrap() {
        let words: Vec<_> = vector["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| decode_word(v.as_str().unwrap()).unwrap())
            .collect();
        assert_eq!(
            encode_hex(&monero::hash_to_scalar(&words)),
            vector["scalar"]
        );
        assert_eq!(
            encode_hex(&monero::reduce_digest(
                decode_word(vector["keccak256"].as_str().unwrap()).unwrap()
            )),
            vector["scalar"]
        );
    }
}

#[test]
fn explicit_snapshot_import_validates_representation_and_preserves_continuation() {
    let mut live = Duplex::new();
    for step in 0..80u32 {
        let snapshot = live.snapshot();
        let mut imported = Duplex::from_snapshot(snapshot.clone()).unwrap();
        assert_eq!(imported.snapshot(), snapshot);
        let mut continuing = live.clone();
        assert_eq!(imported.sample_ext(), continuing.sample_ext());
        assert_eq!(imported.snapshot(), continuing.snapshot());
        if step % 3 == 0 {
            live.sample();
        } else {
            live.observe(&[step]).unwrap();
        }
    }
    let mut invalid = live.snapshot();
    invalid.absorb_index = openvm::RATE;
    assert_eq!(
        Duplex::from_snapshot(invalid).unwrap_err(),
        Error::MalformedReplay
    );
    let mut invalid = live.snapshot();
    invalid.sample_index = openvm::RATE + 1;
    assert_eq!(
        Duplex::from_snapshot(invalid).unwrap_err(),
        Error::MalformedReplay
    );
    let mut invalid = live.snapshot();
    invalid.state[15] = openvm::MODULUS;
    assert_eq!(
        Duplex::from_snapshot(invalid).unwrap_err(),
        Error::NonCanonicalField
    );
    // An importer establishes representation validity, not historical reachability.
    let explicit = openvm::Snapshot {
        state: [7; 16],
        absorb_index: 7,
        sample_index: 8,
    };
    assert_eq!(
        Duplex::from_snapshot(explicit.clone()).unwrap().snapshot(),
        explicit
    );
}
