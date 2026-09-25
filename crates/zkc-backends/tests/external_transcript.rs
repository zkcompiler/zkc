//! Finite correspondence with archived REAL upstream proofs. The fixture
//! schedule/decoder is test code, outside the provider and compiler runtime.
use p3_baby_bear_043::{BabyBear, default_babybear_poseidon2_16};
use p3_challenger_043::{CanObserve, CanSample, DuplexChallenger};
use p3_field_043::{PrimeCharacteristicRing, PrimeField32};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{fs, path::PathBuf};
use zkc_backends::external::{
    Error, Work,
    monero::{self, BP_PLUS_INITIAL, HashChain},
    openvm::{self, Duplex},
    replay::{self, Limits, decode_word, encode_hex},
    wire::{ItemValue, Unobserved, WireItem, WireMap},
};

fn fixture(name: &str) -> PathBuf {
    zkc_test_support::source(&format!("external-transcript/{name}"))
}
fn read_json(name: &str) -> Value {
    serde_json::from_slice(&fs::read(fixture(name)).unwrap()).unwrap()
}
fn run(program: &Value) -> Result<Value, Error> {
    replay::replay_json(&serde_json::to_vec(program).unwrap(), Limits::default())
}
fn item(id: &str, wire_index: Value, kind: &str, values: Value) -> Value {
    json!({"id":id,"origin":format!("fixture:{id}"),"wire_index":wire_index,"kind":kind,"values":values})
}

// Only the bounded canonical fixtures (6..=10 L/R entries, one-byte lengths).
// This is not advertised as a complete Monero decoder or verifier.
fn bp_fields(bytes: &[u8]) -> Result<Vec<(String, Vec<String>)>, ()> {
    if bytes.len() < 194 {
        return Err(());
    }
    let mut fields = Vec::new();
    for (i, name) in ["A", "A1", "B", "r1", "s1", "d1"].into_iter().enumerate() {
        fields.push((
            name.to_owned(),
            vec![encode_hex(&bytes[i * 32..(i + 1) * 32])],
        ));
    }
    let mut cursor = 192;
    let mut previous = None;
    for name in ["L", "R"] {
        let count = *bytes.get(cursor).ok_or(())? as usize;
        cursor += 1;
        if !(6..=10).contains(&count) || previous.is_some_and(|n| n != count) {
            return Err(());
        }
        previous = Some(count);
        let mut entries = Vec::new();
        for _ in 0..count {
            entries.push(encode_hex(bytes.get(cursor..cursor + 32).ok_or(())?));
            cursor += 32;
        }
        fields.push((name.to_owned(), entries));
    }
    if cursor != bytes.len() {
        return Err(());
    }
    Ok(fields)
}
fn bp_program(name: &str) -> Value {
    let expected = read_json(name);
    let proof = fs::read(fixture(&name.replace(".transcript.json", ".proof"))).unwrap();
    let fields = bp_fields(&proof).unwrap();
    let mut items = vec![item("V", Value::Null, "words", expected["V"].clone())];
    for (i, (name, words)) in fields.iter().enumerate() {
        if name == "L" || name == "R" {
            for (j, word) in words.iter().enumerate() {
                // Separate container order (all L before all R) from round order.
                items.push(item(
                    &format!("{name}{j}"),
                    json!(6 + (i - 6) * words.len() + j),
                    "words",
                    json!([word]),
                ));
            }
        } else {
            items.push(item(name, json!(i), "words", json!(words)));
        }
    }
    let rounds = fields[6].1.len();
    let mut events = vec![
        json!({"op":"hash","items":["V"],"output":"Hv"}),
        json!({"op":"update","items":["Hv"]}),
        json!({"op":"update","items":["A"],"expect":expected["y"]}),
        json!({"op":"update","items":[],"expect":expected["z"]}),
    ];
    for i in 0..rounds {
        events.push(json!({"op":"update","items":[format!("L{i}"),format!("R{i}")],"expect":expected["x"][i]}));
    }
    events.push(json!({"op":"update","items":["A1","B"],"expect":expected["e"]}));
    json!({"version":1,"profile":replay::MONERO_PROFILE,"initial":expected["initial"],"items":items,
        "unobserved":[{"item":"r1","guard":"bp-plus:verification-equation"},{"item":"s1","guard":"bp-plus:verification-equation"},{"item":"d1","guard":"bp-plus:verification-equation"}],"events":events})
}
fn ov_program(name: &str) -> Value {
    let source = read_json(name);
    let mut events = Vec::new();
    let mut items = Vec::new();
    for (i, event) in source.as_array().unwrap().iter().enumerate() {
        if event["sample"].as_bool().unwrap() {
            events.push(json!({"op":"sample","expect":event["value"]}));
        } else {
            let id = format!("observation{i}");
            items.push(item(&id, Value::Null, "fields", json!([event["value"]])));
            events.push(json!({"op":"observe","items":[id]}));
        }
    }
    json!({"version":1,"profile":replay::OPENVM_PROFILE,"items":items,"unobserved":[],"events":events})
}

#[test]
fn archived_source_and_fixture_pins_are_explicit_and_fixture_bytes_match() {
    let manifest: Value =
        serde_json::from_str(include_str!("../src/external/provenance.json")).unwrap();
    assert_eq!(manifest["sources"].as_array().unwrap().len(), 6);
    let fixtures = manifest["fixtures"].as_array().unwrap();
    assert_eq!(fixtures.len(), 35);
    for entry in fixtures
        .iter()
        .chain(manifest["primitive_vectors"].as_array().unwrap())
    {
        let actual = Sha256::digest(fs::read(fixture(entry["file"].as_str().unwrap())).unwrap());
        assert_eq!(encode_hex(&actual), entry["sha256"].as_str().unwrap());
    }
    assert!(
        manifest["dependencies"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["name"] == "p3-baby-bear" && entry["version"] == "0.4.3")
    );
}

#[test]
fn all_fifteen_archived_bp_plus_checkpoint_sets_match() {
    let mut count = 0;
    for prefix in ["ordinary", "instrumented"] {
        for (size, bytes) in [
            (1, 578),
            (2, 642),
            (3, 706),
            (4, 706),
            (8, 770),
            (9, 834),
            (16, 834),
        ] {
            let name = format!("{prefix}-monero-{size}.transcript.json");
            assert_eq!(
                fs::read(fixture(&name.replace(".transcript.json", ".proof")))
                    .unwrap()
                    .len(),
                bytes
            );
            let program = bp_program(&name);
            assert_eq!(program["initial"], encode_hex(&BP_PLUS_INITIAL));
            let output = run(&program).unwrap_or_else(|e| panic!("{name}: {e}"));
            let expected = read_json(&name);
            assert_eq!(
                output["checkpoints"].as_array().unwrap().last().unwrap()["value"],
                expected["e"]
            );
            assert_eq!(
                output["work"]["hash_calls"].as_u64().unwrap(),
                expected["x"].as_array().unwrap().len() as u64 + 5
            );
            count += 1;
        }
    }
    run(&bp_program(
        "instrumented-monero-consistent-torsion.transcript.json",
    ))
    .unwrap();
    assert_eq!(count + 1, 15);
}

#[test]
fn all_five_archived_openvm_traces_match_including_mixed_interactions() {
    for (case, count) in [
        ("0", 575),
        ("1", 523),
        ("2", 519),
        ("mixture-1", 2453),
        ("mixture-4", 2801),
    ] {
        let name = format!("ordinary-openvm-{case}.transcript.json");
        let program = ov_program(&name);
        let output = run(&program).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(output["checkpoints"].as_array().unwrap().len(), count);
        let observations = program["items"].as_array().unwrap().len();
        assert_eq!(output["work"]["observes"], observations);
        assert_eq!(output["work"]["samples"], count - observations);
    }
}

#[test]
fn bp_statement_state_order_grouping_and_empty_update_mutations_fail() {
    let original = bp_program("ordinary-monero-3.transcript.json");
    let mut bad = original.clone();
    bad["initial"] = json!(encode_hex(&[0; 32]));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["items"][0]["values"][0] = json!(encode_hex(&[0; 32]));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"].as_array_mut().unwrap().remove(3);
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"][4]["items"] = json!(["R0", "L0"]);
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"][4]["items"] = json!(["R0"]);
    bad["events"]
        .as_array_mut()
        .unwrap()
        .insert(4, json!({"op":"update","items":["L0"]}));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"]
        .as_array_mut()
        .unwrap()
        .insert(4, json!({"op":"update","items":["r1","s1","d1"]}));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    // Response fields are unobserved and therefore do not change the transcript.
    // Their equation guard is an EXTERNAL obligation; replay is no proof verifier.
    let mut changed = original.clone();
    changed["items"][4]["values"][0] = json!(encode_hex(&[0; 32]));
    assert_eq!(run(&changed).unwrap(), run(&original).unwrap());
    // Container order metadata does not sort authored events.
    let mut changed = original.clone();
    changed["items"].as_array_mut().unwrap().reverse();
    assert_eq!(run(&changed).unwrap(), run(&original).unwrap());
}

#[test]
fn openvm_wrong_observe_sample_order_extra_absorb_and_state_check_fail() {
    let original = ov_program("ordinary-openvm-mixture-4.transcript.json");
    let mut bad = original.clone();
    bad["events"].as_array_mut().unwrap().swap(0, 1);
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"].as_array_mut().unwrap().remove(0);
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"][0]["op"] = json!("sample");
    bad["events"][0].as_object_mut().unwrap().remove("items");
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"][0]["expect_state"] = json!({"state":([0;16]),"absorb_index":0,"sample_index":0});
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut omitted = original.clone();
    omitted["items"].as_array_mut().unwrap().push(item(
        "response",
        json!(0),
        "fields",
        json!([17, 19]),
    ));
    omitted["unobserved"] = json!([{"item":"response","guard":"whir:authenticated-opening"}]);
    assert_eq!(run(&omitted).unwrap(), run(&original).unwrap());
    let mut bad = omitted.clone();
    bad["events"]
        .as_array_mut()
        .unwrap()
        .insert(0, json!({"op":"observe","items":["response"]}));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["items"][0]["values"][0] = json!(openvm::MODULUS);
    assert_eq!(run(&bad), Err(Error::NonCanonicalField));
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
fn mappings_refuse_missing_duplicate_uncovered_conflicting_and_unguarded_items() {
    let a = WireItem {
        id: "a".into(),
        origin: "source:a".into(),
        wire_index: Some(0),
        value: ItemValue::Words(vec![[0; 32]]),
    };
    assert_eq!(
        WireMap::new(vec![a.clone(), a.clone()]).unwrap_err(),
        Error::DuplicateIdentity
    );
    let mut b = a.clone();
    b.id = "b".into();
    assert_eq!(
        WireMap::new(vec![a.clone(), b]).unwrap_err(),
        Error::DuplicateIdentity
    );
    let map = WireMap::new(vec![a.clone()]).unwrap();
    assert_eq!(map.validate_mapping(&[], &[]), Err(Error::UnmappedItem));
    assert_eq!(
        map.validate_mapping(&["x".into()], &[]),
        Err(Error::MissingItem)
    );
    let omit = Unobserved {
        item: "a".into(),
        guard: "verified-equation".into(),
    };
    assert_eq!(
        map.validate_mapping(&["a".into()], std::slice::from_ref(&omit)),
        Err(Error::ConflictingMapping)
    );
    assert_eq!(
        map.validate_mapping(&[], &[omit.clone(), omit.clone()]),
        Err(Error::ConflictingMapping)
    );
    assert_eq!(
        map.validate_mapping(
            &[],
            &[Unobserved {
                guard: " ".into(),
                ..omit.clone()
            }]
        ),
        Err(Error::MissingGuard)
    );
    map.validate_mapping(&[], &[omit]).unwrap();
    map.validate_mapping(&["a".into(), "a".into()], &[])
        .unwrap();
    let mut malformed = a;
    malformed.origin.clear();
    assert_eq!(
        WireMap::new(vec![malformed]).unwrap_err(),
        Error::MalformedReplay
    );
}

#[test]
fn replay_admission_unknown_ops_wrong_types_duplicates_limits_and_expectations() {
    let original = bp_program("ordinary-monero-1.transcript.json");
    let mut bad = original.clone();
    bad["unexpected"] = json!(true);
    assert_eq!(run(&bad), Err(Error::UnknownMember));
    let mut bad = original.clone();
    bad["events"][0]["op"] = json!("implicit-absorb");
    assert_eq!(run(&bad), Err(Error::MalformedReplay));
    let mut bad = original.clone();
    bad["events"][0]["items"] = json!(["Hv"]);
    assert_eq!(run(&bad), Err(Error::MissingItem));
    let mut bad = original.clone();
    bad["events"][0]["output"] = json!("V");
    assert_eq!(run(&bad), Err(Error::DuplicateIdentity));
    let mut bad = original.clone();
    bad["items"][0]["kind"] = json!("fields");
    bad["items"][0]["values"] = json!([0]);
    assert_eq!(run(&bad), Err(Error::WrongItemType));
    let mut bad = original.clone();
    bad["events"][0]["expect"] = json!(encode_hex(&[0; 32]));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["events"][0]["expect_state"] = json!(encode_hex(&[0; 32]));
    assert_eq!(run(&bad), Err(Error::ExpectationMismatch));
    let mut bad = original.clone();
    bad["items"][0]["values"][0] = json!("00");
    assert_eq!(run(&bad), Err(Error::MalformedReplay));
    for limits in [
        Limits {
            events: 0,
            ..Limits::default()
        },
        Limits {
            items: 0,
            ..Limits::default()
        },
        Limits {
            values_per_event: 0,
            ..Limits::default()
        },
        Limits {
            hash_bytes: 0,
            ..Limits::default()
        },
        Limits {
            input_bytes: 0,
            ..Limits::default()
        },
    ] {
        assert_eq!(
            replay::replay_json(&serde_json::to_vec(&original).unwrap(), limits),
            Err(Error::ResourceLimit)
        );
    }
    for bytes in [
        b"{\"a\":1,\"a\":2}".as_slice(),
        b"{\"a\":{\"b\":1,\"b\":2}}",
        b"{} {}",
        b"{\"version\":1.5}",
        b"[",
    ] {
        assert_eq!(
            replay::replay_json(bytes, Limits::default()),
            Err(Error::MalformedReplay)
        );
    }
    assert_eq!(decode_word(&"AB".repeat(32)), Err(Error::MalformedReplay));
    assert_eq!(replay::decode_hex("0"), Err(Error::MalformedReplay));
}

#[test]
fn bounded_fixture_decoder_rejects_all_archived_truncations_trailing_and_bad_lengths() {
    for entry in fs::read_dir(fixture("")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "proof") {
            continue;
        }
        let bytes = fs::read(&path).unwrap();
        assert!(bp_fields(&bytes[..bytes.len() - 1]).is_err());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(bp_fields(&trailing).is_err());
        let mut bad = bytes;
        bad[192] = 255;
        assert!(bp_fields(&bad).is_err());
    }
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
fn replay_conversions_trials_live_checks_and_permutation_budget() {
    let mut native = Duplex::new();
    native.observe(&[42]).unwrap();
    let before = native.snapshot();
    let trial = native.trial_witness(3, 17).unwrap().value;
    let snapshot = |s: openvm::Snapshot| json!({"state":s.state,"absorb_index":s.absorb_index,"sample_index":s.sample_index});
    let mut program = json!({"version":1,"profile":replay::OPENVM_PROFILE,
        "items":[item("statement",Value::Null,"fields",json!([42]))],"unobserved":[],
        "events":[{"op":"observe","items":["statement"]},
        {"op":"trial_witness","bits":3,"witness":17,"expect":trial,"expect_state":snapshot(before.clone())},
        {"op":"check_witness","bits":0,"witness":1,"expect":true,"expect_state":snapshot(before)},
        {"op":"check_witness","bits":3,"witness":17,"expect":native.check_witness(3,17).unwrap().value},
        {"op":"sample_ext","expect":native.sample_ext().value},
        {"op":"sample_bits","bits":0,"expect":native.sample_bits(0).unwrap().value}]});
    let output = run(&program).unwrap();
    assert_eq!(
        output["checkpoints"].as_array().unwrap().last().unwrap()["state"],
        snapshot(native.snapshot())
    );
    assert_eq!(
        replay::replay(
            &program,
            Limits {
                permutations: 0,
                ..Limits::default()
            }
        ),
        Err(Error::ResourceLimit)
    );
    program["events"][1]["bits"] = json!(31);
    assert_eq!(run(&program), Err(Error::InvalidBitWidth));
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
