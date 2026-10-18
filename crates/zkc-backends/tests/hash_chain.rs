//! Native hash-chain transcript suites against known answers. The vectors in
//! `hash-chain-vectors.json` come from the independent Python reference
//! `common/tests/support/hash_chain_reference.py`, which implements
//! Keccak-f[1600] itself; this test never computes an expected value with the
//! backend's chain code.
#[path = "domains/support.rs"]
mod support;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use serde_json::{Value as Json, json};
use support::*;
use zkc_backends::{Capability, KoalaBear, KoalaBearExt8, Policy, Value};
use zkc_runtime::interactive::{Backend, Identity, OperationBinding, Runner, admit_supplied};

const BLS: Identity = Identity::HashChainKeccak256Fr64Be;
const OCTIC: Identity = Identity::HashChainKeccak256KoalaBearExt8;

fn vectors() -> Json {
    serde_json::from_str(
        &std::fs::read_to_string(zkc_test_support::source("hash-chain-vectors.json"))
            .expect("frozen hash-chain vector fixture must be present"),
    )
    .unwrap()
}
fn vector(suite: Identity) -> Json {
    vectors()["suites"]
        .as_array()
        .unwrap()
        .iter()
        .find(|v| v["suite"] == suite.name())
        .cloned()
        .unwrap()
}
fn root() -> Vec<u8> {
    tree(&json!([
        "hash-chain-vector",
        "source",
        "descriptor",
        "context",
        "public",
        "configuration"
    ]))
}
fn contract(suite: Identity) -> &'static str {
    if suite == OCTIC {
        "random.koala-bear.ext8-binomial3/0"
    } else {
        "random.bls12-381.fr/0"
    }
}
fn event(suite: Identity, kind: &str) -> Json {
    match kind {
        "message" => json!(["message", "Source", "message", "Schema", "P", "V"]),
        "draw" => json!([
            "query",
            "Source",
            "draw",
            "input_0",
            contract(suite),
            "draw",
            "V"
        ]),
        _ => json!([
            "query",
            "Source",
            "pick",
            "input_0",
            contract(suite),
            "index",
            "V"
        ]),
    }
}
fn origin(suite: Identity, kind: &str, template: bool) -> Vec<u8> {
    let tag = if template {
        "zkc.native-origin-template/0"
    } else {
        "zkc.native-origin/0"
    };
    tree(&json!([tag, "main", [], [], event(suite, kind)]))
}
fn attributes(suite: Identity, kind: &str) -> Vec<String> {
    vec![zkc_test_support::hex(&origin(suite, kind, true))]
}
fn seven(suite: Identity) -> Value {
    if suite == OCTIC {
        Value::KoalaBearExt8Field(KoalaBearExt8::from(KoalaBear::new(7)))
    } else {
        field(false, 7)
    }
}
fn payload(suite: Identity) -> &'static str {
    if suite == OCTIC {
        "field:koala-bear.ext8-binomial3"
    } else {
        "field:bls12-381.fr"
    }
}
fn binding_for(suite: Identity, contract: &str) -> OperationBinding {
    let mut arguments = vec![suite.name().into()];
    if contract == "transcript.native.indexed.observe.data" {
        arguments.push(payload(suite).into());
    }
    OperationBinding {
        contract: contract.into(),
        arguments,
        implementation: format!("{}/{contract}", suite.provider().unwrap()),
    }
}
fn token(v: &Value) -> &Capability {
    let Value::Transcript(t) = v else { panic!() };
    t
}
/// Observe one message and draw one field challenge; the octic suite then
/// draws UniformIndex(bound) from a third input.
fn program_for(suite: Identity) -> Vec<u8> {
    let observe = binding_for(suite, "transcript.native.indexed.observe.data");
    let challenge = binding_for(suite, "transcript.native.indexed.challenge");
    let mut inputs = vec![
        challenge.signature().unwrap().inputs[0].clone(),
        observe.signature().unwrap().inputs[1].clone(),
    ];
    let mut bindings = vec![observe, challenge.clone()];
    let mut ops = vec![
        json!([
            "op",
            "message",
            "b0",
            attributes(suite, "message"),
            ["a0", "a1"],
            ["t1"]
        ]),
        json!([
            "op",
            "draw",
            "b1",
            attributes(suite, "draw"),
            ["t1"],
            ["c", "t2"]
        ]),
    ];
    let mut outputs = challenge.signature().unwrap().outputs;
    let mut returns = vec!["c".to_string(), "t2".to_string()];
    if suite == OCTIC {
        let index = binding_for(suite, "transcript.native.indexed.index");
        let signature = index.signature().unwrap();
        inputs.push(signature.inputs[1].clone());
        ops.push(json!([
            "op",
            "pick",
            "b2",
            attributes(suite, "index"),
            ["t2", "a2"],
            ["i", "t3"]
        ]));
        outputs = vec![
            outputs[0].clone(),
            signature.outputs[0].clone(),
            signature.outputs[1].clone(),
        ];
        returns = vec!["c".into(), "i".into(), "t3".into()];
        bindings.push(index);
    }
    program(&bindings, &inputs, ops, &outputs, &returns)
}
fn coordinates(value: &Value) -> Vec<u32> {
    let Value::KoalaBearExt8Field(x) = value else {
        panic!("octic challenge")
    };
    <KoalaBearExt8 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(x)
        .iter()
        .map(|c| c.as_canonical_u32())
        .collect()
}

#[test]
fn reference_keccak_and_fixture_inputs_agree_with_these_encodings() {
    let v = vectors();
    assert_eq!(v["format"], "zkc.hash-chain-vectors/0");
    // Published Keccak-256 answers, as reproduced by the Python reference.
    assert_eq!(
        v["keccak256"][""],
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
    assert_eq!(
        v["keccak256"]["abc"],
        "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
    );
    let b = backend(Policy::default());
    for suite in [BLS, OCTIC] {
        let v = vector(suite);
        assert_eq!(v["root"], zkc_test_support::hex(&root()));
        assert_eq!(
            v["message"],
            zkc_test_support::hex(&origin(suite, "message", false))
        );
        assert_eq!(
            v["query"],
            zkc_test_support::hex(&origin(suite, "draw", false))
        );
        let wire = b.encode_native_value(&seven(suite)).unwrap();
        assert_eq!(v["wire"], zkc_test_support::hex(&wire));
    }
    let octic = vector(OCTIC);
    assert_eq!(
        octic["index_query"],
        zkc_test_support::hex(&origin(OCTIC, "index", false))
    );
}

#[test]
fn native_kernels_reproduce_the_reference_answers() {
    let bls = vector(BLS);
    let mut b = backend(Policy::default());
    let p = program_for(BLS);
    for _ in 0..2 {
        // A fresh state from the same root repeats the same answer.
        let t = b.issue_transcript_for(BLS, domain(), 2, &root()).unwrap();
        let handle = token(&t).clone();
        let (out, next) = run_program(b, &p, vec![t, seven(BLS)]);
        b = next;
        let out = out.unwrap();
        let Value::Field(c) = &out[0] else { panic!() };
        assert_eq!(c.to_string(), bls["challenges"][0].as_str().unwrap());
        assert_eq!(token(&out[1]).identity(), BLS);
        assert_eq!(b.observe(&handle).unwrap().generation, 2);
    }

    let octic = vector(OCTIC);
    let p = program_for(OCTIC);
    let t = b.issue_transcript_for(OCTIC, domain(), 3, &root()).unwrap();
    let (out, b) = run_program(b, &p, vec![t, seven(OCTIC), Value::Index(256)]);
    let out = out.unwrap();
    let expected: Vec<u32> = serde_json::from_value(octic["challenge"].clone()).unwrap();
    assert_eq!(coordinates(&out[0]), expected);
    let Value::Index(position) = out[1] else {
        panic!("UniformIndex(256)")
    };
    assert_eq!(position, octic["index"].as_u64().unwrap());
    assert_eq!(token(&out[2]).identity(), OCTIC);
    assert_eq!(b.active_frames(), 0);
}

#[test]
fn suites_are_distinct_from_each_other_and_from_merlin() {
    // Same root, same events: a different suite name or construction changes
    // every answer.
    let mut b = backend(Policy::default());
    let mut answers = Vec::new();
    for suite in [
        BLS,
        Identity::Merlin3Fr64Be,
        Identity::Spongefish080KeccakFr64Be,
    ] {
        let t = b.issue_transcript_for(suite, domain(), 2, &root()).unwrap();
        let (out, next) = run_program(b, &program_for(suite), vec![t, seven(BLS)]);
        b = next;
        let Value::Field(c) = out.unwrap()[0] else {
            panic!()
        };
        answers.push(c);
    }
    assert_ne!(answers[0], answers[1]);
    assert_ne!(answers[0], answers[2]);
    assert_ne!(answers[1], answers[2]);
}

#[test]
fn nominal_identity_provider_and_index_capability() {
    for (suite, field, provider) in [
        (BLS, Identity::Bls12381Fr, "arkworks"),
        (OCTIC, Identity::KoalaBearExt8, "plonky3"),
    ] {
        assert_eq!(Identity::parse(suite.name()).unwrap(), suite);
        assert_eq!(suite.transcript(), Some(suite));
        assert_eq!(suite.scalar_field(), Some(field));
        assert_eq!(suite.provider(), Some(provider));
        assert!(
            zkc_backends::domains::TRANSCRIPTS
                .iter()
                .any(|t| t.suite == suite && t.domain.field == field && t.provider == provider)
        );
    }
    assert!(OCTIC.has_index_transcript());
    assert!(!BLS.has_index_transcript());
    // Another byte hash is another installed instance, not a parameter.
    for name in [
        "hash-chain.sha256.bls12-381.fr64be/0",
        "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",
        "hash-chain.keccak256.koala-bear/0",
        "hash-chain.keccak256.ristretto255.scalar64le/0",
    ] {
        assert!(Identity::parse(name).is_err(), "{name}");
    }
    let b = backend(Policy::default());
    for suite in [BLS, OCTIC] {
        for contract in [
            "transcript.native.indexed.challenge",
            "transcript.native.indexed.observe.data",
            "transcript.observe",
            "transcript.challenge",
        ] {
            let valid = binding_for(suite, contract);
            assert_eq!(
                b.binding_signature(&valid),
                Some(valid.signature().unwrap()),
                "{contract}"
            );
            for bad in ["dalek", "spongefish", "uninstalled"] {
                let mut mutant = valid.clone();
                mutant.implementation = format!("{bad}/{contract}");
                assert!(b.binding_signature(&mutant).is_none(), "{bad}/{contract}");
            }
        }
    }
    // UniformIndex transitions exist only where the challenge field has
    // index randomness.
    for contract in ["transcript.native.indexed.index", "transcript.index"] {
        let valid = binding_for(OCTIC, contract);
        assert_eq!(
            b.binding_signature(&valid),
            Some(valid.signature().unwrap())
        );
        let refused = binding_for(BLS, contract);
        assert!(refused.signature().is_err(), "{contract}");
        let mut plonky = refused.clone();
        plonky.implementation = format!("plonky3/{contract}");
        assert!(b.binding_signature(&plonky).is_none(), "{contract}");
    }
    // Observation takes complete logical types only, not wire codecs.
    let mut wrong = binding_for(BLS, "transcript.native.indexed.observe.data");
    wrong.arguments[1] = "zkcv.field.bls12-381.fr/0".into();
    assert!(b.binding_signature(&wrong).is_none());
}

#[test]
fn refusals_leave_no_successor() {
    let mut b = backend(Policy::default());
    for bad in [vec![], vec![1], {
        let mut r = root();
        r.push(0);
        r
    }] {
        for suite in [BLS, OCTIC] {
            let err = b
                .issue_transcript_for(suite, domain(), 2, &bad)
                .unwrap_err();
            assert_eq!(err.code, "refused:transcript-root");
        }
    }
    // A bound that is not a power of two refuses before the state is consumed.
    let p = program_for(OCTIC);
    for bound in [0, 3, 255] {
        let t = b.issue_transcript_for(OCTIC, domain(), 3, &root()).unwrap();
        let handle = token(&t).clone();
        let (out, next) = run_program(b, &p, vec![t, seven(OCTIC), Value::Index(bound)]);
        b = next;
        assert_eq!(out.unwrap_err(), "refused:query-bound");
        assert_eq!(b.observe(&handle).unwrap().generation, 2);
    }
    // An exhausted budget stops at the first transition past it, which
    // consumes the state and returns no successor.
    let t = b.issue_transcript_for(OCTIC, domain(), 2, &root()).unwrap();
    let handle = token(&t).clone();
    let (out, b) = run_program(b, &p, vec![t, seven(OCTIC), Value::Index(256)]);
    assert!(out.unwrap_err().contains("exhausted"));
    assert_eq!(b.observe(&handle).unwrap().generation, 3);
    // A consumed state cannot be supplied again.
    let p = program_for(BLS);
    let mut b = backend(Policy::default());
    let t = b.issue_transcript_for(BLS, domain(), 2, &root()).unwrap();
    let old = t.clone();
    let (out, b) = run_program(b, &p, vec![t, seven(BLS)]);
    assert!(out.is_ok());
    let admitted = admit_supplied(&p, &b).unwrap();
    assert!(Runner::new(&admitted, "main", "P", "session", b, vec![old]).is_err());
    // A state of another suite is not this program's transcript.
    let mut b = backend(Policy::default());
    let wrong = b
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 2, &root())
        .unwrap();
    let admitted = admit_supplied(&p, &b).unwrap();
    assert!(
        Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            b,
            vec![wrong, seven(BLS)]
        )
        .is_err()
    );
}

#[test]
fn the_octic_challenge_is_an_exact_coordinate_draw() {
    // The answer is the first eight masked words of the reference request
    // output; none of them was rejected for this vector.
    let octic = vector(OCTIC);
    let steps = octic["steps"].as_array().unwrap();
    let request = steps
        .iter()
        .find(|s| s["request"][0] == "challenge")
        .unwrap();
    let raw = zkc_test_support::unhex(request["output"].as_str().unwrap());
    let words: Vec<u32> = raw
        .chunks(4)
        .take(8)
        .map(|w| u32::from_le_bytes(w.try_into().unwrap()) & 0x7fff_ffff)
        .collect();
    let expected: Vec<u32> = serde_json::from_value(octic["challenge"].clone()).unwrap();
    assert_eq!(words, expected);
    assert!(words.iter().all(|w| *w < 2_130_706_433));
    assert_eq!(KoalaBear::ZERO.as_canonical_u32(), 0);
}
