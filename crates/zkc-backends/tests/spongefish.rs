#[path = "domains/support.rs"]
mod support;
use serde_json::{Value as Json, json};
use spongefish::{DuplexSpongeInterface, instantiations::Keccak};
use support::*;
use zkc_backends::{Capability, Policy, Value};
use zkc_runtime::interactive::{
    Backend, Identity, OperationBinding, Runner, Value as RuntimeValue, admit_supplied,
};

const SUITE: Identity = Identity::Spongefish074KeccakFr64Be;
fn scalar(v: &Value) -> zkc_backends::Scalar {
    let Value::Field(f) = v else { panic!() };
    *f
}
fn token(v: &Value) -> &Capability {
    let Value::Transcript(t) = v else { panic!() };
    t
}
fn frame(tag: u8, label: &[u8], bytes: &[u8]) -> Vec<u8> {
    [
        vec![tag],
        (label.len() as u64).to_be_bytes().to_vec(),
        label.to_vec(),
        (bytes.len() as u64).to_be_bytes().to_vec(),
        bytes.to_vec(),
    ]
    .concat()
}
fn root() -> Vec<u8> {
    tree(&json!([
        "suite-vector",
        "source",
        "descriptor",
        "context",
        "public",
        "configuration"
    ]))
}
fn origin(kind: &str) -> Vec<u8> {
    tree(&json!([
        "zkc.logical-origin/1",
        "main",
        "instance",
        [],
        [kind, "Source", "site", "Schema", "P", "V"]
    ]))
}
fn binding_for(suite: Identity, contract: &str) -> OperationBinding {
    let mut arguments = vec![suite.name().into()];
    if contract == "transcript.observe.field" {
        arguments.extend(["bls12-381.fr".into(), "zkcv.field.bls12-381.fr/1".into()]);
    }
    OperationBinding {
        contract: contract.into(),
        arguments,
        implementation: format!(
            "{}/{}",
            if suite == SUITE {
                "spongefish"
            } else {
                "arkworks"
            },
            contract
        ),
    }
}
fn program_for(suite: Identity, observations: bool) -> Vec<u8> {
    let challenge = binding_for(suite, "transcript.challenge");
    let observe = binding_for(suite, "transcript.observe.field");
    let mut inputs = challenge.signature().unwrap().inputs;
    let outputs = challenge.signature().unwrap().outputs;
    let attrs = ["Source", "site", "Schema", "P", "V"];
    let (bindings, ops) = if observations {
        inputs.push(observe.signature().unwrap().inputs[1].clone());
        (
            vec![observe, challenge],
            vec![
                json!(["op", "message", "b0", attrs, ["a0", "a1"], ["t1"]]),
                json!(["op", "draw1", "b1", attrs, ["t1"], ["c1", "t2"]]),
                json!(["op", "draw2", "b1", attrs, ["t2"], ["c2", "t3"]]),
            ],
        )
    } else {
        (
            vec![challenge],
            vec![json!(["op", "draw", "b0", attrs, ["a0"], ["c2", "t3"]])],
        )
    };
    program(
        &bindings,
        &inputs,
        ops,
        &outputs,
        &["c2".into(), "t3".into()],
    )
}
fn direct(root: &[u8], wire: &[u8]) -> ([u8; 64], [u8; 64]) {
    let mut t = Keccak::default();
    for data in [
        frame(0, b"domain", b"zkc.artifact/1"),
        frame(0, b"suite", SUITE.name().as_bytes()),
        frame(1, b"binding", root),
        frame(1, b"origin", &origin("message")),
        frame(1, b"value", wire),
    ] {
        t.absorb(&data);
    }
    let mut output = [[0; 64]; 2];
    for wide in &mut output {
        t.absorb(&frame(1, b"origin", &origin("challenge")));
        t.absorb(&frame(2, b"challenge", &64u64.to_be_bytes()));
        t.squeeze(wide);
    }
    (output[0], output[1])
}
#[test]
fn upstream_zero_state_keccak_permutation_vector() {
    // keccak 0.2.0 tests/xkcp.rs, f1600 first permutation, first eight lanes.
    let expected = [
        0xF1258F7940E1DDE7u64,
        0x84D5CCF933C0478A,
        0xD598261EA65AA9EE,
        0xBD1547306F80494D,
        0x8B284E056253D057,
        0xFF97A42D7F8E6FD4,
        0x90FEE5A0A44647C4,
        0x8C5BDA0CD6192E76,
    ];
    let mut t = Keccak::default();
    let mut bytes = [0; 64];
    t.squeeze(&mut bytes);
    assert_eq!(
        bytes.to_vec(),
        expected
            .iter()
            .flat_map(|n| n.to_le_bytes())
            .collect::<Vec<_>>()
    );
}
#[test]
fn independent_frames_vectors_native_sampler_and_fresh_state() {
    let mut b = backend(Policy::default());
    let value = field(false, 7);
    // This fixture is canonical Fr wire, checked independently below.
    let wire = [b"ZKCV\x01\x01".as_slice(), &[7], &[0; 31]].concat();
    assert_eq!(b.encode_value(&value).unwrap(), wire);
    let (first, second) = direct(&root(), &wire);
    let vector: Json = serde_json::from_str(
        &std::fs::read_to_string(zkc_test_support::source("transcript-vectors.json"))
            .expect("frozen transcript vector fixture must be present"),
    )
    .unwrap();
    assert_eq!(zkc_test_support::hex(&root()), vector["root"]);
    assert_eq!(zkc_test_support::hex(&wire), vector["wire"]);
    assert_eq!(zkc_test_support::hex(&first), vector["first"]);
    assert_eq!(zkc_test_support::hex(&second), vector["second"]);
    // Decimal remainders were computed independently with Python integers.
    assert_eq!(
        zkc_arkworks::scalar_from_wide_be(&first).to_string(),
        vector["first_fr"].as_str().unwrap()
    );
    assert_eq!(
        zkc_arkworks::scalar_from_wide_be(&second).to_string(),
        vector["second_fr"].as_str().unwrap()
    );
    let p = program_for(SUITE, true);
    for _ in 0..2 {
        let t = b.issue_transcript_for(SUITE, domain(), 3, &root()).unwrap();
        let handle = token(&t).clone();
        let (out, next) = run_program(b, &p, vec![t, value.clone()]);
        b = next;
        let out = out.unwrap();
        assert_eq!(scalar(&out[0]), zkc_arkworks::scalar_from_wide_be(&second));
        assert_eq!(b.observe(&handle).unwrap().generation, 3);
    }
    let merlin = program_for(Identity::Merlin3Fr64Be, true);
    let t = b
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 3, &root())
        .unwrap();
    let (out, _) = run_program(b, &merlin, vec![t, value]);
    assert_ne!(
        scalar(&out.unwrap()[0]),
        zkc_arkworks::scalar_from_wide_be(&second)
    );
}
#[test]
fn nominal_provider_codec_and_wrong_field_admission() {
    assert_eq!(SUITE.scalar_field(), Some(Identity::Bls12381Fr));
    assert_eq!(SUITE.transcript(), Some(SUITE));
    assert_eq!(Identity::Bls12381Fr.transcript(), None);
    let b = backend(Policy::default());
    for contract in ["transcript.challenge", "transcript.observe.field"] {
        let valid = binding_for(SUITE, contract);
        assert_eq!(
            b.binding_signature(&valid),
            Some(valid.signature().unwrap())
        );
        let bytes = program_for(SUITE, contract.contains("observe"));
        assert!(admit_supplied(&bytes, &b).is_ok());
        for bad in ["arkworks", "dalek", "uninstalled"] {
            let mut mutant = valid.clone();
            mutant.implementation = format!("{bad}/{contract}");
            assert!(mutant.signature().is_err());
            assert!(b.binding_signature(&mutant).is_none());
        }
    }
    let mut obs = binding_for(SUITE, "transcript.observe.field");
    obs.arguments[2] = "zkcv.field.ristretto255.scalar/1".into();
    assert!(obs.signature().is_err());
    assert!(b.binding_signature(&obs).is_none());
    obs.arguments[1] = "ristretto255.scalar".into();
    assert!(obs.signature().is_err());
    assert!(b.binding_signature(&obs).is_none());
    assert!(Identity::parse("spongefish0.7.4.keccak.ristretto255.scalar64le/1").is_err());
}
#[test]
fn malformed_roots_wrong_suite_authority_and_budget() {
    let p = program_for(SUITE, false);
    let mut b = backend(Policy::default());
    assert!(
        b.issue_transcript_for(Identity::Bls12381Fr, domain(), 2, &root())
            .is_err()
    );
    for bad in [vec![], vec![1], {
        let mut r = root();
        r.push(0);
        r
    }] {
        assert!(b.issue_transcript_for(SUITE, domain(), 2, &bad).is_err());
    }
    let wrong = b
        .issue_transcript_for(Identity::Merlin3Fr64Be, domain(), 2, &root())
        .unwrap();
    let admitted = admit_supplied(&p, &b).unwrap();
    assert!(Runner::new(&admitted, "main", "P", "session", b, vec![wrong]).is_err());
    let mut a = backend(Policy::default());
    let t = a.issue_transcript_for(SUITE, domain(), 2, &root()).unwrap();
    let other = backend(Policy::default());
    let admitted = admit_supplied(&p, &other).unwrap();
    assert!(Runner::new(&admitted, "main", "P", "session", other, vec![t]).is_err());
    let mut b = backend(Policy::default());
    let t = b.issue_transcript_for(SUITE, domain(), 0, &root()).unwrap();
    let handle = token(&t).clone();
    let (out, b) = run_program(b, &p, vec![t]);
    assert!(out.unwrap_err().contains("exhausted"));
    assert_eq!(b.observe(&handle).unwrap().generation, 1);
}

#[test]
fn stale_handle_and_malformed_origin_do_not_create_a_successor() {
    let p = program_for(SUITE, false);
    let mut b = backend(Policy::default());
    let t = b.issue_transcript_for(SUITE, domain(), 3, &root()).unwrap();
    let old = t.clone();
    let (out, b) = run_program(b, &p, vec![t]);
    assert!(out.is_ok());
    let admitted = admit_supplied(&p, &b).unwrap();
    assert!(Runner::new(&admitted, "main", "P", "session", b, vec![old]).is_err());
    let b = backend(Policy::default());
    let mut malformed: Json = serde_json::from_slice(&p).unwrap();
    malformed[3][0][4][0][3] = json!(["Source", "site", "Schema", "P", "bad/frame"]);
    assert!(admit_supplied(&serde_json::to_vec(&malformed).unwrap(), &b).is_err());
}
#[test]
fn prefix_lengths_domain_context_and_event_binding() {
    assert_ne!(frame(1, b"ab", b"c"), frame(1, b"a", b"bc"));
    assert_ne!(frame(1, b"value", b"x"), frame(1, b"value", b"x\0"));
    assert_ne!(
        frame(1, b"challenge", &64u64.to_be_bytes()),
        frame(2, b"challenge", &64u64.to_be_bytes())
    );
    let wire = zkc_test_support::unhex(
        "5a4b435601010700000000000000000000000000000000000000000000000000000000000000",
    );
    let base = direct(&root(), &wire);
    for text in [
        "different-source",
        "different-descriptor",
        "different-context",
        "different-public",
        "different-configuration",
    ] {
        assert_ne!(direct(&tree(&json!([text])), &wire), base);
    }
    let mut bad = wire.clone();
    bad.push(0);
    let b = backend(Policy::default());
    let ty = field(false, 7).physical_type();
    assert!(b.decode_typed_value(ty.clone(), &bad).is_err());
    bad = wire;
    bad[1] ^= 1;
    assert!(b.decode_typed_value(ty.clone(), &bad).is_err());
}
