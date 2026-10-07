//! Execute fresh source compiler output with independent participant runners.
use serde_json::json;
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Scalar, Value};
use zkc_runtime::interactive::{Action, Packet, Runner, Value as RuntimeValue, admit_supplied};
use zkc_tools::protocol::run::{HostLimits, RunHost, SetupAuthority};

fn field(n: u64) -> Value {
    Value::Field(Scalar::from(n))
}
fn runner(bundle: &serde_json::Value, role: &str, inputs: Vec<Value>) -> Runner<NativeBackend> {
    let entry = bundle["entry"].as_str().unwrap();
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, "language_test", entry, None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let admitted =
        admit_supplied(bundle["candidate"].as_str().unwrap().as_bytes(), &backend).unwrap();
    Runner::new(&admitted, entry, role, "language_test", backend, inputs)
        .map_err(|failure| failure.error)
        .unwrap()
}
fn next(runner: &mut Runner<NativeBackend>) -> Action<Value> {
    for _ in 0..100 {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            action => return action,
        }
    }
    panic!("participant exceeded bounded fixture steps")
}
fn send(runner: &mut Runner<NativeBackend>) -> Value {
    let action = next(runner);
    assert!(matches!(action, Action::Send(_)));
    runner.take_send(&action.cut().unwrap()).unwrap().payload
}
fn receive(runner: &mut Runner<NativeBackend>, value: Value) {
    let Action::Receive(expected) = next(runner) else {
        panic!("expected receive")
    };
    let bytes = runner.backend().encode_value(&value).unwrap();
    let decoded = runner
        .backend()
        .decode_typed_value(expected.ty, &bytes)
        .unwrap();
    runner
        .deliver(Packet {
            envelope: expected.envelope,
            ty: decoded.physical_type(),
            payload: decoded,
        })
        .unwrap();
}
fn returned(runner: &mut Runner<NativeBackend>) -> Vec<Value> {
    let Action::Returned(values) = next(runner) else {
        panic!("expected return")
    };
    assert_eq!(runner.backend().active_frames(), 0);
    values
}
fn expect_field(value: &Value, n: u64) {
    assert!(matches!(value, Value::Field(actual) if *actual == Scalar::from(n)));
}
fn joint(bundle: &serde_json::Value, verifier_c: u64) {
    let bytes = bundle.to_string().into_bytes();
    let host = RunHost::admit(
        &bytes,
        &Sha256::digest(&bytes).into(),
        HostLimits::default(),
        SetupAuthority::default(),
    )
    .unwrap();
    let ty = "field:bls12-381.fr@arkworks.fr/1";
    let wire = |n: u64| {
        let mut bytes = [0u8; 32];
        bytes[..8].copy_from_slice(&n.to_le_bytes());
        format!(
            "5a4b43560101{}",
            bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
        )
    };
    let inputs = json!([
        "zkc.bundle-inputs/1",
        "joint-language-test",
        [
            [
                "P",
                [["0", ty, ["wire", wire(2)]], ["1", ty, ["wire", wire(3)]]],
                []
            ],
            ["V", [["0", ty, ["wire", wire(verifier_c)]]], []]
        ],
        []
    ]);
    let report = host
        .prepare(inputs.to_string().as_bytes())
        .unwrap()
        .execute();
    let result = report.json();
    assert_eq!(result["outcome"], json!(["completed"]));
    assert!(report.cleanup_errors.is_empty());
    let verifier = &report.execution.as_ref().unwrap().roles[1];
    assert_eq!(verifier.role, "V");
    expect_field(&verifier.outputs[0], 7);
    expect_field(&verifier.outputs[1], 9);
    expect_field(&verifier.outputs[2], 7 - verifier_c);
    assert!(matches!(verifier.outputs[3], Value::Bool(true)));
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("compiler source evidence directory");
    let load = |name: &str| -> serde_json::Value {
        serde_json::from_slice(&std::fs::read(Path::new(&directory).join(name)).unwrap()).unwrap()
    };
    for optimized in [0, 1] {
        for released in [0, 1] {
            let bundle = load(&format!("transfer-{optimized}-{released}.bundle"));
            joint(&bundle, 3);
            joint(&bundle, 5);
            for (verifier_c, injected, expected) in [
                (3, false, (7, 9, 4, true)),
                (5, false, (7, 9, 2, true)),
                (3, true, (13, 17, 10, false)),
            ] {
                let mut prover = runner(&bundle, "P", vec![field(2), field(3)]);
                let mut verifier = runner(&bundle, "V", vec![field(verifier_c)]);
                let first = send(&mut prover);
                let second = send(&mut prover);
                expect_field(&first, 7);
                expect_field(&second, 9);
                receive(&mut verifier, if injected { field(13) } else { first });
                receive(&mut verifier, if injected { field(17) } else { second });
                assert!(returned(&mut prover).is_empty());
                let values = returned(&mut verifier);
                assert_eq!(values.len(), 4);
                expect_field(&values[0], expected.0);
                expect_field(&values[1], expected.1);
                expect_field(&values[2], expected.2);
                assert!(matches!(values[3], Value::Bool(actual) if actual == expected.3));
            }
        }
    }
    for (name, expected) in [("One", 4), ("Two", 6), ("Alias", 4)] {
        let bundle = load(&format!("{name}.bundle"));
        let mut participant = runner(&bundle, "P", vec![field(3)]);
        let result = returned(&mut participant);
        assert_eq!(result.len(), 1);
        expect_field(&result[0], expected);
    }
    let mut helpers = runner(&load("Math.bundle"), "P", vec![field(3)]);
    let values = returned(&mut helpers);
    expect_field(&values[0], 4);
    assert!(matches!(values[1], Value::Bool(true)));
    println!(
        "fresh source: actual receives, per-role inputs, optimization variants and selected Entries passed"
    );
}
