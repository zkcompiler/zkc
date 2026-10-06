//! Bounded execution checks for compiler-generated mathematical participants.
//! Takes the directory of JSON candidates produced by compiler/test/mathematical.py.
//! Supplied admission checks the carrier, without claiming source correspondence.
use std::path::Path;
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{
    Action, ArtifactFormat, Origin, Packet, PathElement, Runner, Stop, StopKind,
    Value as RuntimeValue, admit_supplied,
};

fn backend(role: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, "mathematical_test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}

fn field(value: u64) -> Value {
    Value::Field(Scalar::from(value))
}

fn group(value: u64) -> Value {
    Value::Curve(GroupPoint::generator().scale(Scalar::from(value)))
}

fn runner(bytes: &[u8], role: &str, inputs: Vec<Value>) -> Runner<NativeBackend> {
    let native = backend(role);
    let admitted = admit_supplied(bytes, &native).unwrap();
    assert!(admitted.checked_source().is_none());
    Runner::new(&admitted, "main", role, "mathematical_test", native, inputs)
        .map_err(|failure| failure.error)
        .unwrap()
}

fn next(runner: &mut Runner<NativeBackend>) -> Action<Value> {
    for _ in 0..100 {
        match runner.poll() {
            Action::Local(local) => {
                // A false guard is an ordinary stopped result. Poll observes it.
                runner
                    .execute_local(&local.cut)
                    .expect("valid local execution cut");
            }
            action => return action,
        }
    }
    panic!("bounded example did not reach its next observable action")
}

fn send(runner: &mut Runner<NativeBackend>) -> Value {
    let Action::Send(packet) = next(runner) else {
        panic!("expected send")
    };
    runner
        .take_send(&Action::Send(packet).cut().unwrap())
        .unwrap()
        .payload
}

fn receive(runner: &mut Runner<NativeBackend>, value: Value) {
    let Action::Receive(expected) = next(runner) else {
        panic!("expected receive")
    };
    // The open endpoint receives a supplied value, including adversarial changes.
    // Encode/decode with the actual installed codec before delivering it.
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

fn expect_field(value: Value, expected: u64) {
    assert!(matches!(value, Value::Field(actual) if actual == Scalar::from(expected)));
}

fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("generated candidate directory");
    let load =
        |name: &str| std::fs::read(Path::new(&directory).join(format!("{name}.json"))).unwrap();
    let mixed = load("mixed");
    for (role, inputs, expected) in [
        ("Alice", vec![field(3), field(7)], vec![6, 42]),
        ("Bob", vec![field(11)], vec![22]),
    ] {
        let mut participant = runner(&mixed, role, inputs);
        let Action::Returned(values) = next(&mut participant) else {
            panic!("expected return")
        };
        assert_eq!(values.len(), expected.len());
        for (value, want) in values.into_iter().zip(expected) {
            expect_field(value, want);
        }
    }
    let mut observer = runner(&mixed, "Observer", vec![Value::Bool(false)]);
    assert!(matches!(next(&mut observer), Action::Returned(values) if values.is_empty()));

    let codec = backend("Bob");
    assert!(
        codec
            .decode_typed_value(field(0).physical_type(), &[255; 32])
            .is_err()
    );
    assert!(
        codec
            .decode_typed_value(group(1).physical_type(), &[255; 48])
            .is_err()
    );

    let schnorr = load("schnorr");
    let mut prover = runner(
        &schnorr,
        "Alice",
        vec![group(1), field(13), group(13), field(17)],
    );
    assert!(
        matches!(send(&mut prover), Value::Curve(p) if p == GroupPoint::generator().scale(Scalar::from(17u64)))
    );
    receive(&mut prover, field(19));
    expect_field(send(&mut prover), 264);
    assert!(matches!(next(&mut prover), Action::Returned(values) if values.is_empty()));
    // Replace each of the three messages at the receiving endpoint.
    for (commitment, challenge, response, accepted) in [
        (17, 19, 264, true),
        (18, 19, 264, false),
        (17, 19, 265, false),
        (17, 20, 264, false),
    ] {
        let mut verifier = runner(&schnorr, "Bob", vec![group(1), group(13), field(challenge)]);
        receive(&mut verifier, group(commitment));
        expect_field(send(&mut verifier), challenge);
        receive(&mut verifier, field(response));
        assert!(
            matches!(next(&mut verifier), Action::Returned(values) if matches!(values.as_slice(), [Value::Bool(result)] if *result == accepted))
        );
    }
    // Group identity is an admitted mathematical value, including in scalar action.
    let mut identity = runner(&schnorr, "Bob", vec![group(0), group(0), field(19)]);
    receive(&mut identity, group(0));
    expect_field(send(&mut identity), 19);
    receive(&mut identity, field(264));
    assert!(matches!(next(&mut identity), Action::Returned(values)
        if matches!(values.as_slice(), [Value::Bool(true)])));
    let mut changed_challenge = runner(
        &schnorr,
        "Alice",
        vec![group(1), field(13), group(13), field(17)],
    );
    let _ = send(&mut changed_challenge);
    receive(&mut changed_challenge, field(20));
    expect_field(send(&mut changed_challenge), 277);

    let mut guarded = runner(
        &load("control"),
        "Bob",
        vec![Value::Bool(false), field(3), field(7)],
    );
    expect_field(send(&mut guarded), 7);
    let Action::Stopped(actual) = next(&mut guarded) else {
        panic!("guard stop")
    };
    assert_eq!(actual.local.as_ref().unwrap().site, "check");
    assert_eq!(
        actual.local.as_ref().unwrap().instruction.as_deref(),
        Some("check")
    );
    assert!(!actual.local.as_ref().unwrap().function.is_empty());
    let expected = Stop {
        origin: Origin {
            format: ArtifactFormat::Program,
            session: "mathematical_test".into(),
            entry: "main".into(),
            instance: "main".into(),
            path: vec![PathElement::Conditional {
                site: "guard_control".into(),
                taken: false,
            }],
        },
        role: "Bob".into(),
        site: Some("check".into()),
        kind: StopKind::Explicit("reject".into()),
        cleanup_errors: vec![],
        local: actual.local.clone(),
    };
    assert_eq!(actual, expected);
    assert_eq!(guarded.backend().active_frames(), 0);
    let usage = guarded.usage();
    assert_eq!(usage.live_values, 0);
    assert_eq!(usage.live_value_bytes, 0);
    for _ in 0..3 {
        assert!(matches!(guarded.poll(), Action::Stopped(stop) if stop == expected));
        assert_eq!(guarded.usage(), usage);
    }
    let mut deferred = runner(
        &load("deferred"),
        "Bob",
        vec![Value::Bool(false), field(3), field(7)],
    );
    expect_field(send(&mut deferred), 7);
    expect_field(send(&mut deferred), 3);
    assert!(
        matches!(next(&mut deferred), Action::Returned(values) if matches!(values.first(), Some(Value::Bool(false))))
    );
    let mut peer = runner(&load("control"), "Alice", vec![field(29), field(31)]);
    receive(&mut peer, field(7));
    assert!(matches!(next(&mut peer), Action::Receive(_)));

    let mut fresh = runner(&load("receives"), "Bob", vec![]);
    receive(&mut fresh, field(5));
    receive(&mut fresh, field(11));
    let Action::Returned(values) = next(&mut fresh) else {
        panic!("expected return")
    };
    expect_field(values.into_iter().next().unwrap(), 16);
    println!(
        "generated mathematical participants: native arithmetic, curves, codecs, substituted receives, guard and deferred return passed"
    );
}
