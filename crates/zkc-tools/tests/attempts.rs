//! Stored PIR body -> MLIR projection -> Lean correspondence -> persistent
//! native attempts. This is a lifecycle control, not a range-proof protocol.
use zkc_backends::{Capability, Domain, NativeBackend, Value};
use zkc_runtime::{
    Outcome,
    attempt::{Controller, Decision, Limits},
    interactive::{Backend, Runner, admit_physical},
};
use zkc_tools::{artifact, protocol::ParticipantChecker};

#[path = "common/backend.rs"]
mod fixture;

struct State {
    backend: Option<NativeBackend>,
    coins: Option<Value>,
    original: Capability,
    encodings: usize,
}

#[test]
fn compiled_attempts_reuse_actual_rng_and_release_only_selected_wire_bytes() {
    let input = zkc_test_support::root().join("examples/protocols/attempt-control.pir");
    let source = zkc_test_support::compile("protocol-source", &input);
    let candidate = zkc_test_support::compile("protocol-compile", &input);
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let mut backend = fixture::backend();
    let admitted = admit_physical(&source, &candidate, &backend, &checker).unwrap();
    let coins = backend
        .issue_rng(Domain::new("P", "test", "main", None), 3)
        .unwrap();
    let Value::Rng(original) = coins.clone() else {
        panic!("not rng")
    };
    let state = State {
        backend: Some(backend),
        coins: Some(coins),
        original,
        encodings: 0,
    };
    let result = Controller::new(
        state,
        Limits {
            attempts: 4,
            proof_bytes: 32,
        },
    )
    .advance(4, |number, context| {
        let state = context.state_mut();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "test",
            state.backend.take().unwrap(),
            vec![state.coins.take().unwrap(), Value::Bool(number < 2)],
        )
        .unwrap_or_else(|e| panic!("runner load: {}", e.error));
        let report = artifact::attempt::execute(
            &mut runner,
            4096,
            |mut outputs| {
                let Value::Bool(retry) = outputs.pop().unwrap() else {
                    panic!("retry flag")
                };
                let coins = outputs.pop().unwrap();
                Ok(if retry {
                    Decision::Retry(coins)
                } else {
                    Decision::Complete(coins)
                })
            },
            |messages| {
                state.encodings += 1;
                assert_eq!(messages.len(), 1);
                assert_eq!(messages[0].envelope.schema, "candidate");
                let Value::Field(value) = &messages[0].payload else {
                    panic!("wrong proof field type")
                };
                Ok(zkc_arkworks::encode_scalar(value).unwrap().to_vec())
            },
        );
        assert!(
            report.outcome.is_ok(),
            "{:?}",
            report.outcome.as_ref().err()
        );
        assert_eq!((report.messages, report.bytes), (1, 38));
        assert!(report.cancelled.is_none());
        state.backend = Some(runner.into_backend());
        match report.outcome.unwrap() {
            Decision::Retry(coins) => {
                state.coins = Some(coins);
                Ok(Decision::Retry("requested-test-retry"))
            }
            Decision::Complete(proof) => {
                state.coins = Some(proof.value);
                context.append(&proof.bytes)?;
                Ok(Decision::Complete(()))
            }
        }
    })
    .close();
    let Outcome::Returned(proof) = result.outcome else {
        panic!("not complete")
    };
    assert_eq!((proof.attempt, proof.bytes.len()), (2, 32));
    assert_eq!(result.state.encodings, 1);
    let backend = result.state.backend.unwrap();
    let observation = backend.observe(&result.state.original).unwrap();
    assert_eq!(
        (
            observation.generation,
            observation.draw_count,
            observation.budget
        ),
        (3, 3, 0)
    );
    assert_eq!(backend.active_frames(), 0);
    // The original handle is generation 0; its slot has advanced three times.
    assert_eq!(
        backend
            .validate_value(&Value::Rng(result.state.original))
            .unwrap_err()
            .code,
        "refused:capability-stale"
    );
    backend
        .validate_value(result.state.coins.as_ref().unwrap())
        .unwrap();
}

#[test]
fn compiled_failure_is_not_a_retry_and_keeps_consumed_native_state() {
    let input = zkc_test_support::root().join("examples/protocols/attempt-control.pir");
    let source = zkc_test_support::compile("protocol-source", &input);
    let candidate = zkc_test_support::compile("protocol-compile", &input);
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let mut backend = fixture::backend();
    let admitted = admit_physical(&source, &candidate, &backend, &checker).unwrap();
    let coins = backend
        .issue_rng(Domain::new("P", "test", "main", None), 0)
        .unwrap();
    let Value::Rng(token) = coins.clone() else {
        panic!("not rng")
    };
    let mut runner = Runner::new(
        &admitted,
        "main",
        "P",
        "test",
        backend,
        vec![coins, Value::Bool(true)],
    )
    .unwrap_or_else(|e| panic!("runner load: {}", e.error));
    let result = artifact::attempt::execute(
        &mut runner,
        32,
        |_| -> Result<Decision<(), ()>, artifact::ArtifactFailure> {
            panic!("classified terminal stop")
        },
        |_| panic!("encoded failed attempt"),
    );
    assert!(matches!(
        result.outcome,
        Err(artifact::ArtifactFailure::Stopped(_))
    ));
    assert_eq!((result.messages, result.bytes), (0, 0));
    let backend = runner.into_backend();
    let state = backend.observe(&token).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (1, 1, 0)
    );
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn output_buffer_and_codec_failures_do_not_publish_or_rewind() {
    let input = zkc_test_support::root().join("examples/protocols/attempt-control.pir");
    let source = zkc_test_support::compile("protocol-source", &input);
    let candidate = zkc_test_support::compile("protocol-compile", &input);
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    for mode in ["message-limit", "codec-error", "container-limit"] {
        let mut backend = fixture::backend();
        let admitted = admit_physical(&source, &candidate, &backend, &checker).unwrap();
        let coins = backend
            .issue_rng(Domain::new("P", "test", "main", None), 1)
            .unwrap();
        let Value::Rng(token) = coins.clone() else {
            panic!("not rng")
        };
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "test",
            backend,
            vec![coins, Value::Bool(false)],
        )
        .unwrap_or_else(|e| panic!("runner load: {}", e.error));
        let mut encoded = false;
        let result = artifact::attempt::execute(
            &mut runner,
            if mode == "message-limit" { 0 } else { 4096 },
            |_| Ok::<Decision<(), ()>, artifact::ArtifactFailure>(Decision::Complete(())),
            |_| {
                encoded = true;
                if mode == "codec-error" {
                    Err(artifact::FormatError::Header.into())
                } else {
                    Ok(vec![0; 4097])
                }
            },
        );
        assert!(
            matches!(result.outcome, Err(artifact::ArtifactFailure::Format(_))),
            "{mode}"
        );
        assert_eq!(encoded, mode != "message-limit");
        let backend = runner.into_backend();
        let observation = backend.observe(&token).unwrap();
        assert_eq!(
            (
                observation.generation,
                observation.draw_count,
                observation.budget
            ),
            (1, 1, 0)
        );
        assert_eq!(backend.active_frames(), 0);
    }
}
