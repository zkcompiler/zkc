//! Compiled bytewise zero guard and persistent native attempts. Fault oracle
//! evidence only: no Keccak zero preimage, BP+ proof, or native refinement claim.
use std::cell::{Cell, RefCell};
use zkc_backends::{Capability, Domain, NativeBackend, Value};
use zkc_runtime::{
    Outcome, Stop,
    attempt::{Controller, Decision, Event, Limits, Prepared},
    interactive::{
        Backend, BackendError, BoundSignature, Frame, FrameExit, Invocation, OperationBinding,
        PhysicalType, Runner, StopKind, admit_physical,
    },
    iteration::Execution,
};
use zkc_tools::{
    artifact::{self, ArtifactFailure},
    protocol::{ParticipantChecker, WireBackend},
};

#[path = "common/backend.rs"]
mod fixture;

fn indices(xs: impl Into<Vec<u64>>) -> Value {
    Value::Indices(xs.into().into())
}
fn numbers(value: &Value) -> &[u64] {
    let Value::Indices(xs) = value else {
        panic!("indices")
    };
    xs
}
fn initial_state() -> Value {
    indices([vec![1_514_881_876, 1, 1], vec![7; 32]].concat())
}

struct Transition {
    input: Vec<u64>,
    actual: Vec<u64>,
    emitted: Vec<u64>,
    work: u64,
}

/// Test-only oracle. All signatures, admission, frame/resource operations and
/// wire operations delegate. Even a selected update must first succeed natively;
/// validation/budget failures cannot be overwritten into a retry response.
struct ZeroChallengeFaultOracle {
    native: NativeBackend,
    zero_calls: usize,
    transitions: Vec<Transition>,
    candidates: RefCell<Vec<Vec<u8>>>,
    draws: Vec<String>,
}
impl Backend for ZeroChallengeFaultOracle {
    type Value = Value;
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        self.native.binding_signature(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.native.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.native.enter_frame(frame, args)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[Value],
    ) -> Result<(), BackendError> {
        self.native.leave_frame(frame, exit, outputs)
    }
    fn apply(&mut self, call: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>, BackendError> {
        let mut out = self.native.apply(call, args)?;
        if call.binding.declaration().contract == "random.draw" {
            let Value::Field(value) = &out[0] else {
                panic!("BLS draw")
            };
            self.draws.push(value.to_string());
        }
        if call.binding.declaration().contract == "external.monero.update" {
            assert_eq!(out.len(), 2);
            let actual = numbers(&out[1]).to_vec();
            assert_eq!(actual.len(), 32);
            assert_eq!(&numbers(&out[0])[3..], actual);
            // These fixed native inputs have ordinary nonzero results; the
            // zero outcome below is explicitly substituted, never discovered.
            assert!(actual.iter().any(|b| *b != 0));
            if self.transitions.len() < self.zero_calls {
                let mut state = numbers(&out[0]).to_vec();
                state[3..].fill(0);
                out = vec![indices(state), indices(vec![0; 32])];
                for value in &out {
                    self.native.validate_value(value)?;
                }
            }
            self.transitions.push(Transition {
                input: numbers(&args[0]).to_vec(),
                actual,
                emitted: numbers(&out[1]).to_vec(),
                work: self.native.external_work_spent(),
            });
        }
        Ok(out)
    }
}
impl WireBackend for ZeroChallengeFaultOracle {
    fn encode(&self, value: &Value) -> Result<Vec<u8>, BackendError> {
        let bytes = self.native.encode(value)?;
        self.candidates.borrow_mut().push(bytes.clone());
        Ok(bytes)
    }
    fn decode(&self, ty: PhysicalType, bytes: &[u8]) -> Result<Value, BackendError> {
        self.native.decode(ty, bytes)
    }
}

struct State {
    backend: Option<ZeroChallengeFaultOracle>,
    coins: Option<Value>,
    transcript: Value,
    original: Capability,
    guards: Vec<bool>,
    codecs: usize,
    snapshots: Vec<(u64, u64, u64, u64)>,
    buffers: Vec<(usize, usize)>,
    failure: Option<String>,
}
struct Case {
    zeros: usize,
    draws: u64,
    work: u64,
    attempts: u64,
    items: Vec<u64>,
}
impl Default for Case {
    fn default() -> Self {
        Self {
            zeros: 2,
            draws: 3,
            work: 99,
            attempts: 4,
            items: vec![],
        }
    }
}
type ResultRecord = Execution<State, Event<&'static str>, Prepared<()>>;

fn run(case: Case) -> ResultRecord {
    let input = zkc_test_support::root().join("tests/fixtures/input-families/zero-challenge.pir");
    let source = zkc_test_support::compile("protocol-source", &input);
    // protocol-compile imports authored source into MLIR and projects physical roles.
    let candidate = zkc_test_support::compile("protocol-compile", &input);
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let mut native = fixture::backend().with_external_work_limit(case.work);
    let coins = native
        .issue_rng(Domain::new("P", "test", "main", None), case.draws)
        .unwrap();
    let Value::Rng(original) = coins.clone() else {
        panic!("rng")
    };
    let backend = ZeroChallengeFaultOracle {
        native,
        zero_calls: case.zeros,
        transitions: vec![],
        candidates: RefCell::new(vec![]),
        draws: vec![],
    };
    // Independent Lean common/participant correspondence is required at admission.
    let admitted = admit_physical(&source, &candidate, &backend, &checker).unwrap();
    let state = State {
        backend: Some(backend),
        coins: Some(coins),
        transcript: initial_state(),
        original,
        guards: vec![],
        codecs: 0,
        snapshots: vec![],
        buffers: vec![],
        failure: None,
    };
    Controller::new(
        state,
        Limits {
            attempts: case.attempts,
            proof_bytes: 32,
        },
    )
    .advance(8, |_, context| {
        let state = context.state_mut();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "test",
            state.backend.take().unwrap(),
            vec![
                state.coins.take().unwrap(),
                state.transcript.clone(),
                indices(case.items.clone()),
            ],
        )
        .unwrap_or_else(|e| panic!("runner load: {}", e.error));
        let completion_returned = Cell::new(false);
        let report = artifact::attempt::execute(
            &mut runner,
            1024,
            |outputs| {
                let [coins, next, challenge, Value::Bool(retry)] = outputs.as_slice() else {
                    panic!("returned coins, state, challenge, retry")
                };
                assert_eq!(numbers(challenge).len(), 32);
                assert_eq!(&numbers(next)[..3], &[1_514_881_876, 1, 1]);
                assert_eq!(&numbers(next)[3..], numbers(challenge));
                // Retry is computed by the compiled loop, not supplied by this host.
                assert_eq!(*retry, numbers(challenge).iter().all(|b| *b == 0));
                completion_returned.set(!retry);
                state.guards.push(*retry);
                state.transcript = next.clone();
                state.coins = Some(coins.clone());
                Ok(if *retry {
                    Decision::Retry(())
                } else {
                    Decision::Complete(())
                })
            },
            |messages| {
                assert!(
                    completion_returned.get(),
                    "codec before returned completion"
                );
                state.codecs += 1;
                assert_eq!(messages.len(), 1);
                assert_eq!(messages[0].envelope.schema, "candidate");
                let Value::Field(value) = &messages[0].payload else {
                    panic!("candidate field")
                };
                // Typed test codec, invoked only after the returned completion decision.
                Ok(zkc_arkworks::encode_scalar(value).unwrap().to_vec())
            },
        );
        assert!(report.cancelled.is_none());
        state.buffers.push((report.messages, report.bytes));
        let backend = runner.into_backend();
        assert_eq!(backend.native.active_frames(), 0);
        let o = backend.native.observe(&state.original).unwrap();
        state.snapshots.push((
            o.generation,
            o.draw_count,
            o.budget,
            backend.native.external_work_spent(),
        ));
        assert_eq!(
            backend
                .validate_value(&Value::Rng(state.original.clone()))
                .unwrap_err()
                .code,
            "refused:capability-stale"
        );
        if let Some(coins) = &state.coins {
            backend.validate_value(coins).unwrap();
        }
        state.backend = Some(backend); // retain actual successor even on stop
        match report.outcome {
            Ok(Decision::Retry(())) => Ok(Decision::Retry("zero-challenge-fault-oracle")),
            Ok(Decision::Complete(proof)) => {
                context.append(&proof.bytes)?;
                Ok(Decision::Complete(()))
            }
            Err(ArtifactFailure::Stopped(stop)) => {
                assert!(stop.cleanup_errors.is_empty());
                let StopKind::Backend(error) = stop.kind else {
                    panic!("backend stop")
                };
                let reason = if error.code.starts_with("exhausted:") {
                    Stop::Exhausted
                } else {
                    Stop::Refused
                };
                state.failure = Some(error.code);
                Err(reason)
            }
            Err(other) => panic!("unexpected failure: {other:?}"),
        }
    })
    .close()
}

#[test]
fn two_actual_zero_challenges_then_native_success_release_only_last_candidate() {
    let result = run(Case::default());
    let Outcome::Returned(proof) = &result.outcome else {
        panic!("no proof: {:?}", result.outcome)
    };
    assert_eq!(proof.attempt, 2);
    assert_eq!(result.state.guards, [true, true, false]);
    assert_eq!(result.state.codecs, 1);
    assert_eq!(
        result.state.snapshots,
        [(1, 1, 2, 33), (2, 2, 1, 66), (3, 3, 0, 99)]
    );
    assert_eq!(result.state.buffers, [(1, 38); 3]);
    let backend = result.state.backend.as_ref().unwrap();
    let transitions = &backend.transitions;
    assert_eq!(transitions.len(), 3);
    assert_eq!(transitions[0].input, numbers(&initial_state()));
    for (i, t) in transitions.iter().enumerate() {
        assert_eq!(t.work, 33 * (i as u64 + 1));
        if i < 2 {
            assert_eq!(t.emitted, [0; 32]);
            assert_ne!(t.actual, t.emitted);
        } else {
            assert_eq!(t.emitted, t.actual);
        }
        if i > 0 {
            assert_eq!(&t.input[3..], transitions[i - 1].emitted);
        }
    }
    let candidates = backend.candidates.borrow();
    assert_eq!(candidates.len(), 3);
    assert_eq!(proof.bytes, candidates[2][6..]);
    assert_ne!(proof.bytes, candidates[0][6..]);
    assert_ne!(proof.bytes, candidates[1][6..]);
    assert_eq!(
        result.events,
        [
            Event::Started { attempt: 0 },
            Event::Retried {
                attempt: 0,
                reason: "zero-challenge-fault-oracle",
                bytes: 0
            },
            Event::Started { attempt: 1 },
            Event::Retried {
                attempt: 1,
                reason: "zero-challenge-fault-oracle",
                bytes: 0
            },
            Event::Started { attempt: 2 },
            Event::Produced {
                attempt: 2,
                bytes: 32
            },
        ]
    );
}

#[test]
fn ordinary_native_transition_completes_on_first_attempt() {
    let result = run(Case {
        zeros: 0,
        ..Case::default()
    });
    let Outcome::Returned(proof) = &result.outcome else {
        panic!("ordinary failed")
    };
    assert_eq!(proof.attempt, 0);
    assert_eq!(result.state.guards, [false]);
    assert_eq!(result.state.codecs, 1);
    assert_eq!(result.state.snapshots, [(1, 1, 2, 33)]);
    let backend = result.state.backend.as_ref().unwrap();
    assert_eq!(
        backend.transitions[0].actual,
        backend.transitions[0].emitted
    );
    assert_eq!(proof.bytes, backend.candidates.borrow()[0][6..]);
}

fn assert_stopped(result: &ResultRecord, stop: Stop, code: Option<&str>, retries: usize) {
    assert!(matches!(result.outcome, Outcome::Stopped(s) if s == stop));
    assert_eq!(result.state.failure.as_deref(), code);
    assert_eq!(result.state.codecs, 0);
    assert_eq!(result.state.guards, vec![true; retries]);
    assert_eq!(
        result
            .events
            .iter()
            .filter(|e| matches!(e, Event::Retried { .. }))
            .count(),
        retries
    );
    assert!(
        !result
            .events
            .iter()
            .any(|e| matches!(e, Event::Produced { .. }))
    );
}

#[test]
fn external_work_exhaustion_after_two_retries_retains_draw_and_work() {
    let result = run(Case {
        work: 66,
        zeros: 8,
        ..Case::default()
    });
    assert_stopped(
        &result,
        Stop::Exhausted,
        Some("exhausted:external-work-limit"),
        2,
    );
    assert_eq!(
        result.state.snapshots,
        [(1, 1, 2, 33), (2, 2, 1, 66), (3, 3, 0, 66)]
    );
    assert_eq!(result.state.buffers, [(1, 38); 3]);
    assert_eq!(result.state.backend.as_ref().unwrap().transitions.len(), 2);
}

#[test]
fn malformed_update_stops_after_candidate_without_oracle_or_codec() {
    let result = run(Case {
        items: vec![0],
        ..Case::default()
    });
    assert_stopped(
        &result,
        Stop::Refused,
        Some("refused:external-word-width"),
        0,
    );
    assert_eq!(result.state.snapshots, [(1, 1, 2, 0)]);
    assert_eq!(result.state.buffers, [(1, 38)]);
    assert!(
        result
            .state
            .backend
            .as_ref()
            .unwrap()
            .transitions
            .is_empty()
    );
}

#[test]
fn rng_exhaustion_after_retry_keeps_consuming_failure_and_prior_work() {
    let result = run(Case {
        draws: 1,
        ..Case::default()
    });
    assert_stopped(
        &result,
        Stop::Exhausted,
        Some("exhausted:resource-budget"),
        1,
    );
    assert_eq!(result.state.snapshots, [(1, 1, 0, 33), (2, 2, 0, 33)]);
    assert_eq!(result.state.buffers, [(1, 38), (0, 0)]);
}

#[test]
fn attempt_limit_discards_both_zero_candidates_without_restarting_backend() {
    let result = run(Case {
        attempts: 2,
        ..Case::default()
    });
    assert_stopped(&result, Stop::Exhausted, None, 2);
    assert_eq!(result.state.snapshots, [(1, 1, 2, 33), (2, 2, 1, 66)]);
    assert_eq!(result.state.buffers, [(1, 38); 2]);
}

/// Replay each body with its exact native draw as a reference tape and its
/// selected hash reply as an explicit primitive assumption. Resources start at
/// generation zero for EACH replay: this does not model the host controller or
/// establish persistent native/Lean resource correspondence.
#[test]
fn lean_reference_replays_exact_zero_hash_requests_and_body_guards() {
    use serde_json::{Value as Json, json};
    use std::{fs, process::Command};
    let result = run(Case::default());
    assert!(matches!(result.outcome, Outcome::Returned(_)));
    let backend = result.state.backend.as_ref().unwrap();
    assert_eq!(backend.draws.len(), 3);
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("source.json");
    fs::write(
        &source,
        zkc_test_support::compile(
            "protocol-source",
            zkc_test_support::root().join("tests/fixtures/input-families/zero-challenge.pir"),
        ),
    )
    .unwrap();
    let inputs_path = directory.path().join("inputs.json");
    let reference = |inputs: &Json| -> Json {
        fs::write(&inputs_path, serde_json::to_vec(inputs).unwrap()).unwrap();
        let output = Command::new(zkc_test_support::checker("interactive-protocol"))
            .args(["--generic-role"])
            .arg(&source)
            .arg(&inputs_path)
            .arg("P")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        serde_json::from_slice(&output.stdout).unwrap()
    };
    let strings = |xs: &[u64]| xs.iter().map(u64::to_string).collect::<Vec<_>>();
    for (i, transition) in backend.transitions.iter().enumerate() {
        let mut inputs = json!([
            "zkc.reference-inputs/1",
            "main",
            "test",
            [[
                "P",
                [
                    ["coins", ["rng:bls12-381.fr", ["coins", "0"]]],
                    ["state", ["indices", strings(&transition.input)]],
                    ["items", ["indices", []]]
                ]
            ]],
            [["coins", "P", "Main", "1", ["rng", [backend.draws[i]]]]],
            [],
            []
        ]);
        let pending = reference(&inputs);
        assert_eq!(pending[3][0], "pending-primitive");
        assert_eq!(pending[3][1], "exact-request-missing");
        let request = pending[4].as_array().unwrap().last().unwrap()[1].clone();
        assert_eq!(request[0], "zkc.external-primitive/1");
        assert_eq!(request[2], "monero.v0.18.5.1.keccak256.reduce32");
        assert_eq!(request[3], json!(strings(&transition.input[3..])));
        inputs[5] = json!([[request, ["ok", strings(&transition.emitted)]]]);
        let replay = reference(&inputs);
        assert_eq!(replay[3][0], "returned", "{replay}");
        let mut packed = vec![1_514_881_876, 1, 1];
        packed.extend(&transition.emitted);
        assert_eq!(
            replay[3][1],
            json!([
                ["rng:bls12-381.fr", ["coins", "1"]],
                ["indices", strings(&packed)],
                ["indices", strings(&transition.emitted)],
                ["bool", if i < 2 { "true" } else { "false" }],
            ])
        );
        assert_eq!(
            replay[5],
            json!([["coins", "P", "Main", "1", "1", "0", "rng"]])
        );
        let events = replay[4].as_array().unwrap();
        let sends: Vec<_> = events.iter().filter(|e| e[0] == "send").collect();
        assert_eq!(sends.len(), 1);
        assert_eq!(sends[0][2], "candidate");
        assert_eq!(sends[0][4], json!(["field:bls12-381.fr", backend.draws[i]]));
        assert_eq!(events.iter().filter(|e| e[0] == "external").count(), 1);
        // Supplying a reply to a different input cannot satisfy this request.
        inputs[5][0][0][3][0] = json!("99");
        assert_eq!(reference(&inputs)[3][0], "pending-primitive");
        println!(
            "Lean body {i}: exact hash request, state/scalar, guard={}, candidate and one logical RNG draw checked; wrong-request control pending",
            i < 2
        );
    }
}
