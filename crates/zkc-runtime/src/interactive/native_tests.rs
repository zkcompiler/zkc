//! Runtime transition controls with a deliberately small, noncryptographic backend.
use super::*;
use crate::interactive::{LogicalType, ProgramAction, admit_supplied};
use serde_json::json;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

const FIELD: &str = "field:bls12-381.fr@arkworks.fr/1";
#[derive(Debug)]
struct V {
    clones: Arc<AtomicUsize>,
    ty: PhysicalType,
    size: usize,
    public: bool,
    valid: bool,
    number: u64,
}
impl Clone for V {
    fn clone(&self) -> Self {
        self.clones.fetch_add(1, Ordering::Relaxed);
        Self {
            clones: self.clones.clone(),
            ty: self.ty.clone(),
            size: self.size,
            public: self.public,
            valid: self.valid,
            number: self.number,
        }
    }
}
impl V {
    fn index(number: u64) -> Self {
        Self {
            ty: PhysicalType::parse("index@native.index/1").unwrap(),
            number,
            ..Self::field()
        }
    }
    fn boolean(value: bool) -> Self {
        Self {
            ty: PhysicalType::parse("bool@native.bool/1").unwrap(),
            number: u64::from(value),
            ..Self::field()
        }
    }
    fn field() -> Self {
        Self {
            clones: Arc::default(),
            ty: PhysicalType::parse(FIELD).unwrap(),
            size: 32,
            public: true,
            valid: true,
            number: 0,
        }
    }
}
impl Value for V {
    fn control_bool(&self) -> std::result::Result<bool, BackendError> {
        Ok(self.number != 0)
    }
    fn control_index(&self) -> std::result::Result<u64, BackendError> {
        Ok(self.number)
    }
    // Deliberately broken adapter: the runner must reject this before body entry.
    fn from_control_index(_: u64) -> std::result::Result<Self, BackendError> {
        Ok(Self::field())
    }

    fn physical_type(&self) -> PhysicalType {
        self.ty.clone()
    }
    fn retained_bytes(&self) -> usize {
        self.size
    }
    fn validate_serializable(&self) -> std::result::Result<(), BackendError> {
        if self.public {
            Ok(())
        } else {
            Err(BackendError::new("private"))
        }
    }
}
#[derive(Debug, Default)]
struct Mock {
    frames: usize,
    closes: usize,
    fail_leave: bool,
}
impl Backend for Mock {
    type Value = V;
    fn validate_value(&self, v: &V) -> std::result::Result<(), BackendError> {
        if v.valid {
            Ok(())
        } else {
            Err(BackendError::new("invalid-value"))
        }
    }
    fn enter_frame(&mut self, _: &Frame, _: &[V]) -> std::result::Result<(), BackendError> {
        self.frames += 1;
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        _: FrameExit,
        _: &[V],
    ) -> std::result::Result<(), BackendError> {
        self.frames -= 1;
        self.closes += 1;
        if self.fail_leave {
            Err(BackendError::new(format!("cleanup.{}", frame.id().get())))
        } else {
            Ok(())
        }
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[V]) -> std::result::Result<Vec<V>, BackendError> {
        Err(BackendError::new("unexpected-kernel"))
    }
}
fn program() -> Admitted {
    program_with_type(FIELD)
}
fn program_with_type(field: &str) -> Admitted {
    let value = json!([
        "zkc.program/2",
        [],
        [[
            "function",
            "id",
            [["x", field]],
            [field],
            [["return", ["x"]]],
            ["id", []]
        ]],
        [
            [
                "participant",
                "a",
                "root",
                "Alice",
                [["x", field]],
                [],
                [
                    ["local", "identity", "id", ["x"], ["y"]],
                    ["send", "message", "message", "Bob", "y"],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "b",
                "root",
                "Bob",
                [],
                [field],
                [
                    ["receive", "message", "message", "Alice", "z", field],
                    ["return", ["z"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["Alice", "a"], ["Bob", "b"]]]]
    ]);
    admit_supplied(&serde_json::to_vec(&value).unwrap(), &Mock::default()).unwrap()
}
fn receiver() -> Runner<Mock> {
    Runner::new(
        &program(),
        "main",
        "Bob",
        "session",
        Mock::default(),
        vec![],
    )
    .unwrap()
}
fn expose(r: &mut Runner<Mock>) -> Cut {
    match r.poll() {
        Action::Receive(receive) => receive.cut(),
        _ => panic!("receive"),
    }
}
#[test]
fn send_checks_and_consumption_do_not_clone_pending_payloads() {
    let value = V::field();
    let clones = value.clones.clone();
    let mut sender = Runner::new(
        &program(),
        "main",
        "Alice",
        "session",
        Mock::default(),
        vec![value],
    )
    .unwrap();
    let local = sender.poll_ref().cut().unwrap();
    sender.execute_local(&local).unwrap();
    let Action::Send(packet) = sender.poll_ref() else {
        panic!("send")
    };
    let cut = packet.envelope.cut(CutKind::Send);
    let unrelated = Packet {
        envelope: packet.envelope.clone(),
        ty: packet.ty.clone(),
        payload: V::field(),
    };
    let before = clones.load(Ordering::Relaxed);
    let usage = sender.usage();
    let mut wrong = cut.clone();
    wrong.site.push_str("-stale");
    assert!(matches!(
        sender.take_send(&wrong),
        Err(RuntimeError::WrongCut)
    ));
    assert_eq!(
        sender.check_delivery(&unrelated),
        Err(RuntimeError::WrongAction)
    );
    assert_eq!(sender.usage(), usage);
    let sent = sender.take_send(&cut).unwrap();
    assert!(Arc::ptr_eq(&sent.payload.clones, &clones));
    assert_eq!(clones.load(Ordering::Relaxed), before);
    let mut recipient = receiver();
    let receive = expose(&mut recipient);
    recipient.check_delivery(&sent).unwrap();
    assert_eq!(recipient.poll_ref().cut(), Some(receive));
    assert_eq!(clones.load(Ordering::Relaxed), before);
}

#[test]
fn layout_resolves_send_operand_type_through_local_results() {
    let entry = program().program_entry("main").unwrap();
    assert!(matches!(&entry[0].actions[1], ProgramAction::Send { ty, .. } if ty == &V::field().ty));
    assert!(matches!(&entry[1].actions[1], ProgramAction::Finish));
    assert!(program().program_entry("missing").is_err());
}
#[test]
fn inspection_preserves_unpolled_pending_and_return_states() {
    let mut r = receiver();
    let usage = r.usage();
    for _ in 0..3 {
        assert!(matches!(
            r.inspect_program().unwrap(),
            ProgramState::Unpolled {
                kind: Some(CutKind::Receive),
                ..
            }
        ));
        assert_eq!(r.usage(), usage);
        assert_eq!(r.backend().frames, 1);
    }
    let cut = expose(&mut r);
    assert!(matches!(
        r.inspect_program().unwrap(),
        ProgramState::Pending(ProgramCut {
            kind: CutKind::Receive,
            ..
        })
    ));
    assert_eq!(
        r.complete_receive(&cut, Ok(V::field())),
        Ok(ReceiveCompletion::Delivered)
    );
    let usage = r.usage();
    assert!(matches!(
        r.inspect_program().unwrap(),
        ProgramState::Unpolled {
            kind: None,
            site: None
        }
    ));
    assert_eq!(r.backend().frames, 1);
    assert_eq!(r.usage(), usage);
    assert!(matches!(r.poll(), Action::Returned(_)));
    assert!(matches!(
        r.inspect_program().unwrap(),
        ProgramState::Returned
    ));
    assert_eq!(r.returned_values().unwrap().len(), 1);
    assert_eq!(r.backend().frames, 0);
}
#[test]
fn wrong_unexposed_stale_and_wrong_type_requests_do_not_advance() {
    let mut other = receiver();
    let cut = expose(&mut other);
    let mut r = receiver();
    assert_eq!(
        r.complete_receive(&cut, Err(DecodeReason::Length)),
        Err(RuntimeError::WrongAction)
    );
    assert!(matches!(
        r.inspect_program().unwrap(),
        ProgramState::Unpolled { .. }
    ));
    let cut = expose(&mut r);
    let usage = r.usage();
    for dimension in 0..5 {
        let mut wrong = cut.clone();
        match dimension {
            0 => wrong.role.push('x'),
            1 => wrong.site.push('x'),
            2 => wrong.origin.session.push('x'),
            3 => wrong.origin.instance.push('x'),
            _ => wrong.kind = CutKind::Send,
        }
        assert_eq!(
            r.complete_receive(&wrong, Err(DecodeReason::Header)),
            Err(RuntimeError::WrongCut)
        );
        assert_eq!(r.usage(), usage);
    }
    for private in [false, true] {
        let mut bad = V::field();
        if private {
            bad.public = false;
        } else {
            bad.ty = PhysicalType::parse("bool@native.bool/1").unwrap();
        }
        assert_eq!(
            r.complete_receive(&cut, Ok(bad)),
            Err(RuntimeError::Payload)
        );
        assert_eq!(r.usage(), usage);
    }
    assert_eq!(
        r.complete_receive(&cut, Ok(V::field())),
        Ok(ReceiveCompletion::Delivered)
    );
    let usage = r.usage();
    assert_eq!(
        r.complete_receive(&cut, Ok(V::field())),
        Err(RuntimeError::WrongAction)
    );
    assert_eq!(r.usage(), usage);
}
#[test]
fn accepted_receive_stops_have_exact_site_and_preserve_primary_cause() {
    for reason in [
        DecodeReason::Length,
        DecodeReason::Header,
        DecodeReason::Boolean,
        DecodeReason::Scalar,
        DecodeReason::Group,
    ] {
        let mut r = receiver();
        r.backend.fail_leave = true;
        let cut = expose(&mut r);
        assert_eq!(
            r.complete_receive(&cut, Err(reason)),
            Ok(ReceiveCompletion::Stopped)
        );
        let stop = r.stop().unwrap();
        assert_eq!(stop.kind, StopKind::Decode(reason));
        assert_eq!(stop.site.as_deref(), Some("message"));
        assert_eq!(stop.cleanup_errors.len(), 1);
        assert_eq!(r.backend().frames, 0);
        assert_eq!(r.usage().instructions, 1);
    }
    let mut r = receiver();
    let cut = expose(&mut r);
    let mut bad = V::field();
    bad.valid = false;
    assert_eq!(
        r.complete_receive(&cut, Ok(bad)),
        Ok(ReceiveCompletion::Stopped)
    );
    assert_eq!(
        r.stop().unwrap().kind,
        StopKind::Backend(BackendError::new("invalid-value"))
    );
}
#[test]
fn receive_tick_precedes_decode_and_retention_is_a_limit_stop() {
    let mut r = receiver();
    let cut = expose(&mut r);
    r.usage.instructions = Limits::INSTRUCTIONS;
    assert_eq!(
        r.complete_receive(&cut, Err(DecodeReason::Length)),
        Ok(ReceiveCompletion::Stopped)
    );
    assert_eq!(r.stop().unwrap().kind, StopKind::Limit);
    assert_eq!(r.usage().instructions, Limits::INSTRUCTIONS);
    let mut r = receiver();
    let cut = expose(&mut r);
    r.value_budget.live_bytes = 0;
    assert_eq!(
        r.complete_receive(&cut, Ok(V::field())),
        Ok(ReceiveCompletion::Stopped)
    );
    assert_eq!(r.stop().unwrap().kind, StopKind::Limit);
    assert_eq!(r.usage().instructions, 1);
}
#[test]
fn packet_delivery_preserves_public_value_checks() {
    let mut r = Runner::new(
        &program(),
        "main",
        "Bob",
        "session",
        Mock::default(),
        vec![],
    )
    .unwrap();
    let Action::Receive(request) = r.poll() else {
        panic!("receive")
    };
    let usage = r.usage();
    let mut value = V::field();
    value.public = false;
    assert!(
        r.deliver(Packet {
            envelope: request.envelope.clone(),
            ty: request.ty.clone(),
            payload: value
        })
        .is_err()
    );
    assert_eq!(r.usage(), usage);
    r.deliver(Packet {
        envelope: request.envelope,
        ty: request.ty,
        payload: V::field(),
    })
    .unwrap();
    assert!(matches!(r.poll(), Action::Returned(_)));
}

#[test]
fn existing_numeric_message_types_keep_value_serialization_checks() {
    for logical in [
        "vector:bls12-381.fr",
        "groups:bls12-381.g1",
        "indices",
        "matrix:bls12-381.fr",
    ] {
        let ty = PhysicalType::default_for(LogicalType::parse(logical).unwrap()).unwrap();
        assert!(ty.is_serializable() && ty.has_native_data_frame());
        let private = V {
            ty: ty.clone(),
            public: false,
            ..V::field()
        };
        for native in [false, true] {
            let admitted = program_with_type(&ty.spelling());
            let mut receiving =
                Runner::new(&admitted, "main", "Bob", "session", Mock::default(), vec![]).unwrap();
            let Action::Receive(request) = receiving.poll() else {
                panic!("receive")
            };
            let before = receiving.usage();
            if native {
                assert_eq!(
                    receiving.complete_receive(&request.cut(), Ok(private.clone())),
                    Err(RuntimeError::Payload)
                );
            } else {
                assert!(
                    receiving
                        .deliver(Packet {
                            envelope: request.envelope,
                            ty: ty.clone(),
                            payload: private.clone()
                        })
                        .is_err()
                );
            }
            assert_eq!(receiving.usage(), before);
            let mut sending = Runner::new(
                &admitted,
                "main",
                "Alice",
                "session",
                Mock::default(),
                vec![private.clone()],
            )
            .unwrap();
            let Action::Local(local) = sending.poll() else {
                panic!("local")
            };
            sending.execute_local(&local.cut).unwrap();
            assert!(matches!(sending.poll(), Action::Stopped(stop)
                if matches!(stop.kind, StopKind::Backend(ref error) if error.code == "private")));
        }
    }
}

#[test]
fn borrowed_poll_exposure_finish_and_send_exhaustion_preserve_stops() {
    let mut receive = receiver();
    receive.usage.instructions = Limits::INSTRUCTIONS;
    assert!(matches!(receive.poll_ref(), Action::Stopped(stop) if stop.kind == StopKind::Limit));
    assert_eq!(receive.backend().frames, 0);
    let mut finish = receiver();
    let cut = expose(&mut finish);
    finish.complete_receive(&cut, Ok(V::field())).unwrap();
    finish.usage.instructions = Limits::INSTRUCTIONS;
    assert!(matches!(
        finish.inspect_program().unwrap(),
        ProgramState::Unpolled { kind: None, .. }
    ));
    assert!(matches!(finish.poll_ref(), Action::Stopped(stop) if stop.kind == StopKind::Limit));
    let mut send = Runner::new(
        &program(),
        "main",
        "Alice",
        "session",
        Mock::default(),
        vec![V::field()],
    )
    .unwrap();
    let Action::Local(local) = send.poll() else {
        panic!("local")
    };
    send.execute_local(&local.cut).unwrap();
    let cut = send.poll_ref().cut().unwrap();
    send.usage.instructions = Limits::INSTRUCTIONS;
    assert!(send.take_send(&cut).is_err());
    assert_eq!(send.stop().unwrap().kind, StopKind::Limit);
    assert_eq!(send.backend().frames, 0);
}

fn local_candidate(body: serde_json::Value) -> Admitted {
    let index = "index@native.index/1";
    let boolean = "bool@native.bool/1";
    let ports = json!([["lo", index], ["hi", index], ["flag", boolean]]);
    let carrier = json!([
        "zkc.program/2",
        [],
        [["function", "f", ports, [index], body, ["f", []]]],
        [[
            "participant",
            "a",
            "root",
            "Alice",
            ports,
            [],
            [
                ["local", "call", "f", ["lo", "hi", "flag"], ["out"]],
                ["return", []]
            ],
            []
        ]],
        [["entry", "main", [["Alice", "a"]]]]
    ]);
    admit_supplied(&serde_json::to_vec(&carrier).unwrap(), &Mock::default()).unwrap()
}

#[test]
fn local_cleanup_errors_follow_actual_frame_exit_order() {
    let body = json!([
        [
            "if",
            "branch",
            "flag",
            ["lo"],
            [["stop", "failure", "reject"]],
            [["yield", ["lo"]]],
            ["out"]
        ],
        ["return", ["out"]]
    ]);
    {
        let admitted = local_candidate(body.clone());
        let backend = Mock {
            fail_leave: true,
            ..Mock::default()
        };
        let mut runner = Runner::new(
            &admitted,
            "main",
            "Alice",
            "test",
            backend,
            vec![V::index(0), V::index(1), V::boolean(true)],
        )
        .unwrap();
        {
            let Action::Local(action) = runner.poll() else {
                panic!("local cut")
            };
            runner.execute_local(&action.cut).unwrap();
        }
        let stop = runner.stop().expect("local stop");
        assert!(matches!(&stop.kind, StopKind::Explicit(reason) if reason == "reject"));
        let errors: Vec<_> = stop
            .cleanup_errors
            .iter()
            .map(|e| e.code.as_str())
            .collect();
        assert_eq!(errors, ["cleanup.3", "cleanup.2", "cleanup.1"]);
        assert_eq!(runner.backend().frames, 0);
        assert_eq!(runner.backend().closes, 3);
    }
}

#[test]
fn successful_local_cleanup_failures_stop_once() {
    {
        let admitted = local_candidate(json!([["return", ["lo"]]]));
        let mut runner = Runner::new(
            &admitted,
            "main",
            "Alice",
            "test",
            Mock {
                fail_leave: true,
                ..Mock::default()
            },
            vec![V::index(0), V::index(1), V::boolean(true)],
        )
        .unwrap();
        {
            let Action::Local(action) = runner.poll() else {
                panic!("local cut")
            };
            runner.execute_local(&action.cut).unwrap();
            assert!(runner.execute_local(&action.cut).is_err());
        }
        let stop = runner.stop().expect("cleanup stops the role").clone();
        assert!(matches!(&stop.kind, StopKind::Backend(e) if e.code == "cleanup.2"));
        assert_eq!(stop.site.as_deref(), Some("call"));
        assert_eq!(
            stop.cleanup_errors
                .iter()
                .map(|e| e.code.as_str())
                .collect::<Vec<_>>(),
            ["cleanup.1"]
        );
        let usage = runner.usage();
        for _ in 0..2 {
            assert!(matches!(runner.poll(), Action::Stopped(ref current) if current == &stop));
        }
        assert_eq!(runner.usage(), usage);
        assert_eq!(runner.backend().closes, 2);
        assert_eq!(runner.backend().frames, 0);
    }
}

#[test]
fn local_induction_rejects_a_backend_literal_with_the_wrong_type() {
    let body = json!([
        ["for", "items", "i", "lo", "hi", [], [], [["yield", []]], []],
        ["return", ["lo"]]
    ]);
    let admitted = local_candidate(body);
    let mut runner = Runner::new(
        &admitted,
        "main",
        "Alice",
        "test",
        Mock::default(),
        vec![V::index(0), V::index(1), V::boolean(true)],
    )
    .unwrap();
    let Action::Local(action) = runner.poll() else {
        panic!("local cut")
    };
    runner.execute_local(&action.cut).unwrap();
    let stop = runner.stop().expect("bad induction stops the role");
    assert!(matches!(&stop.kind, StopKind::Backend(e) if e.code == "runtime-contract:Payload"));
    assert_eq!(stop.site.as_deref(), Some("items"));
    // Root and function entered; the body frame never accepted the bad literal.
    assert_eq!(runner.backend().closes, 2);
    assert_eq!(runner.usage().iterations, 1);
}

#[test]
fn protocol_induction_rejects_a_backend_literal_with_the_wrong_type() {
    let carrier = json!([
        "zkc.program/2",
        [],
        [],
        [[
            "participant",
            "a",
            "root",
            "Alice",
            [["n", "index@native.index/1"]],
            [],
            [
                [
                    "loop",
                    "rounds",
                    ["value", "n", "8", "i"],
                    [],
                    [],
                    [["yield", []]],
                    []
                ],
                ["return", []]
            ],
            []
        ]],
        [["entry", "main", [["Alice", "a"]]]]
    ]);
    let admitted =
        admit_supplied(&serde_json::to_vec(&carrier).unwrap(), &Mock::default()).unwrap();
    let mut runner = Runner::new(
        &admitted,
        "main",
        "Alice",
        "test",
        Mock::default(),
        vec![V::index(1)],
    )
    .unwrap();
    let origin = runner.root_origin().clone();
    assert_eq!(runner.loop_count(&origin, "rounds").unwrap(), Some(1));
    runner.enter_loop(&origin, "rounds", 1).unwrap();
    let stop = runner.stop().expect("bad induction stops the role");
    assert!(matches!(&stop.kind, StopKind::Backend(e) if e.code == "runtime-contract:Payload"));
    assert_eq!(stop.site.as_deref(), Some("rounds"));
    assert_eq!(runner.backend().closes, 1);
    assert_eq!(runner.usage().iterations, 1);
}
