mod common;
use common::*;
use serde_json::json;
use std::sync::{Arc, Mutex};
use zkc_backends::*;
use zkc_runtime::interactive::{
    Backend, BackendError, Frame, FrameExit, FrameKind, Invocation, Runner, admit_supplied,
};

fn draw_program() -> Vec<u8> {
    program(
        None,
        &[("r", "rng")],
        vec![op(
            "draw",
            "arkworks/random.draw",
            &["r"],
            &["value", "next"],
        )],
        &["field", "rng"],
        &["value", "next"],
    )
}
#[test]
fn os_draws_use_real_advancing_resources_and_clone_is_only_handle() {
    let mut b = ark_backend(None);
    let r = b.issue_rng(domain(), 3).unwrap();
    let outside = b.issue_rng(domain(), 7).unwrap();
    let before = b.observe(token(&outside)).unwrap();
    let (out, b) = run(&draw_program(), b, vec![r.clone()]);
    let out = out.unwrap();
    let state = b.observe(token(&r)).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (1, 1, 2)
    );
    assert_eq!(b.observe(token(&outside)).unwrap(), before);
    assert!(b.validate_value(&r).unwrap_err().code.contains("stale"));
    let first = scalar(&out[0]);
    let (out, b) = run(&draw_program(), b, vec![out[1].clone()]);
    let out = out.unwrap();
    assert_ne!(scalar(&out[0]), first); // Negligible accidental equality, not a statistical security proof.
    assert_eq!(b.observe(token(&r)).unwrap().generation, 2);
    assert_eq!(b.active_frames(), 0);
}
#[test]
fn actual_alias_cross_backend_wrong_kind_and_domain_are_refused_at_entry() {
    let bytes = program(None, &[("a", "rng"), ("b", "rng")], vec![], &[], &[]);
    let mut b = ark_backend(None);
    let r = b.issue_rng(domain(), 3).unwrap();
    let admitted = admit_supplied(&bytes, &b).unwrap();
    match Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        b,
        vec![r.clone(), r.clone()],
    ) {
        Err(e) => {
            assert!(e.error.to_string().contains("capability-alias"));
            assert_eq!(e.backend.active_frames(), 0);
            assert_eq!(e.backend.observe(token(&r)).unwrap().generation, 0);
        }
        Ok(_) => panic!(),
    }
    let mut owner = ark_backend(None);
    let token = owner.issue_rng(domain(), 2).unwrap();
    let other = ark_backend(None);
    assert_eq!(
        other.validate_value(&token).unwrap_err().code,
        "refused:capability-authority"
    );
    for bad_domain in [
        Domain::new("V", "session", "main", None),
        Domain::new("P", "other", "main", None),
        Domain::new("P", "session", "other", None),
        Domain::new("P", "session", "main", Some("wrong")),
    ] {
        let mut b = ark_backend(None);
        let r = b.issue_rng(bad_domain, 1).unwrap();
        let admitted = admit_supplied(&draw_program(), &b).unwrap();
        match Runner::new(&admitted, "main", "P", "session", b, vec![r]) {
            Err(e) => {
                assert!(e.error.to_string().contains("capability-domain"));
                assert_eq!(e.backend.active_frames(), 0);
            }
            Ok(_) => panic!(),
        }
    }
    let mut g = backend().build();
    let nonce = g.issue_nonce(domain(), 2).unwrap();
    let Value::Nonce(n) = nonce else { panic!() };
    assert!(owner.validate_value(&Value::Rng(n)).is_err());
}
#[test]
fn exhausted_attempt_advances_generation_and_counter_without_touching_other_slot() {
    let mut b = ark_backend(None);
    let r = b.issue_rng(domain(), 0).unwrap();
    let other = b.issue_rng(domain(), 9).unwrap();
    let before = b.observe(token(&other)).unwrap();
    let (out, b) = run(&draw_program(), b, vec![r.clone()]);
    let stop = out.unwrap_err();
    assert_eq!(code(&stop), "exhausted:resource-budget");
    let state = b.observe(token(&r)).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (1, 1, 0)
    );
    assert_eq!(b.observe(token(&other)).unwrap(), before);
    assert_eq!(b.active_frames(), 0);
    let admitted = admit_supplied(&draw_program(), &b).unwrap();
    assert!(Runner::new(&admitted, "main", "P", "session", b, vec![r]).is_err());
}
#[test]
fn successful_and_failed_multi_resource_frames_preserve_completed_prefix_and_outside() {
    for valid in [true, false] {
        let mut b = ark_backend(None);
        let a = b.issue_rng(domain(), 3).unwrap();
        let second = b.issue_rng(domain(), 4).unwrap();
        let outside = b.issue_rng(domain(), 8).unwrap();
        let before = b.observe(token(&outside)).unwrap();
        let bytes = program(
            None,
            &[("a", "rng"), ("b", "rng"), ("cond", "bool")],
            vec![
                op("a", "arkworks/random.draw", &["a"], &["ra", "anext"]),
                op("check", "arkworks/control.require", &["cond"], &[]),
                op("b", "arkworks/random.draw", &["b"], &["rb", "bnext"]),
            ],
            &["field", "field", "rng", "rng"],
            &["ra", "rb", "anext", "bnext"],
        );
        let (out, b) = run(
            &bytes,
            b,
            vec![a.clone(), second.clone(), Value::Bool(valid)],
        );
        if valid {
            assert_eq!(out.unwrap().len(), 4);
        } else {
            assert_eq!(code(&out.unwrap_err()), "rejected:require");
        }
        assert_eq!(b.observe(token(&a)).unwrap().generation, 1);
        assert_eq!(
            b.observe(token(&second)).unwrap().generation,
            u64::from(valid)
        );
        assert_eq!(b.observe(token(&outside)).unwrap(), before);
        assert_eq!(b.active_frames(), 0);
    }
}

struct Probe {
    inner: NativeBackend,
    hidden: Value,
    root: Option<Frame>,
    findings: Arc<Mutex<Vec<String>>>,
    output_failure: bool,
    leave_failure: bool,
    exit_order_probe: bool,
}
impl Backend for Probe {
    type Value = Value;
    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.inner.binding_signature(binding)
    }
    fn validate_value(&self, v: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> Result<(), BackendError> {
        if matches!(f.kind(), FrameKind::Entry) {
            self.root = Some(f.clone());
        }
        if self.exit_order_probe && matches!(f.kind(), FrameKind::Call { .. }) {
            self.inner.enter_frame(f, args)?;
            let count = self.inner.active_frames();
            for exit in [
                FrameExit::Returned,
                FrameExit::Stopped,
                FrameExit::Cancelled,
            ] {
                let error = self
                    .inner
                    .leave_frame(self.root.as_ref().unwrap(), exit, &[])
                    .unwrap_err();
                assert_eq!(error.code, "refused:frame-exit-order");
                assert_eq!(self.inner.active_frames(), count);
                self.findings.lock().unwrap().push(error.code);
            }
            return Ok(());
        }
        if matches!(f.kind(), FrameKind::Local { .. })
            && !self.output_failure
            && !self.leave_failure
        {
            let count = self.inner.active_frames();
            let failure = self
                .inner
                .enter_frame(f, std::slice::from_ref(&self.hidden))
                .unwrap_err();
            self.findings.lock().unwrap().push(failure.code);
            assert_eq!(self.inner.active_frames(), count); // failed child never installs a view
        }
        self.inner.enter_frame(f, args)?;
        let retirement = self.inner.retire(token(&self.hidden)).unwrap_err();
        assert_eq!(retirement.code, "refused:retire-during-frame");
        Ok(())
    }
    fn leave_frame(&mut self, f: &Frame, e: FrameExit, v: &[Value]) -> Result<(), BackendError> {
        if self.leave_failure && matches!(f.kind(), FrameKind::Local { .. }) {
            let count = self.inner.active_frames();
            let result = self
                .inner
                .leave_frame(f, e, std::slice::from_ref(&self.hidden));
            assert!(result.is_err());
            assert_eq!(self.inner.active_frames(), count - 1);
            return result;
        }
        self.inner.leave_frame(f, e, v)
    }
    fn apply(&mut self, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>, BackendError> {
        if self.output_failure {
            let invocation = Invocation {
                frame: i.frame,
                site: i.site,
                kernel: i.kernel,
                attributes: i.attributes,
                max_output_bytes: 0,
                binding: i.binding,
                logical_origin: i.logical_origin,
            };
            return self.inner.apply(&invocation, args);
        }
        if !self.leave_failure {
            let error = self
                .inner
                .apply(i, std::slice::from_ref(&self.hidden))
                .unwrap_err();
            self.findings.lock().unwrap().push(error.code);
            let root = self.root.as_ref().unwrap();
            let invocation = Invocation {
                frame: root,
                site: i.site,
                kernel: i.kernel,
                attributes: i.attributes,
                max_output_bytes: i.max_output_bytes,
                binding: i.binding,
                logical_origin: i.logical_origin,
            };
            self.findings
                .lock()
                .unwrap()
                .push(self.inner.apply(&invocation, args).unwrap_err().code);
        }
        self.inner.apply(i, args)
    }
}
fn nested_program() -> Vec<u8> {
    participants(json!([
        [[
            "function",
            "draw",
            [["r", "rng"]],
            ["rng"],
            [
                op("d", "arkworks/random.draw", &["r"], &["v", "next"]),
                ["return", ["next"]]
            ]
        ]],
        [
            [
                "participant",
                "root",
                "instance",
                "P",
                [],
                [["a", "rng"], ["b", "rng"]],
                ["rng"],
                [
                    ["call", "child_site", "child", ["a"], ["next"]],
                    ["return", ["next"]]
                ]
            ],
            [
                "participant",
                "child",
                "child_instance",
                "P",
                [],
                [["x", "rng"]],
                ["rng"],
                [
                    ["local", "draw_site", "draw", ["x"], ["child_next"]],
                    ["return", ["child_next"]]
                ]
            ]
        ],
        [["entry", "main", [["P", "root"]]]]
    ]))
    .unwrap()
}
#[test]
fn nested_child_cannot_recover_unpassed_ancestor_slot_and_kernel_needs_active_view() {
    for ancestor_slot in [true, false] {
        let mut inner = ark_backend(None);
        let a = inner.issue_rng(domain(), 3).unwrap();
        let b = inner.issue_rng(domain(), 4).unwrap();
        let outside = inner.issue_rng(domain(), 5).unwrap();
        let hidden = if ancestor_slot {
            b.clone()
        } else {
            outside.clone()
        };
        let hidden_before = inner.observe(token(&hidden)).unwrap();
        let findings = Arc::new(Mutex::new(Vec::new()));
        let probe = Probe {
            inner,
            hidden: hidden.clone(),
            root: None,
            findings: findings.clone(),
            output_failure: false,
            leave_failure: false,
            exit_order_probe: false,
        };
        let (out, p) = run(&nested_program(), probe, vec![a.clone(), b.clone()]);
        out.unwrap();
        assert_eq!(
            *findings.lock().unwrap(),
            vec![
                "refused:capability-out-of-view",
                "refused:capability-out-of-view",
                "refused:inactive-frame"
            ]
        );
        assert_eq!(p.inner.observe(token(&hidden)).unwrap(), hidden_before);
        assert_eq!(p.inner.observe(token(&a)).unwrap().generation, 1);
        assert_eq!(p.inner.observe(token(&b)).unwrap().generation, 0);
        assert_eq!(p.inner.active_frames(), 0);
    }
}
#[test]
fn output_failure_keeps_consumption_and_failed_leave_always_removes_view() {
    for leave_failure in [true, false] {
        let mut inner = ark_backend(None);
        let r = inner.issue_rng(domain(), 3).unwrap();
        let hidden = inner.issue_rng(domain(), 9).unwrap();
        let before = inner.observe(token(&hidden)).unwrap();
        let probe = Probe {
            inner,
            hidden: hidden.clone(),
            root: None,
            findings: Arc::default(),
            output_failure: !leave_failure,
            leave_failure,
            exit_order_probe: false,
        };
        let (out, p) = run(&draw_program(), probe, vec![r.clone()]);
        let stop = out.unwrap_err();
        assert_eq!(
            code(&stop),
            if leave_failure {
                "refused:capability-out-of-view"
            } else {
                "exhausted:output-bytes"
            }
        );
        let state = p.inner.observe(token(&r)).unwrap();
        assert_eq!(
            (state.generation, state.draw_count, state.budget),
            (1, 1, 2)
        );
        assert_eq!(p.inner.observe(token(&hidden)).unwrap(), before);
        assert_eq!(p.inner.active_frames(), 0);
    }
}
#[test]
fn non_top_exit_refusal_preserves_views_for_ordered_cleanup_without_resource_effects() {
    let mut inner = ark_backend(None);
    let a = inner.issue_rng(domain(), 3).unwrap();
    let b = inner.issue_rng(domain(), 4).unwrap();
    let outside = inner.issue_rng(domain(), 5).unwrap();
    let before = [&a, &b, &outside].map(|v| inner.observe(token(v)).unwrap());
    let probe = Probe {
        inner,
        hidden: outside.clone(),
        root: None,
        findings: Arc::default(),
        output_failure: false,
        leave_failure: false,
        exit_order_probe: true,
    };
    let mut j: serde_json::Value = serde_json::from_slice(&nested_program()).unwrap();
    j[4][0][6] = json!([
        "rng:bls12-381.fr@host.resource/1",
        "rng:bls12-381.fr@host.resource/1"
    ]);
    j[4][0][7][1] = json!(["return", ["next", "b"]]);
    j[4][1][7] = json!([["return", ["x"]]]);
    let (out, p) = run(
        &serde_json::to_vec(&j).unwrap(),
        probe,
        vec![a.clone(), b.clone()],
    );
    assert_eq!(out.unwrap().len(), 2); // Both views still authorize all their slots.
    assert_eq!(
        *p.findings.lock().unwrap(),
        vec!["refused:frame-exit-order"; 3]
    );
    assert_eq!(p.inner.active_frames(), 0);
    assert_eq!(
        [&a, &b, &outside].map(|v| p.inner.observe(token(v)).unwrap()),
        before
    );
}
#[cfg(feature = "test-utils")]
#[test]
fn explicit_seed_and_tape_are_reproducible_and_tape_failure_keeps_state() {
    let mut outputs = Vec::new();
    for _ in 0..2 {
        let mut b = ark_backend(None);
        let r = b.issue_test_rng(domain(), 3, [42; 32]).unwrap();
        let (out, b) = run(&draw_program(), b, vec![r]);
        let out = out.unwrap();
        let first = scalar(&out[0]);
        let (out, _) = run(&draw_program(), b, vec![out[1].clone()]);
        outputs.push((first, scalar(&out.unwrap()[0])));
    }
    assert_eq!(outputs[0], outputs[1]);
    assert_ne!(outputs[0].0, outputs[0].1);
    let mut b = ark_backend(None);
    let r = b.issue_test_tape(domain(), 4, vec![]).unwrap();
    let (out, b) = run(&draw_program(), b, vec![r.clone()]);
    assert_eq!(code(&out.unwrap_err()), "exhausted:test-tape");
    let state = b.observe(token(&r)).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (1, 1, 3)
    );
}

#[test]
fn nested_failure_and_cancellation_release_all_frames_and_preserve_unpassed_slots() {
    let mut b = ark_backend(None);
    let a = b.issue_rng(domain(), 0).unwrap();
    let second = b.issue_rng(domain(), 4).unwrap();
    let before = b.observe(token(&second)).unwrap();
    let (out, b) = run(&nested_program(), b, vec![a.clone(), second.clone()]);
    assert_eq!(code(&out.unwrap_err()), "exhausted:resource-budget");
    assert_eq!(b.active_frames(), 0);
    assert_eq!(b.observe(token(&a)).unwrap().generation, 1);
    assert_eq!(b.observe(token(&second)).unwrap(), before);
    let mut b = ark_backend(None);
    let a = b.issue_rng(domain(), 3).unwrap();
    let second = b.issue_rng(domain(), 4).unwrap();
    let mut runner = load(&nested_program(), b, vec![a.clone(), second.clone()]);
    assert!(matches!(
        runner.poll(),
        zkc_runtime::interactive::Action::Local(_)
    )); // child entered, no draw yet
    runner.cancel();
    let b = runner.into_backend();
    assert_eq!(b.active_frames(), 0);
    assert_eq!(b.observe(token(&a)).unwrap().generation, 0);
    assert_eq!(b.observe(token(&second)).unwrap().generation, 0);
}

#[test]
fn repeated_loop_iterations_pass_only_current_successor_handle() {
    let bytes = participants(json!([
        [[
            "function",
            "draw",
            [["r", "rng"]],
            ["rng"],
            [
                op("d", "arkworks/random.draw", &["r"], &["v", "next"]),
                ["return", ["next"]]
            ]
        ]],
        [[
            "participant",
            "root",
            "instance",
            "P",
            [],
            [["a", "rng"]],
            ["rng"],
            [
                [
                    "loop",
                    "repeat",
                    "3",
                    [["carried", "a"]],
                    [],
                    [
                        ["local", "draw_site", "draw", ["carried"], ["next_carried"]],
                        ["yield", ["next_carried"]]
                    ],
                    ["final"]
                ],
                ["return", ["final"]]
            ]
        ]],
        [["entry", "main", [["P", "root"]]]]
    ]))
    .unwrap();
    let mut b = ark_backend(None);
    let a = b.issue_rng(domain(), 3).unwrap();
    let (out, b) = run(&bytes, b, vec![a.clone()]);
    out.unwrap();
    let state = b.observe(token(&a)).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (3, 3, 0)
    );
    assert_eq!(b.active_frames(), 0);
}

#[test]
fn retiring_a_failed_attempt_preserves_other_resources_and_never_reuses_identity() {
    let mut backend = ark_backend(None);
    let temporary = backend.issue_rng(domain(), 0).unwrap();
    let persistent = backend.issue_rng(domain(), 9).unwrap();
    let before = backend.observe(token(&persistent)).unwrap();
    let (out, mut backend) = run(&draw_program(), backend, vec![temporary.clone()]);
    assert_eq!(code(&out.unwrap_err()), "exhausted:resource-budget");
    let retired = backend.retire(token(&temporary)).unwrap();
    assert_eq!((retired.generation, retired.draw_count), (1, 1));
    assert_eq!(backend.observe(token(&persistent)).unwrap(), before);
    assert_eq!(
        backend.retire(token(&temporary)).unwrap_err().code,
        "refused:capability-unissued"
    );
    assert_eq!(
        backend.validate_value(&temporary).unwrap_err().code,
        "refused:capability-unissued"
    );
    let replacement = backend.issue_rng(domain(), 1).unwrap();
    assert!(token(&replacement).issued_id() > retired.issued_id);
    let mut foreign = ark_backend(None);
    assert_eq!(
        foreign.retire(token(&replacement)).unwrap_err().code,
        "refused:capability-authority"
    );
}

#[test]
fn finite_attempt_controller_passes_real_successor_rng_without_reinitialization() {
    use std::ops::ControlFlow::{Break, Continue};
    use zkc_runtime::{Outcome, iteration::Execution};
    let mut backend = ark_backend(None);
    let rng = backend
        .issue_test_tape(
            domain(),
            5,
            vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)],
        )
        .unwrap();
    let original = rng.clone();
    let unrelated = backend.issue_rng(domain(), 9).unwrap();
    let outside = backend.observe(token(&unrelated)).unwrap();
    let attempt = |(), (backend, rng)| {
        let (out, backend) = run(&draw_program(), backend, vec![rng]);
        let out = out.expect("fixture draw is admitted and has sufficient budget");
        let value = scalar(&out[0]);
        Execution {
            outcome: Outcome::Returned(if value == Scalar::from(3) {
                Break(value)
            } else {
                Continue(())
            }),
            state: (backend, out[1].clone()),
            events: vec![value],
        }
    };
    let prefix = Execution::pending((), (backend, rng)).advance(2, attempt);
    assert_eq!(prefix.outcome, Outcome::Returned(Continue(())));
    let complete = prefix.advance(20, attempt).close();
    assert_eq!(complete.outcome, Outcome::Returned(Scalar::from(3)));
    assert_eq!(
        complete.events,
        vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)]
    );
    let (backend, current) = complete.state;
    assert_eq!(backend.observe(token(&original)).unwrap().generation, 3);
    assert_eq!(backend.observe(token(&current)).unwrap().budget, 2);
    assert_eq!(backend.observe(token(&unrelated)).unwrap(), outside);
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn stopped_controller_retains_failed_resource_for_host_retirement() {
    use zkc_runtime::{Outcome, Stop, iteration::Execution};

    let mut backend = ark_backend(None);
    let rng = backend.issue_rng(domain(), 0).unwrap();
    let unrelated = backend.issue_rng(domain(), 9).unwrap();
    let outside = backend.observe(token(&unrelated)).unwrap();
    let prefix = Execution::pending((), (backend, rng)).advance(1, |(), (backend, rng)| {
        let (out, backend) = run(&draw_program(), backend, vec![rng.clone()]);
        let error = out.unwrap_err();
        assert_eq!(code(&error), "exhausted:resource-budget");
        Execution {
            outcome: Outcome::Stopped(Stop::Exhausted),
            state: (backend, rng),
            events: vec![code(&error).to_string()],
        }
    });
    let complete: Execution<_, _, ()> = prefix
        .advance(10, |(), _| {
            panic!("a fatal stop cannot start another attempt")
        })
        .close();
    assert_eq!(complete.outcome, Outcome::Stopped(Stop::Exhausted));
    assert_eq!(complete.events, ["exhausted:resource-budget"]);
    let (mut backend, old_handle) = complete.state;
    assert_eq!(backend.active_frames(), 0);
    let actual = backend.observe(token(&old_handle)).unwrap();
    assert_eq!(
        (actual.generation, actual.draw_count, actual.budget),
        (1, 1, 0)
    );
    assert_eq!(backend.retire(token(&old_handle)).unwrap(), actual);
    assert_eq!(backend.observe(token(&unrelated)).unwrap(), outside);
    assert_eq!(
        backend.validate_value(&old_handle).unwrap_err().code,
        "refused:capability-unissued"
    );
}
