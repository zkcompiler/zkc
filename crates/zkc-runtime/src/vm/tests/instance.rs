//! Direct VM frame/accounting controls and evaluator loading-boundary checks.
use super::*;
use crate::vm::instance::Instance;
use std::{cell::RefCell, rc::Rc};

fn program() -> Program {
    Program::decode(&bytes(&one(
        json!([add_fn()]),
        json!([]),
        json!([]),
        json!([["return", []]]),
    )))
    .unwrap()
}

fn instance(program: &Program, backend: Mock) -> Instance<Mock> {
    Instance::new(
        program,
        "main",
        backend,
        "P",
        "session",
        ValueBudget::default(),
        WorkBudget::default(),
    )
    .unwrap()
}

fn root(instance: &mut Instance<Mock>) -> Frame {
    let participant = instance.admitted().participant("main", "P").unwrap();
    instance.entry_frame(Origin {
        session: "session".into(),
        entry: "main".into(),
        instance: participant.instance.clone(),
        path: vec![],
    })
}

fn child(instance: &mut Instance<Mock>, parent: &Frame) -> Frame {
    instance.local_frame(
        parent.origin().clone(),
        std::sync::Arc::new(FrameKind::Local {
            site: "call".into(),
            function: "add".into(),
        }),
        FrameInputs::default(),
    )
}

#[test]
fn decoding_is_independent_of_installation_and_instances() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Program>();
    let program = program();
    assert_eq!(program.entry_names().collect::<Vec<_>>(), ["main"]);
    let mut unavailable = Mock::new();
    unavailable.wrong_signature = true;
    assert_eq!(
        program.check_installation(&unavailable).unwrap_err().code,
        ErrorCode::Backend
    );
    assert!(unavailable.trace.is_empty());

    let mut first = instance(&program, Mock::new());
    let mut second = instance(&program.clone(), Mock::new());
    let a = root(&mut first);
    let b = root(&mut second);
    assert_eq!(a.id(), b.id()); // identifiers are instance-local
    first.enter_frame(&a, &[]).unwrap();
    second.enter_frame(&b, &[]).unwrap();
    first.leave_frame(&a, FrameExit::Returned, &[]).unwrap();
    assert!(first.take_backend().frames.is_empty());
    assert_eq!(second.backend().frames.len(), 1);
    second.leave_frame(&b, FrameExit::Cancelled, &[]).unwrap();
    assert!(second.take_backend().frames.is_empty());
}

#[test]
fn instance_enforces_parent_and_exit_order_before_backend_hooks() {
    let program = program();
    let mut instance = instance(&program, Mock::new());
    let stale = root(&mut instance);
    let a = root(&mut instance);
    instance.enter_frame(&a, &[]).unwrap();
    let trace = instance.backend().trace.clone();
    assert!(
        matches!(instance.enter_frame(&stale, &[]), Err(RuntimeError::Backend(e)) if e.code == "vm-frame-parent")
    );
    assert_eq!(instance.backend().trace, trace);
    let b = child(&mut instance, &a);
    assert_eq!(b.parent(), Some(a.id()));
    instance.enter_frame(&b, &[]).unwrap();
    let trace = instance.backend().trace.clone();
    assert_eq!(
        instance
            .leave_frame(&a, FrameExit::Returned, &[])
            .unwrap_err()
            .code,
        "vm-frame-order"
    );
    assert_eq!(instance.backend().trace, trace);
    instance.leave_frame(&b, FrameExit::Returned, &[]).unwrap();
    instance.leave_frame(&a, FrameExit::Returned, &[]).unwrap();
    assert!(instance.take_backend().frames.is_empty());
}

#[test]
fn frame_proposals_are_instance_local_and_authorize_one_entry_attempt() {
    let program = program();
    let mut first = instance(&program, Mock::new());
    let mut second = instance(&program, Mock::new());
    let foreign = root(&mut second);
    let stale = root(&mut first);
    assert!(foreign.same_boundary(&stale));
    let current = root(&mut first);
    for frame in [&foreign, &stale] {
        assert!(matches!(first.enter_frame(frame, &[]),
            Err(RuntimeError::Backend(e)) if e.code == "vm-frame-entry"));
    }
    assert!(first.backend().trace.is_empty());
    first.enter_frame(&current, &[]).unwrap();
    first
        .leave_frame(&current, FrameExit::Returned, &[])
        .unwrap();
    let trace = first.backend().trace.clone();
    assert!(matches!(first.enter_frame(&current, &[]),
        Err(RuntimeError::Backend(e)) if e.code == "vm-frame-entry"));
    assert_eq!(first.backend().trace, trace);
    // Refusal from another instance did not consume the legitimate proposal.
    second.enter_frame(&foreign, &[]).unwrap();
    second
        .leave_frame(&foreign, FrameExit::Returned, &[])
        .unwrap();
}

#[test]
fn equal_frame_metadata_cannot_close_another_instances_view() {
    let program = program();
    let mut first = instance(&program, Mock::new());
    let mut second = instance(&program, Mock::new());
    let a = root(&mut first);
    let b = root(&mut second);
    assert!(a.same_boundary(&b));
    first.enter_frame(&a, &[]).unwrap();
    let trace = first.backend().trace.clone();
    assert_eq!(
        first
            .leave_frame(&b, FrameExit::Returned, &[])
            .unwrap_err()
            .code,
        "vm-frame-order"
    );
    assert_eq!(first.backend().trace, trace);
    first.leave_frame(&a, FrameExit::Returned, &[]).unwrap();
}

#[test]
fn refused_entry_does_not_push_and_failed_leave_still_removes_view() {
    let program = program();
    let mut backend = Mock::new();
    backend.fail_enter = Some(FrameKind::Local {
        site: "call".into(),
        function: "add".into(),
    });
    backend.fail_leave = true;
    let mut instance = instance(&program, backend);
    let a = root(&mut instance);
    instance.enter_frame(&a, &[]).unwrap();
    let b = child(&mut instance, &a);
    assert!(
        matches!(instance.enter_frame(&b, &[]), Err(RuntimeError::Backend(e)) if e.code == "enter-refused")
    );
    assert!(
        matches!(instance.enter_frame(&b, &[]), Err(RuntimeError::Backend(e)) if e.code == "vm-frame-entry")
    );
    assert_eq!(instance.backend().frames.len(), 1);
    assert_eq!(
        instance
            .leave_frame(&a, FrameExit::Cancelled, &[])
            .unwrap_err()
            .code,
        "leave-failed"
    );
    // A newly minted root proves the failed leave removed the VM view too.
    let c = root(&mut instance);
    assert_eq!(c.parent(), None);
    instance.enter_frame(&c, &[]).unwrap();
    assert!(instance.leave_frame(&c, FrameExit::Cancelled, &[]).is_err());
    assert!(instance.take_backend().frames.is_empty());
}

#[test]
fn dropping_instance_unwinds_all_views_even_when_cleanup_reports_errors() {
    let closed = Rc::new(RefCell::new(Vec::new()));
    let mut backend = Mock::new();
    backend.close_events = Some(closed.clone());
    backend.fail_leave = true;
    let program = program();
    let mut instance = instance(&program, backend);
    let a = root(&mut instance);
    instance.enter_frame(&a, &[]).unwrap();
    let b = child(&mut instance, &a);
    instance.enter_frame(&b, &[]).unwrap();
    drop(instance);
    assert_eq!(
        *closed.borrow(),
        [
            (b.id(), FrameExit::Cancelled),
            (a.id(), FrameExit::Cancelled)
        ]
    );
}

#[test]
fn load_refusal_precedence_preserves_custody_and_zero_work() {
    let program = program();
    for (work, session, unavailable, entry, role, expected) in [
        (
            Limits::INSTRUCTIONS + 1,
            "",
            true,
            "absent",
            "other",
            "limit",
        ),
        (0, "", true, "absent", "other", "session"),
        (0, "session", true, "absent", "other", "installation"),
        (0, "session", false, "absent", "other", "entry"),
        (0, "session", false, "main", "other", "role"),
    ] {
        let mut backend = Mock::new();
        backend.wrong_signature = unavailable;
        let error = Runner::new_with_budgets(
            &program,
            entry,
            role,
            session,
            backend,
            vec![],
            ValueBudget::default(),
            WorkBudget {
                instructions: work,
                ..WorkBudget::default()
            },
        )
        .err()
        .expect("load must refuse");
        let observed = match error.error {
            RuntimeError::Limit => "limit",
            RuntimeError::Session => "session",
            RuntimeError::Admission(e) if e.code == ErrorCode::Backend => "installation",
            RuntimeError::Entry => "entry",
            RuntimeError::Role => "role",
            other => panic!("unexpected error: {other:?}"),
        };
        assert_eq!(observed, expected);
        assert_eq!(error.usage, Usage::default());
        assert!(error.backend.frames.is_empty());
        assert!(error.backend.trace.is_empty());
    }
}

#[test]
fn value_scopes_keep_failed_retention_and_physical_release_accounting_separate() {
    use crate::vm::retention::Retention;
    let program = program();
    let mut instance = instance(&program, Mock::new());
    let input = V::Sized(32);
    let output = V::Sized(64);
    let mut scope = instance
        .open_scope(std::slice::from_ref(&input), Retention::Input)
        .unwrap();
    instance
        .retain_in(&mut scope, std::slice::from_ref(&output), Retention::Result)
        .unwrap();
    assert_eq!(instance.usage().live_values, 2);
    assert_eq!(instance.usage().live_value_bytes, 96);
    let before = instance.usage();
    assert!(matches!(
        instance.retain_in(&mut scope, &[V::Sized(usize::MAX)], Retention::Result),
        Err(RuntimeError::Limit)
    ));
    assert_eq!(instance.usage(), before);
    // Physical release frees the binding's storage but its conservative charge
    // stays until its whole value environment closes.
    instance.release_storage(&mut scope, &input);
    assert_eq!(instance.usage(), before);
    instance.close_scope(scope, std::iter::once(&output));
    assert_eq!(instance.usage().live_values, 0);
    assert_eq!(instance.usage().live_value_bytes, 0);
    assert_eq!(instance.usage().total_value_bytes, 96);
    assert_eq!(instance.usage().logical_bytes, 64);
}

#[test]
fn unwinding_closes_nested_views_before_releasing_each_environment() {
    let program = program();
    let mut instance = instance(&program, Mock::new());
    let a = root(&mut instance);
    instance.enter_frame(&a, &[]).unwrap();
    let b = child(&mut instance, &a);
    instance.enter_frame(&b, &[]).unwrap();
    let mut released = Vec::new();
    let errors = instance.unwind(FrameExit::Stopped, |instance, frame| {
        released.push(frame.id());
        assert_ne!(
            instance.backend().frames.last().map(|(id, _)| *id),
            Some(frame.id())
        );
    });
    assert!(errors.is_empty());
    assert_eq!(released, [b.id(), a.id()]);
    assert!(instance.take_backend().frames.is_empty());
}

#[test]
fn backend_recovery_cancels_views_without_interpreter_cleanup() {
    let closed = Rc::new(RefCell::new(Vec::new()));
    let mut backend = Mock::new();
    backend.close_events = Some(closed.clone());
    let program = program();
    let mut instance = instance(&program, backend);
    let a = root(&mut instance);
    instance.enter_frame(&a, &[]).unwrap();
    let b = child(&mut instance, &a);
    instance.enter_frame(&b, &[]).unwrap();
    assert!(instance.take_backend().frames.is_empty());
    drop(instance);
    assert_eq!(
        *closed.borrow(),
        [
            (b.id(), FrameExit::Cancelled),
            (a.id(), FrameExit::Cancelled)
        ]
    );
}

#[test]
fn refused_entry_returns_custody_and_preserves_charged_input_bytes() {
    let program = Program::decode(&bytes(&one(
        json!([]),
        json!([["value", "field"]]),
        json!([]),
        json!([["return", []]]),
    )))
    .unwrap();
    let mut backend = Mock::new();
    backend.fail_enter = Some(FrameKind::Entry);
    let error = Runner::new(&program, "main", "P", "session", backend, vec![V::Field(3)])
        .err()
        .unwrap();
    assert!(matches!(error.error, RuntimeError::Backend(ref e) if e.code == "enter-refused"));
    assert_eq!(error.usage.live_values, 0);
    assert_eq!(error.usage.live_value_bytes, 0);
    assert_eq!(error.usage.total_value_bytes, 16);
    assert_eq!(error.usage.instructions, 0);
    assert_eq!(error.usage.logical_bytes, 0);
    assert!(error.backend.frames.is_empty());
    assert!(error.backend.refused_frame.is_some());
    assert!(error.backend.trace.is_empty());
}

#[test]
fn vm_loading_owns_input_refusals_without_an_evaluator() {
    let program = Program::decode(&bytes(&one(
        json!([]),
        json!([["value", "field"]]),
        json!([]),
        json!([["return", []]]),
    )))
    .unwrap();
    for (inputs, budget, expected) in [
        (vec![], ValueBudget::default(), RuntimeError::Inputs),
        (
            vec![V::Bool(true)],
            ValueBudget::default(),
            RuntimeError::Payload,
        ),
        (
            vec![V::Field(1)],
            ValueBudget {
                live_bytes: 0,
                total_bytes: 0,
            },
            RuntimeError::Limit,
        ),
    ] {
        let error = Instance::load(
            &program,
            "main",
            "P",
            "session",
            Mock::new(),
            inputs,
            budget,
            WorkBudget::default(),
        )
        .err()
        .unwrap();
        assert_eq!(error.error, expected);
        assert_eq!(error.usage, Usage::default());
        assert!(error.backend.trace.is_empty());
        assert!(error.backend.frames.is_empty());
    }
    let mut loaded = Instance::load(
        &program,
        "main",
        "P",
        "session",
        Mock::new(),
        vec![V::Field(7)],
        ValueBudget::default(),
        WorkBudget::default(),
    )
    .ok()
    .unwrap();
    assert_eq!(loaded.frame.origin().entry, "main");
    assert_eq!(loaded.frame.role(), "P");
    assert_eq!(loaded.instance.usage().instructions, 0);
    assert_eq!(loaded.instance.usage().live_values, 1);
    loaded
        .instance
        .leave_frame(&loaded.frame, FrameExit::Cancelled, &[])
        .unwrap();
    loaded
        .instance
        .close_scope(loaded.scope, loaded.inputs.iter());
    assert_eq!(loaded.instance.usage().live_values, 0);
    assert_eq!(loaded.instance.usage().live_value_bytes, 0);
}

#[test]
fn service_queries_cannot_supply_authority_absent_from_the_active_frame() {
    use crate::vm::retention::Retention;
    let mut source = one(json!([]), json!([]), json!([]), json!([["return", []]]));
    source[3][0][7] = json!([["coins", "random.bls12-381.fr/0", "0"]]);
    let program = Program::decode(&bytes(&source)).unwrap();
    let mut instance = instance(&program, Mock::new());
    let frame = root(&mut instance);
    instance.enter_frame(&frame, &[]).unwrap();
    let mut scope = instance.open_scope(&[], Retention::Transfer).unwrap();
    let mut query = QueryAction {
        cut: Cut {
            origin: frame.origin().clone(),
            role: "P".into(),
            site: "draw".into(),
            kind: CutKind::Query,
        },
        port: ServicePort {
            name: "invented".into(),
            contract: ServiceContract::RandomBls12381Field,
            input_index: 0,
        },
        method: "draw".into(),
        arguments: vec![],
        results: vec![],
    };
    let trace = instance.backend().trace.clone();
    let usage = instance.usage();
    assert!(matches!(instance.query(&mut scope, &query),
        Err(RuntimeError::Backend(e)) if e.code == "vm-service-port"));
    query.port.name = "coins".into();
    query.port.contract = ServiceContract::RandomBn254Field;
    assert!(matches!(instance.query(&mut scope, &query),
        Err(RuntimeError::Backend(e)) if e.code == "vm-service-port"));
    query.port.contract = ServiceContract::RandomBls12381Field;
    query.port.input_index = 1;
    assert!(matches!(instance.query(&mut scope, &query),
        Err(RuntimeError::Backend(e)) if e.code == "vm-service-port"));
    assert_eq!(instance.backend().trace, trace);
    assert_eq!(instance.usage(), usage);
    instance.close_scope(scope, [].iter());
    instance
        .leave_frame(&frame, FrameExit::Cancelled, &[])
        .unwrap();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "unreleased return transfer")]
fn dropping_a_nonempty_return_transfer_is_a_debug_contract_error() {
    use crate::vm::retention::Retention;
    let program = program();
    let mut instance = instance(&program, Mock::new());
    let values = vec![V::Field(1)];
    let scope = instance.open_scope(&values, Retention::Input).unwrap();
    let returned = instance.hold_return(values.clone());
    instance.close_scope(scope, values.iter());
    drop(returned);
}
