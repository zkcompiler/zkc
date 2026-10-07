//! Execute fresh source compiler output with independent participant runners.
use serde_json::json;
use sha2::{Digest, Sha256};
use std::ops::{Deref, DerefMut};
use std::path::Path;
use zkc_backends::services::{ServiceReference, ServiceRegistry};
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, PublicInputs, Scalar, Sequence, Value,
};
use zkc_runtime::interactive::{
    Action, LogicalType, Packet, PathElement, ProgramState, Runner, StopKind,
    Value as RuntimeValue, admit_supplied,
};
use zkc_tools::protocol::run::{Bundle, BundleLimits, HostLimits, RunHost, SetupAuthority};

struct Participant {
    runner: Runner<NativeBackend>,
    loops: Vec<(String, u64, u64)>,
}
impl Deref for Participant {
    type Target = Runner<NativeBackend>;
    fn deref(&self) -> &Self::Target {
        &self.runner
    }
}
impl DerefMut for Participant {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.runner
    }
}
fn field(n: u64) -> Value {
    Value::Field(Scalar::from(n))
}
fn backend(bundle: &serde_json::Value, role: &str) -> NativeBackend {
    let entry = bundle["entry"].as_str().unwrap();
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, "language_test", entry, None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
fn runner(bundle: &serde_json::Value, role: &str, inputs: Vec<Value>) -> Participant {
    start(bundle, role, inputs, backend(bundle, role))
}
fn start(
    bundle: &serde_json::Value,
    role: &str,
    inputs: Vec<Value>,
    backend: NativeBackend,
) -> Participant {
    let entry = bundle["entry"].as_str().unwrap();
    let admitted =
        admit_supplied(bundle["candidate"].as_str().unwrap().as_bytes(), &backend).unwrap();
    Participant {
        runner: Runner::new(&admitted, entry, role, "language_test", backend, inputs)
            .map_err(|failure| failure.error)
            .unwrap(),
        loops: Vec::new(),
    }
}
fn next(runner: &mut Participant) -> Action<Value> {
    for _ in 0..100 {
        let mut origin = runner.root_origin().clone();
        origin.path.extend(
            runner
                .loops
                .iter()
                .map(|(site, _, iteration)| PathElement::Loop {
                    site: site.clone(),
                    iteration: *iteration,
                }),
        );
        match runner.inspect_program().unwrap() {
            ProgramState::Unpolled {
                kind: None,
                site: Some(site),
            } => {
                let site = site.to_owned();
                // Each fixture supplies the intended local count. Joint count
                // agreement is the RunHost driver's separate obligation.
                if let Some(count) = runner.loop_count(&origin, &site).unwrap() {
                    runner.enter_loop(&origin, &site, count).unwrap();
                    if count != 0 {
                        runner.loops.push((site, count, 0));
                    }
                }
                continue;
            }
            ProgramState::Yield => {
                runner.yield_loop(&origin).unwrap();
                let (_, count, iteration) = runner.loops.last_mut().unwrap();
                *iteration += 1;
                if *iteration == *count {
                    runner.loops.pop();
                }
                continue;
            }
            ProgramState::ReturnIf { site } => {
                let site = site.to_owned();
                runner.return_if(&origin, &site).unwrap();
                continue;
            }
            _ => {}
        }
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Query(query) => runner.execute_query(&query.cut).unwrap(),
            action => return action,
        }
    }
    panic!("participant exceeded bounded fixture steps")
}
fn send(runner: &mut Participant) -> Value {
    let action = next(runner);
    assert!(
        matches!(action, Action::Send(_)),
        "expected send, got {action:?}"
    );
    runner.take_send(&action.cut().unwrap()).unwrap().payload
}
fn receive(runner: &mut Participant, value: Value) {
    let Action::Receive(expected) = next(runner) else {
        panic!("expected receive")
    };
    let bytes = runner.backend().encode_native_value(&value).unwrap();
    let decoded = runner
        .backend()
        .decode_native_value(&expected.ty, &bytes)
        .unwrap();
    runner
        .deliver(Packet {
            envelope: expected.envelope,
            ty: decoded.physical_type(),
            payload: decoded,
        })
        .unwrap();
}
fn returned(runner: &mut Participant) -> Vec<Value> {
    let action = next(runner);
    let Action::Returned(values) = action else {
        panic!("expected return, got {action:?}")
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
fn service_backend(
    bundle: &serde_json::Value,
    registry: &ServiceRegistry,
    root: &ServiceReference,
) -> NativeBackend {
    service_backends(bundle, registry, std::slice::from_ref(root))
}
fn service_backends(
    bundle: &serde_json::Value,
    registry: &ServiceRegistry,
    roots: &[ServiceReference],
) -> NativeBackend {
    let admitted = Bundle::admit(
        bundle.to_string().as_bytes(),
        &backend(bundle, "V"),
        BundleLimits::default(),
    )
    .unwrap();
    let role = admitted
        .roles()
        .iter()
        .find(|role| role.entry.role == "V")
        .unwrap();
    assert_eq!(role.entry.services.len(), roots.len());
    let ports = role
        .entry
        .services
        .iter()
        .zip(roots)
        .map(|(port, root)| (port.name.clone(), root.clone()))
        .collect();
    backend(bundle, "V")
        .with_services(registry.clone(), ports)
        .unwrap()
}
fn repeated_queries(bundle: &serde_json::Value, conditional: bool) {
    let cases: &[(u64, bool)] = if conditional {
        &[(0, false), (1, true)]
    } else {
        &[(0, false), (1, true), (3, true), (3, false), (5, true)]
    };
    for &(n, go) in cases {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("V", 4, (1..=4).map(Scalar::from).collect())
            .unwrap();
        let values = if conditional {
            vec![Value::Bool(go)]
        } else {
            vec![Value::Index(n), field(3), Value::Bool(go)]
        };
        let mut verifier = start(
            bundle,
            "V",
            values,
            service_backend(bundle, &registry, &root),
        );
        let expected_draws;
        if conditional {
            let values = returned(&mut verifier);
            expect_field(&values[0], if go { 1 } else { 0 });
            expected_draws = u64::from(go);
        } else if n > 4 || (n > 0 && !go) {
            let Action::Stopped(stop) = next(&mut verifier) else {
                panic!("repeat bound or guard did not stop")
            };
            assert!(stop.cleanup_errors.is_empty());
            if n > 4 {
                assert!(
                    matches!(stop.kind, StopKind::Backend(ref e) if e.code == "loop-count-bound")
                );
            } else {
                assert!(matches!(stop.kind, StopKind::Explicit(ref reason) if reason == "reject"));
            }
            expected_draws = 0;
        } else {
            let mut prover = runner(bundle, "P", vec![Value::Index(n), field(2)]);
            for i in 0..n {
                let value = send(&mut verifier);
                expect_field(&value, i + 1);
                receive(&mut prover, value);
            }
            let sum = n * (n + 1) / 2;
            expect_field(&returned(&mut prover)[0], 2 + sum);
            expect_field(&returned(&mut verifier)[0], 3 + sum);
            expected_draws = n;
        }
        assert_eq!(verifier.backend().active_frames(), 0);
        let observed = registry.observe(&root).unwrap();
        assert!(!observed.leased && !observed.poisoned);
        let state = observed.state.unwrap();
        assert_eq!(state.draw_count, expected_draws);
        assert_eq!(state.budget, 4 - expected_draws);
    }
}
fn ordered_services(bundle: &serde_json::Value) {
    for go in [false, true] {
        let registry = ServiceRegistry::new(Policy::default());
        let first = registry
            .issue_test_tape(
                "V",
                3,
                vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)],
            )
            .unwrap();
        let second = registry
            .issue_test_tape("V", 1, vec![Scalar::from(7)])
            .unwrap();
        let roots = [first, second];
        let mut verifier = start(
            bundle,
            "V",
            vec![Value::Bool(go)],
            service_backends(bundle, &registry, &roots),
        );
        if go {
            let mut prover = runner(bundle, "P", vec![]);
            let value = send(&mut verifier);
            expect_field(&value, 9);
            receive(&mut prover, value);
            expect_field(&returned(&mut prover)[0], 9);
            expect_field(&returned(&mut verifier)[0], 13);
        } else {
            let Action::Stopped(stop) = next(&mut verifier) else {
                panic!("expected guard after one draw")
            };
            assert!(matches!(stop.kind,StopKind::Explicit(ref reason) if reason=="reject"));
            assert!(stop.cleanup_errors.is_empty());
        }
        for (i, root) in roots.iter().enumerate() {
            let observed = registry.observe(root).unwrap();
            assert!(!observed.leased && !observed.poisoned);
            assert_eq!(
                observed.state.unwrap().draw_count,
                if i == 0 {
                    if go { 3 } else { 1 }
                } else {
                    u64::from(go)
                }
            );
        }
    }
}
fn completion_queries(bundle: &serde_json::Value, nested: bool) {
    for go in [false, true] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("V", 4, (1..=4).map(Scalar::from).collect())
            .unwrap();
        let mut verifier = start(
            bundle,
            "V",
            vec![Value::Bool(go), field(7)],
            service_backend(bundle, &registry, &root),
        );
        let mut prover = runner(bundle, "P", vec![field(3)]);
        expect_field(&returned(&mut prover)[0], 6);
        expect_field(&returned(&mut verifier)[0], if go { 7 } else { 14 });
        assert_eq!(verifier.early_return().is_some(), go);
        if go {
            assert_eq!(
                verifier.early_return().unwrap().0.path.len(),
                if nested { 2 } else { 0 }
            );
        }
        let observed = registry.observe(&root).unwrap();
        assert!(!observed.leased && !observed.poisoned);
        let state = observed.state.unwrap();
        let expected = if go {
            0
        } else if nested {
            4
        } else {
            1
        };
        assert_eq!(state.draw_count, expected);
        assert_eq!(state.budget, 4 - expected);
    }
}
fn managed_queries(bundle: &serde_json::Value) {
    for go in [false, true] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("V", 2, vec![Scalar::from(3), Scalar::from(7)])
            .unwrap();
        let provider = service_backend(bundle, &registry, &root);
        let mut verifier = start(bundle, "V", vec![Value::Bool(go)], provider);
        if go {
            let mut prover = runner(bundle, "P", vec![]);
            let challenge = send(&mut verifier);
            expect_field(&challenge, 7);
            receive(&mut prover, challenge);
            expect_field(&returned(&mut prover)[0], 7);
            expect_field(&returned(&mut verifier)[0], 7);
        } else {
            let Action::Stopped(stop) = next(&mut verifier) else {
                panic!("guard did not stop")
            };
            assert!(stop.cleanup_errors.is_empty());
        }
        assert_eq!(verifier.backend().active_frames(), 0);
        let observation = registry.observe(&root).unwrap();
        assert!(!observation.leased && !observation.poisoned);
        let state = observation.state.unwrap();
        assert_eq!(state.draw_count, if go { 2 } else { 0 });
        assert_eq!(state.budget, if go { 0 } else { 2 });
    }
}
fn native_data(directory: &Path, optimized: u32) {
    let load = |name: &str| -> serde_json::Value {
        serde_json::from_slice(
            &std::fs::read(directory.join(format!("typed-{name}-{optimized}.bundle"))).unwrap(),
        )
        .unwrap()
    };
    let dynamic = load("dynamic");
    for count in [2, 6] {
        let mut prover = runner(&dynamic, "P", vec![field(3), Value::Index(count)]);
        let mut verifier = runner(&dynamic, "V", vec![]);
        receive(&mut verifier, send(&mut prover));
        receive(&mut verifier, send(&mut prover));
        assert!(returned(&mut prover).is_empty());
        let result = returned(&mut verifier);
        expect_field(&result[0], 3 * count / 2);
        expect_field(&result[1], 3 * count / 2);
    }
    for count in [0, 1, 3] {
        let mut prover = runner(&dynamic, "P", vec![field(3), Value::Index(count)]);
        let Action::Stopped(stop) = next(&mut prover) else {
            panic!("invalid split length did not stop");
        };
        assert!(matches!(stop.kind, StopKind::Backend(ref error)
            if error.code == "refused:split-length"));
        assert_eq!(prover.backend().active_frames(), 0);
    }
    let matrix = load("matrix");
    let mut prover = runner(
        &matrix,
        "P",
        vec![
            Value::matrix(
                2,
                3,
                &[(0, 1, Scalar::from(9)), (1, 2, Scalar::from(4))],
                &Policy::default(),
            )
            .unwrap(),
            Value::Vector(vec![Scalar::from(2), Scalar::from(3), Scalar::from(5)].into()),
        ],
    );
    let mut verifier = runner(&matrix, "V", vec![]);
    receive(&mut verifier, send(&mut prover));
    receive(&mut verifier, send(&mut prover));
    assert!(returned(&mut prover).is_empty());
    expect_field(&returned(&mut verifier)[0], 47);
    let trace = load("trace");
    for shapes in [vec![], vec![(0, 3), (2, 0), (4, 5)]] {
        let matrices = shapes
            .iter()
            .map(|&(r, c)| Value::matrix(r, c, &[], &Policy::default()).unwrap())
            .collect();
        let data = Value::Sequence(
            Sequence::new(
                LogicalType::parse("matrix:bls12-381.fr").unwrap(),
                matrices,
                &Policy::default(),
            )
            .unwrap(),
        );
        let mut prover = runner(&trace, "P", vec![data]);
        let mut verifier = runner(&trace, "V", vec![]);
        receive(&mut verifier, send(&mut prover));
        assert!(returned(&mut prover).is_empty());
        assert!(matches!(returned(&mut verifier)[0], Value::Index(n)
            if n == shapes.iter().map(|&(r,_)|r as u64).sum::<u64>()));
    }
    let rounds = load("vector_rounds");
    for count in 0..=2 {
        let mut prover = runner(
            &rounds,
            "P",
            vec![
                Value::Vector((1..=4).map(Scalar::from).collect::<Vec<_>>().into()),
                Value::Index(count),
            ],
        );
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("V", 2, vec![Scalar::from(2), Scalar::from(3)])
            .unwrap();
        let backend = service_backend(&rounds, &registry, &root);
        let mut verifier = start(&rounds, "V", vec![field(10), Value::Index(count)], backend);
        for _ in 0..count {
            receive(&mut verifier, send(&mut prover));
            receive(&mut verifier, send(&mut prover));
            receive(&mut prover, send(&mut verifier));
        }
        let expected = [10, 11, 8][count as usize];
        expect_field(&returned(&mut prover)[0], expected);
        expect_field(&returned(&mut verifier)[0], expected);
        assert_eq!(
            registry.observe(&root).unwrap().state.unwrap().draw_count,
            count
        );
    }
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
    for optimized in [0, 1] {
        native_data(Path::new(&directory), optimized);
        ordered_services(&load(&format!("service_order-{optimized}.bundle")));
        let values = returned(&mut runner(
            &load(&format!("dispatch-{optimized}.bundle")),
            "P",
            vec![field(2), field(7)],
        ));
        expect_field(&values[0], 2);
        expect_field(&values[1], 7);
        completion_queries(&load(&format!("completion-{optimized}.bundle")), false);
        completion_queries(
            &load(&format!("completion_nested-{optimized}.bundle")),
            true,
        );
        for n in [0, 1, 3] {
            for go in [false, true] {
                let mut participant = runner(
                    &load(&format!("completion_affine-{optimized}.bundle")),
                    "P",
                    vec![Value::Index(n), Value::Bool(go), field(7)],
                );
                let values = returned(&mut participant);
                assert_eq!(values.len(), 2);
                assert_eq!(participant.backend().live_resource_units(), 1);
                expect_field(&values[1], 7);
                assert_eq!(participant.early_return().is_some(), go && n > 0);
            }
            let values = returned(&mut runner(
                &load(&format!("repeat_affine-{optimized}.bundle")),
                "P",
                vec![Value::Index(n), field(7)],
            ));
            expect_field(&values[0], 7);
            for m in [0, 1, 2] {
                let values = returned(&mut runner(
                    &load(&format!("repeat_nested-{optimized}.bundle")),
                    "P",
                    vec![Value::Index(n), Value::Index(m), field(3)],
                ));
                expect_field(&values[0], 3 * (1 + n * m));
            }
        }
        managed_queries(&load(&format!("services-{optimized}.bundle")));
        repeated_queries(&load(&format!("repeat-{optimized}.bundle")), false);
        repeated_queries(
            &load(&format!("conditional_query-{optimized}.bundle")),
            true,
        );
        let bundle = load(&format!("application-{optimized}.bundle"));
        let mut prover = runner(&bundle, "P", vec![field(2), field(3)]);
        let mut verifier = runner(&bundle, "V", vec![field(5), field(7)]);
        let p = returned(&mut prover);
        let v = returned(&mut verifier);
        assert_eq!(p.len(), 1);
        assert_eq!(v.len(), 1);
        expect_field(&p[0], 6);
        expect_field(&v[0], 12);
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
    for optimized in [0, 1] {
        let bundle = |name: &str| load(&format!("typed-{name}-{optimized}.bundle"));
        for (name, inputs, expected) in [
            ("array", vec![field(3), field(7)], 3),
            ("component", vec![field(3)], 4),
            ("associated", vec![field(3)], 3),
            ("associated_domain", vec![field(3)], 6),
        ] {
            let result = returned(&mut runner(&bundle(name), "P", inputs));
            assert_eq!(result.len(), 1);
            expect_field(&result[0], expected);
        }
        for n in [0, 1, 5] {
            let result = returned(&mut runner(
                &bundle("loop"),
                "P",
                vec![field(3), Value::Index(n)],
            ));
            expect_field(&result[0], n * 3);
        }
        assert!(returned(&mut runner(&bundle("resource"), "P", vec![])).is_empty());
        for n in [0, 1, 5] {
            for go in [false, true] {
                let mut resource = runner(
                    &bundle("resource_control"),
                    "P",
                    vec![Value::Index(n), Value::Bool(go)],
                );
                match next(&mut resource) {
                    Action::Returned(values) => {
                        assert!(go);
                        assert!(values.is_empty());
                    }
                    Action::Stopped(stop) => {
                        assert!(!go);
                        assert!(stop.cleanup_errors.is_empty());
                    }
                    action => panic!("unexpected affine control outcome: {action:?}"),
                }
                assert_eq!(resource.backend().active_frames(), 0);
                assert_eq!(resource.usage().live_values, 0);
            }
        }
        for a in [false, true] {
            for b in [false, true] {
                let result = returned(&mut runner(
                    &bundle("bool"),
                    "P",
                    vec![Value::Bool(a), Value::Bool(b)],
                ));
                assert!(matches!(result[0], Value::Bool(actual) if actual == (a == b)));
            }
            let mut prover = runner(&bundle("branch"), "P", vec![field(3), Value::Bool(a)]);
            let mut verifier = runner(&bundle("branch"), "V", vec![]);
            let value = send(&mut prover);
            expect_field(&value, if a { 6 } else { 3 });
            receive(&mut verifier, value);
            expect_field(&returned(&mut verifier)[0], if a { 6 } else { 3 });
            assert!(returned(&mut prover).is_empty());
        }
        let mut prover = runner(
            &bundle("group"),
            "P",
            vec![Value::Curve(GroupPoint::generator()), field(3)],
        );
        let mut verifier = runner(&bundle("group"), "V", vec![]);
        receive(&mut verifier, send(&mut prover));
        assert!(matches!(&returned(&mut verifier)[0], Value::Curve(point)
            if *point == GroupPoint::generator().scale(Scalar::from(4u64))));
        assert!(returned(&mut prover).is_empty());
        for (a, b, expected) in [
            (true, false, 3),
            (false, true, 7),
            (false, false, 11),
            (true, true, 22),
        ] {
            for name in ["variant", "variant_custody"] {
                let mut local = runner(
                    &bundle(name),
                    "P",
                    vec![
                        field(3),
                        field(7),
                        field(11),
                        Value::Bool(a),
                        Value::Bool(b),
                    ],
                );
                expect_field(&returned(&mut local)[0], expected);
            }
            let mut prover = runner(
                &bundle("variant_wire"),
                "P",
                vec![field(3), field(7), Value::Bool(a), Value::Bool(b)],
            );
            let mut verifier = runner(&bundle("variant_wire"), "V", vec![field(11)]);
            receive(&mut verifier, send(&mut prover));
            expect_field(&returned(&mut verifier)[0], expected);
            assert!(returned(&mut prover).is_empty());
        }
        let index = returned(&mut runner(&bundle("index"), "P", vec![]));
        assert!(matches!(index.as_slice(), [Value::Index(3)]));
        let mut prover = runner(&bundle("record"), "P", vec![field(3), field(7)]);
        let mut verifier = runner(&bundle("record"), "V", vec![]);
        receive(&mut verifier, send(&mut prover));
        receive(&mut verifier, send(&mut prover));
        let result = returned(&mut verifier);
        expect_field(&result[0], 7);
        expect_field(&result[1], 3);
        assert!(returned(&mut prover).is_empty());
    }
    println!(
        "fresh source: receives, static dispatch, aggregates, resources, branches, loops and selected Entries passed"
    );
}
