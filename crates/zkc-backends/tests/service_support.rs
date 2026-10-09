//! Independent service installation, preflight, and live post-consume authority.
#![cfg(feature = "test-utils")]
use serde_json::json;
use zkc_backends::services::ServiceRegistry;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::interactive::{
    Action, Backend, BackendError, ErrorCode, Frame, FrameExit, Invocation, PhysicalType, Runner,
    ServiceContract, ServiceInvocation, ServiceSupport, ValueBudget, admit_supplied,
};

fn native() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("Alice", "session", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn program(contract: &str, output: &str) -> Vec<u8> {
    serde_json::to_vec(&json!([
        "zkc.program",
        [],
        [],
        [[
            "participant",
            "alice",
            "root",
            "Alice",
            [],
            [output],
            [
                ["query", "draw", "rng", "draw", [], ["x"]],
                ["return", ["x"]]
            ],
            [["rng", contract, "0"]]
        ]],
        [["entry", "main", [["Alice", "alice"]]]]
    ]))
    .unwrap()
}
const SERVICES: &[(ServiceContract, &str, &str)] = &[
    (
        ServiceContract::RandomBls12381Field,
        "random.bls12-381.fr/1",
        "field:bls12-381.fr@arkworks.fr/1",
    ),
    (
        ServiceContract::RandomBn254Field,
        "random.bn254.fr/1",
        "field:bn254.fr@arkworks.bn254-fr/1",
    ),
    (
        ServiceContract::RandomRistrettoField,
        "random.ristretto255.scalar/1",
        "field:ristretto255.scalar@dalek.scalar/1",
    ),
    (
        ServiceContract::RandomExtensionField,
        "random.koala-bear.ext8-binomial3/1",
        "field:koala-bear.ext8-binomial3@plonky3.koala-bear.ext8-binomial3/1",
    ),
];
struct Adapter {
    inner: NativeBackend,
    mutate: fn(&mut ServiceSupport),
    invalid_reply: bool,
    calls: usize,
}
impl Backend for Adapter {
    type Value = Value;
    fn service_support(&self, contract: ServiceContract, method: &str) -> Option<ServiceSupport> {
        let mut support = self.inner.service_support(contract, method)?;
        (self.mutate)(&mut support);
        Some(support)
    }
    fn query(
        &mut self,
        call: &ServiceInvocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.calls += 1;
        let mut values = self.inner.query(call, args)?;
        if self.invalid_reply {
            values[0] = Value::Bool(true);
        }
        Ok(values)
    }
    fn reject_service_reply(&mut self, call: &ServiceInvocation<'_>) {
        self.inner.reject_service_reply(call);
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, values: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(frame, values)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[Value],
    ) -> Result<(), BackendError> {
        self.inner.leave_frame(frame, exit, values)
    }
    fn apply(
        &mut self,
        call: &Invocation<'_>,
        values: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.inner.apply(call, values)
    }
}

#[test]
fn independently_authored_shapes_and_bounded_support_are_required_at_installation() {
    let mutations: &[fn(&mut ServiceSupport)] = &[
        |s| s.signature.inputs.push(s.signature.outputs[0].clone()),
        |s| s.signature.outputs.clear(),
        |s| s.signature.outputs.push(s.signature.outputs[0].clone()),
        |s| s.signature.outputs[0] = PhysicalType::parse("bool@native.bool/1").unwrap(),
        |s| {
            s.signature.outputs[0] =
                PhysicalType::parse("field:koala-bear@plonky3.koala-bear/1").unwrap()
        },
        |s| s.max_retained_bytes = usize::MAX,
    ];
    for &(contract, name, output) in SERVICES {
        let native = native();
        let support = native.service_support(contract, "draw").unwrap();
        assert_eq!(support.signature.inputs, vec![]);
        assert_eq!(
            support.signature.outputs,
            [PhysicalType::parse(output).unwrap()]
        );
        assert_eq!(support.max_retained_bytes, 512);
        assert!(native.service_support(contract, "reset").is_none());
        let bytes = program(name, output);
        admit_supplied(&bytes, &native).unwrap();
        for &mutate in mutations {
            let adapter = Adapter {
                inner: self::native(),
                mutate,
                invalid_reply: false,
                calls: 0,
            };
            let error = admit_supplied(&bytes, &adapter).unwrap_err();
            assert_eq!(error.code, ErrorCode::Backend);
            assert_eq!(error.detail, "installed service signature mismatch");
            assert_eq!(adapter.calls, 0);
            assert_eq!(adapter.inner.active_frames(), 0);
        }
    }
}

#[test]
fn service_capacity_precedes_consumption_and_invalid_reply_poisons_live_root() {
    for (limit, invalid_reply, expected_draws) in
        [(511, false, 0), (1024, false, 1), (1024, true, 1)]
    {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("Alice", 3, vec![Scalar::from(7u64)])
            .unwrap();
        let inner = native()
            .with_services(registry.clone(), [("rng".into(), root.clone())].into())
            .unwrap();
        let adapter = Adapter {
            inner,
            mutate: |_| {},
            invalid_reply,
            calls: 0,
        };
        let bytes = program(SERVICES[0].1, SERVICES[0].2);
        let admitted = admit_supplied(&bytes, &adapter).unwrap();
        let mut runner = Runner::new_with_value_budget(
            &admitted,
            "main",
            "Alice",
            "session",
            adapter,
            vec![],
            ValueBudget {
                live_bytes: limit,
                total_bytes: limit,
            },
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let Action::Query(query) = runner.poll() else {
            panic!("query cut");
        };
        runner.execute_query(&query.cut).unwrap();
        if limit == 1024 && !invalid_reply {
            let Action::Returned(values) = runner.poll() else {
                panic!("successful reply");
            };
            assert!(matches!(values.as_slice(), [Value::Field(x)] if *x == Scalar::from(7u64)));
        } else {
            assert!(matches!(runner.poll(), Action::Stopped(_)));
        }
        let adapter = runner.into_backend();
        assert_eq!(adapter.calls, expected_draws);
        assert_eq!(adapter.inner.active_frames(), 0);
        let after = registry.observe(&root).unwrap();
        assert_eq!(after.state.unwrap().draw_count, expected_draws as u64);
        assert_eq!(after.poisoned, invalid_reply);
        assert!(!after.leased);
    }
}

#[test]
fn excessive_work_budget_refuses_before_leasing_and_retains_backend_custody() {
    use zkc_runtime::interactive::{Limits, RuntimeError, Usage, WorkBudget};
    for work in [
        WorkBudget {
            instructions: Limits::INSTRUCTIONS + 1,
            ..WorkBudget::default()
        },
        WorkBudget {
            iterations: Limits::ITERATIONS + 1,
            ..WorkBudget::default()
        },
    ] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("Alice", 1, vec![Scalar::from(7u64)])
            .unwrap();
        let backend = native()
            .with_services(registry.clone(), [("rng".into(), root.clone())].into())
            .unwrap();
        let admitted = admit_supplied(&program(SERVICES[0].1, SERVICES[0].2), &backend).unwrap();
        let failure = match Runner::new_with_budgets(
            &admitted,
            "main",
            "Alice",
            "session",
            backend,
            vec![],
            ValueBudget {
                live_bytes: usize::MAX,
                total_bytes: usize::MAX,
            },
            work,
        ) {
            Ok(_) => panic!("excessive work must refuse"),
            Err(failure) => failure,
        };
        assert!(matches!(failure.error, RuntimeError::Limit));
        assert_eq!(failure.usage, Usage::default());
        assert_eq!(failure.backend.active_frames(), 0);
        assert!(!registry.observe(&root).unwrap().leased);
        let mut runner = Runner::new_with_budgets(
            &admitted,
            "main",
            "Alice",
            "session",
            failure.backend,
            vec![],
            ValueBudget::default(),
            WorkBudget {
                instructions: 0,
                iterations: 0,
            },
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        assert!(matches!(runner.poll(), Action::Stopped(_)));
        assert_eq!(
            registry.observe(&root).unwrap().state.unwrap().draw_count,
            0
        );
    }
}
