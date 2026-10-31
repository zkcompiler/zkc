//! Interactive index blocks through admitted queries and registry-owned roots.
use serde_json::json;
use zkc_cpu::services::{ServiceObservation, ServiceReference, ServiceRegistry};
use zkc_cpu::{CpuBackend, CpuExecution, CpuInstallation, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Action, Backend, BackendError, ErrorCode, Frame, FrameExit, Invocation, PhysicalType, Program,
    ServiceContract, ServiceInvocation, ServiceSupport, StopKind, Usage, Value as _, ValueBudget,
};

const CONTRACTS: [ServiceContract; 4] = [
    ServiceContract::RandomKoalaBearExt4,
    ServiceContract::RandomExtensionField,
    ServiceContract::RandomBabyBearExt4,
    ServiceContract::RandomGoldilocksExt2,
];
const MAX_COUNT: usize = 1 << 20;
const MAX_REPLY: usize = 8 * MAX_COUNT + 256;

fn backend(policy: Policy, installation: CpuInstallation) -> CpuBackend {
    CpuBackend::new_with_installation(
        policy,
        EntryPolicy::new(Domain::new("Alice", "session", "main", None), None),
        Default::default(),
        CpuExecution::serial().unwrap(),
        installation,
    )
    .unwrap()
}

// Source operands are static constants. Supplied carriers can read ingress data,
// which also exercises the installed provider's independent request validation.
fn program(contract: ServiceContract, aliases: bool) -> Vec<u8> {
    let mut code = vec![json!([
        "query",
        "block",
        "rng",
        "indices",
        ["n", "q"],
        ["x"]
    ])];
    let mut ports = vec![json!(["rng", contract.name(), "2"])];
    if aliases {
        ports.push(json!(["alias", contract.name(), "3"]));
        code.push(json!([
            "query",
            "again",
            "alias",
            "indices",
            ["n", "q"],
            ["y"]
        ]));
    }
    code.push(json!(["return", [if aliases { "y" } else { "x" }]]));
    serde_json::to_vec(&json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "alice",
            "root",
            "Alice",
            [["n", "index@native.index/0"], ["q", "index@native.index/0"]],
            ["indices@native.indices/0"],
            code,
            ports
        ]],
        [["entry", "main", [["Alice", "alice"]]]]
    ]))
    .unwrap()
}

fn admitted(bytes: &[u8], backend: &impl Backend) -> Program {
    let program = Program::decode(bytes, zkc_cpu::cpu_contracts()).unwrap();
    program.check_installation(backend).unwrap();
    program
}

#[derive(Debug)]
enum Outcome {
    Reply(Vec<Value>),
    Stopped(StopKind),
}

struct Probe {
    inner: CpuBackend,
    contract: ServiceContract,
    output_limit: Option<usize>,
    invalid_reply: bool,
    calls: usize,
}
impl Backend for Probe {
    type Call = ();
    type Checkpoint = ();
    type Value = Value;
    type Operation = zkc_cpu::CpuOperation;
    fn service_support(&self, contract: ServiceContract, method: &str) -> Option<ServiceSupport> {
        self.inner.service_support(contract, method)
    }
    fn query(
        &mut self,
        call: &ServiceInvocation<'_>,
        arguments: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.calls += 1;
        let call = ServiceInvocation {
            max_output_bytes: self.output_limit.unwrap_or(call.max_output_bytes),
            ..*call
        };
        let mut reply = self.inner.query(&call, arguments)?;
        if self.invalid_reply {
            reply[0] = Value::Bool(true);
        }
        Ok(reply)
    }
    fn reject_service_reply(&mut self, call: &ServiceInvocation<'_>) {
        self.inner.reject_service_reply(call);
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, arguments: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(frame, arguments)
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
        operation: &Self::Operation,
        call: &Invocation<'_>,
        arguments: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.inner.apply(operation, call, arguments)
    }
}

fn probe(registry: &ServiceRegistry, root: &ServiceReference, policy: Policy) -> Probe {
    Probe {
        inner: backend(policy, CpuInstallation::default())
            .with_services(registry.clone(), [("rng".into(), root.clone())].into())
            .unwrap(),
        contract: ServiceContract::parse(root.contract()).unwrap(),
        output_limit: None,
        invalid_reply: false,
        calls: 0,
    }
}

fn run(probe: Probe, bound: u64, count: u64, budget: ValueBudget) -> (Outcome, Usage, Probe) {
    let program = admitted(&program(probe.contract, false), &probe);
    let mut runner = Runner::new_with_value_budget(
        &program,
        "main",
        "Alice",
        "session",
        probe,
        vec![Value::Index(bound), Value::Index(count)],
        budget,
    )
    .unwrap_or_else(|failure| panic!("{}", failure.error));
    let Action::Query(query) = runner.poll() else {
        panic!("query cut");
    };
    runner.execute_query(&query.cut).unwrap();
    let outcome = match runner.poll() {
        Action::Returned(values) => Outcome::Reply(values),
        Action::Stopped(stop) => Outcome::Stopped(stop.kind),
        action => panic!("unexpected action: {action:?}"),
    };
    let usage = runner.usage();
    let probe = runner.into_backend();
    assert_eq!(probe.inner.active_frames(), 0);
    (outcome, usage, probe)
}

fn assert_state(observed: ServiceObservation, generation: u64, draws: u64, budget: u64) {
    let state = observed.state.expect("known completion");
    assert_eq!(state.generation, generation);
    assert_eq!(state.draw_count, draws);
    assert_eq!(state.budget, budget);
}

#[test]
fn all_four_contracts_install_exact_block_signatures_and_refuse_other_contracts() {
    let backend = backend(Policy::default(), CpuInstallation::default());
    let index = PhysicalType::parse("index@native.index/0").unwrap();
    let indices = PhysicalType::parse("indices@native.indices/0").unwrap();
    for contract in CONTRACTS {
        let support = backend.service_support(contract, "indices").unwrap();
        assert_eq!(support.signature.inputs, [index.clone(), index.clone()]);
        assert_eq!(support.signature.outputs, std::slice::from_ref(&indices));
        assert_eq!(support.max_retained_bytes, MAX_REPLY);
        admitted(&program(contract, false), &backend);
    }
    for contract in [
        ServiceContract::RandomBls12381Field,
        ServiceContract::RandomBn254Field,
        ServiceContract::RandomRistrettoField,
    ] {
        assert!(backend.service_support(contract, "draw").is_some());
        assert!(backend.service_support(contract, "indices").is_none());
        assert_eq!(
            Program::decode(&program(contract, false), zkc_cpu::cpu_contracts())
                .unwrap_err()
                .code,
            ErrorCode::Type
        );
    }
    for (inputs, output, code) in [
        (
            json!(["n"]),
            "indices@native.indices/0",
            ErrorCode::Signature,
        ),
        (
            json!(["n", "q", "n"]),
            "indices@native.indices/0",
            ErrorCode::Signature,
        ),
        (
            json!(["n", "q"]),
            "index@native.index/0",
            ErrorCode::Signature,
        ),
    ] {
        let mut malformed: serde_json::Value =
            serde_json::from_slice(&program(CONTRACTS[0], false)).unwrap();
        malformed[3][0][6][0][4] = inputs;
        malformed[3][0][5][0] = json!(output);
        assert_eq!(
            Program::decode(
                &serde_json::to_vec(&malformed).unwrap(),
                zkc_cpu::cpu_contracts()
            )
            .unwrap_err()
            .code,
            code
        );
    }
}

#[test]
fn interactive_blocks_use_one_transition_for_all_contracts_and_extreme_bounds() {
    for contract in CONTRACTS {
        for bound in [1, 1 << 63] {
            let registry = ServiceRegistry::new(Policy::default());
            let root = registry.issue_random_for("Alice", contract, 1).unwrap();
            let backend = backend(Policy::default(), CpuInstallation::default())
                .with_services(registry.clone(), [("rng".into(), root.clone())].into())
                .unwrap();
            let program = admitted(&program(contract, false), &backend);
            let mut runner = Runner::new(
                &program,
                "main",
                "Alice",
                "session",
                backend,
                vec![Value::Index(bound), Value::Index(7)],
            )
            .unwrap_or_else(|failure| panic!("{}", failure.error));
            let before = registry.observe(&root).unwrap();
            let Action::Query(query) = runner.poll() else {
                panic!("query cut")
            };
            assert_eq!(
                registry.observe(&root).unwrap(),
                before,
                "poll has no effect"
            );
            runner.execute_query(&query.cut).unwrap();
            let after = registry.observe(&root).unwrap();
            assert!(after.leased);
            assert!(!after.poisoned);
            assert_state(after, 1, 1, 0);
            let Action::Returned(values) = runner.poll() else {
                panic!("block reply")
            };
            let [Value::Indices(indices)] = values.as_slice() else {
                panic!("indices reply")
            };
            assert_eq!(indices.len(), 7);
            assert!(indices.iter().all(|position| *position < bound));
            if bound == 1 {
                assert_eq!(indices.as_ref(), [0; 7], "duplicates are retained");
            }
            assert_eq!(values[0].retained_bytes(), 8 * 7 + 256);
            assert_eq!(runner.into_backend().active_frames(), 0);
            assert!(!registry.observe(&root).unwrap().leased);
            registry.retire(&root).unwrap();
        }
    }
}

#[test]
fn maximum_count_is_installed_when_policy_allows_it() {
    let policy = Policy {
        max_table_elements: MAX_COUNT,
        ..Policy::default()
    };
    for contract in CONTRACTS {
        let registry = ServiceRegistry::new(policy);
        let root = registry.issue_random_for("Alice", contract, 1).unwrap();
        let backend = backend(policy, CpuInstallation::default())
            .with_services(registry.clone(), [("rng".into(), root.clone())].into())
            .unwrap();
        let program = admitted(&program(contract, false), &backend);
        let mut runner = Runner::new(
            &program,
            "main",
            "Alice",
            "session",
            backend,
            vec![Value::Index(1), Value::Index(MAX_COUNT as u64)],
        )
        .unwrap_or_else(|failure| panic!("{}", failure.error));
        let Action::Query(query) = runner.poll() else {
            panic!("query cut")
        };
        runner.execute_query(&query.cut).unwrap();
        let Action::Returned(values) = runner.poll() else {
            panic!("maximum block reply")
        };
        let [Value::Indices(indices)] = values.as_slice() else {
            panic!("indices reply")
        };
        assert_eq!(indices.len(), MAX_COUNT);
        assert!(indices.iter().all(|position| *position == 0));
        assert_eq!(values[0].retained_bytes(), MAX_REPLY);
        assert_state(registry.observe(&root).unwrap(), 1, 1, 0);
    }
}

#[test]
fn invalid_bound_count_and_policy_refusals_leave_the_root_healthy_for_retry() {
    for (bound, count, policy, expected) in [
        (0, 3, Policy::default(), "refused:query-bound"),
        (3, 3, Policy::default(), "refused:query-bound"),
        (u64::MAX, 3, Policy::default(), "refused:query-bound"),
        (8, 0, Policy::default(), "refused:query-count"),
        (
            8,
            MAX_COUNT as u64 + 1,
            Policy::default(),
            "refused:query-count",
        ),
        (8, u64::MAX, Policy::default(), "refused:query-count"),
        (8, 65_537, Policy::default(), "exhausted:element-limit"),
        (
            8,
            4,
            Policy {
                max_table_elements: 3,
                ..Policy::default()
            },
            "exhausted:element-limit",
        ),
        (
            8,
            40,
            Policy {
                max_value_bytes: 575,
                ..Policy::default()
            },
            "exhausted:output-bytes",
        ),
    ] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry.issue_random_for("Alice", CONTRACTS[0], 1).unwrap();
        let before = registry.observe(&root).unwrap();
        let (outcome, _, probe) = run(
            probe(&registry, &root, policy),
            bound,
            count,
            ValueBudget::default(),
        );
        let Outcome::Stopped(StopKind::Backend(error)) = outcome else {
            panic!("{outcome:?}")
        };
        assert_eq!(error.code, expected);
        assert_eq!(probe.calls, 1);
        assert_eq!(registry.observe(&root).unwrap(), before);
        let (outcome, _, _) = run(
            self::probe(&registry, &root, Policy::default()),
            1,
            3,
            ValueBudget::default(),
        );
        assert!(matches!(outcome, Outcome::Reply(_)));
        assert_state(registry.observe(&root).unwrap(), 1, 1, 0);
    }
}

#[test]
fn exact_output_affordability_is_checked_before_consumption() {
    for (count, limit, accepted) in [
        (1, 263, false),
        (1, 264, true),
        (3, 279, false),
        (3, 280, true),
        (40, 575, false),
        (40, 576, true),
    ] {
        let policy = Policy {
            max_value_bytes: 576,
            ..Policy::default()
        };
        let registry = ServiceRegistry::new(policy);
        let root = registry.issue_random_for("Alice", CONTRACTS[0], 1).unwrap();
        let before = registry.observe(&root).unwrap();
        let mut probe = probe(&registry, &root, policy);
        probe.output_limit = Some(limit);
        let (outcome, _, _) = run(probe, 1, count, ValueBudget::default());
        if !accepted {
            assert!(
                matches!(outcome, Outcome::Stopped(StopKind::Backend(error)) if error.code == "exhausted:output-bytes")
            );
            assert_eq!(registry.observe(&root).unwrap(), before);
        } else {
            let Outcome::Reply(values) = outcome else {
                panic!("{outcome:?}")
            };
            assert_eq!(values[0].retained_bytes(), limit);
            assert_state(registry.observe(&root).unwrap(), 1, 1, 0);
        }
    }
}

#[test]
fn runner_reserves_the_conservative_bound_and_settles_the_actual_reply() {
    // Two ingress indices each retain 512 bytes before the query reservation.
    let frontier = MAX_REPLY + 1024;
    for (live_bytes, total_bytes, accepted) in [
        (frontier - 1, frontier, false),
        (frontier, frontier - 1, false),
        (frontier, frontier, true),
    ] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry.issue_random_for("Alice", CONTRACTS[0], 1).unwrap();
        let before = registry.observe(&root).unwrap();
        let (outcome, usage, probe) = run(
            probe(&registry, &root, Policy::default()),
            1,
            3,
            ValueBudget {
                live_bytes,
                total_bytes,
            },
        );
        assert_eq!(probe.calls, usize::from(accepted));
        if accepted {
            assert!(matches!(outcome, Outcome::Reply(_)));
            assert_eq!(usage.total_value_bytes, 1024 + 8 * 3 + 256);
            assert_state(registry.observe(&root).unwrap(), 1, 1, 0);
        } else {
            assert!(matches!(outcome, Outcome::Stopped(StopKind::Limit)));
            assert_eq!(registry.observe(&root).unwrap(), before);
        }
    }
}

#[test]
fn aliased_blocks_share_one_lease_and_keep_existing_budget_failure_semantics() {
    for budget in [1, 2] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_random_for("Alice", CONTRACTS[0], budget)
            .unwrap();
        let backend = backend(Policy::default(), CpuInstallation::default())
            .with_services(
                registry.clone(),
                [("rng".into(), root.clone()), ("alias".into(), root.clone())].into(),
            )
            .unwrap();
        let program = admitted(&program(CONTRACTS[0], true), &backend);
        let mut runner = Runner::new(
            &program,
            "main",
            "Alice",
            "session",
            backend,
            vec![Value::Index(1), Value::Index(7)],
        )
        .unwrap_or_else(|failure| panic!("{}", failure.error));
        for generation in 1..=2 {
            let Action::Query(query) = runner.poll() else {
                panic!("query cut")
            };
            runner.execute_query(&query.cut).unwrap();
            assert_state(
                registry.observe(&root).unwrap(),
                generation,
                generation,
                budget.saturating_sub(generation),
            );
        }
        if budget == 1 {
            assert!(
                matches!(runner.poll(), Action::Stopped(stop) if matches!(&stop.kind, StopKind::Backend(error) if error.code == "exhausted:resource-budget"))
            );
        } else {
            assert!(matches!(runner.poll(), Action::Returned(_)));
        }
        assert_eq!(registry.observe(&root).unwrap().poisoned, budget == 1);
        assert_eq!(runner.into_backend().active_frames(), 0);
        assert!(!registry.observe(&root).unwrap().leased);
    }
}

#[test]
fn invalid_post_consume_reply_poisons_without_rolling_back_the_block() {
    let registry = ServiceRegistry::new(Policy::default());
    let root = registry.issue_random_for("Alice", CONTRACTS[0], 2).unwrap();
    let mut probe = probe(&registry, &root, Policy::default());
    probe.invalid_reply = true;
    let (outcome, _, probe) = run(probe, 8, 7, ValueBudget::default());
    assert!(matches!(outcome, Outcome::Stopped(_)));
    assert_eq!(probe.calls, 1);
    let after = registry.observe(&root).unwrap();
    assert!(after.poisoned);
    assert!(!after.leased);
    assert_state(after, 1, 1, 1);
}

#[test]
fn live_leases_owner_and_registry_authority_remain_required() {
    let registry = ServiceRegistry::new(Policy::default());
    let root = registry.issue_random_for("Alice", CONTRACTS[0], 1).unwrap();
    let foreign = ServiceRegistry::new(Policy::default());
    let error = match backend(Policy::default(), CpuInstallation::default())
        .with_services(foreign, [("rng".into(), root.clone())].into())
    {
        Ok(_) => panic!("foreign registry authenticated a root"),
        Err(error) => error,
    };
    assert_eq!(error.code, "refused:service-authority");
    let program = admitted(
        &program(CONTRACTS[0], false),
        &probe(&registry, &root, Policy::default()),
    );
    let enter = |backend| {
        Runner::new(
            &program,
            "main",
            "Alice",
            "session",
            backend,
            vec![Value::Index(1), Value::Index(7)],
        )
        .map_err(Box::new)
    };
    let mut first = enter(probe(&registry, &root, Policy::default()))
        .unwrap_or_else(|failure| panic!("{}", failure.error));
    let failure = match enter(probe(&registry, &root, Policy::default())) {
        Ok(_) => panic!("second endpoint acquired the same root"),
        Err(failure) => *failure,
    };
    assert!(
        matches!(failure.error, zkc_runtime::vm::RuntimeError::Backend(error) if error.code == "refused:service-leased")
    );
    assert_eq!(failure.backend.inner.active_frames(), 0);
    assert!(registry.observe(&root).unwrap().leased);
    let Action::Query(query) = first.poll() else {
        panic!("query cut")
    };
    let mut altered = query.cut.clone();
    altered.site = "another-site".into();
    assert!(first.execute_query(&altered).is_err());
    assert_state(registry.observe(&root).unwrap(), 0, 0, 1);
    drop(first);
    assert!(!registry.observe(&root).unwrap().leased);
    let (outcome, _, _) = run(failure.backend, 1, 7, ValueBudget::default());
    assert!(matches!(outcome, Outcome::Reply(_)));
    assert_state(registry.observe(&root).unwrap(), 1, 1, 0);

    let other_owner = registry.issue_random_for("Bob", CONTRACTS[0], 1).unwrap();
    let before = registry.observe(&other_owner).unwrap();
    let failure = match enter(probe(&registry, &other_owner, Policy::default())) {
        Ok(_) => panic!("wrong owner acquired a root"),
        Err(failure) => *failure,
    };
    assert!(
        matches!(failure.error, zkc_runtime::vm::RuntimeError::Backend(error) if error.code == "refused:service-owner")
    );
    assert_eq!(registry.observe(&other_owner).unwrap(), before);
}

#[test]
fn invalid_requests_precede_even_an_exhausted_root_transition() {
    for contract in CONTRACTS {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry.issue_random_for("Alice", contract, 0).unwrap();
        let before = registry.observe(&root).unwrap();
        for (bound, count, expected) in
            [(3, 7, "refused:query-bound"), (8, 0, "refused:query-count")]
        {
            let (outcome, _, _) = run(
                probe(&registry, &root, Policy::default()),
                bound,
                count,
                ValueBudget::default(),
            );
            assert!(
                matches!(outcome, Outcome::Stopped(StopKind::Backend(error)) if error.code == expected)
            );
            assert_eq!(registry.observe(&root).unwrap(), before);
        }
        let (outcome, _, _) = run(
            probe(&registry, &root, Policy::default()),
            8,
            7,
            ValueBudget::default(),
        );
        assert!(
            matches!(outcome, Outcome::Stopped(StopKind::Backend(error)) if error.code == "exhausted:resource-budget")
        );
        let after = registry.observe(&root).unwrap();
        assert!(after.poisoned);
        assert_state(after, 1, 1, 0);
    }
}

#[test]
fn indices_support_requires_the_root_field_provider() {
    let installation = CpuInstallation::builder().finish().unwrap();
    let empty = backend(Policy::default(), installation.clone());
    let registry = ServiceRegistry::with_installation(Policy::default(), installation);
    for contract in CONTRACTS {
        assert!(empty.service_support(contract, "indices").is_none());
        assert_eq!(
            registry
                .issue_random_for("Alice", contract, 1)
                .unwrap_err()
                .code,
            "refused:installation-service"
        );
        let program = Program::decode(&program(contract, false), zkc_cpu::cpu_contracts()).unwrap();
        assert_eq!(
            program.check_installation(&empty).unwrap_err().code,
            ErrorCode::Backend
        );
    }
    let installation = CpuInstallation::builder()
        .include(zkc_cpu::providers::Plonky3)
        .finish()
        .unwrap();
    let selected = backend(Policy::default(), installation);
    for contract in CONTRACTS {
        admitted(&program(contract, false), &selected);
    }
}
