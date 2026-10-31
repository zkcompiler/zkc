//! Reached index constants retain decoded facts across public backend calls.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use support::{backend, program};
use zkc_cpu::{CpuBackend, CpuCall, CpuOperation, Policy, Value};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Action, Backend, BackendError, CallContext, Frame, FrameExit, Invocation, LocalContext,
    OperationBinding, Origin, PathElement, Program, Stop, StopKind, Usage, Value as RuntimeValue,
    ValueBudget, WorkBudget,
};

fn binding(name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![],
        implementation: format!("native/{name}"),
        physical_arguments: vec![],
    }
}

struct Caller {
    inner: CpuBackend,
    call: Option<CpuCall>,
    prepared: bool,
    attributes: Option<Vec<String>>,
    arguments: Option<Vec<Value>>,
    operation: Option<OperationBinding>,
    output_limit: Option<usize>,
    attempts: usize,
}
impl Caller {
    fn new(prepared: bool, policy: Policy) -> Self {
        Self {
            inner: backend(policy),
            call: None,
            prepared,
            attributes: None,
            arguments: None,
            operation: None,
            output_limit: None,
            attempts: 0,
        }
    }
}
impl Backend for Caller {
    type Value = Value;
    type Operation = CpuOperation;
    type Call = ();
    type Checkpoint = ();
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<CpuOperation> {
        self.inner.prepare_binding(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(frame, args)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[Value],
    ) -> Result<(), BackendError> {
        self.inner.leave_frame(frame, exit, outputs)
    }
    fn apply(
        &mut self,
        operation: &CpuOperation,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.attempts += 1;
        let replacement = self.operation.as_ref().map(|binding| {
            self.inner
                .prepare_binding(binding)
                .expect("installed binding")
        });
        let operation = replacement.as_ref().unwrap_or(operation);
        let i = Invocation {
            context: CallContext {
                attributes: self.attributes.as_deref().unwrap_or(i.attributes),
                ..i.context
            },
            max_output_bytes: self.output_limit.unwrap_or(i.max_output_bytes),
            ..*i
        };
        let args = self.arguments.as_deref().unwrap_or(args);
        if self.prepared {
            self.inner
                .apply_prepared(operation, &mut self.call, &i, args)
        } else {
            self.inner.apply(operation, &i, args)
        }
    }
}

fn run<B: Backend<Value = Value>>(
    caller: B,
    bytes: &[u8],
    args: Vec<Value>,
    values: ValueBudget,
    work: WorkBudget,
) -> (Result<Vec<Value>, Stop>, Usage, B) {
    let admitted = Program::decode(bytes, zkc_cpu::cpu_contracts()).unwrap();
    admitted.check_installation(&caller).unwrap();
    let mut runner = Runner::new_with_budgets(
        &admitted, "main", "P", "session", caller, args, values, work,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    loop {
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
            Action::Returned(values) => {
                return (Ok(values), runner.usage(), runner.into_backend());
            }
            Action::Stopped(stop) => {
                return (Err(stop), runner.usage(), runner.into_backend());
            }
            other => panic!("unexpected {other:?}"),
        }
    }
}

fn one(caller: Caller, name: &str, args: Vec<Value>) -> (Result<Vec<Value>, String>, Caller) {
    let (result, caller) = support::one(
        caller,
        binding(name),
        if name == "index.constant" {
            &["12"]
        } else {
            &[]
        },
        args,
    );
    assert_eq!(caller.inner.active_frames(), 0);
    (result, caller)
}

fn warm(prepared: bool) -> Caller {
    let (result, caller) = one(
        Caller::new(prepared, Policy::default()),
        "index.constant",
        vec![],
    );
    assert!(matches!(result.unwrap().as_slice(), [Value::Index(12)]));
    assert_eq!(caller.call.is_some(), prepared);
    caller
}

#[test]
fn changed_attributes_and_rules_do_not_reuse_a_stale_constant() {
    for prepared in [false, true] {
        let mut caller = warm(prepared);
        for (literal, expected) in [("19", 19), ("0", 0), ("18446744073709551615", u64::MAX)] {
            caller.attributes = Some(vec![literal.into()]);
            let (result, next) = one(caller, "index.constant", vec![]);
            assert!(matches!(result.unwrap().as_slice(), [Value::Index(n)] if *n == expected));
            caller = next;
        }
        // The warmed constant's attribute is invalid for an ordinary index rule.
        caller.attributes = Some(vec!["12".into()]);
        let (result, mut caller) = one(caller, "index.add", vec![Value::Index(2), Value::Index(3)]);
        assert_eq!(result.unwrap_err(), "refused:kernel-attributes");
        caller.attributes = None;
        let (result, caller) = one(caller, "index.add", vec![Value::Index(2), Value::Index(3)]);
        assert!(matches!(result.unwrap().as_slice(), [Value::Index(5)]));
        let (result, _) = one(caller, "index.constant", vec![]);
        assert!(matches!(result.unwrap().as_slice(), [Value::Index(12)]));
    }
}

#[test]
fn invalid_decimals_and_arity_refuse_after_warming_and_allow_recovery() {
    for prepared in [false, true] {
        let mut caller = warm(prepared);
        for attributes in [
            vec![],
            vec![""],
            vec!["00"],
            vec!["012"],
            vec!["+12"],
            vec!["-1"],
            vec![" 12"],
            vec!["12\n"],
            vec!["1_2"],
            vec!["１２"],
            vec!["18446744073709551616"],
            vec!["12", "13"],
        ] {
            caller.attributes = Some(attributes.iter().map(|s| (*s).into()).collect());
            let (result, mut next) = one(caller, "index.constant", vec![]);
            assert_eq!(result.unwrap_err(), "refused:kernel-attributes");
            next.attributes = None;
            let (result, next) = one(next, "index.constant", vec![]);
            assert!(matches!(result.unwrap().as_slice(), [Value::Index(12)]));
            caller = next;
        }
    }
}

#[test]
fn binding_and_operand_refusals_still_precede_attributes_and_output_limits() {
    for prepared in [false, true] {
        let mut caller = warm(prepared);
        caller.attributes = Some(vec!["invalid".into()]);
        caller.output_limit = Some(0);
        caller.operation = Some(binding("index.add"));
        let (result, mut caller) = one(caller, "index.constant", vec![]);
        assert_eq!(result.unwrap_err(), "refused:kernel-binding");
        caller.operation = None;
        caller.arguments = Some(vec![Value::Index(3)]);
        let (result, mut caller) = one(caller, "index.constant", vec![]);
        assert_eq!(result.unwrap_err(), "refused:kernel-operands");
        caller.arguments = None;
        let (result, mut caller) = one(caller, "index.constant", vec![]);
        assert_eq!(result.unwrap_err(), "refused:kernel-attributes");
        // Equal signatures do not authorize substituting a different operation.
        assert_eq!(
            binding("index.mod").signature().unwrap(),
            binding("index.div").signature().unwrap()
        );
        caller.operation = Some(binding("index.div"));
        let (result, _) = one(caller, "index.mod", vec![Value::Index(7), Value::Index(0)]);
        assert_eq!(result.unwrap_err(), "refused:kernel-binding");
    }
}

#[test]
fn output_allowance_and_current_policy_are_checked_after_warming() {
    let bytes = Value::Index(12).retained_bytes();
    for prepared in [false, true] {
        let mut caller = warm(prepared);
        for limit in [0, bytes - 1, bytes] {
            caller.output_limit = Some(limit);
            let (result, next) = one(caller, "index.constant", vec![]);
            if limit < bytes {
                assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
            } else {
                assert!(matches!(result.unwrap().as_slice(), [Value::Index(12)]));
            }
            caller = next;
        }
        // Reuse the static facts with a different backend and stricter policy.
        caller.output_limit = None;
        caller.inner = backend(Policy {
            max_value_bytes: bytes - 1,
            ..Policy::default()
        });
        let (result, _) = one(caller, "index.constant", vec![]);
        assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
    }
}

#[test]
fn dormant_constants_do_not_validate_backend_attributes_before_reach() {
    let constant = binding("index.constant");
    let bool_type = Value::Bool(false).physical_type();
    let bytes = program(
        &[constant],
        &[bool_type],
        vec![json!([
            "if",
            "branch",
            "a0",
            [],
            [["op", "literal", "b0", ["12"], [], ["n"]], ["yield", []]],
            [["yield", []]],
            []
        ])],
        &[],
        &[],
    );
    for prepared in [false, true] {
        let mut caller = Caller::new(prepared, Policy::default());
        // Admission checks u64 syntax independently. Inject invalid attributes
        // only at the backend boundary to exercise its reached-call obligation.
        caller.attributes = Some(vec!["012".into()]);
        let (result, _, caller) = run(
            caller,
            &bytes,
            vec![Value::Bool(false)],
            Default::default(),
            Default::default(),
        );
        assert!(result.is_ok());
        assert_eq!(caller.attempts, 0);
        assert!(caller.call.is_none());
        let (result, _, caller) = run(
            caller,
            &bytes,
            vec![Value::Bool(true)],
            Default::default(),
            Default::default(),
        );
        assert_eq!(
            support::code(&result.unwrap_err()),
            "refused:kernel-attributes"
        );
        assert_eq!(caller.attempts, 1);
        assert!(caller.call.is_none());
        assert_eq!(caller.inner.active_frames(), 0);
    }
}

// Fixed observations anchor charging and failure prefixes independently of the
// prepared handler. Deriving both limits and expectations from that handler
// would hide a shared accounting regression.
fn repeated_observation(fail: bool, budget_case: usize) -> (Usage, Option<Stop>) {
    let literal_limit = budget_case == 1 || (!fail && budget_case == 3);
    let (instructions, total_value_bytes, logical_bytes) = if literal_limit {
        (9, 11, 3)
    } else {
        match (fail, budget_case) {
            (false, 0) => (12, 12, 4),
            (false, 2) | (true, 3) => (11, 12, 4),
            (true, 0) => (11, 12, 6),
            (true, 2) => (10, 12, 4),
            _ => panic!("unknown observation"),
        }
    };
    let usage = Usage {
        instructions,
        iterations: 4,
        total_value_bytes: total_value_bytes * zkc_cpu::VALUE_SLOT_BYTES,
        logical_bytes: logical_bytes * zkc_cpu::VALUE_SLOT_BYTES as u64,
        ..Usage::default()
    };
    if !fail && budget_case == 0 {
        return (usage, None);
    }
    let mut stop = Stop {
        origin: Origin {
            session: "session".into(),
            entry: "main".into(),
            instance: "instance".into(),
            path: vec![],
        },
        role: "P".into(),
        site: None,
        kind: StopKind::Limit,
        cleanup_errors: vec![],
        local: None,
    };
    if literal_limit {
        stop.origin.path.push(PathElement::For {
            site: "repeat".into(),
            index: 3,
        });
        stop.site = Some("literal".into());
        stop.kind = StopKind::Backend(BackendError {
            code: "exhausted:output-bytes".into(),
        });
        stop.local = Some(Box::new(LocalContext {
            site: "local".into(),
            function: "testfn".into(),
            instruction: Some("literal".into()),
        }));
    } else if fail {
        stop.site = Some("local".into());
        stop.local = Some(Box::new(LocalContext {
            site: "local".into(),
            function: "testfn".into(),
            instruction: None,
        }));
        if budget_case == 0 {
            stop.kind = StopKind::Backend(BackendError {
                code: "refused:index-zero-divisor".into(),
            });
        }
    }
    (usage, Some(stop))
}

#[test]
fn repeated_sites_preserve_work_output_charging_and_failure_prefixes() {
    let index = Value::Index(0).physical_type();
    for fail in [false, true] {
        let mut body = vec![json!([
            "for",
            "repeat",
            "i",
            "a0",
            "a1",
            [],
            [],
            [["op", "literal", "b0", ["12"], [], ["n"]], ["yield", []]],
            []
        ])];
        if fail {
            body.push(json!(["op", "divide", "b1", [], ["a0", "a0"], ["unused"]]));
        }
        let bytes = program(
            &[binding("index.constant"), binding("index.div")],
            &[index.clone(), index.clone()],
            body,
            &[],
            &[],
        );
        let inputs = || vec![Value::Index(0), Value::Index(4)];
        let (full, _) = repeated_observation(fail, 0);
        for (budget_case, (values, work)) in [
            (ValueBudget::default(), WorkBudget::default()),
            (
                ValueBudget {
                    total_bytes: full.total_value_bytes - 1,
                    ..Default::default()
                },
                WorkBudget::default(),
            ),
            (
                ValueBudget::default(),
                WorkBudget {
                    instructions: full.instructions - 1,
                    ..Default::default()
                },
            ),
            (
                ValueBudget::default(),
                WorkBudget {
                    logical_bytes: full.logical_bytes - 1,
                    ..Default::default()
                },
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let (expected, expected_usage, direct) = run(
                Caller::new(false, Policy::default()),
                &bytes,
                inputs(),
                values,
                work,
            );
            let (actual, actual_usage, warmed) = run(
                Caller::new(true, Policy::default()),
                &bytes,
                inputs(),
                values,
                work,
            );
            // A real CpuBackend also exercises the VM-owned per-site slots.
            let (native, native_usage, native_backend) =
                run(backend(Policy::default()), &bytes, inputs(), values, work);
            let (usage, stop) = repeated_observation(fail, budget_case);
            let outcome = stop.as_ref().map_or(Ok(0), Err);
            for (result, observed_usage) in [
                (&expected, expected_usage),
                (&actual, actual_usage),
                (&native, native_usage),
            ] {
                assert_eq!(result.as_ref().map(Vec::len), outcome);
                assert_eq!(observed_usage, usage);
            }
            assert_eq!(warmed.attempts, direct.attempts);
            assert_eq!(warmed.inner.active_frames(), 0);
            assert_eq!(direct.inner.active_frames(), 0);
            assert_eq!(native_backend.active_frames(), 0);
        }
    }
}
