//! Compare admitted baseline and CFG-reconstructed programs on the existing VM.
//! This bounded test adapter records frame effects; it is not another evaluator.
use serde_json::{Value as Json, json};
use std::{cell::RefCell, path::Path};
use zkc_native::{Domain, EntryPolicy, NativeBackend, NativeOperation, Policy, Scalar, Value};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Action, Backend, BackendError, Frame, FrameExit, Invocation, OperationBinding, Program,
    RuntimeError, Stop, Usage, ValueBudget, WorkBudget,
};

#[derive(Clone, Copy, Default)]
struct Fault {
    enter: Option<u64>,
    leave: Option<u64>,
}
struct Observed {
    native: NativeBackend,
    installed: RefCell<Vec<String>>,
    events: Vec<Json>,
    fault: Fault,
}
impl Backend for Observed {
    type Value = Value;
    type Operation = NativeOperation;
    type Call = ();
    type Checkpoint = ();
    fn supports_boolean_literals(&self) -> bool {
        self.native.supports_boolean_literals()
    }
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<NativeOperation> {
        self.installed.borrow_mut().push(binding.contract.clone());
        self.native.prepare_binding(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.native.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, values: &[Value]) -> Result<(), BackendError> {
        let result = if self.fault.enter == Some(frame.id().get()) {
            Err(BackendError::new("test:enter"))
        } else {
            self.native.enter_frame(frame, values)
        };
        self.events.push(json!([
            "enter",
            frame.id().get(),
            frame.origin().json(),
            values.len(),
            result.as_ref().err().map(|e| &e.code),
            self.native.active_frames()
        ]));
        result
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[Value],
    ) -> Result<(), BackendError> {
        let result = self.native.leave_frame(frame, exit, values).and_then(|()| {
            if self.fault.leave == Some(frame.id().get()) {
                Err(BackendError::new("test:leave"))
            } else {
                Ok(())
            }
        });
        self.events.push(json!([
            "leave",
            frame.id().get(),
            frame.origin().json(),
            format!("{exit:?}"),
            values.len(),
            result.as_ref().err().map(|e| &e.code),
            self.native.active_frames()
        ]));
        result
    }
    fn apply(
        &mut self,
        operation: &NativeOperation,
        invocation: &Invocation<'_>,
        values: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.events.push(json!([
            "apply",
            invocation.site,
            invocation.frame.origin().json(),
            invocation.domain_bytes()
        ]));
        self.native.apply(operation, invocation, values)
    }
}
#[derive(Debug, PartialEq, Eq)]
enum Failure {
    Loading(RuntimeError),
    Stopped(Stop),
}
#[derive(Debug, PartialEq, Eq)]
struct Observation {
    result: Result<Vec<String>, Failure>,
    usage: Usage,
    events: Vec<Json>,
    installed: Vec<String>,
}
fn execute(
    bytes: &[u8],
    inputs: Vec<Value>,
    fault: Fault,
    work: WorkBudget,
    value_budget: ValueBudget,
) -> Observation {
    let backend = Observed {
        native: NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "execution_test", "main", None), None),
            Default::default(),
        )
        .unwrap(),
        installed: Default::default(),
        events: vec![],
        fault,
    };
    let program = Program::decode(bytes, zkc_native::native_contracts()).unwrap();
    program.check_installation(&backend).unwrap();
    let loaded = Runner::new_with_budgets(
        &program,
        "main",
        "P",
        "execution_test",
        backend,
        inputs,
        value_budget,
        work,
    );
    let mut runner = match loaded {
        Ok(runner) => runner,
        Err(error) => {
            assert_eq!(error.backend.native.active_frames(), 0);
            assert_eq!(error.usage.live_values, 0);
            return Observation {
                result: Err(Failure::Loading(error.error)),
                usage: error.usage,
                events: error.backend.events,
                installed: error.backend.installed.into_inner(),
            };
        }
    };
    let result = loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Returned(values) => {
                break Ok(values.iter().map(|v| format!("{v:?}")).collect());
            }
            Action::Stopped(stop) => break Err(Failure::Stopped(stop)),
            other => panic!("unexpected action {other:?}"),
        }
    };
    let usage = runner.usage();
    assert_eq!(runner.backend().native.active_frames(), 0);
    assert_eq!(runner.backend().native.live_resource_units(), 0);
    if result.is_err() {
        assert_eq!(usage.live_values, 0);
        assert_eq!(usage.live_value_bytes, 0);
    }
    let backend = runner.into_backend();
    Observation {
        result,
        usage,
        events: backend.events,
        installed: backend.installed.into_inner(),
    }
}
fn inputs(lower: u64, upper: u64, again: bool) -> Vec<Value> {
    vec![
        Value::Index(lower),
        Value::Index(upper),
        Value::Bool(again),
        Value::Field(Scalar::from(3u64)),
        Value::Field(Scalar::from(5u64)),
    ]
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("execution fixture directory");
    let directory = Path::new(&directory);
    let mut checks = 0;
    for name in [
        "conditional-return",
        "unconditional-return",
        "conditional-stop",
        "unconditional-stop",
        "name-collisions",
        "stopped",
        "terminal-arms",
        "empty",
        "empty-only",
    ] {
        let baseline = std::fs::read(directory.join(format!("{name}-baseline.json"))).unwrap();
        let generated = std::fs::read(directory.join(format!("{name}-generated.json"))).unwrap();
        let compare = |args: Vec<Value>, fault, work, budget| {
            let before = execute(&baseline, args.clone(), fault, work, budget);
            let after = execute(&generated, args, fault, work, budget);
            assert_eq!(before, after, "observable native drift in {name}");
            before
        };
        let empty = name.starts_with("empty");
        for (lower, upper, again) in [
            (0, 0, true),
            (0, 1, true),
            (0, 3, true),
            (0, 3, false),
            (7, 2, false),
        ] {
            let args = if empty {
                vec![]
            } else {
                inputs(lower, upper, again)
            };
            let normal = compare(
                args.clone(),
                Fault::default(),
                WorkBudget::default(),
                ValueBudget::default(),
            );
            checks += 1;
            if name.ends_with("return") || name == "name-collisions" {
                assert!(normal.result.is_ok());
                let iterations = upper.saturating_sub(lower);
                let expected = if again {
                    3 + 5 * iterations
                } else if (name.starts_with("conditional") || name == "name-collisions")
                    && iterations > 0
                {
                    15
                } else {
                    3 * 5u64.pow(iterations as u32)
                };
                assert_eq!(
                    normal.result.as_ref().unwrap(),
                    &vec![format!("{:?}", Value::Field(Scalar::from(expected)))]
                );
            }
            // Every charged prefix must preserve stopping point, cleanup,
            // primary cause, output absence and accounting under this adapter.
            for instructions in 0..=normal.usage.instructions {
                compare(
                    args.clone(),
                    Fault::default(),
                    WorkBudget {
                        instructions,
                        ..WorkBudget::default()
                    },
                    ValueBudget::default(),
                );
                checks += 1;
            }
            for iterations in 0..=normal.usage.iterations {
                compare(
                    args.clone(),
                    Fault::default(),
                    WorkBudget {
                        iterations,
                        ..WorkBudget::default()
                    },
                    ValueBudget::default(),
                );
                checks += 1;
            }
            let frames: Vec<_> = normal
                .events
                .iter()
                .filter(|event| event[0] == "enter")
                .map(|event| event[1].as_u64().unwrap())
                .collect();
            for id in frames {
                for fault in [
                    Fault {
                        enter: Some(id),
                        leave: None,
                    },
                    Fault {
                        enter: None,
                        leave: Some(id),
                    },
                ] {
                    let observed = compare(
                        args.clone(),
                        fault,
                        WorkBudget::default(),
                        ValueBudget::default(),
                    );
                    assert!(observed.result.is_err(), "injected frame failure escaped");
                    checks += 1;
                }
            }
            for total_bytes in [
                normal.usage.total_value_bytes.saturating_sub(1),
                normal.usage.total_value_bytes,
            ] {
                compare(
                    args.clone(),
                    Fault::default(),
                    WorkBudget::default(),
                    ValueBudget {
                        total_bytes,
                        ..ValueBudget::default()
                    },
                );
                checks += 1;
            }
        }
    }
    println!(
        "{checks} baseline/CFG native comparisons passed: results, stops, origins, frames, installation and budgets"
    );
}
