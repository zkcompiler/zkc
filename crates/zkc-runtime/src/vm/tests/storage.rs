use super::*;
use std::cell::Cell;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

// Test-only allocation instrumentation. Drop changes only this counter; neither
// the backend nor the semantic trace can observe it. The payload is real storage.
#[derive(Debug)]
struct Allocation {
    payload: Vec<u8>,
    drops: Arc<AtomicUsize>,
}
impl Drop for Allocation {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}
#[derive(Clone, Debug)]
struct Stored {
    backing: Arc<Allocation>,
    charge: usize,
    index: Option<u64>,
    /// Report `backing` as shared storage instead of binding-owned storage.
    shared: bool,
    /// A view retains its entire parent allocation.
    parent: Option<(Arc<Allocation>, usize)>,
}

#[test]
fn owned_return_transfer_keeps_backing_alive_and_releases_a_refused_condition() {
    use crate::vm::instance::Instance;
    use crate::vm::retention::Retention;
    let drops = Arc::new(AtomicUsize::new(0));
    let value = Stored::new(
        Arc::new(Allocation {
            payload: vec![0; 32],
            drops: drops.clone(),
        }),
        32,
        true,
    );
    let program = Program::decode(&bytes(&one(
        json!([]),
        json!([]),
        json!([]),
        json!([["return", []]]),
    )))
    .unwrap();
    let mut instance = Instance::new(
        &program,
        "main",
        StorageBackend::shared(32, 32),
        "P",
        "session",
        ValueBudget::default(),
        WorkBudget::default(),
    )
    .ok()
    .unwrap();
    instance
        .validate(&value, &value.physical_type(), false)
        .unwrap();
    let inputs = vec![value.clone(), value];
    let scope = instance.open_scope(&inputs, Retention::Input).unwrap();
    let mut returned = instance.hold_return(inputs.clone());
    instance.close_scope(scope, inputs.iter());
    drop(inputs);
    assert_eq!(instance.usage().live_values, 0);
    assert_eq!(instance.usage().live_value_bytes, 32);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    // The test value refuses Boolean inspection. Its handoff reference must
    // still be removed while the remaining alias continues to own the backing.
    assert!(matches!(instance.take_condition(&mut returned),
        Err(RuntimeError::Backend(e)) if e.code == "local-control-bool"));
    assert_eq!(returned.len(), 1);
    assert_eq!(instance.usage().live_value_bytes, 32);
    instance.release_return(returned);
    assert_eq!(instance.usage().live_value_bytes, 0);
    assert_eq!(instance.usage().total_value_bytes, 32);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "return backing is already charged")]
fn return_transfer_rejects_unretained_shared_backing() {
    use crate::vm::instance::Instance;
    let program = admitted(&one(
        json!([]),
        json!([]),
        json!([]),
        json!([["return", []]]),
    ));
    let mut instance = Instance::new(
        &program,
        "main",
        StorageBackend::shared(32, 32),
        "P",
        "session",
        ValueBudget::default(),
        WorkBudget::default(),
    )
    .ok()
    .unwrap();
    let value = Stored::new(
        Arc::new(Allocation {
            payload: vec![0; 32],
            drops: Arc::new(AtomicUsize::new(0)),
        }),
        32,
        true,
    );
    let _returned = instance.hold_return(vec![value]);
}

impl Stored {
    fn new(backing: Arc<Allocation>, charge: usize, shared: bool) -> Self {
        Self {
            backing,
            charge,
            index: None,
            shared,
            parent: None,
        }
    }
}
impl Value for Stored {
    fn control_index(&self) -> Result<u64, BackendError> {
        self.index
            .ok_or_else(|| BackendError::new("expected-index"))
    }
    fn from_control_index(index: u64) -> Result<Self, BackendError> {
        // Index scaffolding has no instrumented payload charge in this storage probe.
        Ok(Self {
            index: Some(index),
            ..Self::new(
                Arc::new(Allocation {
                    payload: vec![],
                    drops: Arc::new(AtomicUsize::new(0)),
                }),
                0,
                false,
            )
        })
    }
    fn physical_type(&self) -> PhysicalType {
        if self.index.is_some() {
            return PhysicalType::default_for(LogicalType::parse("index").unwrap()).unwrap();
        }

        PhysicalType::default_for(LogicalType::parse("field:bls12-381.fr").unwrap()).unwrap()
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn retained_bytes(&self) -> usize {
        self.charge + self.parent.as_ref().map_or(0, |(_, charge)| *charge)
    }
    fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        if !self.shared {
            return self.retained_bytes();
        }
        if shared(Backing::of(&self.backing, self.charge))
            && let Some((parent, charge)) = &self.parent
        {
            shared(Backing::of(parent, *charge));
        }
        0
    }
    fn validation_backing(&self) -> Option<Backing> {
        self.shared.then(|| Backing::of(&self.backing, self.charge))
    }
}
#[derive(Debug)]
struct StorageBackend {
    charge: usize,
    later_charge: usize,
    failure: Option<&'static str>,
    /// Produced values report their allocation as shared storage.
    identity: bool,
    /// Declared operand read extent for the `alias` kernel.
    declared: Option<u64>,
    allocations: usize,
    first_drops: usize,
    first_address: usize,
    freed_before_later: bool,
    reused_address: bool,
    validations: Cell<usize>,
    drops: Arc<AtomicUsize>,
    trace: Vec<String>,
}
impl StorageBackend {
    fn new(charge: usize, failure: Option<&'static str>) -> Self {
        Self {
            charge,
            later_charge: 1,
            failure,
            identity: false,
            declared: None,
            allocations: 0,
            first_drops: 0,
            first_address: 0,
            freed_before_later: false,
            reused_address: false,
            validations: Cell::new(0),
            drops: Arc::new(AtomicUsize::new(0)),
            trace: vec![],
        }
    }
    fn shared(charge: usize, later_charge: usize) -> Self {
        Self {
            later_charge,
            identity: true,
            ..Self::new(charge, None)
        }
    }
    fn all_freed(&self) -> bool {
        self.drops.load(Ordering::SeqCst) == self.allocations
    }
}
impl Backend for StorageBackend {
    type Call = ();
    type Checkpoint = ();
    type Value = Stored;
    type Kernel = crate::vm::BoundSignature;
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<Self::Kernel> {
        binding.signature().ok()
    }
    fn validate_value(&self, value: &Stored) -> Result<(), BackendError> {
        if value.index.is_none() {
            self.validations.set(self.validations.get() + 1);
        }
        Ok(())
    }
    fn operand_work(
        &self,
        _kernel: &Self::Kernel,
        call: &CallContext<'_>,
        _: &[Stored],
    ) -> Option<u64> {
        self.declared.filter(|_| call.site == "alias")
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Stored]) -> Result<(), BackendError> {
        self.trace
            .push(format!("enter:{:?}:{}", frame.kind(), args.len()));
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        args: &[Stored],
    ) -> Result<(), BackendError> {
        self.trace
            .push(format!("leave:{:?}:{exit:?}:{}", frame.kind(), args.len()));
        if self.failure == Some("leave") && !args.is_empty() {
            return Err(BackendError::new("chosen-leave-failure"));
        }
        Ok(())
    }
    fn apply(
        &mut self,
        _kernel: &Self::Kernel,
        call: &Invocation<'_>,
        args: &[Stored],
    ) -> Result<Vec<Stored>, BackendError> {
        self.trace.push(format!(
            "request:{}:{}:{:?}:{:?}:{}",
            call.site,
            call.binding.implementation(),
            call.attributes,
            args.iter()
                .map(|v| v.backing.payload[0])
                .collect::<Vec<_>>(),
            call.max_output_bytes
        ));
        if self.failure == Some(call.site) {
            return Err(BackendError::new("chosen-failure"));
        }
        let values = if call.site == "alias" {
            // This intentionally shares one allocation with both input operands.
            vec![args[0].clone()]
        } else {
            let charge = if call.site == "first" {
                self.charge
            } else {
                self.later_charge
            };
            // The allowance bounds new storage; a view's parent is already retained.
            if charge > call.max_output_bytes {
                return Err(BackendError::new("output-budget"));
            }
            let parent = (call.site == "view").then(|| (args[0].backing.clone(), args[0].charge));
            // Every allocation has equal contents; only creation distinguishes them.
            let allocation = Arc::new(Allocation {
                payload: vec![7; 8192],
                drops: self.drops.clone(),
            });
            let address = Arc::as_ptr(&allocation).addr();
            if call.site == "first" {
                self.first_drops = self.drops.load(Ordering::SeqCst);
                self.first_address = address;
            }
            if call.site == "later" {
                self.freed_before_later = self.drops.load(Ordering::SeqCst) > self.first_drops;
                self.reused_address = address == self.first_address;
            }
            self.allocations += 1;
            vec![Stored {
                parent,
                ..Stored::new(allocation, charge, self.identity)
            }]
        };
        self.trace.push(format!(
            "response:{}:{:?}",
            call.site,
            values
                .iter()
                .map(|v| v.backing.payload[0])
                .collect::<Vec<_>>()
        ));
        Ok(values)
    }
}
fn program(release: bool, repeat: Option<u64>) -> Json {
    let mut body = vec![
        json!(["op", "first", "arkworks/field.constant", ["7"], [], ["a"]]),
        json!(["op", "alias", "arkworks/field.add", [], ["a", "a"], ["b"]]),
    ];
    if release {
        body.push(json!(["release", ["a", "b"]]));
    }
    body.push(json!([
        "op",
        "later",
        "arkworks/field.constant",
        ["7"],
        [],
        ["c"]
    ]));
    if release {
        body.push(json!(["release", ["c"]]));
    }
    body.push(json!(["return", []]));
    let call = json!(["local", "work", "storage", [], []]);
    let control = if let Some(count) = repeat {
        json!([
            [
                "loop",
                "repeat",
                ["value", "count", count.to_string(), "iteration"],
                [],
                [],
                [call, ["yield", []]],
                []
            ],
            ["return", []]
        ])
    } else {
        json!([call, ["return", []]])
    };
    one(
        json!([["function", "storage", [], [], body]]),
        if repeat.is_some() {
            json!([["count", "index@native.index/0"]])
        } else {
            json!([])
        },
        json!([]),
        control,
    )
}
fn run(
    release: bool,
    charge: usize,
    failure: Option<&'static str>,
    repeat: Option<u64>,
) -> (String, Usage, StorageBackend) {
    run_sized(release, charge, 1, failure, repeat)
}
fn run_sized(
    release: bool,
    charge: usize,
    later_charge: usize,
    failure: Option<&'static str>,
    repeat: Option<u64>,
) -> (String, Usage, StorageBackend) {
    run_budgeted(
        release,
        charge,
        later_charge,
        failure,
        repeat,
        ValueBudget::default(),
    )
}
fn run_budgeted(
    release: bool,
    charge: usize,
    later_charge: usize,
    failure: Option<&'static str>,
    repeat: Option<u64>,
    budget: ValueBudget,
) -> (String, Usage, StorageBackend) {
    let mut backend = StorageBackend::new(charge, failure);
    backend.later_charge = later_charge;
    let admitted = crate::vm::Program::decode(&bytes(&program(release, repeat)))
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
    let mut runner = Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "storage-test",
        backend,
        repeat
            .map(|n| vec![Stored::from_control_index(n).unwrap()])
            .unwrap_or_default(),
        budget,
    )
    .unwrap();
    let outcome = loop {
        runner.advance_local_control().unwrap();
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Returned(values) => {
                assert!(values.is_empty());
                break "returned".into();
            }
            Action::Stopped(stop) => break format!("{stop:?}"),
            action => panic!("unexpected {action:?}"),
        }
    };
    let usage = runner.usage();
    // Check while the Runner is alive: dropping it must not hide values retained
    // by argument scratch after a successful or refused kernel call.
    assert!(runner.backend().all_freed());
    (outcome, usage, runner.into_backend())
}

#[test]
fn host_value_budgets_enforce_exact_live_and_cumulative_boundaries() {
    // Each iteration retains 2*7+1 bytes. Frames release their live charge;
    // aliases and earlier iterations still count toward cumulative retention.
    for live in [14, 15, 16] {
        for total in [29, 30, 31] {
            let budget = ValueBudget {
                live_bytes: live,
                total_bytes: total,
            };
            let (result, usage, backend) = run_budgeted(true, 7, 1, None, Some(2), budget);
            assert_eq!(
                result == "returned",
                live >= 15 && total >= 30,
                "{result} {usage:?} live={live} total={total}"
            );
            assert_eq!(usage.live_value_bytes, 0);
            assert!(usage.total_value_bytes <= total);
            assert!(backend.all_freed());
        }
    }
    let (result, usage, _) = run_budgeted(
        false,
        0,
        0,
        None,
        None,
        ValueBudget {
            live_bytes: 0,
            total_bytes: 0,
        },
    );
    assert_eq!(result, "returned");
    assert_eq!(usage.total_value_bytes, 0);
}

#[test]
fn host_value_budget_checks_entry_and_keeps_individual_value_limit() {
    for (charge, live, total, accepted) in [
        (8, 8, 8, true),
        (8, 7, 8, false),
        (8, 8, 7, false),
        (Limits::VALUE_BYTES + 1, usize::MAX, usize::MAX, false),
    ] {
        let backend = StorageBackend::new(0, None);
        let input = Stored::new(
            Arc::new(Allocation {
                payload: vec![0],
                drops: backend.drops.clone(),
            }),
            charge,
            false,
        );
        let program = one(
            json!([]),
            json!([["x", "field"]]),
            json!([]),
            json!([["return", []]]),
        );
        let admitted = crate::vm::Program::decode(&bytes(&program))
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap();
        let result = Runner::new_with_value_budget(
            &admitted,
            "main",
            "P",
            "entry",
            backend,
            vec![input],
            ValueBudget {
                live_bytes: live,
                total_bytes: total,
            },
        );
        match result {
            Ok(mut runner) => {
                assert!(accepted);
                assert!(matches!(runner.poll(), Action::Returned(_)));
                assert_eq!(runner.usage().live_value_bytes, 0);
            }
            Err(error) => {
                assert!(!accepted);
                assert_eq!(error.error, RuntimeError::Limit);
                assert_eq!(error.backend.drops.load(Ordering::SeqCst), 1);
            }
        }
    }
}
#[test]
fn storage_release_frees_real_shared_allocation_before_later_allocation() {
    let (result, usage, dense) = run(false, 8192, None, None);
    let (released_result, released_usage, released) = run(true, 8192, None, None);
    assert_eq!(result, "returned");
    assert_eq!(result, released_result);
    assert_eq!(usage, released_usage);
    assert_eq!(dense.trace, released.trace);
    assert!(!dense.freed_before_later);
    assert!(released.freed_before_later);
    assert_eq!(released.drops.load(Ordering::SeqCst), 2);
    assert_eq!(dense.drops.load(Ordering::SeqCst), 2);
    assert_eq!(usage.total_value_bytes, 2 * 8192 + 1); // shared backing charged twice
    assert_eq!(usage.live_values, 0);
    assert_eq!(usage.live_value_bytes, 0);
    assert_eq!(usage.instructions, 6); // local action + 3 kernels + 2 returns
}
#[test]
fn storage_release_preserves_live_and_cumulative_budget_boundaries_and_failures() {
    for charge in [
        Limits::VALUE_BYTES / 2 - 1,
        Limits::VALUE_BYTES / 2,
        Limits::VALUE_BYTES / 2 + 1,
    ] {
        for failure in [None, Some("first"), Some("alias"), Some("later")] {
            let (result, usage, dense) = run(false, charge, failure, None);
            let (released_result, released_usage, released) = run(true, charge, failure, None);
            assert_eq!(result, released_result);
            assert_eq!(usage, released_usage);
            assert_eq!(dense.trace, released.trace);
            assert_eq!(usage.live_value_bytes, 0);
            assert_eq!(usage.live_values, 0);
            if failure.is_none() {
                assert_eq!(result == "returned", charge < Limits::VALUE_BYTES / 2);
            }
        }
    }
    // Below, exactly at, and above the live ceiling (including shared backing).
    for later in [1, 2, 3] {
        let (result, usage, dense) =
            run_sized(false, Limits::VALUE_BYTES / 2 - 1, later, None, None);
        let (other, other_usage, released) =
            run_sized(true, Limits::VALUE_BYTES / 2 - 1, later, None, None);
        assert_eq!(result, other);
        assert_eq!(usage, other_usage);
        assert_eq!(dense.trace, released.trace);
        assert_eq!(result == "returned", later <= 2, "{result} {usage:?}");
    }
    // Eight locals fit individually; the last crosses only cumulative capacity.
    for later in [1, 2, 3] {
        let charge = Limits::TOTAL_VALUE_BYTES / 16 - 1;
        let (result, usage, dense) = run_sized(false, charge, later, None, Some(8));
        let (other, other_usage, released) = run_sized(true, charge, later, None, Some(8));
        assert_eq!(result, other);
        assert_eq!(usage, other_usage);
        assert_eq!(dense.trace, released.trace);
        assert_eq!(result == "returned", later <= 2, "{result} {usage:?}");
        if later == 2 {
            assert_eq!(usage.total_value_bytes, Limits::TOTAL_VALUE_BYTES);
        }
    }
    // Four locals reach the cumulative ceiling while each local fits live budget.
    for charge in [
        Limits::TOTAL_VALUE_BYTES / 8 - 1,
        Limits::TOTAL_VALUE_BYTES / 8,
    ] {
        let (result, usage, dense) = run(false, charge, None, Some(4));
        let (released_result, released_usage, released) = run(true, charge, None, Some(4));
        assert_eq!(result, released_result);
        assert_eq!(usage, released_usage);
        assert_eq!(dense.trace, released.trace);
    }
}
#[test]
fn storage_release_rejects_hostile_candidates_at_admission() {
    let backend = StorageBackend::new(1, None);
    for (position, names, code) in [
        (0, json!(["a"]), ErrorCode::Ssa), // before definition
        (1, json!(["a"]), ErrorCode::Ssa), // future read
        (2, json!(["a", "a"]), ErrorCode::Ssa),
        (2, json!(["absent"]), ErrorCode::Ssa),
        (2, json!([]), ErrorCode::Record),
    ] {
        let mut candidate = program(false, None);
        candidate[2][0][4]
            .as_array_mut()
            .unwrap()
            .insert(position, json!(["release", names]));
        assert_eq!(
            crate::vm::Program::decode(&bytes(&candidate))
                .and_then(|program| {
                    program.check_installation(&backend)?;
                    Ok(program)
                })
                .unwrap_err()
                .code,
            code
        );
    }
    let mut duplicate = program(true, None);
    duplicate[2][0][4]
        .as_array_mut()
        .unwrap()
        .insert(3, json!(["release", ["a"]]));
    assert_eq!(
        crate::vm::Program::decode(&bytes(&duplicate))
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let mut returned = program(true, None);
    returned[2][0][3] = json!([fixture_type("field")]);
    returned[2][0][4]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap()[1] = json!(["c"]);
    assert_eq!(
        crate::vm::Program::decode(&bytes(&returned))
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let mut rebound = program(true, None);
    rebound[2][0][4][3][5] = json!(["a"]);
    assert_eq!(
        crate::vm::Program::decode(&bytes(&rebound))
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    for ty in [
        "rng",
        "transcript",
        "prover_key",
        "verifier_key",
        "opening_state",
    ] {
        let candidate = one(
            json!([[
                "function",
                "bad",
                [["r", ty]],
                [],
                [["release", ["r"]], ["return", []]]
            ]]),
            json!([]),
            json!([]),
            json!([["return", []]]),
        );
        let admitted = crate::vm::Program::decode(&bytes(&candidate)).and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        });
        if matches!(ty, "rng" | "transcript") {
            assert_eq!(admitted.unwrap_err().code, ErrorCode::Type);
        } else {
            // Private immutable custody has no wire codec, but dropping a
            // local reference grants no transmission or resource authority.
            assert!(admitted.is_ok());
        }
    }
    let mut control = program(false, None);
    control[3][0][6]
        .as_array_mut()
        .unwrap()
        .insert(0, json!(["release", ["a"]]));
    assert_eq!(
        crate::vm::Program::decode(&bytes(&control))
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap_err()
            .code,
        ErrorCode::Record
    );
    let mut logical = program(true, None);
    logical.as_array_mut().unwrap().insert(2, json!("logical"));
    assert_eq!(
        crate::vm::Program::decode(&bytes(&logical))
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap_err()
            .code,
        ErrorCode::Record
    );
}

#[test]
fn storage_release_at_entry_keeps_parent_reference_and_returned_values() {
    let build = |release: bool| {
        let mut body = vec![];
        if release {
            body.push(json!(["release", ["unused"]]));
        }
        body.push(json!(["return", ["kept"]]));
        one(
            json!([[
                "function",
                "Pick",
                [["unused", "field"], ["kept", "field"]],
                ["field"],
                body
            ]]),
            json!([["x", "field"]]),
            json!(["field", "field"]),
            json!([
                ["local", "pick", "Pick", ["x", "x"], ["y"]],
                ["return", ["x", "y"]]
            ]),
        )
    };
    let mut baseline = runner(&build(false), "P", Mock::new(), vec![V::Field(7)]);
    let mut released = runner(&build(true), "P", Mock::new(), vec![V::Field(7)]);
    local(&mut baseline);
    local(&mut released);
    assert_eq!(baseline.poll(), released.poll());
    assert!(
        matches!(released.poll(), Action::Returned(values) if values == [V::Field(7), V::Field(7)])
    );
    assert_eq!(baseline.usage(), released.usage());
    assert_eq!(baseline.backend().trace, released.backend().trace);
    assert_eq!(released.usage().total_value_bytes, 6 * 16);
}

#[test]
fn storage_release_after_affine_consumption_is_rejected() {
    let mut candidate = one(
        json!([[
            "function",
            "draw",
            [["r", "rng"]],
            ["rng"],
            [
                [
                    "op",
                    "draw",
                    "arkworks/random.draw",
                    [],
                    ["r"],
                    ["x", "next"]
                ],
                ["return", ["next"]]
            ]
        ]]),
        json!([]),
        json!([]),
        json!([["return", []]]),
    );
    let backend = StorageBackend::new(1, None);
    crate::vm::Program::decode(&bytes(&candidate))
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
    candidate[2][0][4]
        .as_array_mut()
        .unwrap()
        .insert(1, json!(["release", ["r"]]));
    let error = crate::vm::Program::decode(&bytes(&candidate))
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap_err();
    assert_eq!(error.code, ErrorCode::Ssa);
}

fn drive(
    program: &Json,
    backend: StorageBackend,
    inputs: Vec<Stored>,
    values: ValueBudget,
    work: WorkBudget,
) -> (String, Usage, StorageBackend) {
    let admitted = crate::vm::Program::decode(&bytes(program))
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
    let mut runner = Runner::new_with_budgets(
        &admitted,
        "main",
        "P",
        "storage-test",
        backend,
        inputs,
        values,
        work,
    )
    .unwrap();
    let outcome = loop {
        runner.advance_local_control().unwrap();
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Returned(_) => break "returned".to_owned(),
            Action::Stopped(stop) => break format!("{:?}", stop.kind),
            action => panic!("unexpected {action:?}"),
        }
    };
    let usage = runner.usage();
    (outcome, usage, runner.into_backend())
}
fn values(live_bytes: usize, total_bytes: usize) -> ValueBudget {
    ValueBudget {
        live_bytes,
        total_bytes,
    }
}
fn logical(logical_bytes: u64) -> WorkBudget {
    WorkBudget {
        logical_bytes,
        ..WorkBudget::default()
    }
}
// One allocation captured by every iteration and passed to a local call that
// reads it twice and returns an alias of it.
fn captured(count: u64) -> Json {
    one(
        json!([
            [
                "function",
                "make",
                [],
                ["field"],
                [
                    ["op", "first", "arkworks/field.constant", ["7"], [], ["a"]],
                    ["return", ["a"]]
                ]
            ],
            [
                "function",
                "use",
                [["x", "field"]],
                ["field"],
                [
                    ["op", "alias", "arkworks/field.add", [], ["x", "x"], ["y"]],
                    ["return", ["y"]]
                ]
            ]
        ]),
        json!([["count", "index@native.index/0"]]),
        json!([]),
        json!([
            ["local", "make", "make", [], ["v"]],
            [
                "loop",
                "repeat",
                ["value", "count", count.to_string(), "iteration"],
                [],
                ["v"],
                [["local", "use", "use", ["v"], ["w"]], ["yield", []]],
                []
            ],
            ["return", []]
        ]),
    )
}
fn count(n: u64) -> Vec<Stored> {
    vec![Stored::from_control_index(n).unwrap()]
}
fn unbounded() -> ValueBudget {
    values(usize::MAX, usize::MAX)
}

#[test]
fn shared_allocations_count_once_and_equal_independent_allocations_count_separately() {
    const C: usize = 8192;
    // "first" and "later" create equal contents; "alias" returns first's backing.
    let shared = |live, total, work| {
        drive(
            &program(false, None),
            StorageBackend::shared(C, C),
            vec![],
            values(live, total),
            logical(work),
        )
    };
    let (result, usage, backend) = shared(usize::MAX, usize::MAX, Limits::LOGICAL_BYTES);
    assert_eq!(result, "returned");
    assert_eq!(usage.total_value_bytes, 2 * C);
    // Results allocate first and later; alias reads its shared operand twice.
    assert_eq!(usage.logical_bytes, 4 * C as u64);
    assert_eq!((usage.live_values, usage.live_value_bytes), (0, 0));
    assert!(backend.all_freed());
    for (live, total, work, accepted) in [
        (2 * C, 2 * C, 4 * C as u64, true),
        (2 * C - 1, usize::MAX, Limits::LOGICAL_BYTES, false),
        (usize::MAX, 2 * C - 1, Limits::LOGICAL_BYTES, false),
        (usize::MAX, usize::MAX, 4 * C as u64 - 1, false),
    ] {
        // A refusal comes from the allowance preflight before "later" allocates.
        let (result, usage, backend) = shared(live, total, work);
        assert_eq!(result == "returned", accepted, "{result} {usage:?}");
        assert_eq!(backend.allocations, if accepted { 2 } else { 1 });
    }
    // Without reported identity every binding is charged in full, as before.
    let (result, usage, _) = drive(
        &program(false, None),
        StorageBackend {
            later_charge: C,
            ..StorageBackend::new(C, None)
        },
        vec![],
        unbounded(),
        WorkBudget::default(),
    );
    assert_eq!(result, "returned");
    assert_eq!(usage.total_value_bytes, 3 * C);
    assert_eq!(usage.logical_bytes, 5 * C as u64);
}

#[test]
fn captured_backing_is_retained_once_while_every_read_charges_logical_work() {
    const C: usize = 1 << 20;
    for n in [1u64, 16, 64] {
        let expected = C as u64 + n * 2 * C as u64;
        let (result, usage, backend) = drive(
            &captured(n),
            StorageBackend::shared(C, 1),
            count(n),
            values(C, C),
            logical(expected),
        );
        assert_eq!(result, "returned", "{n}: {usage:?}");
        assert_eq!(usage.total_value_bytes, C);
        assert_eq!(usage.logical_bytes, expected);
        assert_eq!(usage.iterations, n);
        assert!(backend.all_freed());
        // Sharing cannot make the reads free: one byte less stops in the last call.
        let (result, usage, _) = drive(
            &captured(n),
            StorageBackend::shared(C, 1),
            count(n),
            values(C, C),
            logical(expected - 1),
        );
        assert_eq!(result, "Limit");
        assert_eq!(usage.iterations, n);
        assert_eq!(usage.logical_bytes, expected - 2 * C as u64);
    }
    // The previous per-binding charge grows with every iteration.
    let (_, usage, _) = drive(
        &captured(64),
        StorageBackend::new(C, None),
        count(64),
        unbounded(),
        WorkBudget::default(),
    );
    assert!(usage.total_value_bytes > 64 * C);
}

#[test]
fn declared_operand_extent_replaces_the_full_operand_charge() {
    const C: usize = 1 << 20;
    let mut backend = StorageBackend::shared(C, 1);
    backend.declared = Some(40);
    let (result, usage, _) = drive(
        &captured(64),
        backend,
        count(64),
        values(C, C),
        logical(C as u64 + 64 * 40),
    );
    assert_eq!(result, "returned");
    assert_eq!(usage.logical_bytes, C as u64 + 64 * 40);
}

#[test]
fn views_retain_their_parent_allocation_until_the_last_reference() {
    // make returns a small view of a large allocation; its own binding of the
    // allocation ends with the call, but the view keeps it alive.
    let build = |site: &str| {
        one(
            json!([
                [
                    "function",
                    "make",
                    [],
                    ["field"],
                    [
                        ["op", "first", "arkworks/field.constant", ["7"], [], ["a"]],
                        ["op", site, "arkworks/field.add", [], ["a", "a"], ["v"]],
                        ["return", ["v"]]
                    ]
                ],
                [
                    "function",
                    "fresh",
                    [],
                    ["field"],
                    [
                        ["op", "later", "arkworks/field.constant", ["7"], [], ["c"]],
                        ["return", ["c"]]
                    ]
                ]
            ]),
            json!([]),
            json!([]),
            json!([
                ["local", "make", "make", [], ["v"]],
                ["local", "fresh", "fresh", [], ["w"]],
                ["return", []]
            ]),
        )
    };
    const PARENT: usize = 4096;
    const SMALL: usize = 64;
    // A view needs parent + view + later; a detached copy needs only the larger
    // of the two phases.
    for (site, peak) in [("view", PARENT + 2 * SMALL), ("detach", PARENT + SMALL)] {
        for live in [peak - 1, peak] {
            let (result, usage, backend) = drive(
                &build(site),
                StorageBackend::shared(PARENT, SMALL),
                vec![],
                values(live, usize::MAX),
                WorkBudget::default(),
            );
            assert_eq!(
                result == "returned",
                live == peak,
                "{site} {live} {usage:?}"
            );
            assert_eq!(usage.live_value_bytes, 0);
            assert!(backend.all_freed());
        }
    }
}

#[test]
fn identity_release_keeps_ghost_accounting_and_charges_reused_addresses_as_fresh() {
    const C: usize = 8192;
    let run = |release| {
        drive(
            &program(release, None),
            StorageBackend::shared(C, C),
            vec![],
            unbounded(),
            WorkBudget::default(),
        )
    };
    let (result, usage, dense) = run(false);
    let (released_result, released_usage, released) = run(true);
    assert_eq!(result, "returned");
    assert_eq!(result, released_result);
    assert_eq!(usage, released_usage);
    assert_eq!(dense.trace, released.trace);
    assert!(!dense.freed_before_later);
    assert!(released.freed_before_later);
    // The later allocation may reuse the freed address; it is still fresh.
    assert_eq!(released_usage.total_value_bytes, 2 * C);
    // Deferred storage charges keep the released storage until frame cleanup.
    for live in [2 * C - 1, 2 * C] {
        let (result, _, _) = drive(
            &program(true, None),
            StorageBackend::shared(C, C),
            vec![],
            values(live, usize::MAX),
            WorkBudget::default(),
        );
        assert_eq!(result == "returned", live == 2 * C);
    }
}

#[test]
fn validation_is_reused_only_for_bound_aliases_with_reported_identity() {
    for n in [1u64, 16] {
        let (_, _, shared) = drive(
            &captured(n),
            StorageBackend::shared(64, 1),
            count(n),
            unbounded(),
            WorkBudget::default(),
        );
        // Only the produced value is validated; captures, arguments and alias
        // results of the bound allocation reuse that validation.
        assert_eq!(shared.validations.get(), 1);
        let (_, _, owned) = drive(
            &captured(n),
            StorageBackend::new(64, None),
            count(n),
            unbounded(),
            WorkBudget::default(),
        );
        assert_eq!(owned.validations.get(), 1 + 4 * n as usize);
    }
}

fn carried_local() -> Json {
    one(
        json!([[
            "function",
            "work",
            [
                ["lo", "index@native.index/0"],
                ["hi", "index@native.index/0"]
            ],
            ["field"],
            [
                ["op", "first", "field.constant", ["7"], [], ["initial"]],
                [
                    "for",
                    "carry",
                    "i",
                    "lo",
                    "hi",
                    [["state", "initial"]],
                    [],
                    [
                        ["op", "alias", "field.add", [], ["state", "state"], ["read"]],
                        ["op", "later", "field.constant", ["7"], [], ["next"]],
                        ["yield", ["next"]]
                    ],
                    ["result"]
                ],
                ["return", ["result"]]
            ]
        ]]),
        json!([
            ["lo", "index@native.index/0"],
            ["hi", "index@native.index/0"]
        ]),
        json!([]),
        json!([
            ["local", "work", "work", ["lo", "hi"], ["result"]],
            ["return", []]
        ]),
    )
}

#[test]
fn local_carried_backing_keeps_validation_across_region_handoffs() {
    const C: usize = 64;
    for n in [0, 1, 16, 128] {
        let (result, usage, backend) = drive(
            &carried_local(),
            StorageBackend::shared(C, C),
            vec![
                Stored::from_control_index(0).unwrap(),
                Stored::from_control_index(n).unwrap(),
            ],
            values(3 * C, (n as usize + 1) * C),
            WorkBudget::default(),
        );
        assert_eq!(result, "returned", "n={n} {usage:?}");
        assert_eq!(backend.validations.get(), n as usize + 1);
        assert_eq!(backend.allocations, n as usize + 1);
        assert_eq!(usage.total_value_bytes, (n as usize + 1) * C);
        assert_eq!((usage.live_values, usage.live_value_bytes), (0, 0));
        assert!(backend.all_freed());
    }
}

#[test]
fn local_handoff_references_are_released_on_every_failure() {
    for failure in [Some("alias"), Some("later"), Some("leave"), None] {
        for (live, total, instructions, iterations) in [
            (192, 256, 1000, 1000),
            (191, 256, 1000, 1000),
            (192, 255, 1000, 1000),
            (192, 256, 9, 1000),
            (192, 256, 1000, 1),
        ] {
            let backend = StorageBackend {
                failure,
                ..StorageBackend::shared(64, 64)
            };
            let (result, usage, backend) = drive(
                &carried_local(),
                backend,
                vec![
                    Stored::from_control_index(0).unwrap(),
                    Stored::from_control_index(3).unwrap(),
                ],
                values(live, total),
                WorkBudget {
                    instructions,
                    iterations,
                    ..WorkBudget::default()
                },
            );
            let succeeds = failure.is_none()
                && live == 192
                && total == 256
                && instructions == 1000
                && iterations == 1000;
            assert_eq!(result == "returned", succeeds, "{result} {usage:?}");
            assert_eq!(
                (usage.live_values, usage.live_value_bytes),
                (0, 0),
                "{result}"
            );
            assert!(backend.all_freed(), "{result}");
        }
    }
}

fn carried_participant() -> Json {
    one(
        json!([
            [
                "function",
                "make",
                [],
                ["field"],
                [
                    ["op", "first", "field.constant", ["7"], [], ["initial"]],
                    ["return", ["initial"]]
                ]
            ],
            [
                "function",
                "step",
                [["state", "field"]],
                ["field"],
                [
                    ["op", "alias", "field.add", [], ["state", "state"], ["read"]],
                    ["op", "later", "field.constant", ["7"], [], ["next"]],
                    ["return", ["next"]]
                ]
            ]
        ]),
        json!([["count", "index@native.index/0"]]),
        json!([]),
        json!([
            ["local", "make", "make", [], ["initial"]],
            [
                "loop",
                "carry",
                ["value", "count", "128", "i"],
                [["state", "initial"]],
                [],
                [
                    ["local", "step", "step", ["state"], ["next"]],
                    ["yield", ["next"]]
                ],
                ["result"]
            ],
            ["return", []]
        ]),
    )
}

#[test]
fn participant_carried_backing_keeps_validation_across_frame_handoffs() {
    for n in [0, 1, 16, 128] {
        let (result, usage, backend) = drive(
            &carried_participant(),
            StorageBackend::shared(64, 64),
            count(n),
            values(192, (n as usize + 1) * 64),
            WorkBudget::default(),
        );
        assert_eq!(result, "returned", "n={n} {usage:?}");
        assert_eq!(backend.validations.get(), n as usize + 1);
        assert_eq!(backend.allocations, n as usize + 1);
        assert_eq!(usage.total_value_bytes, (n as usize + 1) * 64);
        assert_eq!((usage.live_values, usage.live_value_bytes), (0, 0));
        assert!(backend.all_freed());
    }
}

#[test]
fn participant_handoff_references_are_released_on_every_failure() {
    for failure in [Some("alias"), Some("later"), Some("leave"), None] {
        for (live, total, instructions, iterations) in [
            (192, 256, 1000, 1000),
            (191, 256, 1000, 1000),
            (192, 255, 1000, 1000),
            (192, 256, 9, 1000),
            (192, 256, 1000, 1),
        ] {
            let (result, usage, backend) = drive(
                &carried_participant(),
                StorageBackend {
                    failure,
                    ..StorageBackend::shared(64, 64)
                },
                count(3),
                values(live, total),
                WorkBudget {
                    instructions,
                    iterations,
                    ..WorkBudget::default()
                },
            );
            let succeeds = failure.is_none()
                && live == 192
                && total == 256
                && instructions == 1000
                && iterations == 1000;
            assert_eq!(result == "returned", succeeds, "{result} {usage:?}");
            assert_eq!(
                (usage.live_values, usage.live_value_bytes),
                (0, 0),
                "{result}"
            );
            assert!(backend.all_freed(), "{result}");
        }
    }
}

#[test]
fn logical_work_budget_has_a_hard_ceiling() {
    let backend = StorageBackend::new(1, None);
    let admitted = crate::vm::Program::decode(&bytes(&program(false, None)))
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
    for (budget, accepted) in [
        (Limits::LOGICAL_BYTES, true),
        (Limits::LOGICAL_BYTES + 1, false),
    ] {
        let result = Runner::new_with_budgets(
            &admitted,
            "main",
            "P",
            "storage-test",
            StorageBackend::new(1, None),
            vec![],
            ValueBudget::default(),
            logical(budget),
        );
        match result {
            Ok(_) => assert!(accepted),
            Err(error) => {
                assert!(!accepted);
                assert_eq!(error.error, RuntimeError::Limit);
                assert_eq!(error.usage, Usage::default());
            }
        }
    }
}
