use super::*;
use std::sync::{
    Arc, Weak,
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
}
impl Value for Stored {
    fn type_name(&self) -> &str {
        "field"
    }
    fn physical_type(&self) -> PhysicalType {
        PhysicalType::default_for(LogicalType::parse("field:bls12-381.fr").unwrap())
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn retained_bytes(&self) -> usize {
        self.charge
    }
}
#[derive(Debug)]
struct StorageBackend {
    charge: usize,
    later_charge: usize,
    failure: Option<&'static str>,
    first: Weak<Allocation>,
    freed_before_later: bool,
    drops: Arc<AtomicUsize>,
    trace: Vec<String>,
}
impl StorageBackend {
    fn new(charge: usize, failure: Option<&'static str>) -> Self {
        Self {
            charge,
            later_charge: 1,
            failure,
            first: Weak::new(),
            freed_before_later: false,
            drops: Arc::new(AtomicUsize::new(0)),
            trace: vec![],
        }
    }
}
impl Backend for StorageBackend {
    type Value = Stored;
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        binding.signature().ok()
    }
    fn validate_value(&self, _: &Stored) -> Result<(), BackendError> {
        Ok(())
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
        Ok(())
    }
    fn apply(
        &mut self,
        call: &Invocation<'_>,
        args: &[Stored],
    ) -> Result<Vec<Stored>, BackendError> {
        self.trace.push(format!(
            "request:{}:{}:{:?}:{:?}:{}",
            call.site,
            call.kernel,
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
            if charge > call.max_output_bytes {
                return Err(BackendError::new("output-budget"));
            }
            if call.site == "later" {
                self.freed_before_later = self.first.upgrade().is_none();
            }
            let allocation = Arc::new(Allocation {
                payload: vec![7; 8192],
                drops: self.drops.clone(),
            });
            if call.site == "first" {
                self.first = Arc::downgrade(&allocation);
            }
            vec![Stored {
                backing: allocation,
                charge,
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
                count.to_string(),
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
        json!([]),
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
    let admitted = admit_supplied(&bytes(&program(release, repeat)), &backend).unwrap();
    let mut runner = Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "storage-test",
        backend,
        vec![],
        budget,
    )
    .unwrap();
    let outcome = loop {
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
            assert_eq!(result == "returned", live >= 15 && total >= 30);
            assert_eq!(usage.live_value_bytes, 0);
            assert!(usage.total_value_bytes <= total);
            assert!(backend.first.upgrade().is_none());
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
        let input = Stored {
            backing: Arc::new(Allocation {
                payload: vec![0],
                drops: backend.drops.clone(),
            }),
            charge,
        };
        let program = one(
            json!([]),
            json!([["x", "field"]]),
            json!([]),
            json!([["return", []]]),
        );
        let admitted = admit_supplied(&bytes(&program), &backend).unwrap();
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
        assert_eq!(result == "returned", later <= 2);
    }
    // Eight locals fit individually; the last crosses only cumulative capacity.
    for later in [1, 2, 3] {
        let charge = Limits::TOTAL_VALUE_BYTES / 16 - 1;
        let (result, usage, dense) = run_sized(false, charge, later, None, Some(8));
        let (other, other_usage, released) = run_sized(true, charge, later, None, Some(8));
        assert_eq!(result, other);
        assert_eq!(usage, other_usage);
        assert_eq!(dense.trace, released.trace);
        assert_eq!(result == "returned", later <= 2);
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
fn storage_release_rejects_hostile_candidates_without_trusting_checker() {
    struct ApprovesAnything;
    impl Correspondence for ApprovesAnything {
        fn check_with_mapping(
            &self,
            _: &[u8],
            _: &[u8],
            _: ArtifactFormat,
        ) -> Result<Option<SourceMap>, AdmissionError> {
            Ok(None)
        }

        fn check(&self, _: &[u8], _: &[u8], _: ArtifactFormat) -> Result<(), AdmissionError> {
            Ok(())
        }
    }
    let backend = StorageBackend::new(1, None);
    for (position, names, code) in [
        (0, json!(["a"]), ErrorCode::Ssa), // before definition
        (1, json!(["a"]), ErrorCode::Ssa), // future read
        (2, json!(["a", "a"]), ErrorCode::Ssa),
        (2, json!(["absent"]), ErrorCode::Ssa),
        (2, json!([]), ErrorCode::Record),
    ] {
        let mut candidate = program(false, None);
        candidate[3][0][4]
            .as_array_mut()
            .unwrap()
            .insert(position, json!(["release", names]));
        assert_eq!(
            admit_supplied(&bytes(&candidate), &backend)
                .unwrap_err()
                .code,
            code
        );
        assert_eq!(
            admit_physical(
                b"external source",
                &bytes(&candidate),
                &backend,
                &ApprovesAnything
            )
            .unwrap_err()
            .code,
            code
        );
    }
    let mut duplicate = program(true, None);
    duplicate[3][0][4]
        .as_array_mut()
        .unwrap()
        .insert(3, json!(["release", ["a"]]));
    assert_eq!(
        admit_supplied(&bytes(&duplicate), &backend)
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let mut returned = program(true, None);
    returned[3][0][3] = json!([fixture_type("field")]);
    returned[3][0][4]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap()[1] = json!(["c"]);
    assert_eq!(
        admit_supplied(&bytes(&returned), &backend)
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
    let mut rebound = program(true, None);
    rebound[3][0][4][3][5] = json!(["a"]);
    assert_eq!(
        admit_supplied(&bytes(&rebound), &backend).unwrap_err().code,
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
        let admitted = admit_supplied(&bytes(&candidate), &backend);
        if matches!(ty, "rng" | "transcript") {
            assert_eq!(admitted.unwrap_err().code, ErrorCode::Type);
        } else {
            // Private immutable custody has no wire codec, but dropping a
            // local reference grants no transmission or resource authority.
            assert!(admitted.is_ok());
        }
    }
    let mut control = program(false, None);
    control[4][0][7]
        .as_array_mut()
        .unwrap()
        .insert(0, json!(["release", ["a"]]));
    assert_eq!(
        admit_supplied(&bytes(&control), &backend).unwrap_err().code,
        ErrorCode::Record
    );
    let mut logical = program(true, None);
    logical[2] = json!("logical");
    assert_eq!(
        admit_supplied(&bytes(&logical), &backend).unwrap_err().code,
        ErrorCode::Stage
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
