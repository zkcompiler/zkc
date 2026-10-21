//! Native backend integration, built explicitly to avoid a runtime/backend
//! development-dependency cycle. See the commands in the VM integration notes.
use serde_json::json;
use std::{
    alloc::{GlobalAlloc, Layout, System},
    cell::Cell,
};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::{
    interpreter::LocalRunner,
    vm::{
        Action, ExecutionLedger, Program, StopKind, Value as RuntimeValue, ValueBudget, WorkBudget,
    },
};

thread_local! {
    // Only the executing test thread is observed; unrelated parallel tests do
    // not contribute allocations. The allocator hook itself never allocates.
    static PAYLOAD_ALLOCATIONS: Cell<Option<(usize, usize)>> = const { Cell::new(None) };
}
struct PayloadAllocator;
fn record_allocation(bytes: usize) {
    let _ = PAYLOAD_ALLOCATIONS.try_with(|probe| {
        if let Some((size, count)) = probe.get()
            && bytes == size
        {
            probe.set(Some((size, count + 1)));
        }
    });
}
// SAFETY: All allocation operations delegate unchanged to System. Observation
// uses only a thread-local Cell and does not access the allocated memory.
unsafe impl GlobalAlloc for PayloadAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record_allocation(layout.size());
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record_allocation(layout.size());
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        record_allocation(new_size);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}
#[global_allocator]
static ALLOCATOR: PayloadAllocator = PayloadAllocator;

struct PayloadProbe;
impl PayloadProbe {
    fn start(elements: usize) -> Self {
        PAYLOAD_ALLOCATIONS.with(|probe| {
            assert!(
                probe
                    .replace(Some((elements * size_of::<Value>(), 0)))
                    .is_none()
            );
        });
        Self
    }
    fn count(&self) -> usize {
        PAYLOAD_ALLOCATIONS.with(|probe| probe.get().unwrap().1)
    }
}
impl Drop for PayloadProbe {
    fn drop(&mut self) {
        PAYLOAD_ALLOCATIONS.with(|probe| probe.set(None));
    }
}

const PROGRAM: &str = r#"[
  "zkc.program/0",
  [
    [
      "add",
      "field.add",
      [
        "bls12-381.fr"
      ],
      "arkworks/field.add"
    ]
  ],
  [
    [
      "function",
      "helper",
      [
        [
          "x",
          "field:bls12-381.fr@arkworks.fr/0"
        ],
        [
          "y",
          "field:bls12-381.fr@arkworks.fr/0"
        ]
      ],
      [
        "field:bls12-381.fr@arkworks.fr/0"
      ],
      [
        [
          "op",
          "sum",
          "add",
          [],
          [
            "x",
            "y"
          ],
          [
            "z"
          ]
        ],
        [
          "return",
          [
            "z"
          ]
        ]
      ],
      [
        "helper",
        []
      ]
    ],
    [
      "function",
      "repeat",
      [
        [
          "lo",
          "index@native.index/0"
        ],
        [
          "hi",
          "index@native.index/0"
        ],
        [
          "x",
          "field:bls12-381.fr@arkworks.fr/0"
        ],
        [
          "d",
          "field:bls12-381.fr@arkworks.fr/0"
        ]
      ],
      [
        "field:bls12-381.fr@arkworks.fr/0"
      ],
      [
        [
          "for",
          "loop",
          "i",
          "lo",
          "hi",
          [
            [
              "carry",
              "x"
            ]
          ],
          [
            "d"
          ],
          [
            [
              "op",
              "sum",
              "add",
              [],
              [
                "carry",
                "d"
              ],
              [
                "next"
              ]
            ],
            [
              "yield",
              [
                "next"
              ]
            ]
          ],
          [
            "result"
          ]
        ],
        [
          "return",
          [
            "result"
          ]
        ]
      ],
      [
        "repeat",
        []
      ]
    ]
  ],
  [],
  []
]"#;
fn backend(function: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("", "native", function, None), None),
        Default::default(),
    )
    .unwrap()
}
#[test]
fn numerical_function_root_uses_existing_native_backend() {
    let program = Program::decode(PROGRAM.as_bytes()).unwrap();
    let mut runner = LocalRunner::new(
        &program,
        "helper",
        "native",
        backend("helper"),
        vec![
            Value::Field(Scalar::from(3u64)),
            Value::Field(Scalar::from(4u64)),
        ],
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    assert_eq!(runner.backend().active_frames(), 1);
    assert!(
        matches!(runner.execute(),Action::Returned(v) if matches!(&v[..],[Value::Field(n)] if *n==Scalar::from(7u64)))
    );
    assert_eq!(runner.backend().active_frames(), 0);
}
#[test]
fn numerical_loop_and_output_guard_share_native_ledger() {
    let program = Program::decode(PROGRAM.as_bytes()).unwrap();
    let limits = ValueBudget {
        live_bytes: 16384,
        total_bytes: 262144,
    };
    let ledger = ExecutionLedger::new(limits, WorkBudget::default());
    let mut runner = LocalRunner::new_with_ledger(
        &program,
        "repeat",
        "native",
        backend("repeat"),
        vec![
            Value::Index(0),
            Value::Index(3),
            Value::Field(Scalar::from(1u64)),
            Value::Field(Scalar::from(2u64)),
        ],
        limits,
        WorkBudget::default(),
        Some(ledger.clone()),
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    assert!(
        matches!(runner.execute(),Action::Returned(v) if matches!(&v[..],[Value::Field(n)] if *n==Scalar::from(7u64)))
    );
    assert_eq!(runner.usage().iterations, 3);
    assert_eq!(ledger.snapshot().iterations, 3);
    assert_eq!(runner.backend().active_frames(), 0);
    let (backend, result) = runner.into_retained_outputs();
    assert_eq!(backend.active_frames(), 0);
    assert_eq!(backend.ring_work_spent(), 0);
    assert_eq!(backend.sequence_work_spent(), 0);
    assert_eq!(backend.external_work_spent(), 0);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 16384);
    drop(result);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}
#[test]
fn native_entry_policy_is_still_checked_for_a_local_root() {
    let program = Program::decode(PROGRAM.as_bytes()).unwrap();
    let refusal = LocalRunner::new(
        &program,
        "helper",
        "native",
        backend("wrong_root"),
        vec![
            Value::Field(Scalar::from(1u64)),
            Value::Field(Scalar::from(1u64)),
        ],
    )
    .err()
    .unwrap();
    assert!(
        matches!(refusal.error,zkc_runtime::vm::RuntimeError::Backend(e) if e.code=="refused:entry-domain")
    );
    assert_eq!(refusal.backend.active_frames(), 0);
}

fn variant_program(elements: usize) -> Program {
    let logical =
        zkc_test_support::variants::logical("Packed", json!([["all", vec!["index"; elements]]]));
    let ty = format!("{logical}@logical.variant/0");
    let carrier = json!([
        "zkc.program/0",
        [],
        [[
            "function",
            "pack_many",
            [["x", "index@native.index/0"]],
            [ty],
            [
                ["variant", "pack", ty, "all", vec!["x"; elements], "v"],
                ["return", ["v"]]
            ],
            ["pack_many", []]
        ]],
        [],
        []
    ]);
    Program::decode(&serde_json::to_vec(&carrier).unwrap()).unwrap()
}
fn variant_runner(
    program: &Program,
    total_bytes: usize,
    ledger: Option<ExecutionLedger>,
) -> LocalRunner<NativeBackend> {
    LocalRunner::new_with_ledger(
        program,
        "pack_many",
        "native",
        backend("pack_many"),
        vec![Value::Index(7)],
        ValueBudget {
            live_bytes: 1024 * 1024,
            total_bytes,
        },
        WorkBudget::default(),
        ledger,
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error))
}

#[test]
fn shared_variant_refuses_before_payload_allocation_when_budget_is_exhausted() {
    let program = variant_program(100);
    let input_bytes = Value::Index(7).retained_bytes();
    // Root and Local input bindings consume the entire fresh allowance. Check
    // shared and per-instance exhaustion, including a partial reservation that
    // must be released without allocation.
    for (shared_total, instance_total) in [
        (2 * input_bytes, 1024 * 1024),
        (2 * input_bytes + 1, 1024 * 1024),
        (1024 * 1024, 2 * input_bytes),
        (1024 * 1024, 2 * input_bytes + 1),
    ] {
        let ledger = ExecutionLedger::new(
            ValueBudget {
                live_bytes: 1024 * 1024,
                total_bytes: shared_total,
            },
            WorkBudget::default(),
        );
        let mut runner = variant_runner(&program, instance_total, Some(ledger.clone()));
        let probe = PayloadProbe::start(100);
        let stopped = matches!(runner.execute(), Action::Stopped(s) if s.kind == StopKind::Limit);
        let allocations = probe.count();
        drop(probe);
        assert!(stopped);
        assert_eq!(
            allocations, 0,
            "payload allocated before shared reservation"
        );
        let usage = ledger.snapshot();
        assert_eq!(usage.total_value_bytes, 2 * input_bytes);
        assert_eq!(usage.pending_value_bytes, 0);
        assert_eq!(usage.pending_logical_bytes, 0);
        assert_eq!(usage.live_reserved_bytes, 0);
        assert_eq!(usage.logical_bytes, 0);
        assert_eq!(runner.backend().active_frames(), 0);
    }
}

#[test]
fn shared_variant_allocates_with_capacity_and_settles_its_reservation() {
    for elements in [0, 100] {
        let program = variant_program(elements);
        let ledger = ExecutionLedger::new(
            ValueBudget {
                live_bytes: 1024 * 1024,
                total_bytes: 1024 * 1024,
            },
            WorkBudget::default(),
        );
        let mut runner = variant_runner(&program, 1024 * 1024, Some(ledger.clone()));
        let probe = PayloadProbe::start(elements);
        let returned = matches!(runner.execute(), Action::Returned(_));
        let allocations = probe.count();
        drop(probe);
        assert!(returned);
        if elements != 0 {
            assert!(
                allocations > 0,
                "probe must observe an admitted payload Vec"
            );
        }
        let [Value::Variant(value)] = runner.returned_values().unwrap() else {
            panic!("expected native variant");
        };
        assert_eq!(value.alternative(), 0);
        assert_eq!(value.payload().len(), elements);
        assert!(value.payload().iter().all(|v| matches!(v, Value::Index(7))));
        assert_eq!(
            ledger.snapshot().total_value_bytes,
            runner.usage().total_value_bytes
        );
        assert_eq!(ledger.snapshot().pending_value_bytes, 0);
        assert_eq!(ledger.snapshot().pending_logical_bytes, 0);
        assert_eq!(ledger.snapshot().logical_bytes, 0);
        assert_eq!(runner.backend().active_frames(), 0);
        drop(runner);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }
}

#[test]
fn non_shared_variant_keeps_actual_allocation_budget_semantics() {
    let program = variant_program(100);
    let mut reference = variant_runner(&program, 1024 * 1024, None);
    assert!(matches!(reference.execute(), Action::Returned(_)));
    let actual = reference.usage().total_value_bytes;
    let mut exact = variant_runner(&program, actual, None);
    assert!(matches!(exact.execute(), Action::Returned(_)));
    assert_eq!(exact.usage(), reference.usage());
    assert_eq!(exact.backend().active_frames(), 0);
}
