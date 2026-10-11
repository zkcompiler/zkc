//! Persistent sequences through ordinary admitted Local loops and budgets.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use zkc_backends::{NativeBackend, Policy, Sequence, Value};
use zkc_runtime::interactive::{
    Action, LogicalType, OperationBinding, PhysicalType, Runner, StopKind, Usage, ValueBudget,
    WorkBudget, admit_supplied,
};

fn physical(logical: &str) -> PhysicalType {
    PhysicalType::default_for(LogicalType::parse(logical).unwrap()).unwrap()
}
fn binding(operation: &str, element: &str) -> OperationBinding {
    OperationBinding {
        contract: format!("sequence.{operation}"),
        arguments: vec![element.into()],
        implementation: format!("native/sequence.{operation}"),
    }
}
fn collected(record: bool) -> (Vec<u8>, String) {
    let element = if record {
        zkc_test_support::variants::logical("Row", json!([["row", ["index", "index"]]]))
    } else {
        "index".into()
    };
    let mut step = vec![];
    if record {
        step.push(json!([
            "variant",
            "pack",
            physical(&element).spelling(),
            "row",
            ["i", "i"],
            "item"
        ]));
    }
    step.push(json!([
        "op",
        "append",
        "b1",
        [],
        ["state", if record { "item" } else { "i" }],
        ["next"]
    ]));
    step.push(json!(["yield", ["next"]]));
    let program = support::program(
        &[binding("empty", &element), binding("append", &element)],
        &[physical("index"), physical("index")],
        vec![
            json!(["op", "empty", "b0", [], [], ["empty"]]),
            json!([
                "for",
                "collect",
                "i",
                "a0",
                "a1",
                [["state", "empty"]],
                [],
                step,
                ["out"]
            ]),
        ],
        &[physical(&format!("sequence<{element}>"))],
        &["out".into()],
    );
    (program, element)
}
fn drive(
    program: &[u8],
    backend: NativeBackend,
    inputs: Vec<Value>,
    values: ValueBudget,
    work: WorkBudget,
) -> (Result<Vec<Value>, String>, Usage, NativeBackend) {
    let admitted = admit_supplied(program, &backend).unwrap();
    let mut runner = Runner::new_with_budgets(
        &admitted, "main", "P", "session", backend, inputs, values, work,
    )
    .unwrap_or_else(|error| panic!("{}", error.error));
    let outcome = loop {
        runner.advance_local_control().unwrap();
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Returned(values) => break Ok(values),
            Action::Stopped(stop) => {
                break Err(match stop.kind {
                    StopKind::Backend(error) => error.code,
                    other => format!("{other:?}"),
                });
            }
            other => panic!("unexpected {other:?}"),
        }
    };
    let usage = runner.usage();
    let backend = runner.into_backend();
    assert_eq!(backend.active_frames(), 0);
    (outcome, usage, backend)
}

#[test]
fn large_index_and_record_collections_fit_default_budgets() {
    for (record, count) in [(false, 16_384), (true, 8_192)] {
        let (program, _) = collected(record);
        let (result, usage, backend) = drive(
            &program,
            support::backend(Policy::default()),
            vec![Value::Index(0), Value::Index(count)],
            ValueBudget::default(),
            WorkBudget::default(),
        );
        let values = result.unwrap();
        let [Value::Sequence(sequence)] = values.as_slice() else {
            panic!("sequence output")
        };
        assert_eq!(sequence.len(), count as usize);
        for (i, item) in sequence.iter().enumerate() {
            let i = i as u64;
            if record {
                let Value::Variant(item) = item else {
                    panic!("row")
                };
                assert!(
                    matches!(item.payload(), [Value::Index(a), Value::Index(b)] if *a == i && *b == i)
                );
            } else {
                assert!(matches!(item, Value::Index(value) if *value == i));
            }
        }
        assert!(usage.total_value_bytes < ValueBudget::default().total_bytes);
        assert_eq!(
            backend.sequence_work_spent(),
            3 + count * if record { 15 } else { 9 }
        );
    }
}

#[test]
fn retained_input_traversal_charges_only_the_examined_edge() {
    let n = 16_384;
    let program = support::program(
        &[binding("at", "index")],
        &[
            physical("sequence<index>"),
            physical("index"),
            physical("index"),
        ],
        vec![json!([
            "for",
            "read",
            "i",
            "a1",
            "a2",
            [["last", "a1"]],
            ["a0"],
            [
                ["op", "get", "b0", [], ["a0", "i"], ["next"]],
                ["yield", ["next"]]
            ],
            ["out"]
        ])],
        &[physical("index")],
        &["out".into()],
    );
    let sequence = Sequence::new(
        LogicalType::parse("index").unwrap(),
        (0..n).map(Value::Index).collect(),
        &Policy::default(),
    )
    .unwrap();
    let (result, _, backend) = drive(
        &program,
        support::backend(Policy::default()),
        vec![Value::Sequence(sequence), Value::Index(0), Value::Index(n)],
        ValueBudget::default(),
        WorkBudget::default(),
    );
    assert!(matches!(result.unwrap().as_slice(), [Value::Index(value)] if *value == n - 1));
    assert_eq!(backend.sequence_work_spent(), 9 * n);
}

#[test]
fn collection_budget_failures_release_all_carried_storage() {
    let (program, _) = collected(true);
    let limits = [
        (
            ValueBudget {
                live_bytes: 32_768,
                ..ValueBudget::default()
            },
            WorkBudget::default(),
            u64::MAX,
            "exhausted:output-bytes",
        ),
        (
            ValueBudget {
                total_bytes: 32_768,
                ..ValueBudget::default()
            },
            WorkBudget::default(),
            u64::MAX,
            "exhausted:output-bytes",
        ),
        (
            ValueBudget::default(),
            WorkBudget {
                instructions: 30,
                ..WorkBudget::default()
            },
            u64::MAX,
            "Limit",
        ),
        (
            ValueBudget::default(),
            WorkBudget {
                iterations: 8,
                ..WorkBudget::default()
            },
            u64::MAX,
            "Limit",
        ),
        (
            ValueBudget::default(),
            WorkBudget::default(),
            48,
            "exhausted:sequence-work",
        ),
    ];
    for (values, work, sequence_work, expected) in limits {
        let (result, usage, backend) = drive(
            &program,
            support::backend(Policy::default()).with_sequence_work_limit(sequence_work),
            vec![Value::Index(0), Value::Index(128)],
            values,
            work,
        );
        assert_eq!(result.unwrap_err(), expected, "{usage:?}");
        assert_eq!(usage.live_value_bytes, 0);
        assert!(backend.sequence_work_spent() <= sequence_work);
    }
}
