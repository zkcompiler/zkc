//! Total word arithmetic through independent runtime admission and the CPU.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use support::{Controlled, backend, one, program};
use zkc_cpu::{Policy, Value};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Action, Backend, OperationBinding, Program, Stop, Usage, Value as RuntimeValue, ValueBudget,
    WorkBudget,
};

const OPERATIONS: [&str; 4] = [
    "index.wrapping_add",
    "index.wrapping_sub",
    "index.bit_and",
    "index.logical_shift_right",
];
const MODULUS: u128 = 1u128 << 64;

fn binding(name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![],
        implementation: format!("native/{name}"),
        physical_arguments: vec![],
    }
}

// Arithmetic digit extraction is independent of the CPU's bitwise operator.
fn intersection(mut a: u64, mut b: u64) -> u64 {
    let mut result = 0u128;
    let mut weight = 1u128;
    for _ in 0..64 {
        if a % 2 == 1 && b % 2 == 1 {
            result += weight;
        }
        a /= 2;
        b /= 2;
        weight *= 2;
    }
    result as u64
}

fn reference(name: &str, a: u64, b: u64) -> u64 {
    match name {
        "index.wrapping_add" => ((u128::from(a) + u128::from(b)) % MODULUS) as u64,
        "index.wrapping_sub" => ((u128::from(a) + MODULUS - u128::from(b)) % MODULUS) as u64,
        "index.bit_and" => intersection(a, b),
        "index.logical_shift_right" if b < 64 => (u128::from(a) / 2u128.pow(b as u32)) as u64,
        "index.logical_shift_right" => 0,
        _ => panic!("unknown total operation"),
    }
}

#[test]
fn every_total_operation_matches_independent_word_arithmetic() {
    let values = [
        0,
        1,
        2,
        3,
        6,
        7,
        8,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut cpu = backend(Policy::default());
    for name in OPERATIONS {
        let selected = binding(name);
        assert_eq!(
            cpu.binding_signature(&selected).unwrap(),
            selected.signature().unwrap()
        );
        for a in values {
            for b in values.into_iter().chain([63, 64, 65]) {
                let (result, next) = one(
                    cpu,
                    selected.clone(),
                    &[],
                    vec![Value::Index(a), Value::Index(b)],
                );
                cpu = next;
                assert!(
                    matches!(result.unwrap().as_slice(), [Value::Index(n)] if *n == reference(name, a, b)),
                    "{name}({a},{b})"
                );
            }
        }
    }
}

fn pair_program() -> Vec<u8> {
    let index = Value::Index(0).physical_type();
    program(
        &[
            binding("index.constant"),
            binding("index.logical_shift_right"),
            binding("index.wrapping_sub"),
            binding("index.bit_and"),
            binding("index.wrapping_add"),
        ],
        &[index.clone(), index.clone()],
        vec![
            json!(["op", "one", "b0", ["1"], [], ["one"]]),
            json!(["op", "half", "b1", [], ["a0", "one"], ["half"]]),
            json!(["op", "mask", "b2", [], ["half", "one"], ["mask"]]),
            json!(["op", "low", "b3", [], ["a1", "mask"], ["low"]]),
            json!(["op", "high", "b4", [], ["low", "half"], ["high"]]),
        ],
        &[index.clone(), index],
        &["low".into(), "high".into()],
    )
}

#[test]
fn composed_map_is_total_for_zero_odd_nonpower_and_maximum_shapes() {
    let bytes = pair_program();
    let mut cpu = backend(Policy::default());
    for n in [0, 1, 2, 3, 6, 7, 8, 16, 1 << 63, u64::MAX - 1, u64::MAX] {
        for i in [0, 1, n.saturating_sub(1), n, u64::MAX] {
            let (result, next) =
                support::run_program(cpu, &bytes, vec![Value::Index(n), Value::Index(i)]);
            cpu = next;
            let h = n / 2;
            let mask = ((u128::from(h) + MODULUS - 1) % MODULUS) as u64;
            let low = intersection(i, mask);
            let high = ((u128::from(low) + u128::from(h)) % MODULUS) as u64;
            assert!(
                matches!(result.unwrap().as_slice(), [Value::Index(a), Value::Index(b)] if (*a,*b)==(low,high))
            );
            if n >= 2 {
                assert!(low < n && high < n);
            } else {
                assert_eq!((low, high), (i, i));
            }
        }
    }
    // An independently specified modulo pairing agrees on every small power.
    for n in [2, 4, 8, 16, 32, 64] {
        for i in 0..2 * n {
            let (result, next) =
                support::run_program(cpu, &bytes, vec![Value::Index(n), Value::Index(i)]);
            cpu = next;
            let low = i % (n / 2);
            assert!(
                matches!(result.unwrap().as_slice(), [Value::Index(a), Value::Index(b)] if (*a,*b)==(low,low+n/2))
            );
        }
    }
}

#[test]
fn checked_arithmetic_and_exact_binding_refusals_are_preserved() {
    for (name, a, b, code) in [
        ("index.add", u64::MAX, 1, "refused:index-overflow"),
        ("index.sub", 0, 1, "refused:index-underflow"),
        ("index.div", 1, 0, "refused:index-zero-divisor"),
        ("index.mod", 1, 0, "refused:index-zero-divisor"),
    ] {
        assert_eq!(
            one(
                backend(Policy::default()),
                binding(name),
                &[],
                vec![Value::Index(a), Value::Index(b)]
            )
            .0
            .unwrap_err(),
            code
        );
    }
    for name in OPERATIONS {
        let mut selected = binding(name);
        selected.arguments.push("bls12-381.fr".into());
        assert!(selected.signature().is_err());
        assert!(
            backend(Policy::default())
                .binding_signature(&selected)
                .is_none()
        );
        selected = binding(name);
        selected.implementation = "native/index.add".into();
        assert!(zkc_cpu::cpu_contracts().resolve(selected).is_err());

        let mut cpu = Controlled::new(backend(Policy::default()));
        cpu.attributes = Some(vec!["1".into()]);
        assert_eq!(
            one(
                cpu,
                binding(name),
                &[],
                vec![Value::Index(1), Value::Index(1)]
            )
            .0
            .unwrap_err(),
            "refused:kernel-attributes"
        );
        let mut cpu = Controlled::new(backend(Policy::default()));
        cpu.substitute = Some(Value::Bool(true));
        assert_eq!(
            one(
                cpu,
                binding(name),
                &[],
                vec![Value::Index(1), Value::Index(1)]
            )
            .0
            .unwrap_err(),
            "refused:kernel-operands"
        );
        let mut cpu = Controlled::new(backend(Policy::default()));
        cpu.output_limit = Some(0);
        assert_eq!(
            one(
                cpu,
                binding(name),
                &[],
                vec![Value::Index(1), Value::Index(1)]
            )
            .0
            .unwrap_err(),
            "exhausted:output-bytes"
        );
    }
}

fn measured(name: &str, work: WorkBudget) -> (Result<Vec<Value>, Stop>, Usage) {
    let index = Value::Index(0).physical_type();
    let bytes = program(
        &[binding(name)],
        &[index.clone(), index.clone()],
        vec![json!(["op", "word", "b0", [], ["a0", "a1"], ["out"]])],
        &[index],
        &["out".into()],
    );
    let admitted = Program::decode(&bytes, zkc_cpu::cpu_contracts()).unwrap();
    let cpu = backend(Policy::default());
    admitted.check_installation(&cpu).unwrap();
    let mut runner = Runner::new_with_budgets(
        &admitted,
        "main",
        "P",
        "session",
        cpu,
        vec![Value::Index(u64::MAX), Value::Index(1)],
        ValueBudget::default(),
        work,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    loop {
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
            Action::Returned(values) => return (Ok(values), runner.usage()),
            Action::Stopped(stop) => return (Err(stop), runner.usage()),
            other => panic!("unexpected {other:?}"),
        }
    }
}

#[test]
fn total_words_keep_ordinary_instruction_and_value_work_charges() {
    let (baseline, expected) = measured("index.div", WorkBudget::default());
    baseline.unwrap();
    assert!(
        expected.instructions > 0 && expected.logical_bytes > 0 && expected.total_value_bytes > 0
    );
    for name in OPERATIONS {
        let (result, usage) = measured(name, WorkBudget::default());
        result.unwrap();
        assert_eq!(usage, expected, "{name}");
        for work in [
            WorkBudget {
                instructions: expected.instructions - 1,
                ..WorkBudget::default()
            },
            WorkBudget {
                logical_bytes: expected.logical_bytes - 1,
                ..WorkBudget::default()
            },
        ] {
            assert!(measured(name, work).0.is_err(), "uncharged {name}");
        }
    }
}
