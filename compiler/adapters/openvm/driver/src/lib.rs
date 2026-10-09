//! Differential corpus for the selected upstream subsystem. The adapter,
//! upstream recorder/DAG/debug checkers, and two native Bundle evaluators
//! agree on explicit traces and forgeries; this is finite relation evidence.
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};
use zkc_openvm_relation::bundle::{Data, Outcome, carriers, evaluate};
use zkc_openvm_relation::capture::{capture, export};
use zkc_openvm_relation::field::{F, decimal};
use zkc_openvm_relation::model::Export;
use zkc_openvm_relation::reference::{
    dag_values, recorder_residuals, unbalanced, upstream_accepts, upstream_balanced,
};
use zkc_openvm_relation::slice::{
    BRANCH, Branch, MEMORY, Parameters, Program, RANGE, Registers, Slice, Step,
};

pub struct Case {
    pub name: String,
    pub carriers: [Value; 4],
    pub outcome: Outcome,
}

fn step(op: Branch, rs1: u32, rs2: u32, imm: i32) -> Step {
    Step { op, rs1, rs2, imm }
}

pub fn program() -> Program {
    Program {
        steps: vec![
            step(Branch::Beq, 4, 8, 8),
            step(Branch::Bne, 4, 12, 4), // skipped
            step(Branch::Bne, 4, 12, 8),
            step(Branch::Beq, 4, 12, -4), // skipped
            step(Branch::Beq, 12, 16, 4),
        ],
        exit_code: 0,
    }
}
pub fn registers() -> Registers {
    Registers(vec![
        (4, [1, 2, 3, 4]),
        (8, [1, 2, 3, 4]),
        (12, [1, 2, 3, 5]),
    ])
}

/// Compare nonzero scoped residuals and exact field-weighted bus balances.
/// Native reports also contain zero residuals and balanced keys, which are
/// filtered only after the two complete native reports have been compared.
pub fn check_native(case: &Case, report: &Value) {
    assert_eq!(report["accepted"], true, "{}: {report}", case.name);
    let result = &report["result"];
    assert_eq!(
        result["satisfied"],
        case.outcome.satisfied(),
        "{}",
        case.name
    );
    let residuals: Vec<Value> = result["residuals"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r[3] != "0")
        .cloned()
        .collect();
    let expected: Vec<Value> = case
        .outcome
        .residuals
        .iter()
        .map(|(t, a, r, v)| json!([t, a, r, decimal(*v)]))
        .collect();
    // The native evaluator and the reference enumerate rows differently.
    let sorted = |values: Vec<Value>| {
        let mut values: Vec<String> = values.into_iter().map(|v| v.to_string()).collect();
        values.sort();
        values
    };
    assert_eq!(
        sorted(residuals),
        sorted(expected),
        "{} residuals",
        case.name
    );
    let balances: Vec<Value> = result["balances"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|b| b[5] == false)
        .map(|b| {
            assert_eq!(b[0], "field-balance");
            assert_eq!(b[2], Value::Null);
            json!([b[1], b[3], b[4]])
        })
        .collect();
    let expected: Vec<Value> = case
        .outcome
        .unbalanced
        .iter()
        .map(|(b, t, v)| {
            json!([
                b,
                t.iter().map(|x| decimal(*x)).collect::<Vec<_>>(),
                decimal(*v)
            ])
        })
        .collect();
    assert_eq!(sorted(balances), sorted(expected), "{} balances", case.name);
    assert_eq!(result["range_failures"], json!([]));
}

/// Capture once, then perturb each public, each first/last witness column,
/// and each cached program column, plus optional table omissions. Some
/// unused padding columns legitimately remain unconstrained; the corpus
/// records that outcome and checks it against the upstream implementation.
pub fn corpus() -> (Export, Vec<Case>) {
    let slice = Slice::new(Parameters::default()).unwrap();
    let captured = capture(&slice).unwrap();
    let exported = export(&slice, &captured).unwrap();
    let execution = slice.execute(&program(), &registers()).unwrap();
    let honest = Data::from_execution(&exported, &execution);
    let mut inputs = vec![("honest".into(), honest.clone())];
    for (name, p, r) in [
        (
            "equal-register-fall-through",
            Program {
                steps: vec![
                    step(Branch::Bne, 4, 4, 8),
                    step(Branch::Bne, 8, 8, -4),
                    step(Branch::Bne, 12, 12, 8),
                ],
                exit_code: 7,
            },
            Registers::default(),
        ),
        (
            "fall-through-and-boundary-register",
            Program {
                steps: vec![
                    step(Branch::Beq, 120, 124, -4),
                    step(Branch::Bne, 120, 120, 8),
                    step(Branch::Beq, 124, 124, 4),
                ],
                exit_code: 3,
            },
            Registers(vec![(120, [255, 0, 128, 1]), (124, [254, 0, 128, 1])]),
        ),
    ] {
        let run = slice.execute(&p, &r).unwrap();
        inputs.push((name.into(), Data::from_execution(&exported, &run)));
    }
    let honest_count = inputs.len();
    for slot in 0..honest.publics.len() {
        let mut changed = honest.clone();
        changed.publics[slot] += F::ONE;
        inputs.push((format!("public-{slot}"), changed));
    }
    for (t, original) in honest.tables.iter().enumerate() {
        let Some(original) = original else { continue };
        let width = exported.airs[t].groups.last().unwrap().width;
        for row in [0, original.height - 1] {
            for column in 0..width {
                let mut changed = honest.clone();
                changed.tables[t].as_mut().unwrap().main[row * width + column] += F::ONE;
                inputs.push((format!("table-{t}-row-{row}-column-{column}"), changed));
            }
        }
        for (group, values) in original.cached.iter().enumerate() {
            let width = exported.airs[t].groups[group].width;
            assert_eq!(values.len(), original.height * width);
            for column in 0..width {
                let mut changed = honest.clone();
                changed.tables[t].as_mut().unwrap().cached[group][column] += F::ONE;
                inputs.push((format!("configuration-{t}-{group}-{column}"), changed));
            }
        }
    }
    for t in [BRANCH, RANGE, MEMORY] {
        let mut changed = honest.clone();
        changed.tables[t] = None;
        inputs.push((format!("omit-{t}"), changed));
    }
    let interactions: Vec<_> = captured
        .recorder
        .iter()
        .map(|r| r.interactions.clone())
        .collect();
    let mut cases = vec![];
    for (index, (name, data)) in inputs.into_iter().enumerate() {
        let outcome = evaluate(&exported, &data).unwrap();
        let traces = data.traces(&exported).unwrap();
        let mut expected = vec![];
        for (t, trace) in traces.iter().enumerate() {
            let Some(trace) = trace else { continue };
            let residuals = recorder_residuals(&captured.recorder[t].constraints, trace);
            assert_eq!(
                upstream_accepts(&slice.airs()[t], trace),
                residuals.is_empty(),
                "{name} table {t}"
            );
            let by_constraint: BTreeMap<_, _> =
                residuals.iter().map(|(c, r, v)| ((*c, *r), *v)).collect();
            let air = &exported.airs[t];
            for (a, assertion) in air.assertions.iter().enumerate() {
                for row in 0..trace.height() {
                    if assertion.scope.contains(row, trace.height())
                        && let Some(value) = by_constraint.get(&(assertion.constraint, row))
                    {
                        expected.push((t, a, row, *value));
                    }
                }
            }
            // Every original constraint, including selector classes omitted
            // as identically zero, agrees with the canonical keygen DAG.
            let dag = dag_values(&captured.vk.inner.per_air[t].symbolic_constraints, trace);
            for (c, node) in air.recorder_constraints.iter().enumerate() {
                let position = air
                    .dag
                    .constraint_idx
                    .iter()
                    .position(|n| n == node)
                    .unwrap();
                for (_, row, value) in dag.iter().filter(|(p, _, _)| *p == position) {
                    assert_eq!(
                        *value,
                        by_constraint.get(&(c, *row)).copied().unwrap_or(F::ZERO),
                        "{name} DAG {t}/{c}/{row}"
                    );
                }
            }
        }
        expected.sort_by_key(|(t, a, r, _)| (*t, *r, *a));
        assert_eq!(outcome.residuals, expected, "{name} scoped residuals");
        let mut expected: Vec<_> = unbalanced(&interactions, &traces)
            .into_iter()
            .map(|(bus, tuple, sum)| {
                let channel = exported.buses.iter().position(|b| b.index == bus).unwrap();
                (channel, tuple, sum)
            })
            .collect();
        expected.sort_by_key(|(c, t, _)| {
            (
                *c,
                t.iter().map(|v| v.as_canonical_u32()).collect::<Vec<_>>(),
            )
        });
        assert_eq!(outcome.unbalanced, expected, "{name} buses");
        if index < honest_count {
            assert!(outcome.satisfied(), "{name}");
            assert!(upstream_balanced(&slice, &interactions, &traces));
        }
        cases.push(Case {
            name,
            carriers: carriers(&exported, &data).unwrap(),
            outcome,
        });
    }
    assert!(cases.iter().filter(|c| !c.outcome.satisfied()).count() > 40);
    for name in ["omit-2", "omit-3", "omit-4"] {
        assert!(
            !cases
                .iter()
                .find(|c| c.name == name)
                .unwrap()
                .outcome
                .satisfied()
        );
    }
    (exported, cases)
}

pub fn native_reports(executable: &Path, lines: &[Value]) -> Vec<Value> {
    let input = lines.iter().map(|v| format!("{v}\n")).collect::<String>();
    let mut child = Command::new(executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()).unwrap());
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap();
    assert!(
        output.status.success(),
        "{}: {}",
        executable.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    let reports: Vec<Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    assert_eq!(reports.len(), lines.len());
    reports
}
