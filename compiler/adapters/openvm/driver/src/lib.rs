//! Differential corpus for the selected upstream subsystem. Upstream is the
//! oracle: its recorder constraints on every row, its logical bus messages
//! and its debug checkers, read without the lowering. The adapter's Bundle
//! reading and two native Bundle evaluators must agree with it exactly on
//! explicit traces and forgeries; this is finite relation evidence.
use openvm_stark_backend::interaction::SymbolicInteraction;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};
use zkc_openvm_relation::bundle::{Data, Outcome, carriers, evaluate};
use zkc_openvm_relation::capture::{Capture, capture, export};
use zkc_openvm_relation::field::{F, decimal};
use zkc_openvm_relation::model::Export;
use zkc_openvm_relation::reference::{
    dag_values, recorder_residuals, unbalanced, upstream_accepts, upstream_balanced,
};
use zkc_openvm_relation::refusal::{self, Refusal};
use zkc_openvm_relation::slice::{
    BRANCH, Branch, MEMORY, Parameters, Program, RANGE, Registers, Slice, Step, Trace,
};

/// The pinned upstream relation every comparison is checked against.
pub struct Upstream {
    pub slice: Slice,
    pub capture: Capture,
    interactions: Vec<Vec<SymbolicInteraction<F>>>,
}

impl Upstream {
    pub fn new(parameters: Parameters) -> refusal::Result<Self> {
        let slice = Slice::new(parameters)?;
        let capture = capture(&slice)?;
        let interactions = capture
            .recorder
            .iter()
            .map(|r| r.interactions.clone())
            .collect();
        Ok(Self {
            slice,
            capture,
            interactions,
        })
    }

    /// The adapter's lowering of the capture.
    pub fn export(&self) -> refusal::Result<Export> {
        export(&self.slice, &self.capture)
    }

    /// Upstream's reading of the present traces. Panics when the upstream
    /// readings disagree among themselves: `check_constraints` with the
    /// recorder residuals, the verifying-key DAG with the recorder on any
    /// constraint and row, or `check_logup` with the logical interactions.
    pub fn oracle(&self, traces: &[Option<Trace>]) -> Oracle {
        let mut residuals = vec![];
        let mut accepted = true;
        for (t, trace) in traces.iter().enumerate() {
            let Some(trace) = trace else { continue };
            let found = recorder_residuals(&self.capture.recorder[t].constraints, trace);
            let accepts = upstream_accepts(&self.slice.airs()[t], trace);
            assert_eq!(accepts, found.is_empty(), "table {t} check_constraints");
            accepted &= accepts;
            let by_constraint: BTreeMap<_, _> =
                found.iter().map(|(c, r, v)| ((*c, *r), *v)).collect();
            let dag = &self.capture.vk.inner.per_air[t].symbolic_constraints;
            let positions: Vec<usize> = self.capture.constraint_nodes[t]
                .iter()
                .map(|node| {
                    let constraints = &dag.constraints.constraint_idx;
                    constraints.iter().position(|n| n == node).unwrap()
                })
                .collect();
            let dag: BTreeMap<_, _> = dag_values(dag, trace)
                .into_iter()
                .map(|(p, r, v)| ((p, r), v))
                .collect();
            for row in 0..trace.height() {
                for (c, position) in positions.iter().enumerate() {
                    assert_eq!(
                        dag[&(*position, row)],
                        by_constraint.get(&(c, row)).copied().unwrap_or(F::ZERO),
                        "DAG {t}/{c}/{row}"
                    );
                }
            }
            residuals.extend(found.into_iter().map(|(c, row, v)| (t, c, row, v)));
        }
        let unbalanced = unbalanced(&self.interactions, traces);
        let balanced = upstream_balanced(&self.slice, &self.interactions, traces);
        assert_eq!(balanced, unbalanced.is_empty(), "check_logup");
        Oracle {
            residuals,
            unbalanced,
            accepted: accepted && balanced,
        }
    }
}

/// Upstream's reading of one input, computed without the lowering.
#[derive(Clone, Debug)]
pub struct Oracle {
    /// Nonzero recorder residuals `(table, constraint, row, value)` on every
    /// row of every present table.
    pub residuals: Vec<(usize, usize, usize, F)>,
    /// Unbalanced `(bus index, tuple, sum)` of the logical interactions.
    pub unbalanced: Vec<(u16, Vec<F>, F)>,
    /// `check_constraints` accepts every present table and `check_logup`
    /// balances every bus.
    pub accepted: bool,
}

/// How the Bundle reading of an input under an export departs from upstream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Disagreement {
    /// The input is outside the export's data shape.
    Shape(Refusal),
    /// No lowered assertion of the constraint covers a nonzero upstream residual.
    Uncovered {
        table: usize,
        constraint: usize,
        row: usize,
    },
    /// Several lowered assertions of the constraint cover the same row.
    Overlapping {
        table: usize,
        constraint: usize,
        row: usize,
    },
    /// A lowered residual `(table, assertion, row, value)` upstream lacks.
    Spurious(usize, usize, usize, F),
    /// A covered upstream residual `(table, assertion, row, value)` the
    /// lowering does not report.
    Missing(usize, usize, usize, F),
    /// The unbalanced `(channel, tuple, sum)` keys differ.
    Balances {
        upstream: Vec<(usize, Vec<F>, F)>,
        bundle: Vec<(usize, Vec<F>, F)>,
    },
    /// Bundle satisfaction differs from upstream acceptance.
    Satisfaction { bundle: bool, upstream: bool },
}

/// Compare the Bundle reading of `data` under `exported` with upstream and
/// return the outcome upstream implies. Every nonzero upstream residual must
/// be reported, with its value, by exactly one lowered assertion of its
/// constraint whose scope contains the row, and the lowering reports nothing
/// else. Unbalanced keys must equal upstream's, and Bundle satisfaction must
/// equal upstream acceptance.
pub fn compare(
    exported: &Export,
    data: &Data,
    oracle: &Oracle,
) -> Result<Outcome, Vec<Disagreement>> {
    let lowered = evaluate(exported, data).map_err(|r| vec![Disagreement::Shape(r)])?;
    let mut disagreements = vec![];
    // Keyed by (table, row, assertion), the evaluator's order.
    let mut expected = BTreeMap::new();
    for &(table, constraint, row, value) in &oracle.residuals {
        let height = data.tables[table].as_ref().unwrap().height;
        let covering: Vec<usize> = exported.airs[table]
            .assertions
            .iter()
            .enumerate()
            .filter(|(_, a)| a.constraint == constraint && a.scope.contains(row, height))
            .map(|(a, _)| a)
            .collect();
        match covering.len() {
            0 => disagreements.push(Disagreement::Uncovered {
                table,
                constraint,
                row,
            }),
            1 => {}
            _ => disagreements.push(Disagreement::Overlapping {
                table,
                constraint,
                row,
            }),
        }
        for a in covering {
            expected.insert((table, row, a), value);
        }
    }
    let reported: BTreeMap<_, _> = lowered
        .residuals
        .iter()
        .map(|&(t, a, row, v)| ((t, row, a), v))
        .collect();
    for (&(t, row, a), &v) in &reported {
        if expected.get(&(t, row, a)) != Some(&v) {
            disagreements.push(Disagreement::Spurious(t, a, row, v));
        }
    }
    for (&(t, row, a), &v) in &expected {
        if reported.get(&(t, row, a)) != Some(&v) {
            disagreements.push(Disagreement::Missing(t, a, row, v));
        }
    }
    let mut unbalanced: Vec<_> = oracle
        .unbalanced
        .iter()
        .map(|(bus, tuple, sum)| {
            let channel = exported.buses.iter().position(|b| b.index == *bus);
            (channel.unwrap(), tuple.clone(), *sum)
        })
        .collect();
    unbalanced.sort_by_key(|(c, t, _)| {
        (
            *c,
            t.iter().map(|v| v.as_canonical_u32()).collect::<Vec<_>>(),
        )
    });
    if lowered.unbalanced != unbalanced {
        disagreements.push(Disagreement::Balances {
            upstream: unbalanced.clone(),
            bundle: lowered.unbalanced.clone(),
        });
    }
    if lowered.satisfied() != oracle.accepted {
        disagreements.push(Disagreement::Satisfaction {
            bundle: lowered.satisfied(),
            upstream: oracle.accepted,
        });
    }
    if !disagreements.is_empty() {
        return Err(disagreements);
    }
    Ok(Outcome {
        residuals: expected
            .into_iter()
            .map(|((t, row, a), v)| (t, a, row, v))
            .collect(),
        unbalanced,
    })
}

pub struct Case {
    pub name: String,
    pub data: Data,
    pub oracle: Oracle,
    pub carriers: [Value; 4],
    /// The outcome upstream implies, which the lowering reproduces.
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

fn honest_runs(slice: &Slice, exported: &Export) -> Vec<(String, Data)> {
    [
        ("honest", program(), registers()),
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
    ]
    .into_iter()
    .map(|(name, p, r)| {
        let run = slice.execute(&p, &r).unwrap();
        (name.to_string(), Data::from_execution(exported, &run))
    })
    .collect()
}

/// Field values unrelated to any execution: a deterministic geometric
/// sequence with an arbitrary ratio, so every value is nonzero.
fn independent(state: &mut F, n: usize) -> Vec<F> {
    (0..n)
        .map(|_| {
            *state *= F::from_u32(0x7654_3210);
            *state
        })
        .collect()
}

/// Perturb each public; each column of each configuration and witness group
/// on the first, the second and the last row; and each optional table's
/// presence. Some unused padding columns legitimately remain unconstrained.
/// A single changed column cannot reach every constraint, for instance a
/// product of two witness factors on a zero padding row, so each of those
/// rows is also replaced by independent values in every group.
fn forgeries(exported: &Export, honest: &Data) -> Vec<(String, Data)> {
    let mut inputs = vec![];
    for slot in 0..honest.publics.len() {
        let mut changed = honest.clone();
        changed.publics[slot] += F::ONE;
        inputs.push((format!("public-{slot}"), changed));
    }
    let mut state = F::ONE;
    for (t, original) in honest.tables.iter().enumerate() {
        let Some(original) = original else { continue };
        // Row 1 is interior above height two and is the next row that the
        // first row's transition constraints read.
        let mut rows = vec![0, 1, original.height - 1];
        rows.dedup();
        let groups = &exported.airs[t].groups;
        for &row in &rows {
            let mut changed = honest.clone();
            let table = changed.tables[t].as_mut().unwrap();
            for (values, group) in table.cached.iter_mut().chain([&mut table.main]).zip(groups) {
                let width = group.width;
                values[row * width..(row + 1) * width]
                    .copy_from_slice(&independent(&mut state, width));
            }
            inputs.push((format!("table-{t}-row-{row}-independent"), changed));
        }
        for (g, group) in groups.iter().enumerate() {
            for &row in &rows {
                for column in 0..group.width {
                    let mut changed = honest.clone();
                    let table = changed.tables[t].as_mut().unwrap();
                    let (values, name) = if g < table.cached.len() {
                        let name = format!("configuration-{t}-{g}-row-{row}-column-{column}");
                        (&mut table.cached[g], name)
                    } else {
                        let name = format!("table-{t}-row-{row}-column-{column}");
                        (&mut table.main, name)
                    };
                    values[row * group.width + column] += F::ONE;
                    inputs.push((name, changed));
                }
            }
        }
    }
    for t in [BRANCH, RANGE, MEMORY] {
        let mut changed = honest.clone();
        changed.tables[t] = None;
        inputs.push((format!("omit-{t}"), changed));
    }
    // The range table's padding row forged as (2^b, b, 2^b, 0) for the
    // largest range b: the transition from the row before, (2^b - 1, b, 2^b),
    // still holds, so only last-row assertions reject a table that offers
    // 2^b as a b-bit value.
    let bits = exported.parameters.range_max_bits as u32;
    let mut changed = honest.clone();
    let range = changed.tables[RANGE].as_mut().unwrap();
    let width = exported.airs[RANGE].groups[0].width;
    let last = (range.height - 1) * width;
    let top = F::from_u32(1 << bits);
    assert_eq!(
        range.main[last - width..last - 1],
        [top - F::ONE, F::from_u32(bits), top]
    );
    range.main[last..last + width].copy_from_slice(&[top, F::from_u32(bits), top, F::ZERO]);
    inputs.push(("range-padding-out-of-range".into(), changed));
    inputs
}

/// Capture once, compare every honest run and forgery with upstream, and
/// keep the outcome upstream implies. Panics on any disagreement.
pub fn corpus() -> (Export, Vec<Case>) {
    let upstream = Upstream::new(Parameters::default()).unwrap();
    let exported = upstream.export().unwrap();
    let honest = honest_runs(&upstream.slice, &exported);
    let forged = forgeries(&exported, &honest[0].1);
    let mut cases = vec![];
    for (name, data) in honest.iter().cloned().chain(forged) {
        let oracle = upstream.oracle(&data.traces(&exported).unwrap());
        let outcome =
            compare(&exported, &data, &oracle).unwrap_or_else(|d| panic!("{name}: {d:?}"));
        cases.push(Case {
            carriers: carriers(&exported, &data).unwrap(),
            name,
            data,
            oracle,
            outcome,
        });
    }
    for case in &cases[..honest.len()] {
        assert!(case.outcome.satisfied(), "{}", case.name);
    }
    assert!(cases.iter().filter(|c| !c.outcome.satisfied()).count() > 40);
    for name in ["omit-2", "omit-3", "omit-4", "range-padding-out-of-range"] {
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
