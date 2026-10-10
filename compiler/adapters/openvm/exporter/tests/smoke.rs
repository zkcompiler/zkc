//! Honest execution through the pinned upstream executor and checkers, and
//! the lowering on arbitrary traces.
use zkc_openvm_relation::reference::{
    recorder, recorder_residuals, unbalanced, upstream_accepts, upstream_balanced,
};
use zkc_openvm_relation::slice::{
    AIR_NAMES, Branch, MEMORY, Parameters, Program, Registers, Slice, Step,
};

#[test]
fn honest_execution_satisfies_upstream() {
    let slice = Slice::new(Parameters::default()).unwrap();
    let program = Program {
        steps: vec![
            Step {
                op: Branch::Beq,
                rs1: 4,
                rs2: 8,
                imm: 8,
            }, // equal -> jump to 8
            Step {
                op: Branch::Bne,
                rs1: 4,
                rs2: 12,
                imm: 4,
            }, // skipped
            Step {
                op: Branch::Bne,
                rs1: 4,
                rs2: 12,
                imm: 8,
            }, // at 8: not equal -> jump to 16
            Step {
                op: Branch::Beq,
                rs1: 4,
                rs2: 12,
                imm: -4,
            }, // skipped
            Step {
                op: Branch::Beq,
                rs1: 12,
                rs2: 16,
                imm: 4,
            }, // at 16: 12 vs 16 differ -> fall through to 20
        ],
        exit_code: 0,
    };
    let registers = Registers(vec![
        (4, [1, 2, 3, 4]),
        (8, [1, 2, 3, 4]),
        (12, [1, 2, 3, 5]),
    ]);
    let execution = slice.execute(&program, &registers).unwrap();
    for (i, trace) in execution.traces.iter().enumerate() {
        let shape = trace.as_ref().map(|t| {
            (
                t.height(),
                t.common_main.width,
                t.cached_mains.len(),
                t.public_values.len(),
            )
        });
        println!("{}: {:?}", AIR_NAMES[i], shape);
    }
    println!(
        "from {:?} to {:?} exit {} freqs {:?} touched {:?}",
        execution.from_state,
        execution.to_state,
        execution.exit_code,
        execution.frequencies,
        execution.touched
    );
    let recorders: Vec<_> = slice.airs().iter().map(recorder).collect();
    for (i, (air, trace)) in slice.airs().iter().zip(&execution.traces).enumerate() {
        let Some(trace) = trace else { continue };
        let residuals = recorder_residuals(&recorders[i].constraints, trace);
        println!(
            "{}: {} constraints, {} interactions, residuals {:?}",
            AIR_NAMES[i],
            recorders[i].constraints.len(),
            recorders[i].interactions.len(),
            residuals
        );
        assert!(residuals.is_empty(), "{}", AIR_NAMES[i]);
        assert!(upstream_accepts(air, trace), "{}", AIR_NAMES[i]);
    }
    let interactions: Vec<_> = recorders.iter().map(|r| r.interactions.clone()).collect();
    let open = unbalanced(&interactions, &execution.traces);
    println!("unbalanced: {:?}", open);
    assert!(open.is_empty());
    assert!(upstream_balanced(&slice, &interactions, &execution.traces));
}

#[test]
fn capture_and_lowering_agree_with_upstream() {
    use zkc_openvm_relation::bundle::{Data, carriers, evaluate};
    use zkc_openvm_relation::capture::{capture, export};
    let slice = Slice::new(Parameters::default()).unwrap();
    let cap = capture(&slice).unwrap();
    let exp = export(&slice, &cap).unwrap();
    for air in &exp.airs {
        println!(
            "{}: {} ({} groups, {} inputs, {} nodes, {} assertions, {} vacuous, {} interactions, need_rot {}, degree {}, unused {:?}, dag nodes {}, dag constraints {}, columns {:?})",
            air.name,
            air.upstream_type,
            air.groups.len(),
            air.inputs.len(),
            air.arena.nodes().len(),
            air.assertions.len(),
            air.vacuous.len(),
            air.interactions.len(),
            air.need_rot,
            air.max_constraint_degree,
            air.unused_variables,
            air.dag.nodes.len(),
            air.dag.constraint_idx.len(),
            air.column_names.as_ref().map(|c| c.len())
        );
        for a in &air.assertions {
            print!(" c{}/{}", a.constraint, a.scope.name());
        }
        println!();
    }
    // The memory partner asserts nothing: its messages and counts are free
    // witness data, so the memory bus constrains no read.
    assert!(cap.recorder[MEMORY].constraints.is_empty());
    assert!(exp.airs[MEMORY].assertions.is_empty());
    println!("buses {:?}", exp.buses);
    println!("height constraints {:?}", exp.trace_height_constraints);
    println!(
        "pre-hash {:?} l_skip {} degree {} logup {} {}",
        exp.vk_pre_hash,
        exp.l_skip,
        exp.max_constraint_degree,
        exp.max_interaction_count,
        exp.log_max_message_length
    );
    let program = Program {
        steps: vec![
            Step {
                op: Branch::Beq,
                rs1: 4,
                rs2: 8,
                imm: 8,
            },
            Step {
                op: Branch::Bne,
                rs1: 4,
                rs2: 12,
                imm: 4,
            },
            Step {
                op: Branch::Bne,
                rs1: 4,
                rs2: 12,
                imm: 8,
            },
            Step {
                op: Branch::Beq,
                rs1: 4,
                rs2: 12,
                imm: -4,
            },
            Step {
                op: Branch::Beq,
                rs1: 12,
                rs2: 16,
                imm: 4,
            },
        ],
        exit_code: 0,
    };
    let registers = Registers(vec![
        (4, [1, 2, 3, 4]),
        (8, [1, 2, 3, 4]),
        (12, [1, 2, 3, 5]),
    ]);
    let execution = slice.execute(&program, &registers).unwrap();
    let data = Data::from_execution(&exp, &execution);
    let outcome = evaluate(&exp, &data).unwrap();
    println!("outcome {:?}", outcome);
    assert!(outcome.satisfied());
    let c = carriers(&exp, &data).unwrap();
    let line = serde_json::to_string(&c).unwrap();
    println!("carrier line bytes {}", line.len());
    assert!(line.len() < 1024 * 1024);
}

/// Selector lowering on deterministic arbitrary traces of every table at
/// heights with and without interior rows, ignoring the Bundle height
/// policy: per constraint, assertion scopes and vacuous classes partition
/// the row classes; every in-scope lowered output equals the recorder value,
/// which also equals the verifying-key DAG value; and the recorder value is
/// zero on every class marked vacuous.
#[test]
fn lowered_assertions_equal_recorder_constraints_on_arbitrary_traces() {
    use openvm_stark_backend::p3_matrix::dense::RowMajorMatrix;
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::collections::{BTreeMap, BTreeSet};
    use zkc_openvm_relation::bundle::{TableData, row_outputs};
    use zkc_openvm_relation::capture::{capture, export};
    use zkc_openvm_relation::field::F;
    use zkc_openvm_relation::model::RowClass;
    use zkc_openvm_relation::reference::{dag_values, recorder_values};
    use zkc_openvm_relation::slice::Trace;
    let slice = Slice::new(Parameters::default()).unwrap();
    let cap = capture(&slice).unwrap();
    let exp = export(&slice, &cap).unwrap();
    let mut rng = StdRng::seed_from_u64(7);
    let mut arbitrary = |n: usize| -> Vec<F> {
        (0..n)
            .map(|_| F::from_u32(rng.random_range(0..F::ORDER_U32)))
            .collect()
    };
    let mut nonzero = BTreeSet::new();
    let mut vacuous_rows = BTreeSet::new();
    for (t, air) in exp.airs.iter().enumerate() {
        for c in 0..air.recorder_constraints.len() {
            for class in RowClass::ALL {
                let asserted = air
                    .assertions
                    .iter()
                    .filter(|a| a.constraint == c && a.scope.covers(class))
                    .count();
                let vacuous = usize::from(air.vacuous.contains(&(c, class)));
                assert_eq!(
                    asserted + vacuous,
                    1,
                    "{} constraint {c} {class:?}",
                    air.name
                );
            }
        }
        let (main, cached) = air.groups.split_last().unwrap();
        for height in [2, 4, 8] {
            let table = TableData {
                height,
                cached: cached.iter().map(|g| arbitrary(height * g.width)).collect(),
                main: arbitrary(height * main.width),
            };
            let publics = arbitrary(exp.publics.len());
            let trace = Trace {
                cached_mains: table
                    .cached
                    .iter()
                    .zip(cached)
                    .map(|(values, g)| RowMajorMatrix::new(values.clone(), g.width))
                    .collect(),
                common_main: RowMajorMatrix::new(table.main.clone(), main.width),
                public_values: exp
                    .publics
                    .iter()
                    .zip(&publics)
                    .filter(|((_, a, _), _)| *a == t)
                    .map(|(_, v)| *v)
                    .collect(),
            };
            let recorded: BTreeMap<_, _> = recorder_values(&cap.recorder[t].constraints, &trace)
                .into_iter()
                .map(|(c, row, v)| ((c, row), v))
                .collect();
            let dag: BTreeMap<_, _> =
                dag_values(&cap.vk.inner.per_air[t].symbolic_constraints, &trace)
                    .into_iter()
                    .map(|(p, row, v)| ((p, row), v))
                    .collect();
            for row in 0..height {
                for (c, node) in air.recorder_constraints.iter().enumerate() {
                    let position = air
                        .dag
                        .constraint_idx
                        .iter()
                        .position(|n| n == node)
                        .unwrap();
                    assert_eq!(
                        dag[&(position, row)],
                        recorded[&(c, row)],
                        "{} DAG c{c}",
                        air.name
                    );
                }
                let outputs = row_outputs(air, &table, &publics, row);
                for (a, assertion) in air.assertions.iter().enumerate() {
                    if assertion.scope.contains(row, height) {
                        let value = outputs[assertion.output];
                        assert_eq!(
                            value,
                            recorded[&(assertion.constraint, row)],
                            "{} assertion c{} {} row {row} of {height}",
                            air.name,
                            assertion.constraint,
                            assertion.scope.name()
                        );
                        if value != F::ZERO {
                            nonzero.insert((t, a));
                        }
                    }
                }
                let class = RowClass::of(row, height);
                for &(c, vacuous) in air.vacuous.iter().filter(|(_, v)| *v == class) {
                    assert_eq!(
                        recorded[&(c, row)],
                        F::ZERO,
                        "{} vacuous c{c} row {row}",
                        air.name
                    );
                    vacuous_rows.insert((t, c, vacuous));
                }
            }
        }
    }
    // Comparisons ran on nonzero values and on every vacuous class.
    for (t, air) in exp.airs.iter().enumerate() {
        for a in 0..air.assertions.len() {
            assert!(nonzero.contains(&(t, a)), "{} assertion {a}", air.name);
        }
        for &(c, class) in &air.vacuous {
            assert!(vacuous_rows.contains(&(t, c, class)));
        }
    }
}

/// Upstream `count_weight` is a trace-height coefficient, not a count
/// bound: the Bundle declares none, and the provenance report keeps every
/// weight with the height constraints that use it.
#[test]
fn count_weights_stay_provenance_and_bundle_declares_no_count_bound() {
    use serde_json::{Value, json};
    use zkc_openvm_relation::bundle::bundle;
    use zkc_openvm_relation::capture::{capture, export};
    let slice = Slice::new(Parameters::default()).unwrap();
    let cap = capture(&slice).unwrap();
    let exp = export(&slice, &cap).unwrap();
    let carrier = bundle(&exp).unwrap();
    let records: Vec<&Value> = carrier[3]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|table| table[8].as_array().unwrap())
        .collect();
    assert_eq!(
        records.len(),
        exp.airs.iter().map(|a| a.interactions.len()).sum::<usize>()
    );
    for record in records {
        assert_eq!(record[0], "field-balance");
        assert_eq!(record[6], Value::Null);
    }
    let report = exp.to_value().unwrap();
    let mut positive = 0;
    for (t, air) in report["airs"].as_array().unwrap().iter().enumerate() {
        let upstream: Vec<u64> = cap.vk.inner.per_air[t]
            .symbolic_constraints
            .interactions
            .iter()
            .map(|x| u64::from(x.count_weight))
            .collect();
        positive += upstream.iter().filter(|w| **w > 0).count();
        for recorded in [&air["interactions"], &air["dag"]["interactions"]] {
            let weights: Vec<u64> = recorded
                .as_array()
                .unwrap()
                .iter()
                .map(|x| x[3].as_u64().unwrap())
                .collect();
            assert_eq!(weights, upstream, "{}", air["name"]);
        }
    }
    assert!(positive > 0);
    let heights: Vec<Value> = cap
        .vk
        .inner
        .trace_height_constraints
        .iter()
        .map(|c| json!([c.coefficients, c.threshold]))
        .collect();
    assert!(!heights.is_empty());
    assert_eq!(report["trace_height_constraints"], Value::Array(heights));
}
