//! Honest execution through the pinned upstream executor and checkers.
use zkc_openvm_relation::reference::{
    recorder, recorder_residuals, unbalanced, upstream_accepts, upstream_balanced,
};
use zkc_openvm_relation::slice::{AIR_NAMES, Branch, Parameters, Program, Registers, Slice, Step};

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
    use zkc_openvm_relation::reference::{dag_values, recorder_values};
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
    // Row by row: every lowered assertion equals the recorder constraint on its scope rows,
    // and every DAG constraint equals its recorder constraint.
    for (i, trace) in execution.traces.iter().enumerate() {
        let Some(trace) = trace else { continue };
        let air = &exp.airs[i];
        let rec = recorder_values(&cap.recorder[i].constraints, trace);
        let dag = dag_values(&cap.vk.inner.per_air[i].symbolic_constraints, trace);
        let h = trace.height();
        for (c, row, v) in &rec {
            let node = air.recorder_constraints[*c];
            let position = air
                .dag
                .constraint_idx
                .iter()
                .position(|n| *n == node)
                .unwrap();
            let dv = dag
                .iter()
                .find(|(p, r, _)| p == &position && r == row)
                .unwrap()
                .2;
            assert_eq!(dv, *v, "{} constraint {c} row {row}", air.name);
        }
        let table = data.tables[i].as_ref().unwrap();
        for row in 0..h {
            let outputs = air.arena.evaluate(|slot| match air.inputs[slot] {
                zkc_openvm_relation::model::Input::Read {
                    group,
                    offset,
                    column,
                } => {
                    let width = air.groups[group].width;
                    let values = if group + 1 == air.groups.len() {
                        &table.main
                    } else {
                        &table.cached[group]
                    };
                    values[((row + offset) % h) * width + column]
                }
                zkc_openvm_relation::model::Input::Public(slot) => data.publics[slot],
            });
            for a in &air.assertions {
                if a.scope.contains(row, h) {
                    let upstream = rec
                        .iter()
                        .find(|(c, r, _)| c == &a.constraint && r == &row)
                        .unwrap()
                        .2;
                    assert_eq!(
                        outputs[a.output],
                        upstream,
                        "{} assertion c{} {} row {row}",
                        air.name,
                        a.constraint,
                        a.scope.name()
                    );
                }
            }
            // Vacuous classes really are zero upstream.
            for (c, class) in &air.vacuous {
                let in_class = match class {
                    zkc_openvm_relation::model::RowClass::First => row == 0,
                    zkc_openvm_relation::model::RowClass::Interior => row > 0 && row + 1 < h,
                    zkc_openvm_relation::model::RowClass::Last => row + 1 == h,
                };
                if in_class {
                    let upstream = rec
                        .iter()
                        .find(|(cc, r, _)| cc == c && r == &row)
                        .unwrap()
                        .2;
                    assert_eq!(
                        upstream,
                        p3_field::PrimeCharacteristicRing::ZERO,
                        "{} vacuous c{} row {row}",
                        air.name,
                        c
                    );
                }
            }
        }
    }
    let c = carriers(&exp, &data).unwrap();
    let line = serde_json::to_string(&c).unwrap();
    println!("carrier line bytes {}", line.len());
    assert!(line.len() < 1024 * 1024);
}
