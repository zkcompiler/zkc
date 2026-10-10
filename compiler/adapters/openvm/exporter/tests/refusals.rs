//! Refuse unsupported shapes before the pinned upstream routines index data.
use p3_field::PrimeCharacteristicRing;
use zkc_openvm_relation::bundle::{Data, carriers, evaluate};
use zkc_openvm_relation::capture::{capture, export};
use zkc_openvm_relation::field::F;
use zkc_openvm_relation::slice::{Branch, Parameters, Program, Registers, Slice, Step};

fn branch(rs1: u32, imm: i32) -> Program {
    Program {
        steps: vec![
            Step {
                op: Branch::Beq,
                rs1,
                rs2: 4,
                imm
            };
            2
        ],
        exit_code: 0,
    }
}
#[test]
fn invalid_parameters_are_refused_before_division_or_allocation() {
    for p in [
        Parameters {
            range_max_bits: 0,
            ..Parameters::default()
        },
        Parameters {
            range_max_bits: usize::MAX,
            ..Parameters::default()
        },
        Parameters {
            timestamp_max_bits: usize::MAX,
            ..Parameters::default()
        },
        Parameters {
            timestamp_max_bits: 8,
            ..Parameters::default()
        },
        Parameters {
            step_limit: 0,
            ..Parameters::default()
        },
        Parameters {
            step_limit: 65537,
            ..Parameters::default()
        },
        Parameters {
            pc_base: u32::MAX,
            ..Parameters::default()
        },
        Parameters {
            pc_base: 1,
            ..Parameters::default()
        },
    ] {
        assert_eq!(Slice::new(p).err().unwrap().id, "openvm-parameters");
    }
}
#[test]
fn invalid_runs_have_named_refusals() {
    let slice = Slice::new(Parameters {
        step_limit: 3,
        ..Parameters::default()
    })
    .unwrap();
    for pointer in [1, 127, 128, u32::MAX] {
        assert_eq!(
            slice
                .execute(&branch(pointer, 4), &Registers::default())
                .unwrap_err()
                .id,
            "openvm-register"
        );
        assert_eq!(
            slice
                .execute(&branch(4, 4), &Registers(vec![(pointer, [0; 4])]))
                .unwrap_err()
                .id,
            "openvm-register"
        );
    }
    assert_eq!(
        slice
            .execute(&branch(4, 4), &Registers(vec![(4, [0; 4]), (4, [1; 4])]))
            .unwrap_err()
            .id,
        "openvm-register"
    );
    assert_eq!(
        slice
            .execute(&branch(4, 0), &Registers::default())
            .unwrap_err()
            .id,
        "openvm-step-limit"
    );
    assert_eq!(
        slice
            .execute(&branch(4, 2), &Registers::default())
            .unwrap_err()
            .id,
        "openvm-pc-out-of-program"
    );
    let mut program = branch(4, 4);
    program.exit_code = u32::MAX;
    assert_eq!(
        slice
            .execute(&program, &Registers::default())
            .unwrap_err()
            .id,
        "openvm-exit-code"
    );
}
#[test]
fn malformed_data_and_height_one_are_explicitly_outside_the_export_profile() {
    let slice = Slice::new(Parameters::default()).unwrap();
    let captured = capture(&slice).unwrap();
    let exported = export(&slice, &captured).unwrap();
    let run = slice.execute(&branch(4, 4), &Registers::default()).unwrap();
    let honest = Data::from_execution(&exported, &run);
    assert!(evaluate(&exported, &honest).unwrap().satisfied());
    let mut changes = vec![];
    let mut c = honest.clone();
    c.tables.pop();
    changes.push(c);
    let mut c = honest.clone();
    c.publics.push(F::ONE);
    changes.push(c);
    let mut c = honest.clone();
    c.tables[0] = None;
    changes.push(c);
    let mut c = honest.clone();
    c.tables[1].as_mut().unwrap().height = 4;
    changes.push(c);
    let mut c = honest.clone();
    c.tables[2].as_mut().unwrap().height = usize::MAX;
    changes.push(c);
    let mut c = honest.clone();
    c.tables[2].as_mut().unwrap().main.pop();
    changes.push(c);
    let mut c = honest.clone();
    c.tables[0].as_mut().unwrap().cached.clear();
    changes.push(c);
    let run = slice
        .execute(
            &Program {
                steps: vec![],
                exit_code: 0,
            },
            &Registers::default(),
        )
        .unwrap();
    changes.push(Data::from_execution(&exported, &run));
    for c in changes {
        assert_eq!(evaluate(&exported, &c).unwrap_err().id, "openvm-data-shape");
        assert_eq!(carriers(&exported, &c).unwrap_err().id, "openvm-data-shape");
        assert_eq!(c.traces(&exported).unwrap_err().id, "openvm-data-shape");
    }
}

#[test]
fn timestamp_overflow_is_refused_before_trace_fillers() {
    let slice = Slice::new(Parameters {
        timestamp_max_bits: 2,
        range_max_bits: 1,
        ..Parameters::default()
    })
    .unwrap();
    assert_eq!(
        slice
            .execute(&branch(4, 4), &Registers::default())
            .unwrap_err()
            .id,
        "openvm-timestamp-limit"
    );
}
