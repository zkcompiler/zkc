use serde_json::json;
use std::cell::Cell;
use zkc_runtime::{
    AdmittedProgram, CheckFailure, CheckRequest, Checker, Error, PhaseEvidence, table::TableLibrary,
};

fn artifacts() -> (Vec<u8>, Vec<u8>) {
    let context = json!([
        "trace",
        [["x", ["bool"], ["shared"], "capture"]],
        ["bool"],
        [["table-protocol", "1"]]
    ]);
    let source = json!([
        "zkc-request",
        1,
        "region-source-1",
        context,
        [],
        ["return", 0]
    ]);
    let plan = json!([
        "zkc-plan",
        1,
        "region-source-1",
        [],
        "direct-logical-plan",
        "direct-lowering",
        [
            "equality",
            "logical-outcome-state-events",
            "all-inputs-and-handlers"
        ],
        context,
        [],
        ["return", 0]
    ]);
    (
        source.to_string().into_bytes(),
        plan.to_string().into_bytes(),
    )
}
fn evidence() -> PhaseEvidence {
    PhaseEvidence {
        entry: None,
        profile: "table-round/1".into(),
        certificate: br#"["terminal"]"#.to_vec(),
    }
}
struct Inspect {
    source: Vec<u8>,
    candidate: Vec<u8>,
    calls: Cell<usize>,
    failure: Option<CheckFailure>,
}
impl Checker for Inspect {
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure> {
        assert_eq!(request.source, self.source);
        assert_eq!(request.candidate, self.candidate);
        assert_eq!(request.phase, Some(&evidence()));
        self.calls.set(self.calls.get() + 1);
        self.failure.clone().map_or(Ok(()), Err)
    }
}
#[test]
fn admitted_program_retains_all_checked_inputs() {
    let (source, candidate) = artifacts();
    let checker = Inspect {
        source: source.clone(),
        candidate: candidate.clone(),
        calls: Cell::new(0),
        failure: None,
    };
    let program = AdmittedProgram::admit(
        source.clone(),
        candidate.clone(),
        Some(evidence()),
        &TableLibrary,
        &checker,
    )
    .unwrap_or_else(|e| panic!("{}", e.reason));
    assert_eq!(checker.calls.get(), 1);
    assert_eq!(
        program.retained_bytes(),
        (source.as_slice(), candidate.as_slice())
    );
    assert_eq!(program.clone().phase_evidence(), Some(&evidence()));
}
#[test]
fn failed_check_returns_evidence_and_typed_failure() {
    for code in ["phase-not-admitted", "unchecked-plan"] {
        let (source, candidate) = artifacts();
        let rejection = CheckFailure::NotEstablished(code.into());
        let checker = Inspect {
            source: source.clone(),
            candidate: candidate.clone(),
            calls: Cell::new(0),
            failure: Some(rejection.clone()),
        };
        let Err(failure) = AdmittedProgram::admit(
            source.clone(),
            candidate.clone(),
            Some(evidence()),
            &TableLibrary,
            &checker,
        ) else {
            panic!("rejected evidence admitted");
        };
        assert_eq!(failure.source, source);
        assert_eq!(failure.candidate, candidate);
        assert_eq!(failure.phase, Some(evidence()));
        assert_eq!(failure.checking, Some(rejection));
        assert_eq!(failure.reason, Error(code));
    }
}
#[test]
fn malformed_evidence_is_rejected_before_tool_dispatch() {
    let (source, candidate) = artifacts();
    let checker = Inspect {
        source: source.clone(),
        candidate: candidate.clone(),
        calls: Cell::new(0),
        failure: None,
    };
    for phase in [
        PhaseEvidence {
            entry: None,
            profile: String::new(),
            ..evidence()
        },
        PhaseEvidence {
            entry: None,
            profile: "bad\0profile".into(),
            ..evidence()
        },
        PhaseEvidence {
            entry: None,
            certificate: b"{}".to_vec(),
            ..evidence()
        },
        PhaseEvidence {
            entry: None,
            certificate: vec![b' '; 1024 * 1024 + 1],
            ..evidence()
        },
    ] {
        let Err(failure) = AdmittedProgram::admit(
            source.clone(),
            candidate.clone(),
            Some(phase.clone()),
            &TableLibrary,
            &checker,
        ) else {
            panic!("malformed input admitted");
        };
        assert_eq!(failure.phase, Some(phase));
        assert!(failure.checking.is_none());
    }
    assert_eq!(checker.calls.get(), 0);
}

#[test]
fn endpoint_role_is_checked_before_checker_dispatch() {
    use zkc_runtime::EndpointEntry;
    let (source, candidate) = artifacts();
    let checker = Inspect {
        source: source.clone(),
        candidate: candidate.clone(),
        calls: Cell::new(0),
        failure: None,
    };
    for (role, code) in [
        ("", "invalid-entry-role"),
        ("prover", "endpoint-role-mismatch"),
    ] {
        let phase = PhaseEvidence {
            entry: Some(EndpointEntry {
                role: role.into(),
                phase: json!("ready"),
            }),
            ..evidence()
        };
        let failure = AdmittedProgram::admit(
            source.clone(),
            candidate.clone(),
            Some(phase.clone()),
            &TableLibrary,
            &checker,
        )
        .err()
        .unwrap();
        assert_eq!(failure.reason, Error(code));
        assert_eq!(failure.phase, Some(phase));
        assert!(failure.checking.is_none());
    }
    assert_eq!(checker.calls.get(), 0);
}
