//! Actual native output checked against original generic source by Lean, then
//! driven by source control. This is structural validation plus execution tests,
//! not a native adequacy proof. Differential execution has a separate test suite.

use std::{collections::BTreeMap, process::Command};
use zkc_backends::{GroupPoint, Policy, Scalar, Value};
use zkc_runtime::interactive::{
    AdmissionError, ArtifactFormat, Correspondence, Runner, SourceMap, admit_physical,
};
use zkc_tools::protocol::{
    JointOutcome, LocalTransport, ParticipantChecker, Schedule, ScheduledAction, drive,
};

#[path = "common/backend.rs"]
mod fixture;
use fixture::backend_for as backend;

struct BrokenMapping<'a>(&'a ParticipantChecker, bool);
impl Correspondence for BrokenMapping<'_> {
    fn check(
        &self,
        source: &[u8],
        candidate: &[u8],
        format: ArtifactFormat,
    ) -> Result<(), AdmissionError> {
        self.0.check(source, candidate, format)
    }
    fn check_with_mapping(
        &self,
        source: &[u8],
        candidate: &[u8],
        format: ArtifactFormat,
    ) -> Result<Option<SourceMap>, AdmissionError> {
        let mut result = self
            .0
            .check_with_mapping(source, candidate, format)?
            .unwrap();
        if self.1 {
            result.calls.pop();
        } else {
            result.ports[0].arguments[0].1 = "absent".into();
        }
        Ok(Some(result))
    }
}

struct VerdictOnly;
impl Correspondence for VerdictOnly {
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

#[test]
fn original_generic_source_controls_actual_native_execution() {
    let compiler = zkc_test_support::compiler();
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let input = zkc_test_support::source("generic-operations.pir");
    let compile = |mode| zkc_test_support::compile(mode, &input);
    let source = compile("protocol-source");
    let candidate = compile("protocol-compile");
    let admitted = admit_physical(&source, &candidate, &backend("P"), &checker).unwrap();
    assert_eq!(admitted.checked_source(), Some(source.as_slice()));
    let map = admitted.source_map().unwrap();
    assert_eq!(map.calls.len(), 5);
    let entry = admitted.entry("main").unwrap();
    let p = entry.iter().find(|p| p.role == "P").unwrap();
    assert_eq!(map.port("concrete", "P", "a"), Some(p.inputs[0].0.as_str()));
    assert_ne!(p.inputs[0].0, "a");
    assert_eq!(
        map.call("concrete", "P", "right").unwrap().function,
        map.call("concrete", "P", "shared").unwrap().function
    );
    assert_ne!(
        map.call("concrete", "P", "right").unwrap().function,
        map.call("concrete", "P", "left").unwrap().function
    );

    // Construction preparation preserves source configuration names. The
    // independent checker still relates its compilation to the ORIGINAL library.
    let directory = zkc_test_support::evidence(module_path!());
    let prepared = compile("protocol-prepare");
    let path = directory.path().join("prepared.json");
    std::fs::write(&path, &prepared).unwrap();
    let result = Command::new(&compiler)
        .arg("protocol-compile")
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let checked = admit_physical(&source, &result.stdout, &backend("P"), &checker).unwrap();
    let prepared_map = checked.source_map().unwrap();
    assert_eq!(prepared_map.calls.len(), map.calls.len());
    for call in &map.calls {
        let other = prepared_map
            .call(&call.instance, &call.role, &call.site)
            .unwrap();
        assert_eq!(other.source_function, call.source_function);
    }
    assert_ne!(
        prepared_map
            .call("concrete", "P", "right")
            .unwrap()
            .function,
        prepared_map
            .call("concrete", "P", "shared")
            .unwrap()
            .function
    );

    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    assert_eq!(schedule.inputs().unwrap()["P"][0].0, "a");
    let table = |values: &[u64]| {
        Value::table(
            &values.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    };
    let group = GroupPoint::generator();
    let p = Runner::new(
        &admitted,
        "main",
        "P",
        "test",
        backend("P"),
        vec![
            table(&[0, 1, 4, 9]),
            table(&[2, 3, 5, 7]),
            Value::Curve(group),
            Value::Bool(true),
            Value::Bool(false),
        ],
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    let v = Runner::new(
        &admitted,
        "main",
        "V",
        "test",
        backend("V"),
        vec![Value::Field(Scalar::from(2))],
    )
    .unwrap_or_else(|e| panic!("{:?}", e.error));
    let mut runners = BTreeMap::from([("P".to_owned(), p), ("V".to_owned(), v)]);
    let report = drive(&mut schedule, &mut runners, &mut LocalTransport);
    assert_eq!(report.wire.messages, 1);
    let JointOutcome::Returned(values) = report.outcome else {
        panic!("{:?}", report.outcome)
    };
    for (value, expected) in values["P"][..3].iter().zip([[8u64, 17], [8, 11], [8, 17]]) {
        let Value::Table(table) = value else {
            panic!("wrong representation")
        };
        assert_eq!(table.logical_values().unwrap(), expected.map(Scalar::from));
    }
    assert!(
        matches!(&values["P"][3], Value::Curve(actual) if *actual == group.scale(Scalar::from(2)))
    );
    assert!(matches!(&values["P"][4], Value::Bool(false)));
    assert!(values["V"].is_empty());
    assert!(runners.values().all(|r| r.backend().active_frames() == 0));

    for broken in [
        BrokenMapping(&checker, false),
        BrokenMapping(&checker, true),
    ] {
        assert!(admit_physical(&source, &candidate, &backend("P"), &broken).is_err());
    }
    assert!(
        admit_physical(&source, &candidate, &backend("P"), &VerdictOnly)
            .unwrap_err()
            .detail
            .contains("source-map-required")
    );
    let mut changed: serde_json::Value = serde_json::from_slice(&source).unwrap();
    changed[1][0][3] = serde_json::json!([]);
    assert!(
        admit_physical(
            &serde_json::to_vec(&changed).unwrap(),
            &candidate,
            &backend("P"),
            &checker
        )
        .is_err()
    );
}

/// Family counts reach the schedule only through `bind_family`, after every
/// role has run its own ingress; the schedule refuses to guess one.
#[test]
fn family_counts_must_be_bound_before_the_schedule_uses_them() {
    let checker =
        ParticipantChecker::new(zkc_test_support::checker("interactive-protocol")).unwrap();
    let input = zkc_test_support::source("input-families/counted.pir");
    let source = zkc_test_support::compile("protocol-source", &input);
    let candidate = zkc_test_support::compile("protocol-compile", &input);
    let admitted = admit_physical(&source, &candidate, &backend("P"), &checker).unwrap();
    let selected = |counts: &[(&str, u64)]| {
        counts
            .iter()
            .map(|(role, count)| {
                (
                    role.to_string(),
                    BTreeMap::from([("rounds".to_string(), *count)]),
                )
            })
            .collect::<BTreeMap<_, _>>()
    };

    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    assert_eq!(
        schedule.bind_family(&selected(&[("P", 3)])).unwrap_err(),
        "interactive-family-unbound"
    );
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    assert_eq!(
        schedule
            .bind_family(&selected(&[("P", 3), ("V", 4)]))
            .unwrap_err(),
        "interactive-family-disagreement"
    );
    // Without a binding, the counted loop still carries the ingress record.
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let error = loop {
        match schedule.next_action() {
            Ok(Some(_)) => {}
            Ok(None) => panic!("the counted loop was scheduled without a count"),
            Err(error) => break error,
        }
    };
    assert_eq!(error, "interactive-family-unbound");
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    schedule
        .bind_family(&selected(&[("P", 2), ("V", 2)]))
        .unwrap();
    let mut messages = 0;
    while let Some(action) = schedule.next_action().unwrap() {
        messages += usize::from(matches!(action, ScheduledAction::Message { .. }));
    }
    assert_eq!(messages, 2);
}
