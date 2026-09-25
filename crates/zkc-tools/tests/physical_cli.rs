#![cfg(unix)]
use serde_json::{Value, json};
use std::{fs, os::unix::fs::PermissionsExt, path::Path, process::Command};

struct Files {
    dir: zkc_test_support::Evidence,
    source: std::path::PathBuf,
    candidate: std::path::PathBuf,
    inputs: std::path::PathBuf,
}
fn files(mode: &str) -> Files {
    let dir = zkc_test_support::evidence(module_path!());
    let r = json!(["residual", "f7", 1]);
    let p = json!(["point", "f7"]);
    let s = json!(["scalar", "f7"]);
    let context = json!([
        "trace",
        [
            ["r", r, ["shared"], "capture"],
            ["p", p, ["shared"], "argument"],
            ["s", s, ["shared"], "capture"]
        ],
        s,
        [["table-protocol", "1"]]
    ]);
    let source = dir.path().join("source.json");
    let candidate = dir.path().join("plan.json");
    let inputs = dir.path().join("inputs.json");
    fs::write(
        &source,
        json!([
            "zkc-request",
            1,
            "finite-source-1",
            context,
            [],
            ["apply", ["evaluate", "f7", 1], [0, 1], ["return", 0]]
        ])
        .to_string(),
    )
    .unwrap();
    let op = if mode == "eager" {
        json!(["invoke", ["evaluate", "f7", 1]])
    } else {
        json!(["prepare", mode, "f7", 1])
    };
    fs::write(
        &candidate,
        json!([
            "zkc-table-physical-plan",
            1,
            context,
            ["apply", op, [0, 1], ["return", 0]]
        ])
        .to_string(),
    )
    .unwrap();
    fs::write(
        &inputs,
        json!([
            [["r", r, [3, [2, 5], []]], ["p", p, [1]], ["s", s, 6]],
            [0, 0, 0, [], [3, 6]]
        ])
        .to_string(),
    )
    .unwrap();
    Files {
        dir,
        source,
        candidate,
        inputs,
    }
}
fn run(f: &Files, checker: &Path, storage: &str, extra: &[&str]) -> (bool, Value) {
    let out = Command::new(env!("CARGO_BIN_EXE_zkc"))
        .arg("run-physical")
        .arg(&f.source)
        .arg(&f.candidate)
        .arg(&f.inputs)
        .arg(checker)
        .args(extra)
        .args(["--storage", storage])
        .output()
        .unwrap();
    (
        out.status.success(),
        serde_json::from_slice(&out.stdout)
            .unwrap_or_else(|_| panic!("stdout {:?}, stderr {:?}", out.stdout, out.stderr)),
    )
}
fn fake(f: &Files, realization: &str) -> std::path::PathBuf {
    // Finite fixture authorization only. The helper compares retained bytes; it
    // makes no semantic checking claim. Production uses the installed Lean tool.
    let expected = f.dir.path().join("expected.json");
    fs::copy(&f.candidate, &expected).unwrap();
    let checker = f.dir.path().join("checker");
    fs::write(checker.with_extension("next"),format!("#!/bin/sh\n[ \"$1\" = check ] || exit 8\ncmp -s \"$2\" '{}' || exit 9\ncmp -s \"$3\" '{}' || exit 10\nprintf '%s\\n' '{{\"claim\":\"complete-logical-execution\",\"realization\":\"{realization}\",\"status\":\"checked\"}}'\n",f.source.display(),expected.display())).unwrap();
    fs::set_permissions(
        checker.with_extension("next"),
        fs::Permissions::from_mode(0o700),
    )
    .unwrap();
    fs::rename(checker.with_extension("next"), &checker).unwrap();
    checker
}
fn assert_execution(f: &Files, checker: &Path, mode: &str) {
    for storage in ["packed", "segmented"] {
        let (ok, report) = run(f, checker, storage, &[]);
        assert!(ok, "{report}");
        assert_eq!(
            report,
            json!({"execution":{"status":"executed","outcome":["returned",5],"state":[0,0,0,[],[3,6]],"events":[]},"table-evaluations":1,"scalar-cells":usize::from(mode!="eager")})
        );
    }
}
#[test]
fn cli_uses_the_physical_claim_and_reads_returned_values_in_both_layouts() {
    // One realization mode, because what this judges is the contract with the
    // checker subprocess: the bytes handed over are the source and the
    // candidate unaltered, and an acknowledgment naming the wrong
    // realization, an absent certificate and a checker that exits non-zero
    // are each refused under their own code. Which mode was realized changes
    // the counts in the report rather than the call, so the three modes are
    // run by live_physical_checker_checks_actual_candidate, against the
    // checker whose agreement about them is worth having.
    let f = files("lazy");
    let checker = fake(&f, "table-physical-plan");
    assert_execution(&f, &checker, "lazy");
    let f = files("lazy");
    let checker = fake(&f, "direct-logical-plan");
    assert_eq!(
        run(&f, &checker, "packed", &[]),
        (
            false,
            json!({"status":"refused","code":"malformed-checker-response"})
        )
    );
    for flag in ["--phase", "--endpoint"] {
        assert_eq!(
            run(&f, &checker, "packed", &[flag, "table-round/1", "absent"]),
            (false, json!({"status":"refused","code":"io-error"}))
        );
    }
    let checker = fake(&f, "table-physical-plan");
    let mut p: Value = serde_json::from_slice(&fs::read(&f.candidate).unwrap()).unwrap();
    p[3][3] = json!(["return", 3]);
    fs::write(&f.candidate, p.to_string()).unwrap();
    assert_eq!(
        run(&f, &checker, "packed", &[]),
        (
            false,
            json!({"status":"refused","code":"checker-process-failed"})
        )
    );
}
#[test]
fn live_physical_checker_checks_actual_candidate() {
    let path = zkc_test_support::checker("table-physical-reference");
    let checker = Path::new(&path);
    for mode in ["lazy", "materialized", "eager"] {
        let f = files(mode);
        assert_execution(&f, checker, mode);
        let mut p: Value = serde_json::from_slice(&fs::read(&f.candidate).unwrap()).unwrap();
        // Same-typed substitution must reach and fail the actual checker.
        p[3][3] = json!(["return", 3]);
        fs::write(&f.candidate, p.to_string()).unwrap();
        let (ok, report) = run(&f, checker, "packed", &[]);
        assert!(!ok);
        assert_eq!(report["status"], "refused");
        assert_eq!(report["code"], "check-not-established");
        for start in [None, Some("ready"), Some("sent")] {
            let (f, cert, _) = phase_files(mode, start);
            assert_phase_execution(&f, &cert, checker, mode, start);
            fs::write(&cert, r#"["terminal"]"#).unwrap();
            let (flag, profile) = if start.is_some() {
                ("--endpoint", "table-endpoint/1")
            } else {
                ("--phase", "table-round/1")
            };
            assert_eq!(
                run(
                    &f,
                    checker,
                    "packed",
                    &[flag, profile, cert.to_str().unwrap()]
                ),
                (
                    false,
                    json!({"status":"refused","code":"phase-not-admitted"})
                )
            );
        }
    }
}

fn phase_files(mode: &str, start: Option<&str>) -> (Files, std::path::PathBuf, Value) {
    let f = files(mode);
    let mut source: Value = serde_json::from_slice(&fs::read(&f.source).unwrap()).unwrap();
    let mut candidate: Value = serde_json::from_slice(&fs::read(&f.candidate).unwrap()).unwrap();
    let mut inputs: Value = serde_json::from_slice(&fs::read(&f.inputs).unwrap()).unwrap();
    let sent = start == Some("sent");
    let source_draw = json!(["apply", ["draw"], [], ["return", if sent { 1 } else { 2 }]]);
    let physical_draw = json!([
        "apply",
        ["invoke", ["draw"]],
        [],
        ["return", if sent { 1 } else { 2 }]
    ]);
    source[5][3] = if sent {
        source_draw
    } else {
        json!(["apply", ["send"], [0, 0], source_draw])
    };
    candidate[3][3] = if sent {
        physical_draw
    } else {
        json!(["apply", ["invoke", ["send"]], [0, 0], physical_draw])
    };
    let mut ack = json!({"claim":"complete-logical-execution", "realization":"table-physical-plan", "status":"checked", "phase-profile":"table-round/1"});
    if let Some(start) = start {
        source[3][0] = json!("prover");
        candidate[2][0] = json!("prover");
        inputs[1] = json!(["prover", start, inputs[1]]);
        ack["phase-profile"] = json!("table-endpoint/1");
        ack["entry"] = json!(["prover", start]);
    }
    fs::write(&f.source, source.to_string()).unwrap();
    fs::write(&f.candidate, candidate.to_string()).unwrap();
    fs::write(&f.inputs, inputs.to_string()).unwrap();
    let certificate = f.dir.path().join("certificate.json");
    let mut cert = json!(["terminal"]);
    for _ in 0..if sent { 2 } else { 3 } {
        cert = json!(["next", cert]);
    }
    fs::write(&certificate, cert.to_string()).unwrap();
    (f, certificate, ack)
}
fn policy_fake(f: &Files, cert: &Path, ack: &Value, response: &Value) -> std::path::PathBuf {
    // Explicit fixture authorization; exercise the real subprocess protocol,
    // including exact copied evidence bytes. This is not a semantic checker.
    let expected_source = f.dir.path().join("expected-source.json");
    let expected_plan = f.dir.path().join("expected-plan.json");
    let expected_cert = f.dir.path().join("expected-cert.json");
    fs::copy(&f.source, &expected_source).unwrap();
    fs::copy(&f.candidate, &expected_plan).unwrap();
    fs::copy(cert, &expected_cert).unwrap();
    let (command, entry_check) = if let Some(entry) = ack.get("entry") {
        (
            "admit-entry",
            format!(
                "[ \"$#\" = 6 ] || exit 14\nprintf '%s' '{entry}' | cmp -s - \"$6\" || exit 13"
            ),
        )
    } else {
        ("admit", "[ \"$#\" = 5 ] || exit 14".into())
    };
    let checker = f.dir.path().join("checker");
    fs::write(checker.with_extension("next"), format!(
        "#!/bin/sh\n[ \"$1\" = {command} ] || exit 8\ncmp -s \"$2\" '{}' || exit 9\ncmp -s \"$3\" '{}' || exit 10\n[ \"$4\" = '{}' ] || exit 11\ncmp -s \"$5\" '{}' || exit 12\n{entry_check}\nprintf '%s\\n' '{response}'\n",
        expected_source.display(), expected_plan.display(), ack["phase-profile"].as_str().unwrap(), expected_cert.display()
    )).unwrap();
    fs::set_permissions(
        checker.with_extension("next"),
        fs::Permissions::from_mode(0o700),
    )
    .unwrap();
    fs::rename(checker.with_extension("next"), &checker).unwrap();
    checker
}
fn assert_phase_execution(f: &Files, cert: &Path, checker: &Path, mode: &str, start: Option<&str>) {
    let flag = if start.is_some() {
        "--endpoint"
    } else {
        "--phase"
    };
    let profile = if start.is_some() {
        "table-endpoint/1"
    } else {
        "table-round/1"
    };
    let sent = start == Some("sent");
    for storage in ["packed", "segmented"] {
        let (ok, report) = run(
            f,
            checker,
            storage,
            &[flag, profile, cert.to_str().unwrap()],
        );
        assert!(ok, "{report}");
        let logical = json!([0, 0, 0, if sent { json!([]) } else { json!([[5, 5]]) }, [6]]);
        let state = if start.is_some() {
            json!(["prover", "ready", logical])
        } else {
            logical
        };
        let events = if sent {
            json!([["drawn", 3]])
        } else {
            json!([["sent", 5, 5], ["drawn", 3]])
        };
        assert_eq!(
            report,
            json!({
                "execution":{"status":"executed","outcome":["returned",5],"state":state,"events":events},
                "table-evaluations":if mode == "lazy" && !sent { 3 } else { 1 },
                "scalar-cells":usize::from(mode != "eager")
            })
        );
    }
}
#[test]
fn cli_transports_selected_phase_and_endpoint_entry_with_trailing_storage() {
    // What varies here is the entry, not the realization mode: a phase is
    // admitted with five arguments and an endpoint entry with six, and
    // policy_fake exits non-zero on any other argv, profile string or
    // certificate bytes. The mode is fixed for the same reason as above.
    for start in [None, Some("ready"), Some("sent")] {
        let (f, cert, ack) = phase_files("lazy", start);
        let checker = policy_fake(&f, &cert, &ack, &ack);
        assert_phase_execution(&f, &cert, &checker, "lazy", start);
    }
}
#[test]
fn cli_cannot_drop_policy_entry_or_physical_realization_acknowledgment() {
    for start in [None, Some("ready"), Some("sent")] {
        let (f, cert, ack) = phase_files("lazy", start);
        let flag = if start.is_some() {
            "--endpoint"
        } else {
            "--phase"
        };
        let extra = [
            flag,
            ack["phase-profile"].as_str().unwrap(),
            cert.to_str().unwrap(),
        ];
        let mut responses = vec![];
        for key in ["phase-profile", "entry"] {
            let mut wrong = ack.clone();
            if wrong.as_object_mut().unwrap().remove(key).is_some() {
                responses.push(wrong);
            }
        }
        for realization in ["direct-logical-plan", "table-physical-reference"] {
            let mut wrong = ack.clone();
            wrong["realization"] = json!(realization);
            responses.push(wrong);
        }
        for response in responses {
            let checker = policy_fake(&f, &cert, &ack, &response);
            assert_eq!(
                run(&f, &checker, "packed", &extra),
                (
                    false,
                    json!({"status":"refused","code":"malformed-checker-response"})
                )
            );
        }
        let checker = policy_fake(&f, &cert, &ack, &ack);
        fs::write(&cert, "[]").unwrap();
        assert_eq!(
            run(&f, &checker, "packed", &extra),
            (
                false,
                json!({"status":"refused","code":"checker-process-failed"})
            )
        );
    }
}
#[test]
fn cli_endpoint_rejects_foreign_role_and_unknown_state() {
    let (f, cert, mut ack) = phase_files("lazy", Some("ready"));
    let mut invocation: Value = serde_json::from_slice(&fs::read(&f.inputs).unwrap()).unwrap();
    for (actor, phase, code) in [
        ("verifier", "ready", "endpoint-role-mismatch"),
        ("prover", "unknown", "unknown-endpoint-state"),
    ] {
        invocation[1][0] = json!(actor);
        invocation[1][1] = json!(phase);
        fs::write(&f.inputs, invocation.to_string()).unwrap();
        ack["entry"] = json!([actor, phase]);
        let checker = policy_fake(&f, &cert, &ack, &ack);
        assert_eq!(
            run(
                &f,
                &checker,
                "packed",
                &["--endpoint", "table-endpoint/1", cert.to_str().unwrap()]
            ),
            (false, json!({"status":"refused","code":code}))
        );
    }
}
