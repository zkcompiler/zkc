#![cfg(unix)]
use std::{fs, os::unix::fs::PermissionsExt, time::Duration};
use zkc_runtime::{CheckFailure, CheckRequest, Checker, PhaseEvidence};
use zkc_tools::LeanChecker;

// These fixtures create executable files. Serialize this small suite so another
// test cannot fork while a script inode is still open for writing: an inherited
// writer can make execve fail with ETXTBSY even after the parent closes it.
static SCRIPT_EXECUTION: std::sync::Mutex<()> = std::sync::Mutex::new(());

const SUCCESS: &str = r#"{"claim":"complete-logical-execution","realization":"direct-logical-plan","status":"checked"}"#;

fn request(phase: Option<&PhaseEvidence>) -> CheckRequest<'_> {
    CheckRequest {
        source: b"source",
        candidate: b"candidate",
        phase,
        realization: zkc_runtime::Realization::DirectLogicalPlan,
    }
}
fn script(path: &std::path::Path, body: &str) {
    // Replace the executable inode instead of truncating a recently run script.
    let next = path.with_extension("next");
    fs::write(&next, format!("#!/bin/sh\n{body}\n")).unwrap();
    fs::set_permissions(&next, fs::Permissions::from_mode(0o700)).unwrap();
    fs::rename(next, path).unwrap();
}
#[test]
fn complete_response_and_exit_status_are_both_required() {
    let _scripts = SCRIPT_EXECUTION.lock().unwrap();
    use CheckFailure::*;
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("checker");
    let cases = [
        (SUCCESS.to_owned(), 0, Ok(())),
        (SUCCESS.to_owned(), 1, Err(ProcessFailed)),
        (format!("{SUCCESS}\n{{}}"), 0, Err(MalformedResponse)),
        (
            SUCCESS.replace("\"checked\"", "\"refused\""),
            0,
            Err(MalformedResponse),
        ),
        (
            SUCCESS.replace("\"status\":", "\"status\":\"refused\",\"status\":"),
            0,
            Err(MalformedResponse),
        ),
        ("".to_owned(), 0, Err(MalformedResponse)),
        ("x".repeat(5000), 0, Err(MalformedResponse)),
        (
            r#"{"code":"phase-not-admitted","status":"refused"}"#.into(),
            1,
            Err(NotEstablished("phase-not-admitted".into())),
        ),
        (
            r#"{"code":"unsupported-phase-profile","status":"refused"}"#.into(),
            1,
            Err(Unsupported("unsupported-phase-profile".into())),
        ),
        (
            r#"{"code":"unapproved-requirement","status":"refused"}"#.into(),
            1,
            Err(UnresolvedRequirements("unapproved-requirement".into())),
        ),
        (
            r#"{"code":"unsupported-requirement","status":"refused"}"#.into(),
            1,
            Err(Unsupported("unsupported-requirement".into())),
        ),
        (
            r#"{"code":"phase-not-admitted","status":"refused"}"#.into(),
            0,
            Err(MalformedResponse),
        ),
        (
            r#"{"code":"first","code":"second","status":"refused"}"#.into(),
            1,
            Err(ProcessFailed),
        ),
    ];
    for (response, code, expected) in cases {
        // Fixed local fixtures. Verify exact copied input bytes as well as results.
        script(
            &path,
            &format!(
                "[ \"$1\" = check ] || exit 8\n[ \"$(cat \"$2\")\" = source ] || exit 9\n[ \"$(cat \"$3\")\" = candidate ] || exit 10\nprintf '%s\\n' '{}'\nexit {code}",
                response
            ),
        );
        assert_eq!(
            LeanChecker::new(&path).unwrap().check(request(None)),
            expected
        );
    }
}
#[test]
fn phase_evidence_and_selected_profile_reach_the_tool() {
    let _scripts = SCRIPT_EXECUTION.lock().unwrap();
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("checker");
    let phase = PhaseEvidence {
        entry: None,
        profile: "table-round/1".into(),
        certificate: b"certificate".to_vec(),
    };
    let success = SUCCESS.replace(
        "\"realization\":",
        "\"phase-profile\":\"table-round/1\",\"realization\":",
    );
    script(
        &path,
        &format!(
            "[ \"$1\" = admit ] || exit 8\n[ \"$(cat \"$2\")\" = source ] || exit 9\n[ \"$(cat \"$3\")\" = candidate ] || exit 10\n[ \"$4\" = table-round/1 ] || exit 11\n[ \"$(cat \"$5\")\" = certificate ] || exit 12\nprintf '%s\\n' '{}'",
            success
        ),
    );
    assert_eq!(
        LeanChecker::new(&path)
            .unwrap()
            .check(request(Some(&phase))),
        Ok(())
    );
    for invalid in [
        SUCCESS.to_owned(),
        success.replace("table-round/1", "another-profile/1"),
    ] {
        script(&path, &format!("printf '%s\\n' '{}'", invalid));
        assert_eq!(
            LeanChecker::new(&path)
                .unwrap()
                .check(request(Some(&phase))),
            Err(CheckFailure::MalformedResponse)
        );
    }
    script(&path, &format!("printf '%s\\n' '{}'", success));
    assert_eq!(
        LeanChecker::new(&path).unwrap().check(request(None)),
        Err(CheckFailure::MalformedResponse)
    );
}
#[test]
fn timeout_and_spawn_failure_remain_distinct() {
    let _scripts = SCRIPT_EXECUTION.lock().unwrap();
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("checker");
    script(&path, "exec sleep 5");
    let checker = LeanChecker::new(&path)
        .unwrap()
        .with_timeout(Duration::from_millis(20));
    assert_eq!(
        checker.check(request(None)),
        Err(CheckFailure::BudgetExceeded)
    );
    fs::remove_file(path).unwrap();
    assert_eq!(checker.check(request(None)), Err(CheckFailure::Io));
}

#[test]
fn stateful_acknowledgment_binds_exact_consumer_entry() {
    let _scripts = SCRIPT_EXECUTION.lock().unwrap();
    use serde_json::json;
    use zkc_runtime::EndpointEntry;
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("checker");
    let phase = PhaseEvidence {
        profile: "table-endpoint/1".into(),
        certificate: b"certificate".to_vec(),
        entry: Some(EndpointEntry {
            role: "prover".into(),
            phase: json!("sent"),
        }),
    };
    let mut success: serde_json::Value = serde_json::from_str(SUCCESS).unwrap();
    success["phase-profile"] = json!(phase.profile);
    success["entry"] = json!(["prover", "sent"]);
    script(
        &path,
        &format!(
            "[ \"$1\" = admit-entry ] || exit 8\n[ \"$(cat \"$2\")\" = source ] || exit 9\n[ \"$(cat \"$3\")\" = candidate ] || exit 10\n[ \"$4\" = table-endpoint/1 ] || exit 11\n[ \"$(cat \"$5\")\" = certificate ] || exit 12\n[ \"$(cat \"$6\")\" = '[\"prover\",\"sent\"]' ] || exit 13\nprintf '%s\\n' '{}'",
            success
        ),
    );
    assert_eq!(
        LeanChecker::new(&path)
            .unwrap()
            .check(request(Some(&phase))),
        Ok(())
    );
    for entry in [
        None,
        Some(json!(["prover", "ready"])),
        Some(json!(["verifier", "sent"])),
    ] {
        let mut wrong = success.clone();
        wrong.as_object_mut().unwrap().remove("entry");
        if let Some(entry) = entry {
            wrong["entry"] = entry;
        }
        script(&path, &format!("printf '%s\\n' '{}'", wrong));
        assert_eq!(
            LeanChecker::new(&path)
                .unwrap()
                .check(request(Some(&phase))),
            Err(CheckFailure::MalformedResponse)
        );
    }
    script(&path, &format!("printf '%s\\n' '{}'", success));
    let trace = PhaseEvidence {
        entry: None,
        ..phase
    };
    assert_eq!(
        LeanChecker::new(&path)
            .unwrap()
            .check(request(Some(&trace))),
        Err(CheckFailure::MalformedResponse)
    );
}

#[test]
fn physical_acknowledgment_requires_selected_realization_and_phase() {
    let _scripts = SCRIPT_EXECUTION.lock().unwrap();
    use zkc_runtime::Realization;
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("checker");
    let success = SUCCESS.replace("direct-logical-plan", "table-physical-plan");
    let physical = CheckRequest {
        realization: Realization::TablePhysicalPlan,
        ..request(None)
    };
    for (wire, expected) in [
        (success.clone(), Ok(())),
        (SUCCESS.to_owned(), Err(CheckFailure::MalformedResponse)),
        (
            success.replace("table-physical-plan", "table-physical-reference"),
            Err(CheckFailure::MalformedResponse),
        ),
        (
            success.replace(
                "\"realization\":",
                "\"realization\":\"direct-logical-plan\",\"realization\":",
            ),
            Err(CheckFailure::MalformedResponse),
        ),
        (
            success.replace(
                "\"status\":",
                "\"phase-profile\":\"table-round/1\",\"status\":",
            ),
            Err(CheckFailure::MalformedResponse),
        ),
    ] {
        script(&path, &format!("printf '%s\\n' '{}'", wire));
        assert_eq!(LeanChecker::new(&path).unwrap().check(physical), expected);
    }
    script(&path, &format!("printf '%s\\n' '{}'", success));
    assert_eq!(
        LeanChecker::new(&path).unwrap().check(request(None)),
        Err(CheckFailure::MalformedResponse)
    );
    let phase = PhaseEvidence {
        entry: None,
        profile: "table-round/1".into(),
        certificate: b"[]".to_vec(),
    };
    assert_eq!(
        LeanChecker::new(&path).unwrap().check(CheckRequest {
            phase: Some(&phase),
            ..physical
        }),
        Err(CheckFailure::MalformedResponse)
    );
}

#[test]
fn physical_phase_and_entry_commands_require_exact_acknowledgments() {
    let _scripts = SCRIPT_EXECUTION.lock().unwrap();
    use serde_json::{Value, json};
    use zkc_runtime::{EndpointEntry, Realization};
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("checker");
    for entry in [None, Some("ready"), Some("sent")] {
        let phase = PhaseEvidence {
            profile: if entry.is_some() {
                "table-endpoint/1"
            } else {
                "table-round/1"
            }
            .into(),
            certificate: b"certificate\n\n".to_vec(),
            entry: entry.map(|p| EndpointEntry {
                role: "prover".into(),
                phase: json!(p),
            }),
        };
        let request = CheckRequest {
            realization: Realization::TablePhysicalPlan,
            ..request(Some(&phase))
        };
        let mut success: Value = serde_json::from_str(SUCCESS).unwrap();
        success["realization"] = json!(request.realization.name());
        success["phase-profile"] = json!(phase.profile);
        let entry_check = if let Some(e) = &phase.entry {
            success["entry"] = e.json();
            format!(
                "[ \"$#\" = 6 ] || exit 14\nprintf '%s' '{}' | cmp -s - \"$6\" || exit 13",
                e.json()
            )
        } else {
            "[ \"$#\" = 5 ] || exit 14".into()
        };
        let command = if entry.is_some() {
            "admit-entry"
        } else {
            "admit"
        };
        script(
            &path,
            &format!(
                "[ \"$1\" = {command} ] || exit 8\nprintf '%s' source | cmp -s - \"$2\" || exit 9\nprintf '%s' candidate | cmp -s - \"$3\" || exit 10\n[ \"$4\" = '{}' ] || exit 11\nprintf 'certificate\\n\\n' | cmp -s - \"$5\" || exit 12\n{entry_check}\nprintf '%s\\n' '{success}'",
                phase.profile
            ),
        );
        assert_eq!(LeanChecker::new(&path).unwrap().check(request), Ok(()));
        let mut invalid = vec![];
        for key in ["claim", "realization", "phase-profile", "status"] {
            let mut wrong = success.clone();
            wrong.as_object_mut().unwrap().remove(key);
            invalid.push(wrong.to_string());
        }
        for realization in ["direct-logical-plan", "table-physical-reference"] {
            let mut wrong = success.clone();
            wrong["realization"] = json!(realization);
            invalid.push(wrong.to_string());
        }
        let mut wrong = success.clone();
        wrong["phase-profile"] = json!("foreign/1");
        invalid.push(wrong.to_string());
        let mut wrong = success.clone();
        wrong["claim"] = json!("phase-only");
        invalid.push(wrong.to_string());
        for wrong_entry in [
            None,
            Some(json!(["prover", "unknown"])),
            Some(json!(["verifier", "sent"])),
            Some(json!([
                "prover",
                if entry == Some("sent") {
                    "ready"
                } else {
                    "sent"
                }
            ])),
        ] {
            let mut wrong = success.clone();
            wrong.as_object_mut().unwrap().remove("entry");
            if let Some(e) = wrong_entry {
                wrong["entry"] = e;
            }
            if wrong != success {
                invalid.push(wrong.to_string());
            }
        }
        invalid.push(format!("{success}\n{{}}"));
        invalid.push(
            success
                .to_string()
                .replace("\"status\":", "\"status\":\"checked\",\"status\":"),
        );
        for wire in invalid {
            script(&path, &format!("printf '%s\\n' '{wire}'"));
            assert_eq!(
                LeanChecker::new(&path).unwrap().check(request),
                Err(CheckFailure::MalformedResponse),
                "{wire}"
            );
        }
        script(&path, &format!("printf '%s\\n' '{success}'\nexit 1"));
        assert_eq!(
            LeanChecker::new(&path).unwrap().check(request),
            Err(CheckFailure::ProcessFailed)
        );
        for code in [
            "phase-not-admitted",
            "unsupported-phase-profile",
            "unsupported-phase-role",
        ] {
            script(
                &path,
                &format!("printf '%s\\n' '{{\"code\":\"{code}\",\"status\":\"refused\"}}'\nexit 1"),
            );
            let expected = if code == "phase-not-admitted" {
                CheckFailure::NotEstablished(code.into())
            } else {
                CheckFailure::Unsupported(code.into())
            };
            assert_eq!(
                LeanChecker::new(&path).unwrap().check(request),
                Err(expected)
            );
        }
    }
}
