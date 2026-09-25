//! Replay certificates emitted by C++, without trusting the native search.
use serde_json::{Value, json};
use std::{
    io::Write,
    process::{Command, Stdio},
};
use zkc_tools::artifact::replay_static_requirements;

fn derive(problem: &Value) -> Value {
    let executable = zkc_test_support::tool(
        zkc_test_support::Build::Compiler,
        "test/zkc-requirements-test",
    );
    let mut child = Command::new(executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(problem.to_string().as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn native_application_certificates_are_independently_replayed() {
    for head in ["PCS", "Oracle", "Views"] {
        let problem = json!([
            "zkc.requirements/1",
            [
                [null, "F"],
                [null, "G"],
                ["apply", head, [0]],
                ["apply", head, [1]],
                [2, "State"],
                [3, "State"]
            ],
            [["=", [0, 1]], ["Ready", [2]]],
            [],
            [
                ["=", [2, 3]],
                ["=", [4, 5]],
                ["Ready", [3]],
                ["Unknown", [3]]
            ]
        ]);
        let certificate = derive(&problem);
        assert_eq!(
            replay_static_requirements(&problem, &certificate).unwrap(),
            [true, true, true, false]
        );
        let step = certificate[1]
            .as_array()
            .unwrap()
            .iter()
            .position(|step| step[1] == "application")
            .unwrap();
        // A premise can only name an earlier fact, never the step itself.
        let mut stale = certificate.clone();
        stale[1][step][2] = json!([step]);
        assert_eq!(
            replay_static_requirements(&problem, &stale).unwrap_err(),
            "requirements-index"
        );
        let mut other = problem.clone();
        other[1][3][1] = json!("DifferentSelection");
        assert_eq!(
            replay_static_requirements(&other, &certificate).unwrap_err(),
            "requirements-invalid-derivation"
        );
    }
}

#[test]
fn application_equality_does_not_prove_argument_equality() {
    let problem = json!([
        "zkc.requirements/1",
        [
            [null, "F"],
            [null, "G"],
            ["apply", "Selection", [0]],
            ["apply", "Selection", [1]]
        ],
        [["=", [2, 3]]],
        [],
        [["=", [0, 1]]]
    ]);
    assert_eq!(
        replay_static_requirements(&problem, &derive(&problem)).unwrap(),
        [false]
    );
}
