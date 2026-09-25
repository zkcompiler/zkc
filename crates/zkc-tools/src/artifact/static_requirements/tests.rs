use super::*;
use serde_json::json;

fn static_case() -> (Json, Json) {
    let request = json!([
        "zkc.requirements/1",
        [
            [null, "F"],
            [null, "G"],
            [null, "S"],
            ["apply", "Poly", [0, 2]],
            ["apply", "Poly", [1, 2]],
            [3, "Commitment"],
            [4, "Commitment"],
            ["apply", "Other", [1, 2]],
            ["apply", "Poly", [2, 1]],
            ["apply", "seal:library.Decl", []]
        ],
        [["=", [0, 1]], ["Ready", [5, 2]]],
        [],
        [
            ["=", [5, 6]],
            ["Ready", [6, 2]],
            ["=", [3, 7]],
            ["=", [3, 8]]
        ]
    ]);
    let certificate = json!([
        "zkc.requirements-certificate/1",
        [
            [["=", [0, 1]], "assumption", [], 0],
            [["=", [2, 2]], "reflexivity", [], 0],
            [["=", [3, 4]], "application", [0, 1], 0],
            [["=", [5, 6]], "projection", [2], 0],
            [["Ready", [5, 2]], "assumption", [], 1],
            [["Ready", [6, 2]], "transport", [4, 3, 1], 0],
            [["=", [9, 9]], "application", [], 0]
        ],
        [3, 5, null, null]
    ]);
    (request, certificate)
}

#[test]
fn static_application_replay_and_legacy() {
    let (request, certificate) = static_case();
    assert_eq!(
        replay_static_requirements(&request, &certificate).unwrap(),
        [true, true, false, false]
    );
    let request = json!([
        "zkc.requirements/1",
        [[null, "F"], [0, "Scalar"]],
        [],
        [],
        [["=", [1, 1]]]
    ]);
    let certificate = json!([
        "zkc.requirements-certificate/1",
        [[["=", [1, 1]], "reflexivity", [], 0]],
        [0]
    ]);
    assert_eq!(
        replay_static_requirements(&request, &certificate).unwrap(),
        [true]
    );
}

#[test]
fn static_application_refuses_malformed_steps_even_when_unused() {
    let (request, certificate) = static_case();
    // Premises name earlier facts: a well-formed but wrong list is an invalid
    // derivation, a reference to no earlier fact is a bad index.
    for (label, replacement, code) in [
        (
            "missing child",
            json!([0]),
            "requirements-invalid-derivation",
        ),
        (
            "extra child",
            json!([0, 1, 1]),
            "requirements-invalid-derivation",
        ),
        (
            "wrong order",
            json!([1, 0]),
            "requirements-invalid-derivation",
        ),
        ("self reference", json!([0, 2]), "requirements-index"),
        ("forward reference", json!([0, 6]), "requirements-index"),
        ("out of range", json!([0, 65536]), "requirements-index"),
    ] {
        let mut bad = certificate.clone();
        bad[1][2][2] = replacement;
        assert_eq!(
            replay_static_requirements(&request, &bad).unwrap_err(),
            code,
            "{label}"
        );
    }
    for (label, replacement) in [
        ("different head", json!(["=", [3, 7]])),
        ("reordered children", json!(["=", [3, 8]])),
        ("root instead of application", json!(["=", [0, 1]])),
        ("relation conclusion", json!(["Ready", [3, 4]])),
    ] {
        let mut bad = certificate.clone();
        bad[1][2][0] = replacement;
        bad[2] = json!([null, null, null, null]);
        assert_eq!(
            replay_static_requirements(&request, &bad).unwrap_err(),
            "requirements-invalid-derivation",
            "{label}"
        );
    }
    let mut bad = certificate.clone();
    bad[1][2][3] = json!(1);
    assert_eq!(
        replay_static_requirements(&request, &bad).unwrap_err(),
        "requirements-declaration"
    );
    bad = certificate.clone();
    bad[2][0] = json!(0);
    assert_eq!(
        replay_static_requirements(&request, &bad).unwrap_err(),
        "requirements-wrong-conclusion"
    );
    // One request format and one certificate format; a raised version name
    // is refused rather than read as a variant of the same content.
    bad = certificate.clone();
    bad[0] = json!("zkc.requirements-certificate/2");
    assert_eq!(
        replay_static_requirements(&request, &bad).unwrap_err(),
        "requirements-version"
    );
    let mut raised = request.clone();
    raised[0] = json!("zkc.requirements/2");
    assert_eq!(
        replay_static_requirements(&raised, &certificate).unwrap_err(),
        "requirements-version"
    );
}

#[test]
fn static_application_formation_is_finite_and_exact() {
    let (request, certificate) = static_case();
    for (label, replacement, code) in [
        (
            "empty head",
            json!(["apply", "", [0, 2]]),
            "requirements-name",
        ),
        (
            "long head",
            json!(["apply", "a".repeat(257), [0, 2]]),
            "requirements-name",
        ),
        (
            "self child",
            json!(["apply", "Poly", [3, 2]]),
            "requirements-index",
        ),
        (
            "forward child",
            json!(["apply", "Poly", [4, 2]]),
            "requirements-index",
        ),
        (
            "negative child",
            json!(["apply", "Poly", [-1, 2]]),
            "requirements-index",
        ),
        (
            "noninteger child",
            json!(["apply", "Poly", [0.5, 2]]),
            "requirements-index",
        ),
        (
            "too many children",
            json!(["apply", "Poly", vec![0; 17]]),
            "requirements-limit",
        ),
        (
            "unknown tag",
            json!(["effect", "Poly", [0, 2]]),
            "requirements-term",
        ),
        (
            "extra field",
            json!(["apply", "Poly", [0, 2], null]),
            "requirements-limit",
        ),
        (
            "projection of a later term",
            json!([3, "F"]),
            "requirements-term-index",
        ),
        ("not an array", json!("F"), "requirements-array"),
    ] {
        let mut bad = request.clone();
        bad[1][3] = replacement;
        assert_eq!(
            replay_static_requirements(&bad, &certificate).unwrap_err(),
            code,
            "{label}"
        );
    }
    let mut bad = request.clone();
    bad[1][4] = bad[1][3].clone();
    assert_eq!(
        replay_static_requirements(&bad, &certificate).unwrap_err(),
        "requirements-duplicate-term"
    );
    // Nullary application, projection and root occupy different identities.
    let request = json!([
        "zkc.requirements/1",
        [[null, "X"], ["apply", "X", []], [0, "X"]],
        [],
        [],
        []
    ]);
    assert!(
        replay_static_requirements(&request, &json!(["zkc.requirements-certificate/1", [], []]))
            .is_ok()
    );
}

#[test]
fn static_application_native_certificates_replay_in_rust_and_lean() {
    use std::io::Write;
    use std::process::{Command, Stdio};
    use zkc_test_support::{Build, checker, tool};
    let engine = tool(Build::Compiler, "test/zkc-requirements-test");
    let lean = checker("requirement-checker");
    let invoke = |program: &std::path::Path, value: &Json, accepted: bool| {
        let mut child = Command::new(program)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(&serde_json::to_vec(value).unwrap())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert_eq!(
            output.status.success(),
            accepted,
            "{}: {} {}",
            program.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        if accepted {
            serde_json::from_slice::<Json>(&output.stdout).unwrap()
        } else {
            Json::Null
        }
    };
    let (request, _) = static_case();
    let cert = invoke(&engine, &request, true);
    assert_eq!(
        replay_static_requirements(&request, &cert).unwrap(),
        [true, true, false, false]
    );
    assert_eq!(
        invoke(&lean, &json!([request, cert]), true),
        json!(["checked", ["proved", "proved", "unresolved", "unresolved"]])
    );
    let application = cert[1]
        .as_array()
        .unwrap()
        .iter()
        .position(|s| s[1] == "application")
        .unwrap();
    for (premises, code) in [
        (json!([]), "requirements-invalid-derivation"),
        (json!([application]), "requirements-index"),
        (json!([65536, 0]), "requirements-index"),
    ] {
        let mut damaged = cert.clone();
        damaged[1][application][2] = premises;
        assert_eq!(
            replay_static_requirements(&request, &damaged).unwrap_err(),
            code
        );
        invoke(&lean, &json!([request, damaged]), false);
    }
    // Independent readers reject malformed finite application tables too.
    for (term, code) in [
        (json!(["apply", "Poly", [3, 2]]), "requirements-index"),
        (json!(["apply", "", [0, 2]]), "requirements-name"),
        (json!(["apply", "Poly", vec![0; 17]]), "requirements-limit"),
        (json!(["effect", "Poly", [0, 2]]), "requirements-term"),
    ] {
        let mut malformed = request.clone();
        malformed[1][3] = term;
        invoke(&engine, &malformed, false);
        assert_eq!(
            replay_static_requirements(&malformed, &cert).unwrap_err(),
            code
        );
        invoke(&lean, &json!([malformed, cert]), false);
    }
}

#[test]
fn replay_rules_hold_without_static_applications() {
    let request = json!([
        "zkc.requirements/1",
        [
            [null, "A"],
            [null, "B"],
            [null, "C"],
            [0, "Member"],
            [2, "Member"]
        ],
        [["=", [0, 1]], ["=", [1, 2]], ["Field", [3]]],
        [["Field", "Ring"]],
        [["Ring", [4]]]
    ]);
    let certificate = json!([
        "zkc.requirements-certificate/1",
        [
            [["=", [0, 1]], "assumption", [], 0],
            [["=", [1, 2]], "assumption", [], 1],
            [["=", [0, 0]], "reflexivity", [], 0],
            [["=", [1, 0]], "symmetry", [0], 0],
            [["=", [0, 2]], "transitivity", [0, 1], 0],
            [["=", [3, 4]], "projection", [4], 0],
            [["Field", [3]], "assumption", [], 2],
            [["Field", [4]], "transport", [6, 5], 0],
            [["Ring", [4]], "implication", [7], 0]
        ],
        [8]
    ]);
    assert_eq!(
        replay_static_requirements(&request, &certificate).unwrap(),
        [true]
    );
    // An assumption that is not declared or a false reflexivity is an invalid
    // derivation; a premise that names the step itself is a bad index.
    for i in 0..9 {
        let mut bad = certificate.clone();
        let code = match bad[1][i][1].as_str().unwrap() {
            "assumption" => {
                bad[1][i][3] = json!(3);
                "requirements-invalid-derivation"
            }
            "reflexivity" => {
                bad[1][i][0] = json!(["=", [0, 1]]);
                "requirements-invalid-derivation"
            }
            _ => {
                bad[1][i][2][0] = json!(i);
                "requirements-index"
            }
        };
        assert_eq!(
            replay_static_requirements(&request, &bad).unwrap_err(),
            code,
            "step {i}"
        );
    }
    for (i, wrong) in [(4, json!([1, 0])), (7, json!([6, 4])), (8, json!([6]))] {
        let mut bad = certificate.clone();
        bad[1][i][2] = wrong;
        assert_eq!(
            replay_static_requirements(&request, &bad).unwrap_err(),
            "requirements-invalid-derivation",
            "step {i} conclusion"
        );
    }
}

#[test]
fn malformed_request_and_certificate_shapes_name_the_failed_field() {
    let (request, certificate) = static_case();
    let refused = |request: &Json, certificate: &Json| {
        replay_static_requirements(request, certificate).unwrap_err()
    };
    let mut short = request.clone();
    short.as_array_mut().unwrap().pop();
    assert_eq!(refused(&short, &certificate), "requirements-format");
    let mut short = certificate.clone();
    short.as_array_mut().unwrap().pop();
    assert_eq!(refused(&request, &short), "requirements-format");
    assert_eq!(refused(&json!("x"), &certificate), "requirements-array");
    let mut long = request.clone();
    long[1] = json!(vec![json!([null, "F"]); 129]);
    assert_eq!(refused(&long, &certificate), "requirements-limit");
    for (predicate, code) in [
        (json!(["="]), "requirements-predicate"),
        (json!(["=", [0]]), "requirements-equality"),
        (json!([7, [0, 1]]), "requirements-name"),
    ] {
        let mut bad = request.clone();
        bad[2][0] = predicate;
        assert_eq!(refused(&bad, &certificate), code);
    }
    for (rules, code) in [
        (json!([["Field"]]), "requirements-implication"),
        (json!([["=", "Ring"]]), "requirements-implication"),
    ] {
        let mut bad = request.clone();
        bad[3] = rules;
        assert_eq!(refused(&bad, &certificate), code);
    }
    let mut bad = certificate.clone();
    bad[1][0] = json!([["=", [0, 1]], "assumption", []]);
    assert_eq!(refused(&request, &bad), "requirements-step");
    // The conclusion, premises and declaration all parse before the tag.
    bad = certificate.clone();
    bad[1][0][1] = json!(0);
    assert_eq!(refused(&request, &bad), "requirements-rule");
    bad = certificate.clone();
    bad[1][0][3] = json!(-1);
    assert_eq!(refused(&request, &bad), "requirements-index");
    bad = certificate.clone();
    bad[2] = json!([3, 5, null]);
    assert_eq!(refused(&request, &bad), "requirements-goal-count");
}

#[test]
fn compact_application_dags_and_large_proofs_have_explicit_work_limits() {
    let mut terms = vec![json!([null, "x"])];
    for child in 0..30 {
        terms.push(json!(["apply", "F", [child, child]]));
    }
    let request = json!(["zkc.requirements/1", terms, [], [], [["=", [30, 30]]]]);
    let certificate = json!([
        "zkc.requirements-certificate/1",
        [[["=", [30, 30]], "reflexivity", [], 0]],
        [0]
    ]);
    assert_eq!(
        replay_static_requirements(&request, &certificate).unwrap_err(),
        "requirements-work-limit"
    );

    let terms = request[1].as_array().unwrap()[..13].to_vec();
    let request = json!(["zkc.requirements/1", terms, [], [], [["=", [12, 12]]]]);
    let step = json!([["=", [12, 12]], "reflexivity", [], 0]);
    let small = json!(["zkc.requirements-certificate/1", [step.clone()], [0]]);
    assert_eq!(
        replay_static_requirements(&request, &small).unwrap(),
        [true]
    );
    let large = json!(["zkc.requirements-certificate/1", vec![step; 17], [0]]);
    assert_eq!(
        replay_static_requirements(&request, &large).unwrap_err(),
        "requirements-work-limit"
    );
}
