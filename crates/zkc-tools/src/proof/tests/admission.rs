//! Independently authored Program and deployment: the verifier returns the
//! second received Boolean. Public input binding is a separate Host property.
use super::*;

fn deployment() -> Json {
    let boolean = "bool@native.bool/1";
    let candidate = json!([
        "zkc.program",
        [],
        [],
        [
            [
                "participant",
                "p",
                "root",
                "P",
                [["a", boolean], ["b", boolean], ["public", boolean]],
                [],
                [
                    ["send", "first", "first", "V", "a"],
                    ["send", "second", "second", "V", "b"],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "v",
                "root",
                "V",
                [["public", boolean]],
                [boolean],
                [
                    ["receive", "first", "first", "P", "a", boolean],
                    ["receive", "second", "second", "P", "b", boolean],
                    ["return", ["b"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ]);
    let origin = |site| {
        hex(&logical::encode_tree(&json!([
            "zkc.native-origin-template",
            "main",
            [],
            [],
            ["message", "protocol", site, site, "P", "V"]
        ]))
        .unwrap())
    };
    let first = origin("first");
    let second = origin("second");
    let descriptor = json!([
        "zkc.native-proof-descriptor",
        [
            "zkc.native-proof-policy",
            "main",
            "P",
            "V",
            "3",
            "",
            "",
            ["2"],
            []
        ],
        "zkc.native-origin",
        [["message", first], ["message", second]],
        [["V", "2", "bool", "zkcv.bool/1"]],
        [
            [first, "bool", "zkcv.bool/1"],
            [second, "bool", "zkcv.bool/1"]
        ]
    ]);
    let mut result = json!([
        "zkc.native-proof",
        "0".repeat(64),
        descriptor,
        "",
        candidate.to_string(),
        "",
        [
            [
                "P",
                "p",
                [["0", "bool"], ["1", "bool"], ["2", "bool"]],
                [],
                [],
                ""
            ],
            ["V", "v", [["2", "bool"]], [["3", "bool"]], [], "0"]
        ],
        ["true", "false"],
        [[first, "first"], [second, "second"]]
    ]);
    seal(&mut result);
    result
}

fn seal(value: &mut Json) {
    value[3] = json!(hash(&logical::encode_tree(&value[2]).unwrap()));
    value[5] = json!(hash(value[4].as_str().unwrap().as_bytes()));
}

fn admit(value: &Json) -> Result<NativeDeployment> {
    let bytes = serde_json::to_vec(value).unwrap();
    NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
}

fn request(producer: bool, decision: bool, public: bool) -> ProofInputs {
    let value = |v| InputValue::Native(Box::new(Value::Bool(v)));
    ProofInputs {
        public: vec![value(public)],
        inputs: if producer {
            vec![value(!decision), value(decision), value(public)]
        } else {
            vec![value(public)]
        },
        context: b"independent host case".to_vec(),
        services: vec![],
        transcript_budget: 0,
    }
}

#[test]
fn proof_cli_preserves_trusted_inputs_and_publishes_only_to_distinct_regular_paths() {
    let directory = tempfile::tempdir().unwrap();
    let bundle = directory.path().join("bundle");
    let input = directory.path().join("inputs");
    let proof = directory.path().join("proof");
    let authority = directory.path().join("authority");
    let raw = deployment().to_string();
    let encoded = json!([
        "zkc.native-proof-inputs",
        [["V", "2", "5a4b4356010501"]],
        [
            ["0", ["wire", "5a4b4356010500"]],
            ["1", ["wire", "5a4b4356010501"]],
            ["2", ["wire", "5a4b4356010501"]]
        ],
        "",
        [],
        "0"
    ])
    .to_string();
    std::fs::write(&bundle, &raw).unwrap();
    std::fs::write(&input, &encoded).unwrap();
    std::fs::write(&authority, br#"["zkc.native-setup-authority",[],[]]"#).unwrap();
    let args = |destination: &std::path::Path| {
        vec![
            bundle.display().to_string(),
            hash(raw.as_bytes()),
            input.display().to_string(),
            destination.display().to_string(),
            format!("--setups={}", authority.display()),
            "--allow-header-only".into(),
        ]
    };
    for path in [&bundle, &input, &authority] {
        let previous = std::fs::read(path).unwrap();
        let report = crate::cli::run("prove-bundle", &args(path));
        assert_eq!(report["code"], "artifact-output-path", "{report}");
        assert_eq!(std::fs::read(path).unwrap(), previous);
    }
    std::fs::hard_link(&input, &proof).unwrap();
    assert_eq!(
        crate::cli::run("prove-bundle", &args(&proof))["code"],
        "artifact-output-path"
    );
    std::fs::remove_file(&proof).unwrap();
    let report = crate::cli::run("prove-bundle", &args(&proof));
    assert!(crate::cli::succeeded(&report), "{report}");
    assert_eq!(report["proof_published"], true);
    assert_eq!(report["publication"]["published"], json!(["proof"]));
    assert_eq!(std::fs::read(&input).unwrap(), encoded.as_bytes());
    #[cfg(unix)]
    {
        std::fs::remove_file(&input).unwrap();
        assert!(
            std::process::Command::new("mkfifo")
                .arg(&input)
                .status()
                .unwrap()
                .success()
        );
        let prior = std::fs::read(&proof).unwrap();
        assert_eq!(
            crate::cli::run("prove-bundle", &args(&proof))["code"],
            "artifact-io"
        );
        assert_eq!(std::fs::read(&proof).unwrap(), prior);
    }
}

#[test]
fn proof_cli_rejects_malformed_pins_before_typed_admission() {
    let directory = tempfile::tempdir().unwrap();
    let bundle = directory.path().join("bundle");
    let inputs = directory.path().join("missing-inputs");
    let proof = directory.path().join("proof");
    // Correct lexical pins reach authentication and then decoding of these bytes.
    // Malformed lexical pins must be diagnosed by the CLI before either step.
    std::fs::write(&bundle, b"[").unwrap();
    std::fs::write(&proof, b"previous proof").unwrap();
    for command in ["prove-bundle", "verify-bundle"] {
        for allow_header_only in [false, true] {
            let mut args = vec![
                bundle.display().to_string(),
                String::new(),
                inputs.display().to_string(),
                proof.display().to_string(),
            ];
            if allow_header_only {
                args.push("--allow-header-only".into());
            }
            for pin in [
                String::new(),
                "0".repeat(63),
                "0".repeat(65),
                "AB".repeat(32),
                "g".repeat(64),
                format!("0x{}", "0".repeat(64)),
                format!(" {}", "0".repeat(63)),
                format!("{}\n", "0".repeat(63)),
                "é".repeat(32),
            ] {
                args[1] = pin;
                let report = crate::cli::run(command, &args);
                assert!(!crate::cli::succeeded(&report));
                assert_eq!(report["code"], "native-proof-digest", "{args:?}: {report}");
                assert_eq!(report["phase"], "admission");
                assert!(report.get("binding_scope").is_none());
                assert_eq!(std::fs::read(&proof).unwrap(), b"previous proof");
            }
            for (pin, code) in [
                ("0".repeat(64), "native-proof-deployment-binding"),
                (hash(b"["), "artifact-json"),
            ] {
                args[1] = pin;
                let report = crate::cli::run(command, &args);
                assert_eq!(report["code"], code, "{report}");
                assert_eq!(report["phase"], "admission");
                assert!(report.get("binding_scope").is_none());
                assert_eq!(std::fs::read(&proof).unwrap(), b"previous proof");
            }
        }
    }
}

#[test]
fn proof_cli_requires_explicit_header_policy_after_independent_pin_admission() {
    let directory = tempfile::tempdir().unwrap();
    let bundle = directory.path().join("bundle");
    let producer = directory.path().join("producer");
    let verifier = directory.path().join("verifier");
    let proof = directory.path().join("proof");
    let raw = deployment().to_string();
    let pin = hash(raw.as_bytes());
    std::fs::write(&bundle, &raw).unwrap();
    for (path, inputs) in [
        (
            &producer,
            json!([
                ["0", ["wire", "5a4b4356010500"]],
                ["1", ["wire", "5a4b4356010501"]],
                ["2", ["wire", "5a4b4356010501"]]
            ]),
        ),
        (&verifier, json!([["2", ["wire", "5a4b4356010501"]]])),
    ] {
        std::fs::write(
            path,
            json!([
                "zkc.native-proof-inputs",
                [["V", "2", "5a4b4356010501"]],
                inputs,
                "",
                [],
                "0"
            ])
            .to_string(),
        )
        .unwrap();
    }
    std::fs::write(&proof, b"previous proof").unwrap();
    for (command, input, status) in [
        ("prove-bundle", &producer, "produced"),
        ("verify-bundle", &verifier, "accepted"),
    ] {
        let args = vec![
            bundle.display().to_string(),
            pin.clone(),
            input.display().to_string(),
            proof.display().to_string(),
        ];
        let previous = std::fs::read(&proof).unwrap();
        let refused = crate::cli::run(command, &args);
        assert!(!crate::cli::succeeded(&refused));
        assert_eq!(refused["code"], "native-proof-binding-policy", "{refused}");
        assert_eq!(refused["phase"], "admission");
        assert_eq!(refused["binding_scope"], "header");
        assert_eq!(std::fs::read(&proof).unwrap(), previous);
        let mut absent = args.clone();
        absent[3] = directory.path().join("absent").display().to_string();
        assert_eq!(
            crate::cli::run(command, &absent)["code"],
            "native-proof-binding-policy"
        );
        assert!(!std::path::Path::new(&absent[3]).exists());
        // Invocation bytes and proof reads occur only after the policy check.
        absent[2] = directory
            .path()
            .join("missing-inputs")
            .display()
            .to_string();
        assert_eq!(
            crate::cli::run(command, &absent)["code"],
            "native-proof-binding-policy"
        );
        for options in [vec![], vec!["--allow-header-only"]] {
            let mut wrong_pin = args.clone();
            wrong_pin[1] = "0".repeat(64);
            wrong_pin.extend(options.into_iter().map(String::from));
            let refused = crate::cli::run(command, &wrong_pin);
            assert_eq!(refused["code"], "native-proof-deployment-binding");
            assert!(refused.get("binding_scope").is_none());
        }
        for options in [
            vec!["--allow-header-only", "--allow-header-only"],
            vec!["--allow-header-only=true"],
        ] {
            let mut invalid = args.clone();
            invalid.extend(options.into_iter().map(String::from));
            assert_eq!(
                crate::cli::run(command, &invalid)["code"],
                "native-proof-option"
            );
            assert_eq!(std::fs::read(&proof).unwrap(), previous);
        }
        let mut allowed = args;
        allowed.push("--allow-header-only".into());
        let accepted = crate::cli::run(command, &allowed);
        assert!(crate::cli::succeeded(&accepted), "{accepted}");
        assert_eq!(accepted["status"], status);
        assert_eq!(accepted["binding_scope"], "header");
        if command == "verify-bundle" {
            assert_eq!(std::fs::read(&proof).unwrap(), previous);
        }
    }
}

#[test]
fn actual_received_decision_and_public_context_govern_verification() {
    let deployment = admit(&deployment()).unwrap();
    for decision in [false, true] {
        let produced = deployment
            .execute_typed(&request(true, decision, true), None)
            .unwrap();
        assert!(produced.cleanup_errors.is_empty());
        assert_eq!(produced.messages, 2);
        let proof = produced.outcome.unwrap();
        // Two canonical Boolean frames, in the actual send order.
        assert_eq!(proof.len(), 70);
        let mut expected = Vec::new();
        for value in [!decision, decision] {
            expected.extend([7, 0, 0, 0, 0, 0, 0, 0]);
            expected.extend(b"ZKCV\x01\x05");
            expected.push(u8::from(value));
        }
        assert_eq!(&proof[40..], expected);
        let verified = deployment
            .execute_typed(&request(false, true, true), Some(&proof))
            .unwrap();
        assert_eq!(verified.messages, 2);
        assert!(verified.cleanup_errors.is_empty());
        if decision {
            assert!(verified.outcome.is_ok());
            assert!(matches!(verified.outputs.unwrap()[&3], Value::Bool(true)));
            let changed = deployment
                .execute_typed(&request(false, true, false), Some(&proof))
                .unwrap();
            assert_eq!(changed.outcome.unwrap_err(), "proof-header");
            assert!(changed.outputs.is_none());
        } else {
            assert_eq!(verified.outcome.unwrap_err(), "artifact-rejected");
            assert!(verified.outputs.is_none());
        }
    }
}

#[test]
fn wire_role_public_and_authority_checks_keep_their_refusal_order() {
    let valid = deployment();
    let mut bad = valid.clone();
    bad[8][0][1] = json!("second");
    bad[8][1][1] = json!("first");
    bad[6][0][1] = json!("wrong-participant");
    bad[2][4][0][1] = json!("1");
    seal(&mut bad);
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-wire-map");
    bad[8] = valid[8].clone();
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-role-map");
    bad[6] = valid[6].clone();
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-public-map");
    bad[2][4] = valid[2][4].clone();
    seal(&mut bad);
    let bytes = serde_json::to_vec(&bad).unwrap();
    let extra_authority = SetupAuthority {
        keys: [(2, [0; 32])].into(),
        inputs: BTreeMap::new(),
    };
    assert_eq!(
        NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), extra_authority)
            .unwrap_err(),
        "native-proof-key-authority"
    );
    assert!(admit(&bad).is_ok());
}

#[test]
fn typed_pin_admission_limits_then_authenticates_before_decoding() {
    let bytes = serde_json::to_vec(&deployment()).unwrap();
    let expected_sha256: [u8; 32] = Sha256::digest(&bytes).into();
    let admitted = NativeDeployment::admit(&bytes, &expected_sha256, Default::default()).unwrap();
    assert_eq!(admitted.publication, hex(&expected_sha256));

    assert_eq!(
        NativeDeployment::admit(
            &vec![b'['; INPUT_LIMIT + 1],
            &expected_sha256,
            Default::default(),
        )
        .unwrap_err(),
        "native-proof-deployment-limit"
    );
    assert_eq!(
        NativeDeployment::admit(b"[", &expected_sha256, Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    assert_eq!(
        NativeDeployment::admit(b"[", &Sha256::digest(b"[").into(), Default::default())
            .unwrap_err(),
        "artifact-json"
    );

    // Even a semantically identical JSON payload cannot reuse the original pin.
    let mut changed = bytes;
    changed.push(b'\n');
    assert_eq!(
        NativeDeployment::admit(&changed, &expected_sha256, Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    assert!(
        NativeDeployment::admit(
            &changed,
            &Sha256::digest(&changed).into(),
            Default::default(),
        )
        .is_ok()
    );
}

#[test]
fn authenticated_payload_still_requires_canonical_inner_source_digest() {
    let mut value = deployment();
    for source in [
        String::new(),
        "0".repeat(63),
        "0".repeat(65),
        "AB".repeat(32),
        "g".repeat(64),
        format!("0x{}", "0".repeat(62)),
        "é".repeat(32),
    ] {
        value[1] = json!(source);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-digest");
    }
    value[1] = json!("ab".repeat(32));
    assert!(admit(&value).is_ok());
}

#[test]
fn authentication_and_inner_bindings_precede_candidate_and_interface_checks() {
    assert_eq!(
        NativeDeployment::admit(b"not json", &[0; 32], Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    let mut bad = deployment();
    bad[3] = json!("0".repeat(64));
    bad[4] = json!("invalid candidate");
    bad[6] = json!([]);
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-descriptor-binding");
    bad[3] = json!(hash(&logical::encode_tree(&bad[2]).unwrap()));
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-candidate-binding");
    seal(&mut bad);
    // Compare with independent ordinary Program admission of the same bad bytes.
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "native-proof", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let expected = admit_supplied(b"invalid candidate", &backend)
        .unwrap_err()
        .to_string();
    assert_eq!(admit(&bad).unwrap_err(), expected);
}

#[test]
fn message_origins_are_unique_complete_and_match_both_participants() {
    let valid = deployment();
    let mut duplicate = valid.clone();
    duplicate[2][3][1] = duplicate[2][3][0].clone();
    seal(&mut duplicate);
    assert_eq!(admit(&duplicate).unwrap_err(), "native-proof-origin-map");
    let mut missing = valid.clone();
    missing[2][5].as_array_mut().unwrap().pop();
    seal(&mut missing);
    assert_eq!(admit(&missing).unwrap_err(), "native-proof-message-map");
    let mut drift = valid;
    let mut candidate: Json = serde_json::from_str(drift[4].as_str().unwrap()).unwrap();
    candidate[3][1][6][0][2] = json!("other-schema");
    drift[4] = json!(candidate.to_string());
    seal(&mut drift);
    assert_eq!(admit(&drift).unwrap_err(), "native-proof-wire-map");
}
