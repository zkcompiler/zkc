use crate::files::hex;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use zkc_runtime::logical;
fn hash(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn deployment() -> Json {
    let boolean = "bool@native.bool/0";
    let candidate = json!([
        "zkc.program/0",
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
            "zkc.native-origin-template/0",
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
        "zkc.native-proof-descriptor/0",
        [
            "zkc.native-proof-policy/0",
            "main",
            "P",
            "V",
            "3",
            "",
            [],
            ["2"],
            [],
            "zkc.framed/0",
            ""
        ],
        "zkc.native-origin/0",
        [["message", first], ["message", second]],
        [["V", "2", "bool", "zkcv.bool/0"]],
        [
            [first, "bool", "zkcv.bool/0"],
            [second, "bool", "zkcv.bool/0"]
        ],
        []
    ]);
    let mut result = json!([
        "zkc.native-proof/0",
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
        ["true", "false", "false", "true", "false", "true"],
        [[first, "first"], [second, "second"]]
    ]);
    seal(&mut result);
    result
}

fn seal(value: &mut Json) {
    value[3] = json!(hash(&logical::encode_tree(&value[2]).unwrap()));
    value[5] = json!(hash(value[4].as_str().unwrap().as_bytes()));
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
        "zkc.native-proof-inputs/0",
        [["V", "2", "5a4b4356000501"]],
        [
            ["0", ["wire", "5a4b4356000500"]],
            ["1", ["wire", "5a4b4356000501"]],
            ["2", ["wire", "5a4b4356000501"]]
        ],
        "",
        [],
        "0"
    ])
    .to_string();
    std::fs::write(&bundle, &raw).unwrap();
    std::fs::write(&input, &encoded).unwrap();
    std::fs::write(&authority, br#"["zkc.native-setup-authority/0",[],[]]"#).unwrap();
    let args = |destination: &std::path::Path| {
        vec![
            bundle.display().to_string(),
            hash(raw.as_bytes()),
            input.display().to_string(),
            destination.display().to_string(),
            format!("--setups={}", authority.display()),
            "--allow-authored".into(),
        ]
    };
    for path in [&bundle, &input, &authority] {
        let previous = std::fs::read(path).unwrap();
        let report = crate::cli::run("bundle prove", &args(path));
        assert_eq!(report["code"], "artifact-output-path", "{report}");
        assert_eq!(std::fs::read(path).unwrap(), previous);
    }
    std::fs::hard_link(&input, &proof).unwrap();
    assert_eq!(
        crate::cli::run("bundle prove", &args(&proof))["code"],
        "artifact-output-path"
    );
    std::fs::remove_file(&proof).unwrap();
    let report = crate::cli::run("bundle prove", &args(&proof));
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
            crate::cli::run("bundle prove", &args(&proof))["code"],
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
    for command in ["bundle prove", "bundle verify"] {
        for allow_authored in [false, true] {
            let mut args = vec![
                bundle.display().to_string(),
                String::new(),
                inputs.display().to_string(),
                proof.display().to_string(),
            ];
            if allow_authored {
                args.push("--allow-authored".into());
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
                assert_eq!(report["phase"], "arguments");
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
                ["0", ["wire", "5a4b4356000500"]],
                ["1", ["wire", "5a4b4356000501"]],
                ["2", ["wire", "5a4b4356000501"]]
            ]),
        ),
        (&verifier, json!([["2", ["wire", "5a4b4356000501"]]])),
    ] {
        std::fs::write(
            path,
            json!([
                "zkc.native-proof-inputs/0",
                [["V", "2", "5a4b4356000501"]],
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
        ("bundle prove", &producer, "produced"),
        ("bundle verify", &verifier, "accepted"),
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
        for options in [vec![], vec!["--allow-authored"]] {
            let mut wrong_pin = args.clone();
            wrong_pin[1] = "0".repeat(64);
            wrong_pin.extend(options.into_iter().map(String::from));
            let refused = crate::cli::run(command, &wrong_pin);
            assert_eq!(refused["code"], "native-proof-deployment-binding");
            assert!(refused.get("binding_scope").is_none());
        }
        for options in [
            vec!["--allow-authored", "--allow-authored"],
            vec!["--allow-authored=true"],
        ] {
            let mut invalid = args.clone();
            invalid.extend(options.into_iter().map(String::from));
            assert_eq!(crate::cli::run(command, &invalid)["code"], "cli-option");
            assert_eq!(std::fs::read(&proof).unwrap(), previous);
        }
        let mut allowed = args;
        allowed.push("--allow-authored".into());
        allowed.push("--threads=2".into());
        let accepted = crate::cli::run(command, &allowed);
        assert!(crate::cli::succeeded(&accepted), "{accepted}");
        assert_eq!(accepted["status"], status);
        assert_eq!(accepted["binding_scope"], "header");
        assert_eq!(accepted["cpu"]["workers"], 2);
        if command == "bundle verify" {
            assert_eq!(std::fs::read(&proof).unwrap(), previous);
        }
    }
}
