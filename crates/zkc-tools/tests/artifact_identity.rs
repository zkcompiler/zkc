//! CLI ingress and independent inspection are available without a compiler/Lean
//! installation. Normalized construction execution is in artifact_identity.py.
use serde_json::{Value, json};
use std::{fs, process::Command};

fn inspect(source: &[u8], descriptor: &Value, configuration: &Value) -> (bool, Value) {
    let dir = zkc_test_support::evidence(module_path!());
    let s = dir.path().join("source.json");
    let d = dir.path().join("descriptor.json");
    let c = dir.path().join("configuration.json");
    fs::write(&s, source).unwrap();
    fs::write(&d, serde_json::to_vec(descriptor).unwrap()).unwrap();
    fs::write(&c, serde_json::to_vec(configuration).unwrap()).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_zkc"))
        .arg("inspect-artifact-identity")
        .args([s, d, c])
        .output()
        .unwrap();
    (
        result.status.success(),
        serde_json::from_slice(&result.stdout).unwrap(),
    )
}

fn fixture() -> (Value, Value, Value) {
    (
        json!([
            "zkc.protocol/1",
            [],
            [],
            [[
                "protocol",
                "Exchange",
                ["P", "V"],
                [],
                [["a", "P", "bool"], ["b", "V", "bool"]],
                [["V", "bool"]],
                [],
                [
                    [
                        "message",
                        "original_site",
                        "bool-wire",
                        "P",
                        "V",
                        "a",
                        "received"
                    ],
                    ["return", ["received"]]
                ]
            ]],
            [[
                "instance",
                "exchange",
                "Exchange",
                [],
                [],
                [["P", "P"], ["V", "V"]]
            ]],
            [["entry", "main", "exchange"]]
        ]),
        json!([
            "zkc.construction/1",
            "main",
            "P",
            "V",
            [],
            ["coins", []],
            "0",
            "merlin3.bls12-381.fr64be/1",
            "normalized"
        ]),
        json!([
            "zkc.public-configuration/1",
            [],
            [],
            [["exchange", "V", "original_site", "vk"]]
        ]),
    )
}

#[test]
fn inspection_emits_reviewable_trees_and_separates_byte_digest_from_identity() {
    let (s, d, c) = fixture();
    let (ok, report) = inspect(&serde_json::to_vec(&s).unwrap(), &d, &c);
    assert!(ok);
    assert_eq!(report["status"], "inspected");
    // This deliberately lacks a selected RNG: inspection makes no admission claim.
    assert_eq!(report["admission"], "not-checked");
    assert_eq!(report["normalized_protocol"].as_array().unwrap().len(), 7);
    assert_eq!(report["resolved_source"][3][0][7][0][1], "site0");
    assert_eq!(report["resolved_configuration"][3][0][2], "site0");
    assert_eq!(
        report["normalized_protocol"][3][0][7][0],
        json!(["message", "site0", "bool-wire", "P", "V", "v0", "v2"])
    );
    let (_, pretty) = inspect(&serde_json::to_vec_pretty(&s).unwrap(), &d, &c);
    assert_eq!(pretty["normalized_protocol"], report["normalized_protocol"]);
    assert_ne!(pretty["source_sha256"], report["source_sha256"]);
}

#[test]
fn inspection_checks_bytes_and_tree_before_parsing_or_resolving() {
    let (_, d, c) = fixture();
    for (source, code) in [
        (vec![b' '; (1 << 20) + 1], "artifact-byte-limit"),
        (vec![b'['; 66], "artifact-json-depth"),
        (b"{}".to_vec(), "artifact-json-kind"),
        (b"[0]".to_vec(), "tree-kind"),
        (b"[]".to_vec(), "identity-source-version"),
    ] {
        let (ok, report) = inspect(&source, &d, &c);
        assert!(!ok);
        assert_eq!(report["code"], code);
    }
}
