use super::*;
use serde_json::json;
use std::fs;

pub(crate) fn source_record(entry: &str, body: &str) -> Value {
    let identity = "00".repeat(32);
    let limits = json!({"rounds":10,"public_elements":1024,"frame_bytes":65536,
        "public_bytes":131072,"context_bytes":4096,"proof_bytes":65536,
        "calldata_bytes":262144,"root_bytes":262144,"memory_bytes":2097152,
        "transcript_transitions":64,"practical_gas":20000000});
    let policy = json!([
        "zkc.native-proof-policy/0",
        "main",
        "P",
        "V",
        "0",
        "hash-chain.keccak256.bls12-381.fr64be/0",
        ["1"],
        ["0"],
        [["challenge", "delivery"]],
        "zkc.framed/0",
        "",
        []
    ]);
    let origin = |event: Value| {
        crate::io::bytes::hex(
            &zkc_format::logical::encode_tree(&json!([
                "zkc.native-origin-template/0",
                "main",
                [],
                [],
                event
            ]))
            .unwrap(),
        )
    };
    let query = origin(json!([
        "query",
        "main",
        "challenge",
        "input_1",
        "random.bls12-381.fr/0",
        "draw",
        "V"
    ]));
    let message = origin(json!(["message", "main", "delivery", "delivery", "P", "V"]));
    let descriptor = json!([
        "zkc.native-proof-descriptor/0",
        policy,
        "zkc.native-origin/0",
        [["query", query], ["message", message]],
        [["V", "0", "field:bls12-381.fr", "zkcv.field.bls12-381.fr/0"]],
        [[message, "field:bls12-381.fr", "zkcv.field.bls12-381.fr/0"]],
        [],
        [],
        "{\"authentication\":\"per-query\",\"format\":\"zkc.oracle-selection/0\",\"order\":\"unrestricted\",\"roots\":{\"entries\":[],\"kind\":\"exact\"}}"
    ]);
    let manifest = json!({"format":"zkc.evm-source-manifest/0", "target":"evm", "fork":"cancun",
        "entry":entry, "capture":identity, "installation":identity,
        "original":identity, "source_sha256":identity, "source_format":"zkc.original-mlir/0",
        "producer":"P", "validator":"V", "compiler":identity,
        "yul_sha256":hash(body.as_bytes()), "limits":limits, "solc_version":"0.8.38",
        "optimizer_steps":":", "release_validation":"pending-deployment-and-dynamic-trace"});
    json!({"format":"zkc.evm-source/0", "target":"evm", "fork":"cancun",
        "yul":body, "abi":super::calldata::abi(),"entry":entry,
        "capture":identity,"installation":identity,"original":identity,"source_sha256":identity,
        "manifest":manifest,"limits":limits,"descriptor":descriptor,"policy":policy})
}
fn source(body: &str) -> Source {
    Source::capture(&serde_json::to_vec(&source_record("Main::Proof", body)).unwrap()).unwrap()
}

// Keep malformed JSON at the selected location, including identical objects
// repeated in the response and its manifest. Value cannot retain duplicate keys.
fn with_raw_json(value: &Value, path: &str, raw: &str) -> String {
    if path.is_empty() {
        return raw.into();
    }
    let (head, tail) = path
        .strip_prefix('/')
        .unwrap()
        .split_once('/')
        .map_or((&path[1..], String::new()), |(head, tail)| {
            (head, format!("/{tail}"))
        });
    match value {
        Value::Object(object) => format!(
            "{{{}}}",
            object
                .iter()
                .map(|(key, value)| {
                    let text = if key == head {
                        with_raw_json(value, &tail, raw)
                    } else {
                        value.to_string()
                    };
                    format!("{}:{text}", serde_json::to_string(key).unwrap())
                })
                .collect::<Vec<_>>()
                .join(",")
        ),
        Value::Array(array) => format!(
            "[{}]",
            array
                .iter()
                .enumerate()
                .map(|(index, value)| {
                    if index.to_string() == head {
                        with_raw_json(value, &tail, raw)
                    } else {
                        value.to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join(",")
        ),
        _ => panic!("invalid fixture path {path}"),
    }
}
#[cfg(unix)]
fn fake_tool(directory: &Path, response: &str) -> Solc {
    use std::os::unix::fs::PermissionsExt;
    let path = directory.join("solc");
    fs::write(&path, format!("#!/bin/sh\nif [ \"$1\" = --version ]; then\n printf 'Version: {SOLC_VERSION}.Linux.g++\\n'\nelse\n cat >/dev/null\n printf '%s' '{}'\nfi\n", response.replace('\'', "'\\''"))).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    Solc::new(&path, &hash(&fs::read(&path).unwrap())).unwrap()
}
const RESPONSE: &str = r#"{"contracts":{"verifier.yul":{"Verifier":{"evm":{"bytecode":{"object":"60006000f3"},"deployedBytecode":{"object":"00"}}}}}}"#;
#[test]
fn source_transport_is_explicit_and_bounded() {
    assert!(Source::capture(br#"{"format":"zkc.native-package/0","yul":"x","abi":[]}"#).is_err());
    assert!(Source::capture(br#"{"format":"zkc.evm-source/0","yul":"","abi":[]}"#).is_err());
    let s = source("object \"Verifier\" { code {} }");
    assert_eq!(s.entry(), "Main::Proof");
    let mut missing = s.metadata().clone();
    missing.as_object_mut().unwrap().remove("capture");
    assert!(Source::capture(&serde_json::to_vec(&missing).unwrap()).is_err());
    let mut mismatch = s.metadata().clone();
    mismatch["entry"] = json!("Other::Proof");
    assert!(Source::capture(&serde_json::to_vec(&mismatch).unwrap()).is_err());
}

#[test]
fn source_objects_require_every_current_field_and_refuse_unknown_fields() {
    let valid = source_record("Main::Proof", "object \"Verifier\" { code {} }");
    let bytes = serde_json::to_vec_pretty(&valid).unwrap();
    assert_eq!(Source::capture(&bytes).unwrap().bytes(), bytes);
    for (path, code) in [
        ("", "evm-source-format"),
        ("/manifest", "evm-source-format"),
        ("/limits", "evm-source-limits"),
        ("/manifest/limits", "evm-source-limits"),
    ] {
        let fields = valid.pointer(path).unwrap().as_object().unwrap();
        for field in fields.keys() {
            let mut changed = valid.clone();
            changed
                .pointer_mut(path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .remove(field);
            assert_eq!(
                Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
                code,
                "missing {path}/{field}"
            );
            let mut changed = valid.clone();
            changed.pointer_mut(path).unwrap()[field] = Value::Null;
            assert!(
                Source::capture(&encode(&changed).unwrap()).is_err(),
                "null {path}/{field}"
            );
        }
        let mut changed = valid.clone();
        changed.pointer_mut(path).unwrap()["unknown"] = json!(0);
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            code,
            "unknown {path}"
        );
        for wrong in [Value::Null, json!([]), json!("object"), json!(true)] {
            let mut changed = valid.clone();
            *changed.pointer_mut(path).unwrap() = wrong;
            assert_eq!(
                Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
                code,
                "object kind {path}"
            );
        }
    }
    for path in ["/abi/0", "/abi/0/inputs/0", "/abi/0/outputs/0"] {
        let mut changed = valid.clone();
        changed.pointer_mut(path).unwrap()["unknown"] = json!(0);
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            "evm-source-format",
            "{path}"
        );
    }
}

#[test]
fn source_duplicate_keys_refuse_even_when_equal_escaped_or_nested() {
    let valid = source_record("Main::Proof", "object \"Verifier\" { code {} }");
    let serialized = serde_json::to_string(&valid).unwrap();
    for path in [
        "",
        "/manifest",
        "/limits",
        "/manifest/limits",
        "/abi/0",
        "/abi/0/inputs/0",
        "/abi/0/outputs/0",
    ] {
        let object = valid.pointer(path).unwrap();
        let original = serde_json::to_string(object).unwrap();
        for (key, value) in object.as_object().unwrap() {
            let escaped = format!("\"\\u{:04x}{}\"", key.as_bytes()[0], &key[1..]);
            for spelling in [serde_json::to_string(key).unwrap(), escaped] {
                for duplicate in [value.clone(), json!("contradictory duplicate")] {
                    let object = original.replacen('{', &format!("{{{spelling}:{duplicate},"), 1);
                    let malformed = with_raw_json(&valid, path, &object);
                    assert_ne!(malformed, serialized);
                    assert_eq!(
                        Source::capture(malformed.as_bytes()).unwrap_err().0,
                        "evm-json",
                        "{path}/{key}: {spelling}"
                    );
                }
            }
        }
    }
}

#[test]
fn source_formats_digests_and_repeated_metadata_are_checked_at_capture() {
    let valid = source_record("Main::Proof", "object \"Verifier\" { code {} }");
    for path in [
        "/format",
        "/target",
        "/fork",
        "/yul",
        "/entry",
        "/manifest/format",
        "/manifest/source_format",
        "/manifest/solc_version",
        "/manifest/optimizer_steps",
        "/manifest/release_validation",
    ] {
        let mut changed = valid.clone();
        *changed.pointer_mut(path).unwrap() = json!("");
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            "evm-source-format",
            "{path}"
        );
    }
    for key in [
        "capture",
        "installation",
        "original",
        "source_sha256",
        "entry",
        "target",
        "fork",
        "limits",
    ] {
        let mut changed = valid.clone();
        changed["manifest"][key] = match key {
            "entry" => json!("Other::Proof"),
            "target" => json!("cpu"),
            "fork" => json!("other"),
            "limits" => {
                let mut limits = valid["limits"].clone();
                limits["rounds"] = json!(9);
                limits
            }
            _ => json!("ab".repeat(32)),
        };
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            "evm-source-identity",
            "repeated {key}"
        );
    }
    for path in [
        "/capture",
        "/installation",
        "/original",
        "/source_sha256",
        "/manifest/compiler",
        "/manifest/yul_sha256",
    ] {
        for bad in [
            json!("aa"),
            json!("GG".repeat(32)),
            json!("AA".repeat(32)),
            json!(7),
        ] {
            let mut changed = valid.clone();
            *changed.pointer_mut(path).unwrap() = bad;
            assert_eq!(
                Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
                "evm-source-identity",
                "digest {path}"
            );
        }
    }
    let mut changed = valid.clone();
    changed["original"] = json!("ab".repeat(32));
    changed["manifest"]["original"] = changed["original"].clone();
    assert_eq!(
        Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
        "evm-source-identity"
    );
    let mut changed = valid;
    changed["yul"] = json!("changed Yul with an unchanged digest");
    assert_eq!(
        Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
        "evm-source-identity"
    );
}

#[test]
fn source_limits_are_positive_bounded_integers_with_the_complete_current_shape() {
    let valid = source_record("Main::Proof", "object \"Verifier\" { code {} }");
    for path in ["/limits", "/manifest/limits"] {
        for (key, ceiling) in valid["limits"].as_object().unwrap() {
            for bad in [
                json!(0),
                json!(ceiling.as_u64().unwrap() + 1),
                json!("1"),
                json!(true),
                Value::Null,
            ] {
                let mut changed = valid.clone();
                changed.pointer_mut(path).unwrap()[key] = bad;
                assert_eq!(
                    Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
                    "evm-source-limits",
                    "{path}/{key}"
                );
            }
            for bad in ["-1", "1.0", "1e0", "18446744073709551616"] {
                let original = serde_json::to_string(valid.pointer(path).unwrap()).unwrap();
                let object =
                    original.replace(&format!("\"{key}\":{ceiling}"), &format!("\"{key}\":{bad}"));
                let malformed = with_raw_json(&valid, path, &object);
                assert_eq!(
                    Source::capture(malformed.as_bytes()).unwrap_err().0,
                    "evm-json",
                    "{path}/{key}={bad}"
                );
            }
        }
    }
    let mut lowered = valid;
    for path in ["/limits", "/manifest/limits"] {
        for (key, value) in lowered.pointer_mut(path).unwrap().as_object_mut().unwrap() {
            *value = json!(if key == "memory_bytes" { 4096 } else { 1 });
        }
    }
    Source::capture(&encode(&lowered).unwrap()).unwrap();
    lowered["limits"]["memory_bytes"] = json!(4095);
    lowered["manifest"]["limits"] = lowered["limits"].clone();
    assert_eq!(
        Source::capture(&encode(&lowered).unwrap()).unwrap_err().0,
        "evm-source-limits"
    );
}

#[test]
fn source_descriptor_and_policy_keep_the_current_carriers_and_associations() {
    let valid = source_record("Main::Proof", "object \"Verifier\" { code {} }");
    for (path, bad) in [
        ("/descriptor", json!([])),
        ("/descriptor/0", json!("other")),
        ("/descriptor/2", json!("other")),
        ("/descriptor/3", json!({})),
        ("/descriptor/3/0", json!(["query"])),
        ("/descriptor/3/0/0", json!("unknown")),
        ("/descriptor/4/0", json!(["V", "0", "field:bls12-381.fr"])),
        ("/descriptor/5/0/1", json!(7)),
        ("/descriptor/6", json!(["unknown"])),
        ("/descriptor/7", Value::Null),
        ("/descriptor/8", json!("{}")),
    ] {
        let mut changed = valid.clone();
        *changed.pointer_mut(path).unwrap() = bad;
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            "evm-source-descriptor",
            "{path}"
        );
    }
    for (slot, bad) in [
        (0, json!("other")),
        (1, json!("")),
        (2, json!("V")),
        (4, json!("01")),
        (4, json!("1024")),
        (5, json!("other")),
        (6, json!([])),
        (6, json!(["1", "1"])),
        (7, json!(["0", "0"])),
        (7, json!(["1024"])),
        (8, json!([])),
        (8, json!([["challenge"]])),
        (8, json!([["challenge", "challenge"]])),
        (8, json!([["with space", "delivery"]])),
        (9, json!("zkc.raw-bytes/0")),
        (10, json!("custom")),
        (11, json!([["unknown", "0"]])),
        (11, json!([["challenge", "65"]])),
        (11, json!([["challenge", "0"], ["challenge", "0"]])),
    ] {
        let mut changed = valid.clone();
        changed["policy"][slot] = bad;
        changed["descriptor"][1] = changed["policy"].clone();
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            "evm-source-descriptor",
            "policy {slot}"
        );
    }
    for path in [
        "/descriptor/1/1",
        "/descriptor/4/0/0",
        "/descriptor/4/0/1",
        "/manifest/producer",
        "/manifest/validator",
    ] {
        let mut changed = valid.clone();
        *changed.pointer_mut(path).unwrap() = json!("different");
        let code = if path == "/descriptor/1/1" {
            "evm-source-descriptor"
        } else {
            "evm-source-identity"
        };
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            code,
            "{path}"
        );
    }
}

#[test]
fn source_capture_bounds_bytes_and_refuses_trailing_documents() {
    let valid = source("object \"Verifier\" { code {} }");
    let mut bytes = valid.bytes().to_vec();
    bytes.resize(MAX_BYTES, b' ');
    assert_eq!(Source::capture(&bytes).unwrap().bytes().len(), MAX_BYTES);
    bytes.push(b' ');
    assert_eq!(Source::capture(&bytes).unwrap_err().0, "evm-artifact-limit");
    let mut bytes = valid.bytes().to_vec();
    bytes.extend_from_slice(b"{}");
    assert_eq!(Source::capture(&bytes).unwrap_err().0, "evm-json");
}

#[test]
#[cfg(unix)]
fn artifact_import_rechecks_source_shape_even_with_matching_file_hashes_and_pin() {
    let directory = tempfile::tempdir().unwrap();
    let source = source("object \"Verifier\" { code {} }");
    let artifact = fake_tool(directory.path(), RESPONSE)
        .compile(Build {
            source: &source,
            compiler_sha256: &"09".repeat(32),
            reuse: None,
        })
        .unwrap();
    let output = directory.path().join("artifact");
    artifact.publish(&output).unwrap();
    let mut missing = source.metadata().clone();
    missing.as_object_mut().unwrap().remove("limits");
    let duplicate = with_raw_json(
        source.metadata(),
        "/manifest",
        &format!(
            "{{\"target\":\"cpu\",{}",
            &source.metadata()["manifest"].to_string()[1..]
        ),
    );
    for (bytes, code) in [
        (encode(&missing).unwrap(), "evm-source-format"),
        (duplicate.into_bytes(), "evm-json"),
    ] {
        let mut manifest = artifact.manifest().clone();
        manifest.files.insert("source.json".into(), hash(&bytes));
        let manifest = encode(&manifest).unwrap();
        fs::write(output.join("source.json"), &bytes).unwrap();
        fs::write(output.join("manifest.json"), &manifest).unwrap();
        assert_eq!(
            Artifact::capture(&output, &hash(&manifest)).unwrap_err().0,
            code
        );
    }
}
#[test]
#[cfg(unix)]
fn authenticated_cache_and_tool_identity_apply_on_every_path() {
    let directory = tempfile::tempdir().unwrap();
    let solc = fake_tool(directory.path(), RESPONSE);
    let s = source("object \"Verifier\" { code {} }");
    let pin = "01".repeat(32);
    let artifact = solc
        .compile(Build {
            source: &s,
            compiler_sha256: &pin,
            reuse: None,
        })
        .unwrap();
    let reused = solc
        .compile(Build {
            source: &s,
            compiler_sha256: &pin,
            reuse: Some(&artifact),
        })
        .unwrap();
    assert_eq!(artifact.identity(), reused.identity());
    for (changed, compiler) in [
        (source("other executable source"), pin.clone()),
        (s.clone(), "02".repeat(32)),
    ] {
        assert_eq!(
            solc.compile(Build {
                source: &changed,
                compiler_sha256: &compiler,
                reuse: Some(&artifact)
            })
            .unwrap_err()
            .0,
            "evm-cache-key"
        );
    }
    fs::write(solc.path(), b"changed executable").unwrap();
    for reuse in [None, Some(&artifact)] {
        assert_eq!(
            solc.compile(Build {
                source: &s,
                compiler_sha256: &pin,
                reuse
            })
            .unwrap_err()
            .0,
            "evm-solc-pin"
        );
    }
}
#[test]
#[cfg(unix)]
fn fresh_directory_publication_and_external_pin_refuse_replacement() {
    let directory = tempfile::tempdir().unwrap();
    let tool = fake_tool(directory.path(), RESPONSE);
    let s = source("object \"Verifier\" { code {} }");
    let artifact = tool
        .compile(Build {
            source: &s,
            compiler_sha256: &"03".repeat(32),
            reuse: None,
        })
        .unwrap();
    let output = directory.path().join("verifier");
    artifact.publish(&output).unwrap();
    let imported = Artifact::capture(&output, &artifact.identity()).unwrap();
    assert_eq!(imported.runtime_bytecode(), &[0]);
    assert_eq!(
        artifact.publish(&output).unwrap_err().0,
        "evm-output-exists"
    );
    assert_eq!(
        Artifact::capture(&output, &"ff".repeat(32)).unwrap_err().0,
        "evm-artifact-pin"
    );
    // Even replacing every internal checksum cannot satisfy the retained pin.
    let mut manifest: Value =
        serde_json::from_slice(&fs::read(output.join("manifest.json")).unwrap()).unwrap();
    fs::write(output.join("runtime.bin"), [0x60, 1, 0x00]).unwrap();
    manifest["files"]["runtime.bin"] = json!(hash(&[0x60, 1, 0x00]));
    fs::write(
        output.join("manifest.json"),
        serde_json::to_vec(&manifest).unwrap(),
    )
    .unwrap();
    assert_eq!(
        Artifact::capture(&output, &artifact.identity())
            .unwrap_err()
            .0,
        "evm-artifact-pin"
    );
}
#[test]
#[cfg(unix)]
fn exit_zero_severity_error_does_not_publish_bytecode() {
    let dir = tempfile::tempdir().unwrap();
    let tool = fake_tool(
        dir.path(),
        r#"{"errors":[{"severity":"error","message":"bad Yul"}]}"#,
    );
    assert_eq!(
        tool.compile(Build {
            source: &source("bad Yul"),
            compiler_sha256: &"04".repeat(32),
            reuse: None
        })
        .unwrap_err()
        .0,
        "evm-solc-diagnostic"
    );
}

#[test]
#[cfg(unix)]
fn malformed_tool_responses_never_form_an_artifact() {
    for response in ["{", "null", "{\"contracts\":{}}"] {
        let dir = tempfile::tempdir().unwrap();
        let tool = fake_tool(dir.path(), response);
        assert!(
            tool.compile(Build {
                source: &source("invalid response control"),
                compiler_sha256: &"07".repeat(32),
                reuse: None,
            })
            .is_err()
        );
        assert!(!dir.path().join("artifact").exists());
    }
}

#[test]
#[cfg(target_os = "linux")]
fn competing_publications_leave_one_complete_authenticated_artifact() {
    let directory = tempfile::tempdir().unwrap();
    let artifact = fake_tool(directory.path(), RESPONSE)
        .compile(Build {
            source: &source("publication control"),
            compiler_sha256: &"08".repeat(32),
            reuse: None,
        })
        .unwrap();
    let output = directory.path().join("artifact");
    let start = std::sync::Barrier::new(2);
    let successes = std::thread::scope(|scope| {
        let publish = || {
            start.wait();
            artifact.publish(&output).is_ok()
        };
        let first = scope.spawn(publish);
        let second = scope.spawn(publish);
        usize::from(first.join().unwrap()) + usize::from(second.join().unwrap())
    });
    assert_eq!(successes, 1);
    assert_eq!(
        Artifact::capture(&output, &artifact.identity())
            .unwrap()
            .identity(),
        artifact.identity()
    );
    assert!(std::fs::read_dir(directory.path()).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".zkc-evm-")
    }));
}

#[test]
#[ignore = "requires an explicitly pinned installed solc"]
fn pinned_solc_compiles_and_authenticates_a_real_yul_artifact() {
    let tool = Solc::new(
        std::env::var("ZKC_SOLC").unwrap(),
        &std::env::var("ZKC_SOLC_SHA256").unwrap(),
    )
    .unwrap();
    let s = source(
        r#"object "Verifier" { code { datacopy(0,dataoffset("Runtime"),datasize("Runtime")) return(0,datasize("Runtime")) } object "Runtime" { code { mstore(0,1) return(0,32) } } }"#,
    );
    let a = tool
        .compile(Build {
            source: &s,
            compiler_sha256: &"05".repeat(32),
            reuse: None,
        })
        .unwrap();
    let dir = tempfile::tempdir().unwrap();
    a.publish(dir.path().join("artifact")).unwrap();
    assert_eq!(
        Artifact::capture(dir.path().join("artifact"), &a.identity())
            .unwrap()
            .runtime_bytecode(),
        a.runtime_bytecode()
    );
}

#[test]
#[cfg(unix)]
fn calldata_has_the_exact_context_before_proof_order_and_padding() {
    let dir = tempfile::tempdir().unwrap();
    let artifact = fake_tool(dir.path(), RESPONSE)
        .compile(Build {
            source: &source("source"),
            compiler_sha256: &"06".repeat(32),
            reuse: None,
        })
        .unwrap();
    let calldata = artifact
        .calldata(Invocation {
            public_inputs: &[b"a", b"bc"],
            context: b"ctx",
            proof: b"proof",
        })
        .unwrap();
    assert_eq!(&calldata[..4], &[0xa4, 0x88, 0xe1, 0xe4]);
    let number =
        |at: usize| u64::from_be_bytes(calldata[at + 24..at + 32].try_into().unwrap()) as usize;
    assert_eq!(number(4), 96);
    assert_eq!(number(36), 320);
    assert_eq!(number(68), 384);
    assert_eq!(number(100), 2);
    assert_eq!(number(132), 64);
    assert_eq!(number(164), 128);
    assert_eq!(&calldata[356..359], b"ctx");
    assert_eq!(&calldata[420..425], b"proof");
    assert_eq!(calldata.len(), 452);
    assert!(calldata[425..].iter().all(|b| *b == 0));
    assert!(
        artifact
            .calldata(Invocation {
                public_inputs: &[],
                context: &vec![0; 4097],
                proof: &[]
            })
            .is_err()
    );
}
