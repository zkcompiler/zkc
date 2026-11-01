use super::*;
use serde_json::json;
use std::fs;

fn source(body: &str) -> Source {
    let identity = "00".repeat(32);
    let manifest = json!({"entry":"Main::Proof", "capture":identity, "installation":identity,
        "original":identity, "source_sha256":identity, "yul_sha256":hash(body.as_bytes())});
    Source::capture(&serde_json::to_vec(&json!({"format":"zkc.evm-source/0", "target":"evm", "fork":"cancun",
        "yul":body, "abi":super::calldata::abi(),"entry":"Main::Proof",
        "capture":identity,"installation":identity,"original":identity,"source_sha256":identity,
        "manifest":manifest,"limits":{"public_bytes":131072,"proof_bytes":65536,"context_bytes":4096,"calldata_bytes":262144}})).unwrap()).unwrap()
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
