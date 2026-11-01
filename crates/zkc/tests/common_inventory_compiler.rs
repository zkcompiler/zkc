//! Explicit fresh compiler gate. Hand-built SDK fixtures cannot satisfy this test.
#![cfg(all(feature = "cpu", feature = "files"))]
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    process::Command,
};
use zkc::entry::{self, Package, RoleInputs, RunEntry, RunRequest};

/// The explicit pairing gate uses the compiler build selected by
/// `ZKC_COMPILER_BIN`; a relative path is resolved from the checkout root.
fn compiler() -> PathBuf {
    let directory = std::env::var_os("ZKC_COMPILER_BIN")
        .expect("set ZKC_COMPILER_BIN to the freshly built compiler directory");
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(directory)
        .join("zkc-compile")
}
fn capture(bytes: &[u8]) -> Package {
    Package::capture(bytes, &Sha256::digest(bytes).into(), Package::MAX_BYTES).unwrap()
}
fn compile(compiler: &Path, source: &Path, entry: &str, format: &str) -> Package {
    let output = Command::new(compiler)
        .arg("language-package")
        .arg(format!("--source-format={format}"))
        .arg(format!("--module=m={}", source.display()))
        .arg(format!("--entry=m::{entry}"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{entry}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let package = capture(&output.stdout);
    let artifact: Json = serde_json::from_str(package.artifact()).unwrap();
    if artifact["format"] == "zkc.host/0" {
        // Default Protocol Entries are Host wrappers. Retain/check the actual
        // child package; do not invent inputs on the container function.
        let deployments = entry::FunctionInterface::deployment_interfaces(&package).unwrap();
        assert!(!deployments.is_empty());
        capture(
            artifact["deployments"][0]["package"]
                .as_str()
                .unwrap()
                .as_bytes(),
        )
    } else {
        package
    }
}
fn request(run: &RunEntry, p: Json, v: Json) -> RunRequest {
    let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
    let roles = run
        .interface()
        .input_groups()
        .iter()
        .zip([p, v])
        .map(|(group, values)| {
            (
                group.name().to_owned(),
                RoleInputs {
                    inputs: decoder
                        .decode(group, values.to_string().as_bytes(), None)
                        .unwrap(),
                    ..Default::default()
                },
            )
        })
        .collect();
    RunRequest {
        session: "fresh-common-inputs".into(),
        roles,
        setups: BTreeMap::new(),
    }
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
#[ignore = "explicit gate: pairs the SDK with the fresh zkc-compile in ZKC_COMPILER_BIN"]
fn fresh_compiler_common_inventories_bind_actual_named_cpu_runs() {
    let compiler = compiler();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/common_inputs.zkc");
    for name in ["Boolean", "Tag", "Payload", "Permuted"] {
        let package = compile(&compiler, &source, name, "zkc-layout");
        let artifact: Json = serde_json::from_str(package.artifact()).unwrap();
        let program = artifact["candidate"].as_str().unwrap();
        let run = RunEntry::admit(package.clone(), Default::default(), Default::default()).unwrap();
        let required = run.common_input_requirements().unwrap();
        assert!(
            !required.is_empty(),
            "{name}: producer must supply the demanded inventory"
        );
        let (p, v) = match name {
            "Boolean" => (json!({"flag":true}), json!({"flag":true})),
            "Tag" => (
                json!({"choice":{"case":"Some","fields":{"0":true}}}),
                json!({"choice":{"case":"Some","fields":{"0":false}}}),
            ),
            "Payload" => (
                json!({"choice":{"case":"Some","fields":{"0":true}}}),
                json!({"choice":{"case":"Some","fields":{"0":true}}}),
            ),
            _ => (
                json!({"state_nested_flag":true,"state_nested_empty":null,"state_empty":null}),
                json!({"state_prefix":false,"state_nested_unrelated":false,"state_nested_flag":true}),
            ),
        };
        let matching = request(&run, p.clone(), v.clone());
        let mismatch = if name == "Tag" {
            json!({"choice":{"case":"None","fields":{}}})
        } else if name == "Boolean" {
            json!({"flag":false})
        } else if name == "Payload" {
            json!({"choice":{"case":"Some","fields":{"0":false}}})
        } else {
            json!({"state_prefix":false,"state_nested_unrelated":false,"state_nested_flag":false})
        };
        let disagreeing = request(&run, p, mismatch);
        let rows: Vec<_> = required
            .iter()
            .map(|r| {
                let components: Vec<_> = r
                    .components
                    .iter()
                    .map(|c| {
                        json!([
                            c.role,
                            c.input.to_string(),
                            c.path
                                .iter()
                                .flat_map(|(a, p)| [a.to_string(), p.to_string()])
                                .collect::<Vec<_>>()
                        ])
                    })
                    .collect();
                let (facet, expected) = match r.observation {
                    entry::Observation::Tag => (json!("tag"), "30".to_owned()),
                    entry::Observation::Value => (json!("value"), "5a4b4356000501".to_owned()),
                    entry::Observation::Extent { .. } => panic!("unexpected extent in {name}"),
                };
                json!([components, r.ty.spelling(), facet, ["active", expected]])
            })
            .collect();
        let bytes = zkc_format::logical::encode_tree(&json!([
            "zkc.input-bindings/0",
            hex(&Sha256::digest(program.as_bytes())),
            artifact["entry"],
            rows
        ]))
        .unwrap();
        let pin = Sha256::digest(&bytes).into();
        let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
        assert_eq!(
            bound.prepare(disagreeing).err().unwrap().code(),
            "input-binding-Value",
            "{name}"
        );
        assert!(
            bound.prepare(matching).unwrap().execute().is_success(),
            "{name}"
        );
        let run = RunEntry::admit(package, Default::default(), Default::default()).unwrap();
        let omitted = zkc_format::logical::encode_tree(&json!([
            "zkc.input-bindings/0",
            hex(&Sha256::digest(program.as_bytes())),
            artifact["entry"],
            []
        ]))
        .unwrap();
        assert!(
            run.bind_common_inputs(&omitted, &Sha256::digest(&omitted).into())
                .is_err()
        );
    }
}

#[test]
#[ignore = "explicit gate: pairs the SDK with the fresh zkc-compile in ZKC_COMPILER_BIN"]
fn fresh_compiler_extent_inventory_executes_zero_one_and_multiple_iterations() {
    let compiler = compiler();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/common_extents.zkc");
    let package = compile(&compiler, &source, "Extent", "zkc");
    let artifact: Json = serde_json::from_str(package.artifact()).unwrap();
    for count in [0usize, 1, 3] {
        let run = RunEntry::admit(package.clone(), Default::default(), Default::default()).unwrap();
        let required = run.common_input_requirements().unwrap();
        assert_eq!(required.len(), 1);
        assert_eq!(
            required[0].observation,
            entry::Observation::Extent { axis: 0 }
        );
        let r = &required[0];
        let rows = json!([[
            r.components
                .iter()
                .map(|c| json!([c.role, c.input.to_string(), []]))
                .collect::<Vec<_>>(),
            r.ty.spelling(),
            ["extent", "0"],
            ["active", hex(count.to_string().as_bytes())]
        ]]);
        let bytes = zkc_format::logical::encode_tree(&json!([
            "zkc.input-bindings/0",
            hex(&Sha256::digest(
                artifact["candidate"].as_str().unwrap().as_bytes()
            )),
            artifact["entry"],
            rows
        ]))
        .unwrap();
        let make = |len, number| {
            let vector =
                zkc_cpu::Value::KoalaBearVector(vec![zkc_cpu::KoalaBear::new(number); len].into());
            RoleInputs {
                inputs: [("values".to_owned(), entry::Value::from(vector))].into(),
                ..Default::default()
            }
        };
        let matching = RunRequest {
            session: "fresh-extent".into(),
            setups: BTreeMap::new(),
            roles: [("P".into(), make(count, 2)), ("V".into(), make(count, 9))].into(),
        };
        let disagreeing = RunRequest {
            session: "fresh-extent".into(),
            setups: BTreeMap::new(),
            roles: [
                ("P".into(), make(count, 2)),
                ("V".into(), make(count + 1, 9)),
            ]
            .into(),
        };
        let bound = run
            .bind_common_inputs(&bytes, &Sha256::digest(&bytes).into())
            .unwrap();
        assert_eq!(
            bound.prepare(disagreeing).err().unwrap().code(),
            "input-binding-Value"
        );
        assert!(bound.prepare(matching).unwrap().execute().is_success());
    }
}
