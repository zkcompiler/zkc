//! Compile and consume generated bindings against this crate, without a compiler build.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{path::Path, process::Command};
use zkc::entry::{Package, bindings};

fn digest(s: &str) -> String {
    zkc_test_support::hex(&Sha256::digest(s.as_bytes()))
}
fn schema(kind: &str, key: &str, leaves: Json) -> Json {
    json!({"kind":kind,"identity":digest(key),"type":key,"generated":null,"custody":0,"sealed":false,"roles":[],"element":null,"constructible":true,
        "permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":leaves})
}
fn port(name: &str, index: usize, ty: &Json, native: usize) -> Json {
    json!({"name":name,"index":index,"native":(native..native + ty["leaves"].as_array().unwrap().len()).collect::<Vec<_>>(),
        "placement":{"kind":"data","roles":[0]},"components": if ty["fields"].as_array().unwrap().is_empty() {
            (0..ty["leaves"].as_array().unwrap().len()).map(|i| json!({"path":[],"leaf":i,"role":0,"facet":"data","native":native+i})).collect::<Vec<_>>()
        } else {
            ty["fields"].as_array().unwrap().iter().enumerate().map(|(i,_)|json!({"path":[i],"leaf":0,"role":0,"facet":"data","native":native+i})).collect::<Vec<_>>()
        },"type":ty["type"],"schema":ty})
}
fn package() -> Package {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let names = [
        "α",
        "𐐀",
        "a\u{316}\u{315}",
        "__zkc_ceb1",
        "Self",
        "type",
        "gen",
        "value",
        "fields",
    ];
    let mut record = schema("record", "Record", json!(vec!["bool"; names.len()]));
    record["fields"] = names
        .iter()
        .enumerate()
        .map(|(i, name)| json!({"name":name,"offset":i,"public":true,"placement":null,"schema":boolean}))
        .collect();
    let key = "数学::Choice";
    let payload_names = [
        "α",
        "None",
        "Some",
        "Ok",
        "Err",
        "PROVER",
        "VERIFIER",
        "PACKAGE_SHA256",
    ];
    let native = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            zkc::source_names::encode_nominal_identity(key)
        ],
        [
            ["case00000000", vec!["bool"; payload_names.len()]],
            ["case00000001", []],
            ["case00000002", []]
        ]
    ]));
    let mut variant = schema("variant", key, json!([native]));
    variant["alternatives"] = json!([
        {"name":"有値","fields":payload_names.iter().enumerate().map(|(index, name)|
            json!({"name":name,"offset":index,"public":true,"placement":null,"schema":boolean})).collect::<Vec<_>>()},
        {"name":"Self","fields":[]},{"name":"__zkc_e69c89e580a4","fields":[]}
    ]);
    let mut collision = schema("record", "Record", json!([]));
    collision["identity"] = json!(digest("different generic Record"));
    let reserved = schema("record", "PROVER", json!([]));
    let vk = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut key = schema("builtin", vk, json!([vk]));
    key["constructible"] = json!(false);
    let inputs = vec![
        port("data", 0, &record, 0),
        port("choice", 1, &variant, names.len()),
        port("collision", 2, &collision, names.len() + 1),
        port("reserved", 3, &reserved, names.len() + 1),
        port("key", 4, &key, names.len() + 1),
    ];
    let doc = json!({"format":"zkc.language-interface/0","capture":digest("capture"),"original":digest("original"),"toolchain":"test","entry":"数学::Entry","protocol":"main",
        "protocols":[{"symbol":"main","roles":["役"],"inputs":inputs,"outputs":[],"services":[{"name":"乱数", "owner":"役", "contract":"random.bls12-381.fr/0", "native":names.len()+2}],"common_input_requirements":[],"clauses":[]}],"relations":[],"setups":[{"name":"鍵₂", "inputs":[{"port":4,"path":[]}]}],"job":{"kind":"run"}});
    let frame = json!({"format":"zkc.entry/0","original":"original","interface":doc.to_string(),"artifact":"metadata-only binding fixture","options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": zkc::entry::OracleSelection::default()},"assets":[]}).to_string();
    Package::capture(
        frame.as_bytes(),
        &Sha256::digest(frame.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}
fn extern_library(deps: &Path) -> std::path::PathBuf {
    // Select this test's actual Cargo dependency, including its feature set.
    // Modification time can choose a retained no-feature library after a later
    // feature build is reused without rebuilding it. Cargo fingerprints belong
    // to the repository's pinned toolchain, not the SDK artifact contract.
    let executable = std::env::current_exe().unwrap();
    let hash = executable
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .strip_prefix("unicode_bindings-")
        .unwrap();
    let fingerprints = deps.parent().unwrap().join(".fingerprint");
    let metadata: Json = serde_json::from_slice(
        &std::fs::read(fingerprints.join(format!(
            "zkc-{hash}/test-integration-test-unicode_bindings.json"
        )))
        .unwrap(),
    )
    .unwrap();
    let fingerprint = metadata["deps"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row[1] == "zkc")
        .unwrap()[3]
        .as_u64()
        .unwrap();
    let expected = zkc_test_support::hex(&fingerprint.to_le_bytes());
    let matching: Vec<_> = std::fs::read_dir(deps)
        .unwrap()
        .map(Result::unwrap)
        .map(|e| e.path())
        .filter(|path| {
            let Some(hash) = path
                .file_name()
                .and_then(|n| n.to_str())
                .and_then(|n| n.strip_prefix("libzkc-"))
                .and_then(|n| n.strip_suffix(".rlib"))
            else {
                return false;
            };
            std::fs::read_to_string(fingerprints.join(format!("zkc-{hash}/lib-zkc")))
                .is_ok_and(|actual| actual.trim() == expected)
        })
        .collect();
    assert_eq!(matching.len(), 1, "exact Cargo SDK dependency");
    matching.into_iter().next().unwrap()
}

#[test]
fn escaped_members_variants_and_colliding_types_compile_and_preserve_source_keys() {
    let code = bindings::rust(&package()).unwrap();
    assert!(
        code.contains("pub struct r#Record2"),
        "generated type allocator resolves duplicate preferred names"
    );
    for (source, escaped) in [
        ("α", "__zkc_ceb1"),
        ("Self", "__zkc_53656c66"),
        ("type", "__zkc_74797065"),
        ("gen", "__zkc_67656e"),
        ("__zkc_ceb1", "__zkc_5f5f7a6b635f63656231"),
    ] {
        assert!(code.contains(&format!("r#{escaped}")), "{source}");
        assert!(
            code.contains(&format!("{source:?}")),
            "serialized key {source}"
        );
    }
    let mut consumer = code;
    consumer.push_str(r#"
fn main() {
    let record = Record {
        __zkc_ceb1: true,
        __zkc_f0909080: false,
        __zkc_61cc96cc95: true,
        __zkc_5f5f7a6b635f63656231: false,
        __zkc_53656c66: true,
        __zkc_74797065: false,
        __zkc_67656e: true,
        value: false,
        fields: true,
    };
    let data: ::zkc::entry::Value = record.into();
    let ::zkc::entry::Value::Record(fields) = &data else { panic!() };
    assert!(fields.contains_key("α") && fields.contains_key("__zkc_ceb1") && fields.contains_key("𐐀"));
    let record = Record::try_from(data).unwrap();
    assert!(record.__zkc_ceb1 && !record.__zkc_5f5f7a6b635f63656231);
    let choice = __zkc_e695b0e5ada63a3a43686f696365::__zkc_e69c89e580a4 {
        __zkc_ceb1: true, None: false, Some: true, Ok: false, Err: true,
        PROVER: false, VERIFIER: true, PACKAGE_SHA256: false,
    };
    let value: ::zkc::entry::Value = choice.into();
    let ::zkc::entry::Value::Variant { alternative, fields } = &value else { panic!() };
    assert_eq!(alternative, "有値"); assert!(fields.contains_key("α"));
    for name in ["None", "Some", "Ok", "Err", "PROVER", "VERIFIER", "PACKAGE_SHA256"] {
        assert!(fields.contains_key(name), "missing source field {name}");
    }
    let choice = __zkc_e695b0e5ada63a3a43686f696365::try_from(value).unwrap();
    let __zkc_e695b0e5ada63a3a43686f696365::__zkc_e69c89e580a4 {
        None: none_value, Some: some_value, PROVER: prover_value,
        VERIFIER: verifier_value, ..
    } = &choice else { panic!() };
    assert!(!*none_value && *some_value && !*prover_value && *verifier_value);
    let input = __zkc_e5bdb9496e70757473 { data: record, choice, collision: Record2 {}, reserved: PROVER2 {} };
    let (role, inputs) = input.into_role();
    assert_eq!(role, "役"); assert!(inputs.inputs.contains_key("choice"));
    assert_eq!(setups::__zkc_e98db5e28282, "鍵₂");
    assert_eq!(services::__zkc_e4b9b1e695b0, "乱数");
    let round_trip = __zkc_e5bdb9496e70757473::try_from(inputs.inputs).unwrap();
    assert!(round_trip.data.__zkc_ceb1);
}
"#);
    let evidence = zkc_test_support::evidence(module_path!());
    let source = evidence.path().join("consumer.rs");
    let executable = evidence.path().join("consumer");
    std::fs::write(&source, consumer).unwrap();
    let current = std::env::current_exe().unwrap();
    let deps = current.parent().unwrap();
    let output = Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()))
        .args([
            "--edition=2024",
            "--crate-name=unicode_binding_consumer",
            "-Dwarnings",
        ])
        .arg(&source)
        .arg("-o")
        .arg(&executable)
        .arg("--extern")
        .arg(format!("zkc={}", extern_library(deps).display()))
        .arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(executable).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn zero_array_bindings_use_the_retained_element_type() {
    let mut array = schema("array", "[bool;0]", json!([]));
    array["element"] = schema("boolean", "bool", json!(["bool"]));
    let doc = json!({"format":"zkc.language-interface/0","capture":digest("capture"),"original":digest("original"),"toolchain":"test","entry":"sample::Main","protocol":"main",
        "protocols":[{"symbol":"main","roles":["P"],"inputs":[port("empty",0,&array,0)],"outputs":[],"services":[],"common_input_requirements":[],"clauses":[]}],"relations":[],"setups":[],"job":{"kind":"run"}});
    let bytes=json!({"format":"zkc.entry/0","original":"original","interface":doc.to_string(),"artifact":"metadata-only binding fixture","assets":[],"options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":zkc::entry::OracleSelection::default()}}).to_string();
    let package = Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap();
    assert!(
        bindings::rust(&package)
            .unwrap()
            .contains("[::core::primitive::bool;0]")
    );
}
