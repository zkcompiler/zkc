//! Compile and consume generated bindings against this crate, without a compiler build.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{path::Path, process::Command};
use zkc_tools::entry::{Package, bindings};

fn digest(s: &str) -> String {
    format!("{:x}", Sha256::digest(s.as_bytes()))
}
fn schema(kind: &str, key: &str, leaves: Json) -> Json {
    json!({"kind":kind,"identity":digest(key),"type":key,"custody":false,
        "permissions":["Copy","Drop","Share","Wire"],"fields":[],"alternatives":[],"leaves":leaves})
}
fn port(name: &str, index: usize, ty: &Json, native: usize) -> Json {
    json!({"name":name,"index":index,"native":(native..native + ty["leaves"].as_array().unwrap().len()).collect::<Vec<_>>(),
        "roles":["役"],"type":ty["type"],"schema":ty})
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
        .map(|(i, name)| json!({"name":name,"offset":i,"schema":boolean}))
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
            zkc_tools::source_names::encode_nominal_identity(key)
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
            json!({"name":name,"offset":index,"schema":boolean})).collect::<Vec<_>>()},
        {"name":"Self","fields":[]},{"name":"__zkc_e69c89e580a4","fields":[]}
    ]);
    let mut collision = schema("record", "Record", json!([]));
    collision["identity"] = json!(digest("different generic Record"));
    let reserved = schema("record", "PROVER", json!([]));
    let vk = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut key = schema("builtin", vk, json!([vk]));
    key["permissions"] = json!(["Copy", "Drop"]);
    let inputs = vec![
        port("data", 0, &record, 0),
        port("choice", 1, &variant, names.len()),
        port("collision", 2, &collision, names.len() + 1),
        port("reserved", 3, &reserved, names.len() + 1),
        port("key", 4, &key, names.len() + 1),
    ];
    let doc = json!({"format":"zkc.language-interface/0","capture":digest("capture"),"original":digest("original"),"toolchain":"test","entry":"数学::Entry","protocol":"main",
        "protocols":[{"symbol":"main","roles":["役"],"inputs":inputs,"outputs":[],"services":[{"name":"乱数", "owner":"役", "contract":"random.bls12-381.fr/0", "native":names.len()+2}],"clauses":[]}],"relations":[],"setups":[{"name":"鍵₂", "inputs":[{"port":4,"path":[]}]}],"job":{"kind":"run"}});
    let frame = json!({"format":"zkc.entry/0","original":"original","interface":doc.to_string(),"artifact":"metadata-only binding fixture","options":{"simplify":true,"release_storage":false,"fuse_vector_reductions":false},"assets":[]}).to_string();
    Package::capture(
        frame.as_bytes(),
        &Sha256::digest(frame.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}
fn extern_library(deps: &Path) -> std::path::PathBuf {
    // Cargo builds this integration target and its library with the same profile.
    // Select the newest artifact when a developer retains previous feature builds.
    std::fs::read_dir(deps)
        .unwrap()
        .map(Result::unwrap)
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .unwrap()
                .to_str()
                .is_some_and(|n| n.starts_with("libzkc_tools-") && n.ends_with(".rlib"))
        })
        .max_by_key(|p| p.metadata().unwrap().modified().unwrap())
        .expect("Cargo's zkc-tools library")
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
    let data: ::zkc_tools::entry::Value = record.into();
    let ::zkc_tools::entry::Value::Record(fields) = &data else { panic!() };
    assert!(fields.contains_key("α") && fields.contains_key("__zkc_ceb1") && fields.contains_key("𐐀"));
    let record = Record::try_from(data).unwrap();
    assert!(record.__zkc_ceb1 && !record.__zkc_5f5f7a6b635f63656231);
    let choice = __zkc_e695b0e5ada63a3a43686f696365::__zkc_e69c89e580a4 {
        __zkc_ceb1: true, None: false, Some: true, Ok: false, Err: true,
        PROVER: false, VERIFIER: true, PACKAGE_SHA256: false,
    };
    let value: ::zkc_tools::entry::Value = choice.into();
    let ::zkc_tools::entry::Value::Variant { alternative, fields } = &value else { panic!() };
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
        .arg(format!("zkc_tools={}", extern_library(deps).display()))
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
