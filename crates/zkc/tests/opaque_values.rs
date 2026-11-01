//! Public SDK controls independent of any mutable native compiler build.
#![cfg(all(feature = "cpu", feature = "files"))]
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path, process::Command};
use zkc::entry::{self, FunctionEntry, FunctionRequest, Package, Value};

fn digest(s: &str) -> String {
    zkc_test_support::hex(&Sha256::digest(s.as_bytes()))
}
fn schema(kind: &str, name: &str, leaves: Json) -> Json {
    json!({"kind":kind,"identity":digest(name),"type":name,"generated":null,"custody":0,"sealed":false,
        "roles":[],"element":null,"constructible":true,"permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":leaves})
}
fn index() -> Json {
    schema("index", "index", json!(["index"]))
}
fn record(name: &str, fields: Vec<(&str, bool, Json)>) -> Json {
    let mut leaves = vec![];
    let mut members = vec![];
    let mut constructible = true;
    for (name, public, child) in fields {
        members.push(json!({"name":name,"offset":leaves.len(),"public":public,"placement":null,"schema":child}));
        leaves.extend(child["leaves"].as_array().unwrap().iter().cloned());
        constructible &= public && child["constructible"] == true;
    }
    let mut s = schema("record", name, json!(leaves));
    s["fields"] = json!(members);
    s["constructible"] = json!(constructible);
    s
}
fn package(result: &Json, identity: bool) -> Package {
    let parameters = if identity {
        vec![json!({"name":"value","schema":result})]
    } else {
        result["leaves"]
            .as_array()
            .unwrap()
            .iter()
            .enumerate()
            .map(|(i, _)| json!({"name":format!("input{i}"),"schema":index()}))
            .collect()
    };
    let signature = json!({"symbol":"test::Main","parameters":parameters,"result":result});
    let arguments: Vec<_> = parameters
        .iter()
        .enumerate()
        .map(|(i, p)| json!({"id":i,"schema":p["schema"]}))
        .collect();
    let count = parameters.len();
    let physical = zkc_runtime::vm::PhysicalType::default_for(
        zkc_runtime::vm::LogicalType::parse("index").unwrap(),
    )
    .unwrap()
    .spelling();
    let names: Vec<_> = (0..count).map(|i| format!("input{i}")).collect();
    let program = json!([
        "zkc.program/0",
        [],
        [[
            "function",
            "pass",
            names
                .iter()
                .map(|n| json!([n, physical]))
                .collect::<Vec<_>>(),
            vec![physical; count],
            [["return", names]],
            ["pass", []]
        ]],
        [],
        []
    ]);
    let operations = if identity {
        json!([])
    } else {
        json!([{"op":"numeric","calculation":"pass","operands":(0..count).collect::<Vec<_>>(),"results":[{"id":count,"schema":result}]}])
    };
    let artifact = json!({"format":"zkc.host/0","original":digest("original"),"entry":"test::Main",
        "functions":[{"signature":signature,"body":{"arguments":arguments,"operations":operations,"returns":[if identity {0} else {count}]}}],
        "calculations":if identity {json!([])} else {json!([{"id":"pass","parameters":vec![index();count],"results":[result],"function":"pass","program":program.to_string()}])},"deployments":[]});
    let interface = json!({"format":"zkc.language-interface/0","capture":digest("capture"),"original":digest("original"),"toolchain":"test","entry":"test::Main",
        "selection":{"kind":"function","function":"test::Main"},"functions":[signature],"protocols":[],"relations":[],"setups":[]});
    let bytes = json!({"format":"zkc.entry/0","original":"original","interface":interface.to_string(),"artifact":artifact.to_string(),"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":entry::OracleSelection::default()}}).to_string();
    capture(bytes.as_bytes())
}
fn capture(bytes: &[u8]) -> Package {
    Package::capture(bytes, &Sha256::digest(bytes).into(), Package::MAX_BYTES).unwrap()
}
fn admit(package: Package) -> FunctionEntry {
    FunctionEntry::admit(package, Default::default(), BTreeMap::new()).unwrap()
}
fn produce(package: Package, inputs: &[u64]) -> Value {
    let host = admit(package);
    let report = host
        .prepare(FunctionRequest {
            arguments: inputs
                .iter()
                .enumerate()
                .map(|(i, v)| (format!("input{i}"), (*v).into()))
                .collect(),
            ..Default::default()
        })
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    report.value.unwrap().into_value()
}
#[test]
fn retained_outputs_roundtrip_but_representations_and_nominal_substitution_refuse() {
    let secret = record("Secret", vec![("value", false, index())]);
    let value = produce(package(&secret, false), &[7]);
    let Value::Opaque(owner) = value else {
        panic!("private output must remain opaque")
    };
    assert_eq!(owner.field("value").unwrap_err(), "entry-value-projection");
    assert!(!format!("{owner:?}").contains("Index(7)"));
    let host = admit(package(&secret, true));
    let run = |value| {
        host.prepare(FunctionRequest {
            arguments: [("value".into(), value)].into(),
            ..Default::default()
        })
    };
    let report = run(Value::Opaque(owner.clone())).unwrap().execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    assert!(matches!(
        report.value.unwrap().into_value(),
        Value::Opaque(_)
    ));
    assert_eq!(
        run(Value::Record([("value".into(), 7u64.into())].into()))
            .err()
            .unwrap()
            .code(),
        "entry-input-constructor"
    );
    let mut different = secret.clone();
    different["identity"] = json!(digest("OtherSecret"));
    let other = admit(package(&different, true));
    assert_eq!(
        other
            .prepare(FunctionRequest {
                arguments: [("value".into(), Value::Opaque(owner.clone()))].into(),
                ..Default::default()
            })
            .err()
            .unwrap()
            .code(),
        "entry-value-schema"
    );
    different = secret;
    different["fields"][0]["public"] = json!(true);
    let forged = admit(package(&different, true));
    assert_eq!(
        forged
            .prepare(FunctionRequest {
                arguments: [("value".into(), Value::Opaque(owner.clone()))].into(),
                ..Default::default()
            })
            .err()
            .unwrap()
            .code(),
        "entry-value-schema"
    );
    assert_eq!(
        host.check_result_encoding().unwrap_err().code(),
        "entry-output-opaque"
    );
    assert_eq!(
        entry::outputs::function_output(
            &Value::Opaque(owner.clone()),
            Default::default(),
            Default::default()
        )
        .unwrap_err(),
        "entry-output-opaque"
    );
    assert_eq!(
        entry::outputs::proof_outputs(
            &[("out".into(), Value::Opaque(owner.clone()))].into(),
            Default::default(),
            Default::default()
        )
        .unwrap_err(),
        "entry-output-opaque"
    );
    assert_eq!(
        entry::outputs::run_outputs(
            &[("P".into(), [("out".into(), Value::Opaque(owner))].into())].into(),
            Default::default(),
            Default::default()
        )
        .unwrap_err(),
        "entry-output-opaque"
    );
}
fn extern_library(deps: &Path) -> std::path::PathBuf {
    std::fs::read_dir(deps)
        .unwrap()
        .map(Result::unwrap)
        .map(|e| e.path())
        .filter(|p| {
            p.file_name()
                .unwrap()
                .to_str()
                .is_some_and(|n| n.starts_with("libzkc-") && n.ends_with(".rlib"))
        })
        .max_by_key(|p| p.metadata().unwrap().modified().unwrap())
        .unwrap()
}
fn compile_rust(dir: &Path, name: &str, code: &str, success: bool) -> std::path::PathBuf {
    let source = dir.join(format!("{name}.rs"));
    let executable = dir.join(name);
    std::fs::write(&source, code).unwrap();
    let current = std::env::current_exe().unwrap();
    let deps = current.parent().unwrap();
    let output = Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()))
        .args(["--edition=2024", "-Dwarnings"])
        .arg(&source)
        .arg("-o")
        .arg(&executable)
        .arg("--extern")
        .arg(format!("zkc={}", extern_library(deps).display()))
        .arg("-L")
        .arg(format!("dependency={}", deps.display()))
        .output()
        .unwrap();
    assert_eq!(
        output.status.success(),
        success,
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    if !success {
        let expected = match name {
            "private_field" => "E0609",
            "private_getter" | "sealed_getter" => "E0599",
            "private_constructor" => "E0560",
            "private_storage" => "E0616",
            "opaque_constructor" => "private fields",
            _ => panic!("unregistered compile-fail control"),
        };
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(expected),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    executable
}
#[test]
fn generated_bindings_keep_storage_private_and_compile_public_getters() {
    let secret = record("Secret", vec![("value", false, index())]);
    let mixed = record(
        "Mixed",
        vec![
            ("public", true, index()),
            ("child", true, secret.clone()),
            ("hidden", false, index()),
        ],
    );
    let mixed_package = package(&mixed, false);
    let generated = entry::bindings::rust(&mixed_package).unwrap();
    assert!(!generated.contains("pub r#hidden:") && !generated.contains("pub r#value:"));
    let dir = zkc_test_support::evidence(module_path!());
    let path = dir.path().join("package.json");
    std::fs::write(&path, mixed_package.bytes()).unwrap();
    let code = format!(
        r#"#[allow(dead_code)]
mod generated {{ {generated} }}
fn main() {{
    let bytes=::std::fs::read({path:?}).unwrap();
    let host=generated::admit(&bytes,Default::default(),Default::default()).unwrap();
    let result=generated::call(&host,generated::Arguments{{input0:5,input1:19,input2:281}},Default::default()).unwrap();
    assert!(result.report.is_success());
    assert!(result.conversion_error.is_none());
    let value=result.value.unwrap();
    assert_eq!(value.public().unwrap(),5);
    let child=value.child().unwrap();
    let opaque: ::zkc::entry::Value=child.into();
    assert!(matches!(opaque,::zkc::entry::Value::Opaque(_)));
    assert!(!format!("{{value:?}}").contains("281"));
    let raw: ::zkc::entry::Value=value.into();
    let ::zkc::entry::Value::Opaque(owner)=&raw else {{panic!()}};
    assert_eq!(generated::Secret::try_from(::zkc::entry::Value::Opaque(owner.clone())).unwrap_err(),"entry-value-schema");
    let roundtrip=generated::Mixed::try_from(raw).unwrap();
    assert_eq!(roundtrip.public().unwrap(),5);
    assert!(generated::Secret::try_from(::zkc::entry::Value::Record([("value".into(),7u64.into())].into())).is_err());
}}
"#
    );
    let executable = compile_rust(dir.path(), "public_getters", &code, true);
    assert!(Command::new(executable).status().unwrap().success());
    for (name, body) in [
        (
            "private_field",
            "fn inspect(value: generated::Mixed) { let _ = value.hidden; }",
        ),
        (
            "private_getter",
            "fn inspect(value: generated::Secret) { let _ = value.value(); }",
        ),
        (
            "private_constructor",
            "fn inspect() { let _ = generated::Secret { value: 7 }; }",
        ),
        (
            "private_storage",
            "fn inspect(value: generated::Secret) { let _ = value.__zkc_value; }",
        ),
        (
            "opaque_constructor",
            "fn inspect() { let _ = ::zkc::entry::OpaqueValue {}; }",
        ),
    ] {
        compile_rust(
            dir.path(),
            name,
            &format!(
                "#[allow(dead_code)]\nmod generated {{{generated}}}\n#[allow(dead_code)]\n{body}\nfn main(){{}}"
            ),
            false,
        );
    }
    let mut sealed = record("Sealed", vec![("public", true, index())]);
    sealed["sealed"] = json!(true);
    sealed["constructible"] = json!(false);
    let code = entry::bindings::rust(&package(&sealed, false)).unwrap();
    compile_rust(
        dir.path(),
        "sealed_getter",
        &format!(
            "#[allow(dead_code)]\nmod generated {{{code}}}\n#[allow(dead_code)]\nfn inspect(value:generated::Sealed){{let _=value.public();}}\nfn main(){{}}"
        ),
        false,
    );
}

#[test]
#[ignore = "requires an explicitly pinned completed native compiler; set ZKC_OPAQUE_COMPILER"]
fn fresh_source_private_outputs_are_opaque_and_reusable() {
    let compiler =
        std::env::var_os("ZKC_OPAQUE_COMPILER").expect("explicit immutable compiler path");
    let dir = zkc_test_support::evidence(module_path!());
    let source = dir.path().join("opaque.zkc");
    std::fs::write(&source, include_str!("fixtures/opaque_values.zkc")).unwrap();
    let mut secret_identity = None;
    for name in [
        "Fetch",
        "FetchSealed",
        "FetchMixed",
        "FetchNested",
        "FetchEmpty",
        "FetchArray",
        "FetchChoice",
        "FetchAlias",
    ] {
        let output = Command::new(&compiler)
            .arg("language-package")
            .arg("--source-format=zkc-layout")
            .arg(format!("--module=m={}", source.display()))
            .arg(format!("--entry=m::{name}"))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let package = capture(&output.stdout);
        std::fs::write(dir.path().join(format!("{name}.json")), package.bytes()).unwrap();
        let generated = entry::bindings::rust(&package).unwrap();
        let package_path = dir.path().join(format!("{name}.json"));
        let consumer = format!(
            r#"#[allow(dead_code)] mod generated {{{generated}}}
fn main() {{
    let bytes=::std::fs::read({package_path:?}).unwrap();
    let host=generated::admit(&bytes,Default::default(),Default::default()).unwrap();
    let report=generated::call(&host,generated::Arguments{{}},Default::default()).unwrap();
    assert!(report.report.is_success());
    assert!(report.conversion_error.is_none());
    let _value: ::zkc::entry::Value=report.value.unwrap().into();
}}
"#
        );
        let consumer = compile_rust(dir.path(), name, &consumer, true);
        assert!(Command::new(consumer).status().unwrap().success());
        let host = admit(package);
        let report = host.prepare(Default::default()).unwrap().execute();
        assert!(report.is_success(), "{name}: {}", report.diagnostics());
        let value = report.value.unwrap().into_value();
        if name == "FetchMixed" {
            assert_eq!(u64::try_from(value.field("public").unwrap()).unwrap(), 5);
            assert!(value.field("hidden").is_err());
            assert!(value.field("child").unwrap().field("value").is_err());
        } else if name == "FetchChoice" {
            assert_eq!(value.alternative().unwrap(), "Some");
            assert!(
                value
                    .variant_field("Some", "0")
                    .unwrap()
                    .field("value")
                    .is_err()
            );
        } else {
            assert!(
                matches!(value, Value::Opaque(_)),
                "{name}: retained storage"
            );
            let inaccessible = match name {
                "FetchNested" => "child",
                "FetchEmpty" => "private",
                "FetchArray" => "0",
                _ => "value",
            };
            assert_eq!(
                value.field(inaccessible).unwrap_err(),
                "entry-value-projection"
            );
            assert_eq!(value.leaf().unwrap_err(), "entry-value-projection");
            if let Value::Opaque(owner) = &value {
                if name == "Fetch" {
                    secret_identity = Some(owner.schema().identity.clone());
                }
                if name == "FetchAlias" {
                    assert_eq!(Some(&owner.schema().identity), secret_identity.as_ref());
                }
            }
        }
    }
}

#[test]
#[ignore = "requires a freshly built C++ compiler with retained root inputs; set ZKC_OPAQUE_COMPILER"]
fn fresh_source_retained_root_roundtrip() {
    let compiler =
        std::env::var_os("ZKC_OPAQUE_COMPILER").expect("explicit immutable compiler path");
    let dir = zkc_test_support::evidence(module_path!());
    let source = dir.path().join("opaque.zkc");
    std::fs::write(&source, include_str!("fixtures/opaque_values.zkc")).unwrap();
    let compile = |name: &str| {
        let output = Command::new(&compiler)
            .arg("language-package")
            .arg("--source-format=zkc-layout")
            .arg(format!("--module=m={}", source.display()))
            .arg(format!("--entry=m::{name}"))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        admit(capture(&output.stdout))
    };
    let fetch = compile("Fetch");
    let report = fetch.prepare(Default::default()).unwrap().execute();
    assert!(report.is_success());
    let value = report.value.unwrap().into_value();
    let echo = compile("Echo");
    let report = echo
        .prepare(FunctionRequest {
            arguments: [("value".into(), value)].into(),
            ..Default::default()
        })
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    assert!(matches!(
        report.value.unwrap().into_value(),
        Value::Opaque(_)
    ));
}
