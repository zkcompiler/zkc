//! Generate with a default-feature CLI, then unify different JSON features in
//! independently built consumers of the same freshly compiled source package.
#![cfg(all(feature = "cpu", feature = "files"))]
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::{path::Path, process::Command};
use zkc::entry::{FunctionInterface, InterfaceLimits, Package};

fn run(command: &mut Command) -> std::process::Output {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn metadata(manifest: &Path, ordered: bool, locked: bool) -> Json {
    let mut command = Command::new("cargo");
    command.args([
        "metadata",
        "--offline",
        "--format-version=1",
        "--manifest-path",
    ]);
    command.arg(manifest);
    if locked {
        command.arg("--locked");
    }
    if ordered {
        command.args(["--features", "ordered"]);
    }
    serde_json::from_slice(&run(&mut command).stdout).unwrap()
}

fn check_json_features(document: &Json, ordered: bool) {
    let package = document["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == "serde_json")
        .unwrap();
    assert_eq!(package["version"], "1.0.152");
    let node = document["resolve"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["id"] == package["id"])
        .unwrap();
    assert_eq!(
        node["features"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f == "preserve_order"),
        ordered
    );
}

#[test]
#[ignore = "requires pinned ZKC_OPAQUE_COMPILER and default-feature ZKC_OPAQUE_BINDINGS_CLI"]
fn generated_bindings_survive_downstream_json_feature_unification() {
    let compiler = std::env::var_os("ZKC_OPAQUE_COMPILER").expect("pinned completed compiler");
    let cli = std::env::var_os("ZKC_OPAQUE_BINDINGS_CLI").expect("default-feature bindings CLI");
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let generator_metadata = metadata(&workspace.join("Cargo.toml"), false, true);
    check_json_features(&generator_metadata, false);
    let evidence = zkc_test_support::evidence(module_path!());
    let directory = evidence.path();
    std::fs::write(
        directory.join("generator-metadata.json"),
        generator_metadata.to_string(),
    )
    .unwrap();

    let mut packages = Vec::new();
    let mut schemas = Vec::new();
    for (name, sealed, visibility, argument) in [
        ("original", "", "", "1"),
        ("privacy", "", "pub ", "1"),
        ("sealing", "#[sealed]\n", "", "1"),
        ("static_argument", "", "", "2"),
    ] {
        let source = directory.join(format!("{name}.zkc"));
        std::fs::write(
            &source,
            format!(
                "pub struct Child:\n    hidden: index\n\
                 {sealed}pub struct Secret<N: nat>:\n    pub child: Child\n    {visibility}value: index\n    guard: ()\n\
                 entry def Fetch() -> Secret<{argument}>:\n    return Secret<{argument}> {{child: Child {{hidden: 7}}, value: 9, guard: ()}}\n"
            ),
        )
        .unwrap();
        let output = run(Command::new(&compiler)
            .arg("language-package")
            .arg("--source-format=zkc-layout")
            .arg(format!("--module=m={}", source.display()))
            .arg("--entry=m::Fetch"));
        let pin: [u8; 32] = Sha256::digest(&output.stdout).into();
        let package = Package::capture(&output.stdout, &pin, Package::MAX_BYTES).unwrap();
        let schema = FunctionInterface::read(&package, InterfaceLimits::DEFAULT)
            .unwrap()
            .signature()
            .result
            .clone();
        assert!(!schema.constructible);
        schemas.push(schema);
        let path = directory.join(format!("{name}.zkpkg"));
        std::fs::write(&path, package.bytes()).unwrap();
        packages.push((name, path, pin));
    }
    assert_eq!(schemas[0].identity, schemas[1].identity);
    assert_eq!(schemas[0].identity, schemas[2].identity);
    assert_ne!(schemas[0].identity, schemas[3].identity);
    assert_ne!(schemas[0].fields[1].public, schemas[1].fields[1].public);
    assert_ne!(schemas[0].sealed, schemas[2].sealed);
    assert_eq!(schemas[0].leaves, schemas[3].leaves);

    let bindings = directory.join("bindings.rs");
    run(Command::new(&cli)
        .args(["--json", "bindings"])
        .arg(format!("--package={}", packages[0].1.display()))
        .arg(format!(
            "--sha256={}",
            zkc_test_support::hex(&packages[0].2)
        ))
        .arg(format!("--output={}", bindings.display())));

    let sdk_path = Path::new(env!("CARGO_MANIFEST_DIR"));
    let manifest = directory.join("Cargo.toml");
    std::fs::write(
        &manifest,
        format!(
            "[package]\nname=\"opaque-fingerprint-consumer\"\nversion=\"0.0.0\"\nedition=\"2024\"\n\
             [workspace]\n[dependencies]\nzkc={{path={sdk_path:?},default-features=false,features=[\"cpu\"]}}\n\
             serde_json=\"=1.0.152\"\n[features]\nordered=[\"serde_json/preserve_order\"]\n\
             [[bin]]\nname=\"opaque-fingerprint-consumer\"\npath=\"main.rs\"\n"
        ),
    )
    .unwrap();
    std::fs::copy(workspace.join("Cargo.lock"), directory.join("Cargo.lock")).unwrap();
    let inputs = packages
        .iter()
        .map(|(name, path, pin)| format!("({name:?}, include_bytes!({path:?}), {pin:?}),"))
        .collect::<String>();
    std::fs::write(
        directory.join("main.rs"),
        format!(
            r##"#[allow(dead_code)] mod generated {{ include!("bindings.rs"); }}
use zkc::entry::{{FunctionEntry, Package, Value}};
fn refuses<T: TryFrom<Value, Error=String>>(_: &T, value: Value) {{
    let Err(error) = T::try_from(value) else {{panic!("changed schema accepted")}};
    assert_eq!(error,"entry-value-schema");
}}
fn main() {{
    let order=serde_json::json!({{"z":0,"a":1}}).to_string();
    assert_eq!(order,if cfg!(feature="ordered") {{r#"{{"z":0,"a":1}}"#}} else {{r#"{{"a":1,"z":0}}"#}});
    let packages: &[(&str,&[u8],[u8;32])]=&[{inputs}];
    let host=generated::admit(packages[0].1,Default::default(),Default::default()).unwrap();
    let report=generated::call(&host,generated::Arguments{{}},Default::default()).unwrap();
    assert!(report.report.is_success());
    assert!(report.conversion_error.is_none(),"{{:?}}",report.conversion_error);
    let value=report.value.unwrap();
    let child: Value=value.child().unwrap().into();
    assert_eq!(child.field("hidden").unwrap_err(),"entry-value-projection");
    for (name,bytes,pin) in &packages[1..] {{
        let package=Package::capture(bytes,pin,Package::MAX_BYTES).unwrap();
        let host=FunctionEntry::admit(package,Default::default(),Default::default()).unwrap();
        let report=host.prepare(Default::default()).unwrap().execute();
        assert!(report.is_success(),"{{name}}");
        refuses(&value,report.value.unwrap().into_value());
    }}
    let mut changed=packages[0].1.to_vec();
    changed.push(b' ');
    assert_eq!(generated::admit(&changed,Default::default(),Default::default()).err().unwrap().code(),"entry-package-identity");
    println!("opaque conversion and privacy/sealing/static-identity refusals passed; ordered={{}}",cfg!(feature="ordered"));
}}
"##
        ),
    )
    .unwrap();
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| directory.join("target"));
    for ordered in [false, true] {
        let features = metadata(&manifest, ordered, ordered);
        check_json_features(&features, ordered);
        std::fs::write(
            directory.join(format!("consumer-ordered-{ordered}-metadata.json")),
            features.to_string(),
        )
        .unwrap();
        let mut build = Command::new("cargo");
        build
            .args([
                "build",
                "--offline",
                "--locked",
                "--jobs=2",
                "--manifest-path",
            ])
            .arg(&manifest)
            .arg("--target-dir")
            .arg(&target);
        if ordered {
            build.args(["--features", "ordered"]);
        }
        run(&mut build);
        let output = run(
            Command::new(target.join("debug/opaque-fingerprint-consumer"))
                .env("PATH", "")
                .env("ZKC_COMPILER_BIN", "/unavailable")
                .env("ZKC_NATIVE_BIN", "/unavailable")
                .current_dir(directory),
        );
        std::fs::write(
            directory.join(format!("consumer-ordered-{ordered}.log")),
            output.stdout,
        )
        .unwrap();
    }
}
