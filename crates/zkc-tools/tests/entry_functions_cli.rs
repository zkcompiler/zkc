//! Adapter tests use independently authored authenticated Host carriers. Source
//! compiler integration is exercised separately by the common protocol suite.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn schema(kind: &str, ty: &str, leaves: &[&str]) -> Json {
    json!({"kind":kind,"identity":hex(&Sha256::digest(ty.as_bytes())),"type":ty,
        "custody":false,"constructible":true,"permissions":["Copy","Drop"],
        "fields":[],"alternatives":[],"leaves":leaves})
}
fn interface(schema: &Json, parameter: bool) -> Json {
    json!({"format":"zkc.language-interface/0","capture":hex(&Sha256::digest(b"capture")),
        "original":hex(&Sha256::digest(b"checked source")),"toolchain":hex(&Sha256::digest(b"toolchain")),
        "entry":"sample::Main","selection":{"kind":"function","function":"sample::Main"},
        "functions":[{"symbol":"sample::Main","parameters":if parameter {
            json!([{"name":"flag","schema":schema}])
        } else {json!([])},"result":schema}],"protocols":[],"relations":[],"setups":[]})
}
fn package(interface: &Json, operations: Json, arguments: Json, returns: Json) -> Vec<u8> {
    let artifact = json!({"format":"zkc.host/0","original":interface["original"],
        "entry":"sample::Main","functions":[{"signature":interface["functions"][0],
        "body":{"arguments":arguments,"operations":operations,"returns":returns}}],
        "calculations":[],"deployments":[]});
    serde_json::to_vec(&json!({"format":"zkc.entry/0","original":"checked source",
        "interface":interface.to_string(),"artifact":artifact.to_string(),"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
        "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true}}))
    .unwrap()
}
fn boolean_package(required: bool) -> Vec<u8> {
    let schema = schema("boolean", "bool", &["bool"]);
    package(
        &interface(&schema, true),
        if required {
            json!([{"op":"require","operands":[0],"results":[]}])
        } else {
            json!([])
        },
        json!([{"id":0,"schema":schema}]),
        json!([0]),
    )
}
fn record(ty: &str, fields: &[(&str, Json)], constructible: bool) -> Json {
    let leaves = fields
        .iter()
        .flat_map(|(_, schema)| schema["leaves"].as_array().unwrap().iter().cloned())
        .collect::<Vec<_>>();
    let mut result = schema("record", ty, &[]);
    result["constructible"] = json!(constructible);
    result["leaves"] = json!(leaves);
    let mut offset = 0;
    result["fields"] = json!(
        fields
            .iter()
            .map(|(name, schema)| {
                let field = json!({"name":name,"offset":offset,"schema":schema});
                offset += schema["leaves"].as_array().unwrap().len();
                field
            })
            .collect::<Vec<_>>()
    );
    result
}
fn joint_package() -> Vec<u8> {
    let boolean = schema("boolean", "bool", &["bool"]);
    let physical = zkc_runtime::vm::PhysicalType::default_for(
        zkc_runtime::vm::LogicalType::parse("bool").unwrap(),
    )
    .unwrap()
    .spelling();
    let program = json!([
        "zkc.program/0",
        [],
        [],
        [
            [
                "participant",
                "participant0",
                "root",
                "role00000000",
                [["x", physical]],
                [physical],
                [["return", ["x"]]],
                []
            ],
            [
                "participant",
                "participant1",
                "root",
                "role00000001",
                [["x", physical]],
                [physical],
                [["return", ["x"]]],
                []
            ]
        ],
        [[
            "entry",
            "pair",
            [
                ["role00000000", "participant0"],
                ["role00000001", "participant1"]
            ]
        ]]
    ]);
    let native = json!({"format":"zkc.run/0","candidate":program.to_string(),"entry":"pair",
        "roles":["role00000000","role00000001"],"steps":[
            {"role":0,"instruction":0,"anchor":null},{"role":1,"instruction":0,"anchor":null}]});
    let port = json!({"name":"value","index":0,"native":[0],"roles":["P","V"],
        "type":"bool","schema":boolean});
    let child_interface = json!({"format":"zkc.language-interface/0","setups":[],"relations":[],
        "capture":hex(&Sha256::digest(b"capture")),"original":hex(&Sha256::digest(b"checked source")),
        "toolchain":hex(&Sha256::digest(b"toolchain")),"entry":"sample::Pair::run",
        "protocol":"pair","job":{"kind":"run"},"protocols":[{"symbol":"pair",
            "roles":["P","V"],"inputs":[port],"outputs":[port],"services":[],"clauses":[]}]});
    let mut child: Json = serde_json::from_slice(&boolean_package(false)).unwrap();
    child["interface"] = json!(child_interface.to_string());
    child["artifact"] = json!(native.to_string());
    let input = record(
        "sample::Pair::Inputs",
        &[
            (
                "P",
                record(
                    "sample::Pair::Inputs::P",
                    &[("value", boolean.clone())],
                    true,
                ),
            ),
            (
                "V",
                record(
                    "sample::Pair::Inputs::V",
                    &[("value", boolean.clone())],
                    true,
                ),
            ),
        ],
        true,
    );
    let output = record(
        "sample::Pair::RunResult",
        &[
            (
                "P",
                record(
                    "sample::Pair::RunResult::P",
                    &[("value", boolean.clone())],
                    false,
                ),
            ),
            (
                "V",
                record("sample::Pair::RunResult::V", &[("value", boolean)], false),
            ),
        ],
        false,
    );
    let mut view = interface(&input, true);
    view["functions"][0]["result"] = output.clone();
    let mut root: Json = serde_json::from_slice(&package(&view,
        json!([{"op":"invoke","deployment":"child.Pair","operands":[0],"results":[{"id":1,"schema":output}]}]),
        json!([{"id":0,"schema":input}]),json!([1]))).unwrap();
    let mut artifact: Json = serde_json::from_str(root["artifact"].as_str().unwrap()).unwrap();
    artifact["deployments"] = json!([{"id":"child.Pair","operation":"run",
        "parameters":[input],"results":[output],"package":child.to_string()}]);
    root["artifact"] = json!(artifact.to_string());
    serde_json::to_vec(&root).unwrap()
}
fn joint_setup_package() -> Vec<u8> {
    let mut root: Json = serde_json::from_slice(&joint_package()).unwrap();
    let mut host: Json = serde_json::from_str(root["artifact"].as_str().unwrap()).unwrap();
    let mut child: Json =
        serde_json::from_str(host["deployments"][0]["package"].as_str().unwrap()).unwrap();
    let mut view: Json = serde_json::from_str(child["interface"].as_str().unwrap()).unwrap();
    let mut native: Json = serde_json::from_str(child["artifact"].as_str().unwrap()).unwrap();
    let mut program: Json = serde_json::from_str(native["candidate"].as_str().unwrap()).unwrap();
    for (index, name, logical) in [
        (1, "pk", "prover_key:multilinear.kzg.bls12-381/0"),
        (2, "vk", "verifier_key:multilinear.kzg.bls12-381/0"),
    ] {
        let mut ty = schema("builtin", logical, &[logical]);
        ty["constructible"] = json!(false);
        view["protocols"][0]["inputs"].as_array_mut().unwrap().push(
            json!({"name":name,"index":index,"native":[index],"roles":["P"],
                "type":logical,"schema":ty}),
        );
        let physical = zkc_runtime::vm::PhysicalType::default_for(
            zkc_runtime::vm::LogicalType::parse(logical).unwrap(),
        )
        .unwrap()
        .spelling();
        program[3][0][4]
            .as_array_mut()
            .unwrap()
            .push(json!([name, physical]));
    }
    view["setups"] = json!([{"name":"pcs","inputs":[{"port":1,"path":[]},{"port":2,"path":[]}]}]);
    native["candidate"] = json!(program.to_string());
    child["interface"] = json!(view.to_string());
    child["artifact"] = json!(native.to_string());
    host["deployments"][0]["package"] = json!(child.to_string());
    root["artifact"] = json!(host.to_string());
    serde_json::to_vec(&root).unwrap()
}
fn pinned(directory: &Path, bytes: &[u8]) -> Vec<String> {
    let path = directory.join("entry.zkpkg");
    std::fs::write(&path, bytes).unwrap();
    vec![
        format!("--package={}", path.display()),
        format!("--sha256={}", hex(&Sha256::digest(bytes))),
    ]
}
fn run(command: &str, arguments: &[String], extra: &[String]) -> Json {
    let arguments = arguments.iter().chain(extra).cloned().collect::<Vec<_>>();
    zkc_tools::cli::run(command, &arguments)
}

#[test]
fn pinned_inspection_templates_and_false_return_use_one_argument_map() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &boolean_package(false));
    let inspected = run("inspect", &options, &[]);
    assert_eq!(inspected["status"], "inspected", "{inspected}");
    assert_eq!(
        inspected["interface"]["signature"]["parameters"][0]["name"],
        "flag"
    );
    assert!(inspected.get("execution").is_none());
    let templates = dir.path().join("templates");
    let initialized = run(
        "prepare",
        &options,
        &[format!("--output={}", templates.display())],
    );
    assert_eq!(initialized["status"], "prepared", "{initialized}");
    let arguments = templates.join("arguments.json");
    assert_eq!(
        std::fs::read_to_string(&arguments).unwrap(),
        "{\n  \"flag\": null\n}\n"
    );
    assert_eq!(
        initialized["entries"][0]["commands"][0][4],
        format!("--input={}", arguments.display())
    );
    std::fs::write(&arguments, r#"{"flag":false}"#).unwrap();
    let results = dir.path().join("result.json");
    let invocation = [
        format!("--input={}", arguments.display()),
        format!("--results={}", results.display()),
    ];
    let report = run("run", &options, &invocation);
    assert_eq!(report["status"], "executed", "{report}");
    let result: Json = serde_json::from_slice(&std::fs::read(&results).unwrap()).unwrap();
    assert_eq!(
        result,
        json!({"format":"zkc.entry-outputs/0","value":false})
    );
    assert_eq!(report["publication"]["published"], json!(["results"]));
}

#[test]
fn native_proof_bytes_round_trip_without_scalar_reformatting() {
    let dir = tempfile::tempdir().unwrap();
    let bytes = schema("builtin", "builtin(\"bytes\")", &["bytes"]);
    let proof = record("sample::Family::Proof", &[("bytes", bytes)], true);
    let options = pinned(
        dir.path(),
        &package(
            &interface(&proof, true),
            json!([]),
            json!([{"id":0,"schema":proof}]),
            json!([0]),
        ),
    );
    let arguments = dir.path().join("arguments.json");
    let results = dir.path().join("results.json");
    let invocation = [
        format!("--input={}", arguments.display()),
        format!("--results={}", results.display()),
    ];
    let value = json!({"bytes":[0,90,127,255]});
    for _ in 0..2 {
        std::fs::write(&arguments, json!({"flag":value}).to_string()).unwrap();
        let report = run("run", &options, &invocation);
        assert_eq!(report["status"], "executed", "{report}");
        let result: Json = serde_json::from_slice(&std::fs::read(&results).unwrap()).unwrap();
        assert_eq!(result["value"], value);
    }
    std::fs::write(&arguments, r#"{"flag":{"bytes":["90"]}}"#).unwrap();
    let report = run("run", &options, &invocation);
    assert_eq!(report["code"], "entry-input-byte", "{report}");
    assert_eq!(report["input_path"], "arguments.flag.bytes");
    let prior: Json = serde_json::from_slice(&std::fs::read(&results).unwrap()).unwrap();
    assert_eq!(prior["value"], value);
}

#[test]
fn checked_metadata_inspection_precedes_native_calculation_admission() {
    let dir = tempfile::tempdir().unwrap();
    let boolean = schema("boolean", "bool", &["bool"]);
    let mut document: Json = serde_json::from_slice(&boolean_package(false)).unwrap();
    let mut artifact: Json = serde_json::from_str(document["artifact"].as_str().unwrap()).unwrap();
    artifact["functions"][0]["body"]["operations"] = json!([{
        "op":"numeric","calculation":"invalid-native-code","operands":[0],
        "results":[{"id":1,"schema":boolean}]
    }]);
    artifact["functions"][0]["body"]["returns"] = json!([1]);
    artifact["calculations"] = json!([{"id":"invalid-native-code","parameters":[boolean],
        "results":[boolean],"function":"calculation","program":"invalid native program"}]);
    document["artifact"] = json!(artifact.to_string());
    let options = pinned(dir.path(), &serde_json::to_vec(&document).unwrap());
    let inspected = run("inspect", &options, &[]);
    assert_eq!(inspected["status"], "inspected", "{inspected}");
    let templates = dir.path().join("inputs");
    let initialized = run(
        "prepare",
        &options,
        &[format!("--output={}", templates.display())],
    );
    assert_eq!(initialized["status"], "prepared", "{initialized}");
    std::fs::write(templates.join("arguments.json"), r#"{"flag":true}"#).unwrap();
    let refused = run(
        "run",
        &options,
        &[format!(
            "--input={}",
            templates.join("arguments.json").display()
        )],
    );
    assert_eq!(refused["status"], "refused", "{refused}");
    assert_eq!(refused["phase"], "admission");
    assert!(refused.get("execution").is_none());
}

#[test]
fn checks_prepare_without_executing_and_failure_preserves_output() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &boolean_package(true));
    let arguments = dir.path().join("arguments.json");
    std::fs::write(&arguments, r#"{"flag":false}"#).unwrap();
    let input = format!("--input={}", arguments.display());
    let checked = run("run", &options, &["--dry-run".into(), input.clone()]);
    assert_eq!(checked["status"], "inputs-checked", "{checked}");
    assert!(checked.get("execution").is_none());
    let results = dir.path().join("result.json");
    std::fs::write(&results, b"prior result").unwrap();
    let stopped = run(
        "run",
        &options,
        &[input, format!("--results={}", results.display())],
    );
    assert_eq!(stopped["status"], "refused", "{stopped}");
    assert_eq!(stopped["phase"], "execution");
    assert!(stopped["execution"]["failure"].is_object());
    assert_eq!(std::fs::read(&results).unwrap(), b"prior result");
    assert!(stopped.get("publication").is_none());
}

#[test]
fn exact_names_shape_pins_and_output_identity_are_enforced() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &boolean_package(false));
    assert_eq!(run("run", &options, &[])["code"], "entry-input-missing");
    let arguments = dir.path().join("arguments.json");
    let input = format!("--input={}", arguments.display());
    for (contents, code, path) in [
        (r#"{}"#, "entry-input-names", "arguments.flag"),
        (r#"{"flag":null}"#, "entry-input-unfilled", "arguments.flag"),
        (
            r#"{"flag":true,"extra":false}"#,
            "entry-input-names",
            "arguments.extra",
        ),
        (r#"[]"#, "entry-input-shape", "arguments"),
        (
            r#"{"flag":true,"flag":false}"#,
            "entry-request-format",
            "arguments",
        ),
    ] {
        std::fs::write(&arguments, contents).unwrap();
        let report = run("run", &options, &["--dry-run".into(), input.clone()]);
        assert_eq!(report["code"], code, "{report}");
        assert_eq!(report["input_path"], path);
    }
    std::fs::write(&arguments, r#"{"flag":true}"#).unwrap();
    let report = run(
        "run",
        &options,
        &[input, format!("--results={}", arguments.display())],
    );
    assert_eq!(report["code"], "entry-output-path", "{report}");
    assert_eq!(
        std::fs::read_to_string(&arguments).unwrap(),
        r#"{"flag":true}"#
    );
    let mut wrong_pin = options.clone();
    wrong_pin[1] = format!("--sha256={}", "0".repeat(64));
    assert_eq!(
        run("inspect", &wrong_pin, &[])["code"],
        "entry-package-identity"
    );
    assert_eq!(
        run("prove", &options, &["--output=unused".into()])["code"],
        "source-entry-selection"
    );
}

#[test]
fn invocation_context_is_explicit_strict_and_protected_from_publication() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &boolean_package(false));
    let arguments = dir.path().join("arguments=map.json");
    std::fs::write(&arguments, r#"{"flag":true}"#).unwrap();
    let input = format!("--input={}", arguments.display());
    let context = dir.path().join("context.json");
    let invocation_file = format!("--invocations={}", context.display());
    let empty = json!({"format":"zkc.entry-invocations/0","deployments":{}});
    std::fs::write(&context, empty.to_string()).unwrap();
    let checked = run(
        "run",
        &options,
        &["--dry-run".into(), input.clone(), invocation_file.clone()],
    );
    assert_eq!(checked["status"], "inputs-checked", "{checked}");
    let protected = run(
        "run",
        &options,
        &[
            input.clone(),
            invocation_file.clone(),
            format!("--results={}", context.display()),
        ],
    );
    assert_eq!(protected["code"], "entry-output-path", "{protected}");
    assert_eq!(
        std::fs::read_to_string(&context).unwrap(),
        empty.to_string()
    );
    for contents in [
        r#"{"format":"zkc.entry-invocations/0","deployments":{},"extra":true}"#,
        r#"["zkc.entry-invocations/0",{}]"#,
        r#"{"format":"zkc.entry-invocations/0","deployments":{"child":{"operation":"run","session":true,"authority":{"format":"zkc.entry-setups/0","keys":{}},"services":{},"setups":{}}}}"#,
    ] {
        std::fs::write(&context, contents).unwrap();
        let report = run(
            "run",
            &options,
            &["--dry-run".into(), input.clone(), invocation_file.clone()],
        );
        assert_eq!(report["code"], "entry-invocation-format", "{report}");
        assert!(report.get("execution").is_none());
    }
}

#[test]
fn joint_children_use_native_defaults_and_exact_context_overrides() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &joint_package());
    let inspected = run("inspect", &options, &[]);
    assert_eq!(inspected["status"], "inspected", "{inspected}");
    assert_eq!(inspected["invocations"][0]["id"], "child.Pair");
    assert_eq!(inspected["invocations"][0]["operation"], "run");
    assert_eq!(inspected["invocations"][0]["setups"], json!([]));
    assert_eq!(inspected["invocations"][0]["roles"][0]["role"], "P");
    let values = json!({"P":{"value":true},"V":{"value":false}});
    let input = dir.path().join("arguments.json");
    std::fs::write(&input, json!({"flag":values}).to_string()).unwrap();
    let results = dir.path().join("results.json");
    let arguments = [
        format!("--input={}", input.display()),
        format!("--results={}", results.display()),
    ];
    let report = run("run", &options, &arguments);
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["execution"]["calls"][0]["operation"], "run");
    let returned: Json = serde_json::from_slice(&std::fs::read(&results).unwrap()).unwrap();
    assert_eq!(returned["value"], values);
    let context = dir.path().join("invocations.json");
    let mut document = json!({"format":"zkc.entry-invocations/0","deployments":{
        "child.Pair":{"operation":"run","authority":{"format":"zkc.entry-setups/0","keys":{}},
            "session":"chosen-session","services":{},"setups":{}}
    }});
    std::fs::write(&context, document.to_string()).unwrap();
    let checks = [
        "--dry-run".into(),
        arguments[0].clone(),
        format!("--invocations={}", context.display()),
    ];
    let checked = run("run", &options, &checks);
    assert_eq!(checked["status"], "inputs-checked", "{checked}");
    assert!(checked.get("execution").is_none());
    for (services, code) in [
        (json!({"unknown":{}}), "entry-host-context-role"),
        (json!({"P":{"unknown":0}}), "entry-service-names"),
    ] {
        document["deployments"]["child.Pair"]["services"] = services;
        std::fs::write(&context, document.to_string()).unwrap();
        let refused = run("run", &options, &checks);
        assert_eq!(refused["code"], code, "{refused}");
        assert!(refused.get("execution").is_none());
    }
    document["deployments"]["child.Pair"] = json!({"operation":"verify",
        "authority":{"format":"zkc.entry-setups/0","keys":{}},"context":"","services":{},"setups":{}});
    std::fs::write(&context, document.to_string()).unwrap();
    let refused = run("run", &options, &checks);
    assert_eq!(refused["code"], "entry-invocation-deployments", "{refused}");
}

#[test]
fn child_setup_inputs_use_confined_key_initializers_and_independent_authority() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &joint_setup_package());
    let bounds = zkc_native::Policy::default().ark_bounds();
    let keys = zkc_kernels::Keys::setup_for_development(1, &bounds).unwrap();
    let verifier = keys.verifier_key();
    let prover = keys.prover_key();
    std::fs::write(
        dir.path().join("verifier.key"),
        verifier.to_bytes(&bounds).unwrap(),
    )
    .unwrap();
    let prover_bytes = prover.to_bytes(&bounds).unwrap();
    std::fs::write(dir.path().join("prover.key"), &prover_bytes).unwrap();
    let input = dir.path().join("arguments.json");
    std::fs::write(
        &input,
        r#"{"flag":{"P":{"value":true},"V":{"value":false}}}"#,
    )
    .unwrap();
    let context = dir.path().join("invocations.json");
    let mut document = json!({"format":"zkc.entry-invocations/0","deployments":{
        "child.Pair":{"operation":"run","authority":{"format":"zkc.entry-setups/0",
            "keys":{"pcs":hex(&verifier.metadata().key_id())}},"session":"setup-test",
            "services":{},"setups":{"pcs":"verifier.key"},"inputs":{"P":{
                "pk":{"file":"prover.key","fingerprint":hex(&prover.material_fingerprint())}
            }}}
    }});
    std::fs::write(&context, document.to_string()).unwrap();
    let args = [
        format!("--input={}", input.display()),
        format!("--invocations={}", context.display()),
    ];
    let checked = run(
        "run",
        &options,
        &[vec!["--dry-run".into()], args.to_vec()].concat(),
    );
    assert_eq!(checked["status"], "inputs-checked", "{checked}");
    assert!(checked.get("execution").is_none());
    let executed = run("run", &options, &args);
    assert_eq!(executed["status"], "executed", "{executed}");
    let mut forged = document.clone();
    forged["deployments"]["child.Pair"]["inputs"]["P"]["pk"]["fingerprint"] = json!("0".repeat(64));
    std::fs::write(&context, forged.to_string()).unwrap();
    let refused = run(
        "run",
        &options,
        &[vec!["--dry-run".into()], args.to_vec()].concat(),
    );
    assert_eq!(refused["code"], "key-mismatch", "{refused}");
    assert!(refused.get("execution").is_none());
    std::fs::write(&context, document.to_string()).unwrap();
    let protected = run(
        "run",
        &options,
        &[
            args.to_vec(),
            vec![format!(
                "--results={}",
                dir.path().join("prover.key").display()
            )],
        ]
        .concat(),
    );
    assert_eq!(protected["code"], "entry-output-path", "{protected}");
    assert_eq!(
        std::fs::read(dir.path().join("prover.key")).unwrap(),
        prover_bytes
    );
    for (inputs, code) in [
        (json!({"P":{"value":true}}), "entry-input-names"),
        (json!({"unknown":{}}), "entry-host-context-role"),
        (
            json!({"P":{"pk":{"file":"../prover.key","fingerprint":hex(&prover.material_fingerprint())}}}),
            "entry-input-reference",
        ),
    ] {
        document["deployments"]["child.Pair"]["inputs"] = inputs;
        std::fs::write(&context, document.to_string()).unwrap();
        let refused = run("run", &options, &args);
        assert_eq!(refused["code"], code, "{refused}");
        assert!(refused.get("execution").is_none());
    }
}

#[cfg(unix)]
#[test]
fn function_file_references_reuse_confinement_and_inode_protection() {
    let dir = tempfile::tempdir().unwrap();
    let options = pinned(dir.path(), &boolean_package(false));
    let backend = zkc_native::NativeBackend::new(
        Default::default(),
        zkc_native::EntryPolicy::new(
            zkc_native::Domain::new("session", "test", "entry", None),
            None,
        ),
        Default::default(),
    )
    .unwrap();
    let wire = backend
        .encode_native_value(&zkc_native::Value::Bool(true))
        .unwrap();
    let data = dir.path().join("data");
    std::fs::create_dir(&data).unwrap();
    let leaf = data.join("boolean.zkcv");
    let alias = data.join("alias.zkcv");
    std::fs::write(&leaf, &wire).unwrap();
    std::fs::hard_link(&leaf, &alias).unwrap();
    let arguments = data.join("arguments.json");
    let input = format!("--input={}", arguments.display());
    let pin = hex(&Sha256::digest(&wire));
    std::fs::write(
        &arguments,
        json!({"flag":{"file":"boolean.zkcv","sha256":pin}}).to_string(),
    )
    .unwrap();
    let checked = run("run", &options, &["--dry-run".into(), input.clone()]);
    assert_eq!(checked["status"], "inputs-checked", "{checked}");
    let protected = run(
        "run",
        &options,
        &[input.clone(), format!("--results={}", alias.display())],
    );
    assert_eq!(protected["code"], "entry-output-path", "{protected}");
    assert_eq!(std::fs::read(&leaf).unwrap(), wire);
    for relative in ["../data/boolean.zkcv", "/absolute", "./boolean.zkcv"] {
        std::fs::write(
            &arguments,
            json!({"flag":{"file":relative,"sha256":pin}}).to_string(),
        )
        .unwrap();
        let checked = run("run", &options, &["--dry-run".into(), input.clone()]);
        assert_eq!(checked["code"], "entry-input-reference", "{checked}");
        assert_eq!(checked["input_path"], "arguments.flag");
    }
}

#[test]
fn zero_parameter_unit_return_is_explicit_and_needs_no_input_file() {
    let dir = tempfile::tempdir().unwrap();
    let unit = schema("unit", "()", &[]);
    let bytes = package(
        &interface(&unit, false),
        json!([{
            "op":"construct","operands":[],"results":[{"id":0,"schema":unit}],"alternative":""
        }]),
        json!([]),
        json!([0]),
    );
    let options = pinned(dir.path(), &bytes);
    let result_path = dir.path().join("result.json");
    let report = run(
        "run",
        &options,
        &[format!("--results={}", result_path.display())],
    );
    assert_eq!(report["status"], "executed", "{report}");
    let result: Json = serde_json::from_slice(&std::fs::read(result_path).unwrap()).unwrap();
    assert_eq!(result, json!({"format":"zkc.entry-outputs/0","value":null}));
    let templates = dir.path().join("templates");
    let report = run(
        "prepare",
        &options,
        &[format!("--output={}", templates.display())],
    );
    assert_eq!(report["status"], "prepared", "{report}");
    assert_eq!(
        std::fs::read_to_string(templates.join("arguments.json")).unwrap(),
        "{}\n"
    );
}

#[test]
fn structured_arguments_and_returns_follow_the_same_schema() {
    let dir = tempfile::tempdir().unwrap();
    let index = schema("index", "index", &["index"]);
    let boolean = schema("boolean", "bool", &["bool"]);
    let unit = schema("unit", "()", &[]);
    let mut pair = schema("tuple", "((),index)", &["index"]);
    pair["fields"] =
        json!([{"name":"0","offset":0,"schema":unit},{"name":"1","offset":0,"schema":index}]);
    let mut record = schema("record", "sample::Data", &["index", "bool"]);
    record["fields"] =
        json!([{"name":"item","offset":0,"schema":pair},{"name":"ok","offset":1,"schema":boolean}]);
    let bytes = package(
        &interface(&record, true),
        json!([]),
        json!([{"id":0,"schema":record}]),
        json!([0]),
    );
    let options = pinned(dir.path(), &bytes);
    let arguments = dir.path().join("arguments.json");
    let data = json!({"item":[null,u64::MAX.to_string()],"ok":false});
    std::fs::write(&arguments, json!({"flag":data}).to_string()).unwrap();
    let results = dir.path().join("result.json");
    let report = run(
        "run",
        &options,
        &[
            format!("--input={}", arguments.display()),
            format!("--results={}", results.display()),
        ],
    );
    assert_eq!(report["status"], "executed", "{report}");
    let document: Json = serde_json::from_slice(&std::fs::read(&results).unwrap()).unwrap();
    assert_eq!(document["value"], data);
}

#[cfg(unix)]
#[test]
fn source_inspection_preparation_and_execution_share_checked_metadata() {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let boolean = schema("boolean", "bool", &["bool"]);
    let metadata = interface(&boolean, true);
    std::fs::write(root.join("interface.json"), metadata.to_string()).unwrap();
    let port = |name, index, roles: Json| {
        json!({"name":name,"index":index,"native":[index],
        "roles":roles,"type":"bool","schema":boolean})
    };
    let proof = json!({"format":"zkc.language-interface/0","capture":metadata["capture"],
        "original":metadata["original"],"toolchain":metadata["toolchain"],"entry":"sample::Proof",
        "protocol":"sample_Protocol","setups":[],"relations":[],"protocols":[{
            "symbol":"sample_Protocol","roles":["P","V"],
            "inputs":[port("statement",0,json!(["P","V"])),port("secret",1,json!(["P"]))],
            "outputs":[port("accepted",0,json!(["V"]))],"services":[],"clauses":[]}],
        "job":{"kind":"proof","prover":"P","verifier":"V","public":[0],"completion":null,"target":null,
            "acceptance":{"direction":"output","port":0,"role":"V","path":[]},
            "construction":{"kind":"authored","format":"zkc.framed/0"}}});
    std::fs::write(root.join("proof-interface.json"), proof.to_string()).unwrap();
    std::fs::write(root.join("package.json"), boolean_package(false)).unwrap();
    let check = json!({"format":"zkc.source-check/0","status":"checked","phase":"complete",
        "scope":"definitions","capture":metadata["capture"],"installation":metadata["toolchain"],
        "entries":[{"name":"sample::Main","kind":"function"},{"name":"sample::Proof","kind":"proof"}]});
    std::fs::write(root.join("check.json"), check.to_string()).unwrap();
    let source = root.join("main.zkc");
    std::fs::write(
        &source,
        "module sample; entry fn Main(flag: bool) -> bool { return flag; }\n",
    )
    .unwrap();
    let manifest = root.join("zkc.toml");
    std::fs::write(
        &manifest,
        "format = \"zkc.project/0\"\n[modules]\nsample = \"main.zkc\"\n",
    )
    .unwrap();
    let compiler = root.join("compiler");
    let quote = |p: &Path| format!("'{}'", p.to_str().unwrap().replace('\'', "'\\''"));
    let script = format!(
        "#!/bin/sh\ncase \"$1\" in\nlanguage-interface)\n  for arg do\n    if [ \"$arg\" = '--entry=sample::Proof' ]; then cat {}; exit; fi\n  done\n  cat {};;\nlanguage-check) cat {};;\nlanguage-package)\n  found=false\n  for arg do\n    if [ \"$arg\" = '--entry-kind=function' ]; then found=true; fi\n  done\n  [ \"$found\" = true ] || exit 9\n  cat {};;\n*) exit 8;;\nesac\n",
        quote(&root.join("proof-interface.json")),
        quote(&root.join("interface.json")),
        quote(&root.join("check.json")),
        quote(&root.join("package.json"))
    );
    std::fs::write(&compiler, script).unwrap();
    std::fs::set_permissions(&compiler, std::fs::Permissions::from_mode(0o755)).unwrap();
    let options = vec![
        format!("--project={}", manifest.display()),
        format!("--compiler={}", compiler.display()),
    ];
    let inspected = run("inspect", &options, &[]);
    assert_eq!(inspected["status"], "inspected", "{inspected}");
    assert!(inspected.get("package_sha256").is_none());
    let prepared = run("prepare", &options, &[]);
    assert_eq!(prepared["status"], "prepared", "{prepared}");
    let arguments = root.join("inputs/sample.Main/arguments.json");
    let public = root.join("inputs/sample.Proof/public.json");
    let witness = root.join("inputs/sample.Proof/witness.json");
    assert_eq!(prepared["files"], json!([arguments, public, witness]));
    assert_eq!(
        std::fs::read_to_string(&public).unwrap(),
        "{\n  \"statement\": null\n}\n"
    );
    assert_eq!(
        std::fs::read_to_string(&witness).unwrap(),
        "{\n  \"secret\": null\n}\n"
    );
    std::fs::write(&arguments, r#"{"flag":false}"#).unwrap();
    let again = run("prepare", &options, &[]);
    assert_eq!(again["preserved"], json!([arguments, public, witness]));
    let checked = run("run", &options, &["--dry-run".into()]);
    assert_eq!(checked["status"], "inputs-checked", "{checked}");
    let executed = run("run", &options, &[]);
    assert_eq!(executed["status"], "executed", "{executed}");
    let output = root.join("build/zkc/sample.Main.results.json");
    let document: Json = serde_json::from_slice(&std::fs::read(&output).unwrap()).unwrap();
    assert_eq!(document["value"], false);
    assert_eq!(executed["inputs"], json!({"arguments":arguments}));
    let suppressed = run("run", &options, &["--no-results".into()]);
    assert_eq!(suppressed["status"], "executed", "{suppressed}");
    assert!(suppressed.get("publication").is_none());
    assert!(suppressed.get("results").is_none());
}
