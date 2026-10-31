use super::*;
use crate::entry::Value;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};

fn digest(s: &str) -> String {
    crate::io::bytes::hex(&Sha256::digest(s.as_bytes()))
}
fn schema(kind: &str, name: &str, leaves: Json) -> Json {
    json!({"kind":kind,"type":name,"identity":digest(name),"custody":false,"constructible":true,
        "permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":leaves})
}
fn boolean() -> Json {
    schema("boolean", "bool", json!(["bool"]))
}
fn index() -> Json {
    schema("index", "index", json!(["index"]))
}
fn unit() -> Json {
    schema("unit", "()", json!([]))
}
fn record(name: &str, fields: Vec<(&str, Json)>, constructible: bool) -> Json {
    let mut offset = 0;
    let mut leaves = Vec::new();
    let mut result = Vec::new();
    for (name, s) in fields {
        result.push(json!({"name":name,"offset":offset,"schema":s}));
        let children = s["leaves"].as_array().unwrap();
        offset += children.len();
        leaves.extend(children.iter().cloned());
    }
    let mut s = schema("record", name, json!(leaves));
    s["fields"] = json!(result);
    s["constructible"] = json!(constructible);
    s
}
fn variant(name: &str, arms: Vec<(&str, Vec<(&str, Json)>)>, constructible: bool) -> Json {
    let payload = arms
        .iter()
        .enumerate()
        .map(|(i, (_, fields))| {
            json!([
                format!("case{i:08}"),
                fields
                    .iter()
                    .flat_map(|(_, s)| s["leaves"].as_array().unwrap().iter())
                    .map(|leaf| match leaf.as_str() {
                        Some(s) if s.starts_with("variant:") => zkc_test_support::variants::tree(s),
                        _ => leaf.clone(),
                    })
                    .collect::<Vec<_>>()
            ])
        })
        .collect::<Vec<_>>();
    let spelling = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity(name)
        ],
        payload
    ]));
    let mut s = schema("variant", name, json!([spelling]));
    s["constructible"] = json!(constructible);
    s["alternatives"] = json!(
        arms.into_iter()
            .map(|(name, fields)| {
                let product = record("payload", fields, constructible);
                json!({"name":name,"fields":product["fields"]})
            })
            .collect::<Vec<_>>()
    );
    s
}
fn signature(name: &str, parameters: Vec<(&str, Json)>, result: Json) -> Json {
    json!({"symbol":name,"parameters":parameters.into_iter().map(|(name,schema)|json!({"name":name,"schema":schema})).collect::<Vec<_>>(),"result":result})
}
fn definition(id: u32, schema: Json) -> Json {
    json!({"id":id,"schema":schema})
}
fn block(arguments: Json, operations: Json, returns: Json) -> Json {
    json!({"arguments":arguments,"operations":operations,"returns":returns})
}
fn document(parameters: Vec<(&str, Json)>, result: Json, operations: Json, returns: Json) -> Json {
    let args = parameters
        .iter()
        .enumerate()
        .map(|(i, (_, s))| definition(i as u32, s.clone()))
        .collect::<Vec<_>>();
    json!({"format":"zkc.host/0","original":digest("original"),"entry":"example::Main",
        "functions":[{"signature":signature("example::Main",parameters,result),"body":block(json!(args),operations,returns)}],"calculations":[],"deployments":[]})
}
fn capture(doc: &Json) -> Package {
    let interface = json!({"format":"zkc.language-interface/0","capture":digest("capture"),"original":digest("original"),"toolchain":"test",
        "entry":"example::Main","selection":{"kind":"function","function":doc["entry"]},
        "functions":doc["functions"].as_array().unwrap().iter().map(|f|f["signature"].clone()).collect::<Vec<_>>(),"protocols":[],"relations":[],"setups":[]});
    package(&interface, &doc.to_string())
}
fn package(interface: &Json, artifact: &str) -> Package {
    let bytes=json!({"format":"zkc.entry/0","original":"original","interface":interface.to_string(),"artifact":artifact,"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
    Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}
fn admit(doc: &Json) -> Result<FunctionEntry> {
    FunctionEntry::admit(capture(doc), FunctionOptions::default(), BTreeMap::new())
}
fn request(values: Vec<(&str, Value)>) -> FunctionRequest {
    FunctionRequest {
        arguments: values.into_iter().map(|(n, v)| (n.into(), v)).collect(),
        ..Default::default()
    }
}
fn refusal(doc: &Json, code: &str) {
    let e = admit(doc).err().expect("must refuse");
    assert_eq!(e.code(), code, "{e:?}");
}

#[test]
fn compact_source_schemas_cannot_exceed_the_native_descriptor_cache_limit() {
    for count in [6, 9] {
        let schemas: Vec<_> = (0..count)
            .map(|i| {
                let inner = json!(["inner", [["A", vec!["bool"; 128]]]]);
                let outer = json!([format!("outer{i}"), [["B", vec![inner; 64]]]]);
                let spelling = format!(
                    "sequence<{}>",
                    zkc_test_support::variants::encode_tree(outer)
                );
                schema("builtin", &spelling, json!([spelling]))
            })
            .collect();
        let names: Vec<_> = (0..count).map(|i| format!("p{i}")).collect();
        let parameters = names
            .iter()
            .zip(schemas)
            .map(|(name, schema)| (name.as_str(), schema))
            .collect();
        let operations = json!([{
            "op":"construct", "alternative":"", "operands":[],
            "results":[definition(count, unit())]
        }]);
        let doc = document(parameters, unit(), operations, json!([count]));
        // Source inspection remains independent of native cache layout.
        FunctionInterface::read(&capture(&doc)).unwrap();
        if count == 6 {
            admit(&doc).unwrap();
        } else {
            refusal(&doc, "entry-interface-limit");
        }
    }
}

fn calculation() -> Json {
    let field = schema(
        "field",
        "field<bls12-381.fr>",
        json!(["field:bls12-381.fr"]),
    );
    let physical = "field:bls12-381.fr@arkworks.fr/0";
    let program = json!([
        "zkc.program/0",
        [[
            "add",
            "field.add",
            ["bls12-381.fr"],
            "arkworks/field.add",
            []
        ]],
        [[
            "function",
            "sum",
            [["a", physical], ["b", physical]],
            [physical],
            [
                ["op", "sum", "add", [], ["a", "b"], ["out"]],
                ["return", ["out"]]
            ],
            ["sum", []]
        ]],
        [],
        []
    ]);
    json!({"id":"sum","function":"sum","parameters":[field.clone(),field.clone()],"results":[field],"program":program.to_string()})
}
#[test]
fn standalone_numerical_assets_are_authenticated_including_dormant_branches() {
    use zkc_runtime::{
        ring::{Expression, Node},
        vm::{Identity, LogicalType, PhysicalType},
    };
    let arena = |product| {
        Expression::new(
            vec![Identity::KoalaBear; 2],
            vec![
                Node::Input(0),
                Node::Input(1),
                if product {
                    Node::Mul(0, 1)
                } else {
                    Node::Add(0, 1)
                },
            ],
            if product { vec![2] } else { vec![2, 0] },
        )
        .unwrap()
        .canonical()
    };
    let executed = arena(true);
    let dormant = arena(false);
    let vector = schema(
        "builtin",
        "Vector<koala-bear>",
        json!(["vector:koala-bear"]),
    );
    let physical = PhysicalType::default_for(LogicalType::parse("vector:koala-bear").unwrap())
        .unwrap()
        .spelling();
    let boolean_physical = PhysicalType::default_for(LogicalType::parse("bool").unwrap())
        .unwrap()
        .spelling();
    let program = json!([
        "zkc.program/0",
        [[
            "ring",
            "ring.point",
            ["koala-bear"],
            "plonky3/ring.point",
            []
        ]],
        [[
            "function",
            "evaluate",
            [["x", physical], ["flag", boolean_physical]],
            [physical],
            [
                [
                    "if",
                    "branch",
                    "flag",
                    ["x"],
                    [
                        ["op", "hidden", "ring", [digest(&dormant)], ["x"], ["t"]],
                        ["yield", ["t"]]
                    ],
                    [["yield", ["x"]]],
                    ["chosen"]
                ],
                [
                    "op",
                    "evaluate",
                    "ring",
                    [digest(&executed)],
                    ["chosen"],
                    ["out"]
                ],
                ["return", ["out"]]
            ],
            ["evaluate", []]
        ]],
        [],
        []
    ]);
    let mut d = document(
        vec![("x", vector.clone()), ("flag", boolean())],
        vector.clone(),
        json!([{"op":"numeric","calculation":"evaluate","operands":[0,1],"results":[definition(2,vector.clone())]}]),
        json!([2]),
    );
    d["calculations"] = json!([{"id":"evaluate","function":"evaluate","parameters":[vector.clone(),boolean()],"results":[vector],"program":program.to_string()}]);
    let capture_assets = |assets: Vec<(String, String)>| {
        let mut package: Json = serde_json::from_slice(capture(&d).bytes()).unwrap();
        let mut assets = assets;
        assets.sort();
        package["assets"] = json!(assets);
        let bytes = package.to_string();
        Package::capture(
            bytes.as_bytes(),
            &Sha256::digest(bytes.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap()
    };
    let missing = FunctionEntry::admit(
        capture_assets(vec![(digest(&executed), executed.clone())]),
        Default::default(),
        BTreeMap::new(),
    )
    .err()
    .expect("dormant reference must be admitted");
    assert_eq!(missing.code(), "entry-asset-missing");
    let wrong = FunctionEntry::admit(
        capture_assets(vec![
            (digest(&executed), executed.clone()),
            (digest(&dormant), executed.clone()),
        ]),
        Default::default(),
        BTreeMap::new(),
    )
    .err()
    .expect("asset body must match its independent identity");
    assert_eq!(wrong.phase, crate::entry::EntryPhase::Assets);
    let entry = FunctionEntry::admit(
        capture_assets(vec![
            (digest(&executed), executed),
            (digest(&dormant), dormant),
        ]),
        Default::default(),
        BTreeMap::new(),
    )
    .unwrap();
    assert_eq!(entry.assets().references().len(), 2);
    for (flag, expected) in [(false, 12u32), (true, 21u32)] {
        let report = entry
            .prepare(request(vec![
                (
                    "x",
                    zkc_cpu::Value::KoalaBearVector(
                        vec![zkc_cpu::KoalaBear::new(3), zkc_cpu::KoalaBear::new(4)].into(),
                    )
                    .into(),
                ),
                ("flag", flag.into()),
            ]))
            .unwrap()
            .execute();
        assert!(report.is_success(), "{}", report.diagnostics());
        assert!(report.usage.ring_work > 0);
        let Value::Leaf(crate::execution::InputValue::Native(v)) =
            report.value.unwrap().into_value()
        else {
            panic!("vector")
        };
        let zkc_cpu::Value::KoalaBearVector(values) = *v else {
            panic!("vector")
        };
        assert_eq!(values.as_ref(), &[zkc_cpu::KoalaBear::new(expected)]);
    }
}
fn numeric_document() -> Json {
    let c = calculation();
    let field = c["results"][0].clone();
    let mut doc = document(
        vec![("a", field.clone()), ("b", field.clone())],
        field.clone(),
        json!([{"op":"numeric","calculation":"sum","operands":[0,1],"results":[definition(2,field)]}]),
        json!([2]),
    );
    doc["calculations"] = json!([c]);
    doc
}
#[test]
fn numerical_standalone_uses_native_field_calculation_and_named_plans() {
    let entry = admit(&numeric_document()).unwrap();
    assert_eq!(entry.signature().parameters[0].name, "a");
    assert_eq!(entry.functions().count(), 1);
    let report = entry
        .prepare(request(vec![
            (
                "a",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(7u64)).into(),
            ),
            (
                "b",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(9u64)).into(),
            ),
        ]))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    assert_eq!(
        report.execution_counts.json().is_some(),
        zkc_runtime::vm::ExecutionCounts::ENABLED
    );
    if let Some(counts) = report.execution_counts.json() {
        assert_eq!(counts["operations"]["field.add"], json!(1));
    }
    assert_eq!(report.calls[0].operation, "numeric");
    assert!(report.usage.execution.instructions > 1);
    let Value::Leaf(crate::execution::InputValue::Native(v)) = report.value.unwrap().into_value()
    else {
        panic!("native result")
    };
    let zkc_cpu::Value::Field(v) = *v else {
        panic!("field")
    };
    assert_eq!(v, zkc_cpu::Scalar::from(16u64));
}

#[test]
fn cpu_context_reaches_numerical_backends_and_all_admitted_children() {
    let cpu = CpuExecution::new(1).unwrap();
    let worker = |cpu: &CpuExecution| cpu.execute(|| std::thread::current().id());
    let id = worker(&cpu);
    let first_default = admit(&numeric_document()).unwrap();
    let second_default = admit(&numeric_document()).unwrap();
    if cfg!(feature = "parallel") {
        assert_ne!(worker(first_default.cpu()), worker(second_default.cpu()));
    } else {
        assert_eq!(worker(first_default.cpu()), worker(second_default.cpu()));
    }
    if cfg!(feature = "parallel") {
        assert_ne!(worker(first_default.cpu()), id);
    } else {
        assert_eq!(worker(first_default.cpu()), id);
    }
    let numerical = FunctionEntry::admit_with_cpu(
        capture(&numeric_document()),
        Default::default(),
        BTreeMap::new(),
        cpu.clone(),
    )
    .unwrap();
    let backend = data::numerical_backend(numerical.host(), Default::default(), "sum").unwrap();
    assert_eq!(worker(backend.cpu()), id);
    assert_eq!(
        worker(
            data::backend(Default::default(), cpu.clone(), Default::default())
                .unwrap()
                .cpu()
        ),
        id
    );
    let report = numerical
        .prepare(request(vec![
            (
                "a",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(7u64)).into(),
            ),
            (
                "b",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(9u64)).into(),
            ),
        ]))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());

    let joint = FunctionEntry::admit_with_cpu(
        capture(&joint_document()),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
        cpu.clone(),
    )
    .unwrap();
    let proof = |producing| {
        FunctionEntry::admit_with_cpu(
            capture(&proof_document(producing)),
            FunctionOptions {
                binding: crate::entry::BindingPolicy::AllowAuthored,
                ..Default::default()
            },
            BTreeMap::from([("proof".into(), SetupAuthority::default())]),
            cpu.clone(),
        )
        .unwrap()
    };
    let producer = proof(true);
    let verifier = proof(false);
    let rebound = FunctionEntry::admit_with_cpu(
        capture(&joint_document()),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
        CpuExecution::serial().unwrap(),
    )
    .unwrap()
    .with_cpu(cpu.clone());
    #[allow(clippy::drop_non_drop)] // Serial builds have no owned pool to release.
    drop(cpu);
    for entry in [&joint, &producer, &verifier, &rebound] {
        assert_eq!(worker(entry.cpu()), id);
        for deployment in entry.host.deployments.values() {
            let child = match &deployment.kind {
                DeploymentKind::Run(entry) => entry.cpu(),
                DeploymentKind::Proof { entry, .. } => entry.cpu(),
            };
            assert_eq!(worker(child), id);
        }
    }
    let report = joint.prepare(joint_request()).unwrap().execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let report = producer
        .prepare(proof_request(true, true, vec![]))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let report = verifier
        .prepare(proof_request(false, true, produced_bytes()))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
}
#[test]
fn normal_false_is_data_and_entry_calls_share_one_execution() {
    let mut doc = document(
        vec![("flag", boolean())],
        boolean(),
        json!([{"op":"call","callee":"example::Child","operands":[0],"results":[definition(1,boolean())]}]),
        json!([1]),
    );
    doc["functions"].as_array_mut().unwrap().push(json!({"signature":signature("example::Child",vec![("flag",boolean())],boolean()),"body":block(json!([definition(0,boolean())]),json!([]),json!([0]))}));
    let entry = admit(&doc).unwrap();
    let r = entry
        .prepare(request(vec![("flag", false.into())]))
        .unwrap()
        .execute();
    assert!(r.is_success());
    assert!(!bool::try_from(r.value.unwrap().into_value()).unwrap());
    assert_eq!(r.calls.len(), 1);
    assert!(r.calls[0].completed);
    let mut cycle = doc.clone();
    cycle["functions"][1]["body"] = block(
        json!([definition(0, boolean())]),
        json!([{"op":"call","callee":"example::Main","operands":[0],"results":[definition(1,boolean())]}]),
        json!([1]),
    );
    refusal(&cycle, "entry-host-cycle");
    doc["functions"][1]["signature"]["symbol"] = json!("unused");
    refusal(&doc, "entry-host-callee");
}
#[test]
fn call_depth_includes_previously_admitted_callee_suffixes() {
    for length in [64, 65] {
        let mut doc = document(vec![("flag", boolean())], boolean(), json!([]), json!([0]));
        let mut operations = Vec::new();
        for i in 0..length {
            let callee = format!("example::Step{i:03}");
            operations.push(json!({"op":"call","callee":callee,"operands":[0],
                "results":[definition(i + 1, boolean())]}));
            let body = if i == 0 {
                block(json!([definition(0, boolean())]), json!([]), json!([0]))
            } else {
                block(
                    json!([definition(0, boolean())]),
                    json!([{"op":"call","callee":format!("example::Step{:03}", i - 1),
                        "operands":[0],"results":[definition(1, boolean())]}]),
                    json!([1]),
                )
            };
            doc["functions"].as_array_mut().unwrap().push(json!({
                "signature":signature(&callee, vec![("flag", boolean())], boolean()), "body":body}));
        }
        doc["functions"][0]["body"]["operations"] = json!(operations);
        doc["functions"][0]["body"]["returns"] = json!([length]);
        if length == 64 {
            assert!(
                admit(&doc).is_ok(),
                "the exact depth boundary must remain valid"
            );
        } else {
            refusal(&doc, "entry-host-depth");
        }
    }
}
#[test]
fn dormant_branches_are_admitted_without_speculative_execution() {
    let branch = |id| block(json!([definition(id, boolean())]), json!([]), json!([id]));
    let mut doc = document(
        vec![("flag", boolean())],
        boolean(),
        json!([{"op":"if","operands":[0,0],"results":[definition(3,boolean())],"regions":[branch(1),branch(2)]}]),
        json!([3]),
    );
    doc["functions"][0]["body"]["operations"][0]["regions"][1] = block(
        json!([definition(2, boolean())]),
        json!([{"op":"require","operands":[2],"results":[]}]),
        json!([2]),
    );
    let entry = admit(&doc).unwrap();
    assert!(
        entry
            .prepare(request(vec![("flag", true.into())]))
            .unwrap()
            .execute()
            .is_success()
    );
    let r = entry
        .prepare(request(vec![("flag", false.into())]))
        .unwrap()
        .execute();
    assert!(r.value.is_none());
    assert_eq!(r.failure.unwrap().code, "entry-host-require");
    doc["functions"][0]["body"]["operations"][0]["regions"][1]["operations"][0] =
        json!({"op":"invoke","deployment":"missing","operands":[],"results":[]});
    refusal(&doc, "entry-host-deployment");
}
#[test]
fn malformed_shapes_dominance_signatures_and_stage_are_refused_independently() {
    let base = document(vec![("flag", boolean())], boolean(), json!([]), json!([0]));
    for (path, value, code) in [
        ("/extra", json!(true), "entry-host-format"),
        ("/original", json!(digest("other")), "entry-host-identity"),
        (
            "/functions/0/body/returns",
            json!([99]),
            "entry-host-dominance",
        ),
        (
            "/functions/0/body/arguments/0/id",
            json!(-1),
            "entry-interface-format",
        ),
        (
            "/functions/0/body/arguments/0/schema/identity",
            json!(digest("other")),
            "entry-host-signature",
        ),
        (
            "/functions/0/body/operations",
            json!([{"op":"numeric","calculation":"missing","operands":[0],"results":[]}]),
            "entry-host-calculation",
        ),
    ] {
        let mut d = base.clone();
        if path == "/extra" {
            d["extra"] = value;
        } else {
            *d.pointer_mut(path).unwrap() = value;
        }
        refusal(&d, code);
    }
    let mut d = base.clone();
    d["functions"][0]["body"]["arguments"]
        .as_array_mut()
        .unwrap()
        .push(definition(0, boolean()));
    refusal(&d, "entry-host-signature");
    let mut d = base.clone();
    d["functions"][0]["body"]["operations"] = json!([{"op":"construct","alternative":"","operands":[],"results":[definition(1,unit())]},{"op":"construct","alternative":"","operands":[],"results":[definition(1,unit())]}]);
    refusal(&d, "entry-host-ssa");
}
#[test]
fn package_authentication_and_duplicate_keys_are_exact() {
    let d = document(vec![("flag", boolean())], boolean(), json!([]), json!([0]));
    let p = capture(&d);
    assert!(Package::capture(p.bytes(), &[0; 32], Package::MAX_BYTES).is_err());
    let text = d.to_string();
    for key in ["format", "original", "entry"] {
        let value = d[key].to_string();
        let field = format!("\"{key}\":{value}");
        let escaped = format!("\\u{:04x}{}", key.as_bytes()[0], &key[1..]);
        let changed = text.replacen(&field, &format!("{field},\"{escaped}\":{value}"), 1);
        let interface: Json = serde_json::from_str(p.interface()).unwrap();
        let e = FunctionEntry::admit(
            package(&interface, &changed),
            Default::default(),
            BTreeMap::new(),
        )
        .err()
        .unwrap();
        assert_eq!(e.code(), "entry-host-format");
    }
}
#[test]
fn projection_only_native_results_cannot_be_constructed_or_imported() {
    let r = record("Projection", vec![("flag", boolean())], false);
    let doc = document(
        vec![("flag", boolean())],
        r.clone(),
        json!([{"op":"construct","alternative":"","operands":[0],"results":[definition(1,r.clone())]}]),
        json!([1]),
    );
    refusal(&doc, "entry-host-constructor");
    let d = document(vec![("result", r.clone())], r, json!([]), json!([0]));
    let e = admit(&d).unwrap();
    assert_eq!(
        e.prepare(request(vec![(
            "result",
            Value::Record(BTreeMap::from([("flag".into(), true.into())]))
        )]))
        .err()
        .unwrap()
        .code(),
        "entry-input-constructor"
    );
}
#[test]
fn match_requires_complete_coverage_and_exact_nominal_payloads() {
    let choice = variant(
        "Choice",
        vec![("Empty", vec![]), ("Flag", vec![("value", boolean())])],
        true,
    );
    let mut doc = document(
        vec![("choice", choice.clone()), ("fallback", boolean())],
        boolean(),
        json!([{"op":"match","operands":[0,1],"results":[definition(5,boolean())],"alternatives":["Empty","Flag"],
        "regions":[block(json!([definition(2,boolean())]),json!([]),json!([2])),block(json!([definition(3,boolean()),definition(4,boolean())]),json!([]),json!([3]))]}]),
        json!([5]),
    );
    let entry = admit(&doc).unwrap();
    let r = entry
        .prepare(request(vec![
            (
                "choice",
                Value::Variant {
                    alternative: "Flag".into(),
                    fields: BTreeMap::from([("value".into(), true.into())]),
                },
            ),
            ("fallback", false.into()),
        ]))
        .unwrap()
        .execute();
    assert!(bool::try_from(r.value.unwrap().into_value()).unwrap());
    doc["functions"][0]["body"]["operations"][0]["alternatives"] = json!(["Empty", "Empty"]);
    refusal(&doc, "entry-host-coverage");
}
#[test]
fn repeated_children_exhaust_one_cumulative_meter_and_suppress_return() {
    let c = calculation();
    let f = c["results"][0].clone();
    let mut d = document(
        vec![
            ("a", f.clone()),
            ("b", f.clone()),
            ("lo", index()),
            ("hi", index()),
        ],
        f.clone(),
        json!([{"op":"for","carried":1,"operands":[2,3,0,1],"results":[definition(8,f.clone())],
        "regions":[block(json!([definition(4,index()),definition(5,f.clone()),definition(6,f.clone())]),json!([{"op":"numeric","calculation":"sum","operands":[5,6],"results":[definition(7,f.clone())]}]),json!([7]))]}]),
        json!([8]),
    );
    d["calculations"] = json!([c]);
    let mut options = FunctionOptions::default();
    options.limits.capacity.work.instructions = 14;
    options.journal_events = 1;
    let entry = FunctionEntry::admit(capture(&d), options.clone(), BTreeMap::new()).unwrap();
    let r = entry
        .prepare(request(vec![
            (
                "a",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(1u64)).into(),
            ),
            (
                "b",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(1u64)).into(),
            ),
            ("lo", 0u64.into()),
            ("hi", 20u64.into()),
        ]))
        .unwrap()
        .execute();
    assert!(r.failure.is_some());
    assert!(r.value.is_none());
    assert!(r.journal_truncated);
    assert_eq!(r.calls.len(), 1);
    assert!(r.usage.execution.instructions <= 14);
    assert!(r.usage.execution.instructions > 1);
}
#[test]
fn repeated_children_share_logical_work_and_fresh_allocation_before_dispatch() {
    let input = || {
        request(vec![
            (
                "a",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(1u64)).into(),
            ),
            (
                "b",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(2u64)).into(),
            ),
        ])
    };
    let one = admit(&numeric_document())
        .unwrap()
        .prepare(input())
        .unwrap()
        .execute();
    assert!(one.is_success());
    let mut d = numeric_document();
    let field = d["calculations"][0]["results"][0].clone();
    d["functions"][0]["body"]["operations"].as_array_mut().unwrap().push(json!({"op":"numeric","calculation":"sum","operands":[0,1],"results":[definition(3,field)]}));
    d["functions"][0]["body"]["returns"] = json!([3]);
    for logical in [false, true] {
        let mut options = FunctionOptions::default();
        if logical {
            options.limits.capacity.work.logical_bytes =
                one.usage.execution.logical_bytes + 16 * 1024;
        } else {
            options.limits.capacity.values.total_bytes =
                one.usage.execution.total_value_bytes + 16 * 1024;
        }
        let entry = FunctionEntry::admit(capture(&d), options.clone(), BTreeMap::new()).unwrap();
        let report = entry.prepare(input()).unwrap().execute();
        assert!(report.value.is_none());
        assert!(report.failure.is_some());
        assert_eq!(report.calls.len(), 1);
        assert!(report.calls[0].completed);
        assert!(report.usage.execution.logical_bytes <= options.limits.capacity.work.logical_bytes);
        assert!(
            report.usage.execution.total_value_bytes <= options.limits.capacity.values.total_bytes
        );
    }
}
#[test]
fn stop_retains_reached_prefix_and_never_executes_later_children() {
    let mut d = numeric_document();
    let f = d["functions"][0]["signature"]["result"].clone();
    d["functions"][0]["signature"]["parameters"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":"flag","schema":boolean()}));
    d["functions"][0]["body"]["arguments"]
        .as_array_mut()
        .unwrap()
        .push(definition(3, boolean()));
    d["functions"][0]["body"]["operations"].as_array_mut().unwrap().extend([json!({"op":"require","operands":[3],"results":[]}),json!({"op":"numeric","calculation":"sum","operands":[0,1],"results":[definition(4,f)]})]);
    let entry = admit(&d).unwrap();
    let r = entry
        .prepare(request(vec![
            (
                "a",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(1u64)).into(),
            ),
            (
                "b",
                zkc_cpu::Value::Field(zkc_cpu::Scalar::from(1u64)).into(),
            ),
            ("flag", false.into()),
        ]))
        .unwrap()
        .execute();
    assert!(r.value.is_none());
    assert_eq!(r.calls.len(), 1);
    assert!(r.calls[0].completed);
    assert_eq!(r.failure.unwrap().code, "entry-host-require");
}

fn row(fields: Vec<(&str, Value)>) -> Value {
    Value::Record(fields.into_iter().map(|(n, v)| (n.into(), v)).collect())
}
fn child_package(interface: &Json, artifact: &str) -> String {
    String::from_utf8(package(interface, artifact).bytes().to_vec()).unwrap()
}
fn joint_document() -> Json {
    joint_document_with_schema(boolean())
}
fn joint_document_with_schema(leaf: Json) -> Json {
    let (mut interface, artifact) = crate::entry::interface::tests::unicode::run_fixture(
        &leaf,
        &["P", "V"],
        &["role00000000", "role00000001"],
    );
    interface["entry"] = json!("main::run");
    let input = record(
        "main::Inputs",
        vec![
            (
                "P",
                record("main::Inputs::P", vec![("入力", leaf.clone())], true),
            ),
            (
                "V",
                record("main::Inputs::V", vec![("入力", leaf.clone())], true),
            ),
        ],
        true,
    );
    let output = record(
        "main::RunResult",
        vec![
            (
                "P",
                record("main::RunResult::P", vec![("結果", leaf.clone())], false),
            ),
            (
                "V",
                record("main::RunResult::V", vec![("結果", leaf.clone())], false),
            ),
        ],
        false,
    );
    let mut d = document(
        vec![("inputs", input.clone())],
        output.clone(),
        json!([{"op":"invoke","deployment":"joint","operands":[0],"results":[definition(1,output.clone())]}]),
        json!([1]),
    );
    d["deployments"] = json!([{"id":"joint","operation":"run","parameters":[input],"results":[output],"package":child_package(&interface,&artifact)}]);
    d
}
fn joint_request() -> FunctionRequest {
    let mut request = request(vec![(
        "inputs",
        row(vec![
            ("P", row(vec![("入力", true.into())])),
            ("V", row(vec![("入力", false.into())])),
        ]),
    )]);
    request.context.deployments.insert(
        "joint".into(),
        InvocationBinding::Run(RunContext {
            session: Some("fresh-session".into()),
            ..Default::default()
        }),
    );
    request
}
#[test]
fn joint_inputs_keep_independent_role_copies_and_cleanup_receipt() {
    let entry = FunctionEntry::admit(
        capture(&joint_document()),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let report = entry.prepare(joint_request()).unwrap().execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let Value::Record(mut roles) = report.value.unwrap().into_value() else {
        panic!("record")
    };
    let Value::Record(mut p) = roles.remove("P").unwrap() else {
        panic!("P")
    };
    let Value::Record(mut v) = roles.remove("V").unwrap() else {
        panic!("V")
    };
    assert!(bool::try_from(p.remove("結果").unwrap()).unwrap());
    assert!(!bool::try_from(v.remove("結果").unwrap()).unwrap());
    assert_eq!(report.usage.dispatches, 3);
    assert!(
        report.calls[0].native["cleanup_errors"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(report.calls[0].native["outcome"], json!(["completed"]));
    for role in report.calls[0].native["roles"].as_array().unwrap() {
        assert_eq!(role["usage"]["instructions"], json!(1));
    }
}
#[test]
fn concurrently_live_joint_runners_share_instruction_and_live_limits() {
    let mut options = FunctionOptions::default();
    options.limits.capacity.work.instructions = 3;
    let entry = FunctionEntry::admit(
        capture(&joint_document()),
        options.clone(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let report = entry.prepare(joint_request()).unwrap().execute();
    assert!(report.value.is_none());
    assert!(report.failure.is_some());
    assert!(report.usage.execution.instructions <= 3);
    assert_eq!(report.calls.len(), 1);
    assert!(!report.calls[0].completed);
    assert!(report.calls[0].native["roles"].as_array().is_some());
}
fn proof_schemas() -> (Json, Json, Json, Json, Json) {
    let family = "数学::証明₂";
    let public = record(
        &format!("{family}::Public"),
        vec![("公開", boolean())],
        true,
    );
    let witness = record(
        &format!("{family}::Witness"),
        vec![("秘密", boolean())],
        true,
    );
    let proof = record(
        &format!("{family}::Proof"),
        vec![(
            "bytes",
            schema("builtin", "builtin(\"bytes\")", json!(["bytes"])),
        )],
        true,
    );
    let produced = record(
        &format!("{family}::ProveResult"),
        vec![
            ("proof", proof.clone()),
            (
                "outputs",
                record(
                    &format!("{family}::ProverOutputs"),
                    vec![("結果", boolean())],
                    false,
                ),
            ),
        ],
        false,
    );
    let verified = variant(
        &format!("{family}::VerifyResult"),
        vec![
            (
                "Accepted",
                vec![(
                    "outputs",
                    record(
                        &format!("{family}::VerifierOutputs"),
                        vec![("受理", boolean())],
                        false,
                    ),
                )],
            ),
            ("Rejected", vec![]),
        ],
        false,
    );
    (public, witness, proof, produced, verified)
}
fn proof_document(producing: bool) -> Json {
    let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
    let (public, witness, proof, produced, verified) = proof_schemas();
    let (private, result, name, operation) = if producing {
        (witness, produced, "witness", "prove")
    } else {
        (proof, verified, "proof", "verify")
    };
    let mut d = document(
        vec![("public", public.clone()), (name, private.clone())],
        result.clone(),
        json!([{"op":"invoke","deployment":"proof","operands":[0,1],"results":[definition(2,result.clone())]}]),
        json!([2]),
    );
    d["deployments"] = json!([{"id":"proof","operation":operation,"parameters":[public,private],"results":[result],"package":child_package(&interface,&artifact)}]);
    d
}
fn proof_entry(producing: bool) -> FunctionEntry {
    let options = FunctionOptions {
        binding: crate::entry::BindingPolicy::AllowAuthored,
        ..FunctionOptions::default()
    };
    FunctionEntry::admit(
        capture(&proof_document(producing)),
        options.clone(),
        BTreeMap::from([("proof".into(), SetupAuthority::default())]),
    )
    .unwrap()
}
fn proof_request(producing: bool, public: bool, proof: Vec<u8>) -> FunctionRequest {
    let (name, private) = if producing {
        ("witness", row(vec![("秘密", false.into())]))
    } else {
        (
            "proof",
            row(vec![("bytes", zkc_cpu::Value::Bytes(proof.into()).into())]),
        )
    };
    let mut request = request(vec![
        ("public", row(vec![("公開", public.into())])),
        (name, private),
    ]);
    request.context.deployments.insert(
        "proof".into(),
        InvocationBinding::Proof(ProofContext::default()),
    );
    request
}
fn produced_bytes() -> Vec<u8> {
    let report = proof_entry(true)
        .prepare(proof_request(true, true, vec![]))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let Value::Record(mut result) = report.value.unwrap().into_value() else {
        panic!("result")
    };
    let Value::Record(mut proof) = result.remove("proof").unwrap() else {
        panic!("proof")
    };
    let Value::Leaf(crate::execution::InputValue::Native(v)) = proof.remove("bytes").unwrap()
    else {
        panic!("bytes")
    };
    let zkc_cpu::Value::Bytes(b) = *v else {
        panic!("bytes")
    };
    b.to_vec()
}
#[test]
fn proof_exact_bytes_round_trip_wrong_public_and_malformed_are_distinct() {
    let bytes = produced_bytes();
    assert_eq!(bytes.len(), 40);
    let entry = proof_entry(false);
    let accepted = entry
        .prepare(proof_request(false, true, bytes.clone()))
        .unwrap()
        .execute();
    assert!(accepted.is_success(), "{}", accepted.diagnostics());
    let Value::Variant {
        alternative,
        fields,
    } = accepted.value.unwrap().into_value()
    else {
        panic!("variant")
    };
    assert_eq!(alternative, "Accepted");
    assert!(fields.contains_key("outputs"));
    let wrong = entry
        .prepare(proof_request(false, false, bytes.clone()))
        .unwrap()
        .execute();
    assert!(wrong.value.is_none());
    assert!(wrong.failure.is_some());
    assert_eq!(wrong.calls[0].native["verification_decision"], Json::Null);
    let mut malformed = bytes;
    malformed.pop();
    let malformed = entry
        .prepare(proof_request(false, true, malformed))
        .unwrap()
        .execute();
    assert!(malformed.value.is_none());
    assert!(malformed.failure.is_some());
}
#[test]
fn disabled_journal_keeps_reserved_final_failure_without_source_output() {
    let options = FunctionOptions {
        journal_events: 0,
        binding: crate::entry::BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    let entry = FunctionEntry::admit(
        capture(&proof_document(false)),
        options.clone(),
        BTreeMap::from([("proof".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let report = entry
        .prepare(proof_request(false, true, vec![]))
        .unwrap()
        .execute();
    assert!(report.value.is_none());
    assert!(report.calls.is_empty());
    assert!(report.journal_truncated);
    let native = report.failure.as_ref().unwrap().native.as_ref().unwrap();
    assert_eq!(native["verification_decision"], Json::Null);
    assert!(native["cleanup_errors"].is_array());
    assert!(report.usage.execution.live_reserved_bytes >= crate::host::diagnostics::SCRATCH_BYTES);
}
#[test]
fn verification_rejection_has_no_outputs_and_cleanup_remains_separate() {
    // The same public statement is false in both invocations: framing matches,
    // then the admitted validator returns an ordinary false decision.
    let producer = proof_entry(true);
    let produced = producer
        .prepare(proof_request(true, false, vec![]))
        .unwrap()
        .execute();
    assert!(produced.is_success(), "{}", produced.diagnostics());
    let Value::Record(mut result) = produced.value.unwrap().into_value() else {
        panic!("result")
    };
    let Value::Record(mut proof) = result.remove("proof").unwrap() else {
        panic!("proof")
    };
    let Value::Leaf(crate::execution::InputValue::Native(v)) = proof.remove("bytes").unwrap()
    else {
        panic!("bytes")
    };
    let zkc_cpu::Value::Bytes(bytes) = *v else {
        panic!("bytes")
    };
    let report = proof_entry(false)
        .prepare(proof_request(false, false, bytes.to_vec()))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let Value::Variant {
        alternative,
        fields,
    } = report.value.unwrap().into_value()
    else {
        panic!("variant")
    };
    assert_eq!(alternative, "Rejected");
    assert!(fields.is_empty());
    assert_eq!(
        report.calls[0].native["verification_decision"],
        json!("rejected")
    );
}

#[test]
fn identity_projection_preserves_nominal_data_and_drop_removes_dominance() {
    let d = document(
        vec![("flag", boolean())],
        boolean(),
        json!([{"op":"project","operands":[0],"path":[],"results":[definition(1,boolean())]}]),
        json!([1]),
    );
    let report = admit(&d)
        .unwrap()
        .prepare(request(vec![("flag", true.into())]))
        .unwrap()
        .execute();
    assert!(bool::try_from(report.value.unwrap().into_value()).unwrap());
    let mut invalid = d;
    invalid["functions"][0]["body"]["operations"]
        .as_array_mut()
        .unwrap()
        .insert(0, json!({"op":"drop","operands":[0],"results":[]}));
    refusal(&invalid, "entry-host-dominance");
}
#[test]
fn generated_nominal_families_and_stage_cannot_be_rebound() {
    let mut doc = joint_document();
    doc["deployments"][0]["operation"] = json!("prove");
    let e = FunctionEntry::admit(
        capture(&doc),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .err()
    .unwrap();
    assert_eq!(e.code(), "entry-job-kind");
    let mut doc = joint_document();
    doc["deployments"][0]["parameters"][0]["type"] = json!("different::Inputs");
    doc["functions"][0]["signature"]["parameters"][0]["schema"] =
        doc["deployments"][0]["parameters"][0].clone();
    doc["functions"][0]["body"]["arguments"][0]["schema"] =
        doc["deployments"][0]["parameters"][0].clone();
    let e = FunctionEntry::admit(
        capture(&doc),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .err()
    .unwrap();
    assert_eq!(e.code(), "entry-host-nominal");
}
#[test]
fn dormant_contexts_validate_membership_and_material_without_execution() {
    let entry = FunctionEntry::admit(
        capture(&joint_document()),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let mut bad = joint_request();
    let InvocationBinding::Run(context) = bad.context.deployments.get_mut("joint").unwrap() else {
        unreachable!()
    };
    context.roles.insert(
        "P".into(),
        crate::entry::RoleInputs {
            services: BTreeMap::from([("not-declared".into(), 0)]),
            ..Default::default()
        },
    );
    assert_eq!(
        entry.prepare(bad).err().unwrap().code(),
        "entry-service-names"
    );
    let mut bad = joint_request();
    let InvocationBinding::Run(context) = bad.context.deployments.get_mut("joint").unwrap() else {
        unreachable!()
    };
    context.setups.insert("not-declared".into(), vec![]);
    assert_eq!(
        entry.prepare(bad).err().unwrap().code(),
        "entry-setup-material"
    );
}
#[test]
fn native_output_retention_does_not_require_public_input_codec() {
    use zkc_runtime::vm::{ExecutionLedger, Value as RuntimeValue};
    let polynomial = schema("builtin", "Polynomial", json!(["polynomial:bls12-381.fr"]));
    let d = document(
        vec![("polynomial", polynomial.clone())],
        polynomial,
        json!([]),
        json!([0]),
    );
    let entry = admit(&d).unwrap();
    let schema = &entry.signature().result;
    let backing = [zkc_cpu::Scalar::from(2u64), zkc_cpu::Scalar::from(3u64)].into();
    let native = zkc_cpu::Value::Polynomial(backing);
    assert!(!zkc_cpu::has_native_wire(&native.physical_type()));
    let ledger = ExecutionLedger::new(Default::default(), Default::default());
    let typed = data::from_output(entry.host(), schema, native.into(), &ledger).unwrap();
    assert!(ledger.snapshot().live_reserved_bytes > 0);
    let Value::Leaf(crate::execution::InputValue::Native(v)) = typed.into_value() else {
        panic!("native polynomial")
    };
    assert!(matches!(*v, zkc_cpu::Value::Polynomial(_)));
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}
#[test]
fn numerical_polynomial_flows_directly_into_joint_child_without_wire_ingress() {
    use zkc_runtime::vm::{LogicalType, PhysicalType};
    let vector = schema("builtin", "Vector", json!(["vector:bls12-381.fr"]));
    let polynomial = schema("builtin", "Polynomial", json!(["polynomial:bls12-381.fr"]));
    let physical = |name| {
        PhysicalType::default_for(LogicalType::parse(name).unwrap())
            .unwrap()
            .spelling()
    };
    let program = json!([
        "zkc.program/0",
        [[
            "poly",
            "poly.from_coefficients",
            ["bls12-381.fr"],
            "arkworks/poly.from_coefficients",
            []
        ]],
        [[
            "function",
            "polynomial",
            [["coefficients", physical("vector:bls12-381.fr")]],
            [physical("polynomial:bls12-381.fr")],
            [
                ["op", "construct", "poly", [], ["coefficients"], ["out"]],
                ["return", ["out"]]
            ],
            ["construct", []]
        ]],
        [],
        []
    ]);
    let (mut interface, artifact) = crate::entry::interface::tests::unicode::run_fixture(
        &polynomial,
        &["P"],
        &["role00000000"],
    );
    interface["entry"] = json!("main::run");
    let role_input = record("main::Inputs::P", vec![("入力", polynomial.clone())], true);
    let input = record("main::Inputs", vec![("P", role_input.clone())], true);
    let output = record(
        "main::RunResult",
        vec![(
            "P",
            record(
                "main::RunResult::P",
                vec![("結果", polynomial.clone())],
                false,
            ),
        )],
        false,
    );
    let mut d = document(
        vec![("coefficients", vector.clone())],
        output.clone(),
        json!([
            {"op":"numeric","calculation":"polynomial","operands":[0],"results":[definition(1,polynomial.clone())]},
            {"op":"construct","alternative":"","operands":[1],"results":[definition(2,role_input)]},
            {"op":"construct","alternative":"","operands":[2],"results":[definition(3,input.clone())]},
            {"op":"invoke","deployment":"joint","operands":[3],"results":[definition(4,output.clone())]}
        ]),
        json!([4]),
    );
    d["calculations"] = json!([{"id":"polynomial","function":"polynomial","parameters":[vector],"results":[polynomial],"program":program.to_string()}]);
    d["deployments"] = json!([{"id":"joint","operation":"run","parameters":[input],"results":[output],"package":child_package(&interface,&artifact)}]);
    let entry = FunctionEntry::admit(
        capture(&d),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let coefficients: zkc_cpu::Buffer<_> =
        [zkc_cpu::Scalar::from(2u64), zkc_cpu::Scalar::from(3u64)].into();
    let mut request = request(vec![(
        "coefficients",
        zkc_cpu::Value::Vector(coefficients.clone()).into(),
    )]);
    request.context.deployments.insert(
        "joint".into(),
        InvocationBinding::Run(RunContext {
            session: Some("polynomial".into()),
            ..Default::default()
        }),
    );
    let report = entry.prepare(request).unwrap().execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let Value::Record(mut roles) = report.value.unwrap().into_value() else {
        panic!("roles")
    };
    let Value::Record(mut outputs) = roles.remove("P").unwrap() else {
        panic!("outputs")
    };
    let Value::Leaf(crate::execution::InputValue::Native(value)) = outputs.remove("結果").unwrap()
    else {
        panic!("polynomial")
    };
    let zkc_cpu::Value::Polynomial(output) = *value else {
        panic!("polynomial")
    };
    assert_eq!(output.as_ref(), coefficients.as_ref());
}
#[test]
fn producer_accepts_internal_polynomial_witness_without_relaxing_public_ingress() {
    use zkc_runtime::vm::{LogicalType, PhysicalType};
    let vector = schema("builtin", "Vector", json!(["vector:bls12-381.fr"]));
    let polynomial = schema("builtin", "Polynomial", json!(["polynomial:bls12-381.fr"]));
    let physical = |name| {
        PhysicalType::default_for(LogicalType::parse(name).unwrap())
            .unwrap()
            .spelling()
    };
    let (mut interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
    interface["protocols"][0]["inputs"][1]["schema"] = polynomial.clone();
    interface["protocols"][0]["outputs"][1]["schema"] = polynomial.clone();
    interface["protocols"][0]["inputs"][1]["type"] = polynomial["type"].clone();
    interface["protocols"][0]["outputs"][1]["type"] = polynomial["type"].clone();
    let mut artifact: Json = serde_json::from_str(&artifact).unwrap();
    let mut program: Json = serde_json::from_str(artifact[4].as_str().unwrap()).unwrap();
    program[3][1][4][1][1] = json!(physical("polynomial:bls12-381.fr"));
    program[3][1][5][0] = json!(physical("polynomial:bls12-381.fr"));
    artifact[4] = json!(program.to_string());
    artifact[5] = json!(digest(artifact[4].as_str().unwrap()));
    artifact[6][1][2][1][1] = json!("polynomial:bls12-381.fr");
    artifact[6][1][3][0][1] = json!("polynomial:bls12-381.fr");
    let options = crate::entry::ProofOptions {
        binding: crate::entry::BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    let refused = crate::entry::ProofEntry::admit_operation(
        package(&interface, &artifact.to_string()),
        options.clone(),
        SetupAuthority::default(),
        crate::entry::ProofOperation::Prove,
    )
    .err()
    .expect("public ingress remains closed");
    assert_eq!(refused.code(), "entry-input-codec");
    let (public, _, proof, _, _) = proof_schemas();
    let family = "数学::証明₂";
    let witness = record(
        &format!("{family}::Witness"),
        vec![("秘密", polynomial.clone())],
        true,
    );
    let result = record(
        &format!("{family}::ProveResult"),
        vec![
            ("proof", proof),
            (
                "outputs",
                record(
                    &format!("{family}::ProverOutputs"),
                    vec![("結果", polynomial.clone())],
                    false,
                ),
            ),
        ],
        false,
    );
    let calculation = json!([
        "zkc.program/0",
        [[
            "poly",
            "poly.from_coefficients",
            ["bls12-381.fr"],
            "arkworks/poly.from_coefficients",
            []
        ]],
        [[
            "function",
            "polynomial",
            [["coefficients", physical("vector:bls12-381.fr")]],
            [physical("polynomial:bls12-381.fr")],
            [
                ["op", "construct", "poly", [], ["coefficients"], ["out"]],
                ["return", ["out"]]
            ],
            ["construct", []]
        ]],
        [],
        []
    ]);
    let mut d = document(
        vec![("public", public.clone()), ("coefficients", vector.clone())],
        result.clone(),
        json!([
            {"op":"numeric","calculation":"polynomial","operands":[1],"results":[definition(2,polynomial.clone())]},
            {"op":"construct","alternative":"","operands":[2],"results":[definition(3,witness.clone())]},
            {"op":"invoke","deployment":"proof","operands":[0,3],"results":[definition(4,result.clone())]}
        ]),
        json!([4]),
    );
    d["calculations"] = json!([{"id":"polynomial","function":"polynomial","parameters":[vector],"results":[polynomial],"program":calculation.to_string()}]);
    d["deployments"] = json!([{"id":"proof","operation":"prove","parameters":[public,witness],"results":[result],"package":child_package(&interface,&artifact.to_string())}]);
    let entry = FunctionEntry::admit(
        capture(&d),
        FunctionOptions {
            binding: crate::entry::BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        BTreeMap::from([("proof".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let coefficients: zkc_cpu::Buffer<_> =
        [zkc_cpu::Scalar::from(2u64), zkc_cpu::Scalar::from(3u64)].into();
    let mut request = request(vec![
        ("public", row(vec![("公開", true.into())])),
        (
            "coefficients",
            zkc_cpu::Value::Vector(coefficients.clone()).into(),
        ),
    ]);
    request.context.deployments.insert(
        "proof".into(),
        InvocationBinding::Proof(ProofContext::default()),
    );
    let report = entry.prepare(request).unwrap().execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let Value::Record(mut result) = report.value.unwrap().into_value() else {
        panic!("result")
    };
    let Value::Record(mut outputs) = result.remove("outputs").unwrap() else {
        panic!("outputs")
    };
    let Value::Leaf(crate::execution::InputValue::Native(value)) = outputs.remove("結果").unwrap()
    else {
        panic!("polynomial")
    };
    let zkc_cpu::Value::Polynomial(output) = *value else {
        panic!("polynomial")
    };
    assert_eq!(output.as_ref(), coefficients.as_ref());
}
fn single_operation_package(producing: bool) -> String {
    let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
    let mut artifact: Json = serde_json::from_str(&artifact).unwrap();
    let mut program: Json = serde_json::from_str(artifact[4].as_str().unwrap()).unwrap();
    let role = if producing {
        "role00000001"
    } else {
        "role00000000"
    };
    program[3].as_array_mut().unwrap().retain(|p| p[3] == role);
    program[4][0][2]
        .as_array_mut()
        .unwrap()
        .retain(|p| p[0] == role);
    artifact[6].as_array_mut().unwrap().retain(|m| m[0] == role);
    // Unrelated numerical definitions remain structurally admitted, without
    // inventing a producer participant or loading its private source map.
    if !producing {
        let c = calculation();
        let numerical: Json = serde_json::from_str(c["program"].as_str().unwrap()).unwrap();
        program[1] = numerical[1].clone();
        program[2] = numerical[2].clone();
    }
    artifact[4] = json!(program.to_string());
    artifact[5] = json!(digest(artifact[4].as_str().unwrap()));
    child_package(&interface, &artifact.to_string())
}
#[test]
fn single_endpoint_proof_children_preserve_independent_operation_closures() {
    let mut producer = proof_document(true);
    producer["deployments"][0]["package"] = json!(single_operation_package(true));
    let mut verifier = proof_document(false);
    verifier["deployments"][0]["package"] = json!(single_operation_package(false));
    let options = FunctionOptions {
        binding: crate::entry::BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    let authority = || BTreeMap::from([("proof".into(), SetupAuthority::default())]);
    let producer = FunctionEntry::admit(capture(&producer), options.clone(), authority()).unwrap();
    let verifier = FunctionEntry::admit(capture(&verifier), options.clone(), authority()).unwrap();
    let report = producer
        .prepare(proof_request(true, true, vec![]))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    let Value::Record(mut result) = report.value.unwrap().into_value() else {
        panic!("result")
    };
    let Value::Record(mut proof) = result.remove("proof").unwrap() else {
        panic!("proof")
    };
    let Value::Leaf(crate::execution::InputValue::Native(v)) = proof.remove("bytes").unwrap()
    else {
        panic!("bytes")
    };
    let zkc_cpu::Value::Bytes(bytes) = *v else {
        panic!("bytes")
    };
    let report = verifier
        .prepare(proof_request(false, true, bytes.to_vec()))
        .unwrap()
        .execute();
    assert!(report.is_success(), "{}", report.diagnostics());
}
fn service_document() -> Json {
    let mut d = joint_document();
    let package = d["deployments"][0]["package"].as_str().unwrap();
    let package: Json = serde_json::from_str(package).unwrap();
    let mut interface: Json = serde_json::from_str(package["interface"].as_str().unwrap()).unwrap();
    interface["protocols"][0]["services"] =
        json!([{"name":"randomness","contract":"random.bls12-381.fr/0","owner":"P","native":1}]);
    let mut artifact: Json = serde_json::from_str(package["artifact"].as_str().unwrap()).unwrap();
    let mut program: Json = serde_json::from_str(artifact["candidate"].as_str().unwrap()).unwrap();
    program[3][0][7] = json!([["randomness", "random.bls12-381.fr/0", "1"]]);
    artifact["candidate"] = json!(program.to_string());
    d["deployments"][0]["package"] = json!(child_package(&interface, &artifact.to_string()));
    let output = d["deployments"][0]["results"][0].clone();
    d["functions"][0]["body"]["operations"].as_array_mut().unwrap().push(json!({"op":"invoke","deployment":"joint","operands":[0],"results":[definition(2,output)]}));
    d["functions"][0]["body"]["returns"] = json!([2]);
    d
}
#[test]
fn service_allowances_are_cumulative_before_issuance_with_usable_default() {
    let d = service_document();
    let authority = || BTreeMap::from([("joint".into(), SetupAuthority::default())]);
    let entry = FunctionEntry::admit(capture(&d), Default::default(), authority()).unwrap();
    let report = entry.prepare(joint_request()).unwrap().execute();
    assert!(report.is_success(), "{}", report.diagnostics());
    assert_eq!(
        report.usage.service_allowances,
        2 * crate::entry::DEFAULT_DRAW_BUDGET
    );
    assert_eq!(report.usage.service_draws, 0);
    let options = FunctionOptions {
        service_draws: crate::entry::DEFAULT_DRAW_BUDGET,
        ..Default::default()
    };
    let entry = FunctionEntry::admit(capture(&d), options.clone(), authority()).unwrap();
    let report = entry.prepare(joint_request()).unwrap().execute();
    assert!(report.value.is_none());
    assert_eq!(report.failure.unwrap().code, "entry-host-service-limit");
    assert_eq!(report.calls.len(), 2);
    assert!(report.calls[0].completed);
    assert!(!report.calls[1].completed);
    assert_eq!(report.calls[1].native["phase"], "preparation");
}
#[test]
fn parent_live_reservations_limit_child_construction_before_effects() {
    let entry = FunctionEntry::admit(
        capture(&service_document()),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    let prepared = entry.prepare(joint_request()).unwrap();
    // Withhold almost all free live bytes after parent input/context admission.
    let remaining = entry.host.options.limits.capacity.values.live_bytes
        - prepared.ledger.snapshot().live_reserved_bytes;
    let parent = prepared.ledger.reserve_live(remaining - 1024).unwrap();
    let report = prepared.execute();
    assert!(report.failure.is_some());
    assert!(report.value.is_none());
    assert!(report.calls.is_empty());
    assert!(report.usage.execution.live_reserved_bytes >= parent.bytes());
    drop(parent);
}

#[test]
fn repeated_joint_calls_draw_fresh_sessions_unless_explicitly_selected() {
    let mut doc = joint_document();
    let body = &mut doc["functions"][0]["body"];
    let mut second = body["operations"][0].clone();
    second["results"][0]["id"] = json!(2);
    body["operations"].as_array_mut().unwrap().push(second);
    body["returns"] = json!([2]);
    let entry = FunctionEntry::admit(
        capture(&doc),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    for explicit in [false, true] {
        let mut request = joint_request();
        if !explicit {
            let InvocationBinding::Run(context) =
                request.context.deployments.get_mut("joint").unwrap()
            else {
                panic!()
            };
            context.session = None;
        }
        let report = entry.prepare(request).unwrap().execute();
        assert!(report.is_success(), "{}", report.diagnostics());
        assert_eq!(report.calls.len(), 2);
        let sessions: Vec<_> = report
            .calls
            .iter()
            .map(|c| c.native["session"].as_str().unwrap())
            .collect();
        if explicit {
            assert_eq!(sessions, ["fresh-session", "fresh-session"]);
        } else {
            assert_eq!(sessions[0].len(), 32);
            assert_eq!(sessions[1].len(), 32);
            assert_ne!(sessions[0], sessions[1]);
        }
    }
}

#[test]
fn child_specialization_is_bound_independently_of_parent_schemas() {
    fn specialize(value: &mut Json) {
        match value {
            Json::Object(o) => {
                if o.get("identity").is_some()
                    && o.get("type")
                        .and_then(Json::as_str)
                        .is_some_and(|s| s.starts_with("main::"))
                {
                    let name = format!("{}<1>", o["type"].as_str().unwrap());
                    o.insert("identity".into(), json!(digest(&name)));
                    o.insert("type".into(), json!(name));
                }
                for v in o.values_mut() {
                    specialize(v);
                }
            }
            Json::Array(a) => {
                for v in a {
                    specialize(v);
                }
            }
            _ => {}
        }
    }
    let mut doc = joint_document();
    specialize(&mut doc);
    let mut child: Json =
        serde_json::from_str(doc["deployments"][0]["package"].as_str().unwrap()).unwrap();
    let mut interface: Json = serde_json::from_str(child["interface"].as_str().unwrap()).unwrap();
    for (argument, valid) in [("1", true), ("2", false)] {
        interface["entry"] = json!(format!(
            "main::run_{}",
            digest(&format!("main<{argument}>"))
        ));
        child["interface"] = json!(interface.to_string());
        doc["deployments"][0]["package"] = json!(child.to_string());
        let admitted = FunctionEntry::admit(
            capture(&doc),
            Default::default(),
            BTreeMap::from([("joint".into(), SetupAuthority::default())]),
        );
        if valid {
            admitted.unwrap();
        } else {
            assert_eq!(admitted.err().unwrap().code(), "entry-host-nominal");
        }
    }
}

#[test]
fn packing_existing_native_results_does_not_authorize_external_fabrication() {
    let mut doc = joint_document();
    let result = doc["functions"][0]["signature"]["result"].clone();
    let wrapper = record("example::Wrapped", vec![("result", result)], true);
    doc["functions"][0]["signature"]["result"] = wrapper.clone();
    doc["functions"][0]["body"]["operations"].as_array_mut().unwrap().push(
        json!({"op":"construct","alternative":"","operands":[1],"results":[definition(2,wrapper.clone())]}));
    doc["functions"][0]["body"]["returns"] = json!([2]);
    let entry = FunctionEntry::admit(
        capture(&doc),
        Default::default(),
        BTreeMap::from([("joint".into(), SetupAuthority::default())]),
    )
    .unwrap();
    assert!(
        entry
            .prepare(joint_request())
            .unwrap()
            .execute()
            .is_success()
    );
    let schema = serde_json::from_value(wrapper).unwrap();
    assert_eq!(
        crate::entry::interface::schemas::check_import(&schema).unwrap_err(),
        "entry-input-constructor"
    );
}

fn pair_variant_document(leaf: Json, nested: bool) -> Json {
    let inner = variant("Inner", vec![("One", vec![("value", leaf.clone())])], true);
    let child = if nested { inner.clone() } else { leaf.clone() };
    let pair = variant(
        "Two",
        vec![
            ("Empty", vec![]),
            ("Pair", vec![("a", child.clone()), ("b", child)]),
        ],
        true,
    );
    let mut operations = Vec::new();
    let input = if nested {
        operations.push(json!({"op":"construct","alternative":"One","operands":[0],"results":[definition(1,inner)]}));
        1
    } else {
        0
    };
    operations.push(json!({"op":"construct","alternative":"Pair","operands":[input,input],"results":[definition(2,pair.clone())]}));
    document(vec![("x", leaf)], pair, json!(operations), json!([2]))
}
fn admit_with_capacity(doc: &Json, capacity: crate::execution::Capacity) -> FunctionEntry {
    let mut options = FunctionOptions::default();
    options.limits.capacity = capacity;
    FunctionEntry::admit(capture(doc), options.clone(), BTreeMap::new()).unwrap()
}
fn pair_value(value: &zkc_cpu::Value, nested: bool) -> Value {
    let child = || {
        if nested {
            Value::Variant {
                alternative: "One".into(),
                fields: BTreeMap::from([("value".into(), value.clone().into())]),
            }
        } else {
            value.clone().into()
        }
    };
    Value::Variant {
        alternative: "Pair".into(),
        fields: BTreeMap::from([("a".into(), child()), ("b".into(), child())]),
    }
}

#[test]
fn host_variant_pack_and_owned_outputs_enforce_complete_active_counts() {
    use crate::execution::Capacity;
    use zkc_runtime::vm::ExecutionLedger;
    let vector = schema("builtin", "Vector", json!(["vector:bls12-381.fr"]));
    let groups = schema("builtin", "Groups", json!(["groups:bls12-381.g1"]));
    for nested in [false, true] {
        for group in [false, true] {
            let leaf = if group {
                groups.clone()
            } else {
                vector.clone()
            };
            let native = if group {
                zkc_cpu::Value::Groups(vec![zkc_cpu::G1::generator(); 3].into())
            } else {
                zkc_cpu::Value::Vector(vec![zkc_cpu::Scalar::from(7); 3].into())
            };
            let doc = pair_variant_document(leaf, nested);
            for legal in [false, true] {
                let capacity = Capacity {
                    elements: if group {
                        32
                    } else if legal {
                        6
                    } else if nested {
                        5
                    } else {
                        4
                    },
                    groups: if legal { 6 } else { 4 },
                    ..Capacity::default()
                };
                let entry = admit_with_capacity(&doc, capacity);
                let prepared = entry
                    .prepare(request(vec![("x", native.clone().into())]))
                    .unwrap();
                let report = prepared.execute();
                assert_eq!(
                    report.is_success(),
                    legal,
                    "nested={nested}, group={group}: {}",
                    report.diagnostics()
                );
                if !legal {
                    assert!(report.value.is_none());
                    assert_eq!(report.failure.unwrap().code, "native-wire-limit");
                }
                let ledger = ExecutionLedger::new(capacity.values, capacity.work);
                let output = data::from_output(
                    entry.host(),
                    &entry.signature().result,
                    pair_value(&native, nested),
                    &ledger,
                );
                assert_eq!(
                    output.is_ok(),
                    legal,
                    "nested={nested}, group={group}: {output:?}"
                );
                if !legal {
                    assert_eq!(output.as_ref().unwrap_err(), "native-wire-limit");
                }
                drop(output);
                assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
            }
        }
    }
}

#[test]
fn owned_variants_accept_internal_polynomials_and_count_shared_occurrences() {
    use crate::execution::Capacity;
    use zkc_runtime::vm::ExecutionLedger;
    let polynomial = schema("builtin", "Polynomial", json!(["polynomial:bls12-381.fr"]));
    let doc = pair_variant_document(polynomial, true);
    let native = zkc_cpu::Value::Polynomial(vec![zkc_cpu::Scalar::from(7); 3].into());
    for elements in [5, 6] {
        let capacity = Capacity {
            elements,
            ..Capacity::default()
        };
        let entry = admit_with_capacity(&doc, capacity);
        let ledger = ExecutionLedger::new(capacity.values, capacity.work);
        let result = data::from_output(
            entry.host(),
            &entry.signature().result,
            pair_value(&native, true),
            &ledger,
        );
        assert_eq!(result.is_ok(), elements == 6, "{result:?}");
        if elements == 5 {
            assert_eq!(result.unwrap_err(), "native-wire-limit");
        }
        let backend =
            data::backend(capacity, entry.cpu().clone(), entry.installation().clone()).unwrap();
        assert!(
            backend.measure_native_input(&native).is_err(),
            "public codec stays closed"
        );
        let live = std::sync::Arc::new(ledger.reserve_live(8192).unwrap());
        let leaf = &entry.signature().parameters[0].schema;
        let mut leaves = [native.clone()].into_iter();
        let value = data::collect(entry.host(), leaf, &mut leaves, live).unwrap();
        let outer = &entry.signature().result;
        let inner = &outer.alternatives[1].fields[0].schema;
        let inner = data::pack(entry.host(), inner, "One", vec![value], &ledger).unwrap();
        let result = data::pack(
            entry.host(),
            outer,
            "Pair",
            vec![inner.clone(), inner],
            &ledger,
        );
        assert_eq!(result.is_ok(), elements == 6, "{result:?}");
    }
}

#[test]
fn host_variant_retention_preflight_checks_peak_before_assembly() {
    use crate::execution::Capacity;
    use zkc_runtime::vm::{ExecutionLedger, PhysicalType};
    let vector = schema("builtin", "Vector", json!(["vector:bls12-381.fr"]));
    let doc = pair_variant_document(vector, false);
    let entry = admit(&doc).unwrap();
    let native = zkc_cpu::Value::Vector(vec![zkc_cpu::Scalar::from(7); 3].into());
    let capacity = Capacity::default();
    let backend =
        data::backend(capacity, entry.cpu().clone(), entry.installation().clone()).unwrap();
    let sizes = [
        backend.measure_native_value(&native).unwrap(),
        backend.measure_native_value(&native).unwrap(),
    ];
    let ty =
        PhysicalType::default_for(entry.host.types[&entry.signature().result.leaves[0]].clone())
            .unwrap();
    let retained = backend
        .measure_native_variant(&ty, 1, &sizes)
        .unwrap()
        .retained_bytes();
    for sufficient in [false, true] {
        let capacity = Capacity {
            value_bytes: 2 * retained - usize::from(!sufficient),
            ..capacity
        };
        let entry = admit_with_capacity(&doc, capacity);
        let backend =
            data::backend(capacity, entry.cpu().clone(), entry.installation().clone()).unwrap();
        assert!(
            backend.measure_native_input(&native).is_ok(),
            "each child fits"
        );
        let report = entry
            .prepare(request(vec![("x", native.clone().into())]))
            .unwrap()
            .execute();
        assert_eq!(report.is_success(), sufficient, "{}", report.diagnostics());
        if !sufficient {
            assert_eq!(report.failure.unwrap().code, "native-wire-limit");
        }
        let ledger = ExecutionLedger::new(capacity.values, capacity.work);
        let output = data::from_output(
            entry.host(),
            &entry.signature().result,
            pair_value(&native, false),
            &ledger,
        );
        assert_eq!(output.is_ok(), sufficient, "{output:?}");
        drop(output);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }
    // The allocation ledger remains independently authoritative at the exact
    // per-value policy boundary; no native spine can be retained on refusal.
    let capacity = Capacity {
        values: zkc_runtime::vm::ValueBudget {
            live_bytes: 1,
            ..capacity.values
        },
        ..capacity
    };
    let ledger = ExecutionLedger::new(capacity.values, capacity.work);
    assert!(
        data::from_output(
            entry.host(),
            &entry.signature().result,
            pair_value(&native, false),
            &ledger
        )
        .is_err()
    );
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn standalone_outputs_keep_owner_policy_without_native_measurement() {
    use crate::execution::Capacity;
    use zkc_runtime::vm::{Backend, ExecutionLedger, Value as RuntimeValue, WorkBudget};
    let group = schema("group", "Group", json!(["group:bls12-381.g1"]));
    let native = zkc_cpu::Value::Curve(zkc_cpu::G1::generator());
    let capacity = Capacity {
        groups: 0,
        ..Capacity::default()
    };
    data::backend(
        capacity,
        CpuExecution::serial().unwrap(),
        Default::default(),
    )
    .unwrap()
    .validate_value(&native)
    .unwrap();
    let product = record(
        "Groups",
        vec![("a", group.clone()), ("b", group.clone())],
        true,
    );
    for (s, value) in [
        (group.clone(), native.clone().into()),
        (
            product,
            Value::Record(BTreeMap::from([
                ("a".into(), native.clone().into()),
                ("b".into(), native.clone().into()),
            ])),
        ),
        (index(), Value::from(zkc_cpu::Value::Index(7))),
    ] {
        let doc = document(vec![("x", s.clone())], s, json!([]), json!([0]));
        let entry = admit_with_capacity(&doc, capacity);
        let ledger = ExecutionLedger::new(
            capacity.values,
            WorkBudget {
                logical_bytes: 0,
                ..capacity.work
            },
        );
        let output = data::from_output(entry.host(), &entry.signature().result, value, &ledger)
            .expect("standalone leaves retain their owner's validation");
        assert_eq!(ledger.snapshot().logical_bytes, 0);
        drop(output);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }

    let doc = pair_variant_document(group, false);
    let entry = admit_with_capacity(&doc, capacity);
    let ledger = ExecutionLedger::new(capacity.values, capacity.work);
    let result = data::from_output(
        entry.host(),
        &entry.signature().result,
        pair_value(&native, false),
        &ledger,
    );
    assert_eq!(result.unwrap_err(), "native-wire-limit");
    assert_eq!(
        ledger.snapshot().logical_bytes,
        native.retained_bytes() as u64
    );
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    let value = data::from_output(
        entry.host(),
        &entry.signature().parameters[0].schema,
        native.clone().into(),
        &ledger,
    )
    .unwrap();
    let result = data::pack(
        entry.host(),
        &entry.signature().result,
        "Pair",
        vec![value.clone(), value],
        &ledger,
    );
    assert_eq!(result.unwrap_err(), "native-wire-limit");
    assert_eq!(
        ledger.snapshot().logical_bytes,
        2 * native.retained_bytes() as u64
    );
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn nested_variant_measurement_refuses_with_exhausted_shared_work() {
    use crate::execution::Capacity;
    use zkc_runtime::vm::{ExecutionLedger, Value as RuntimeValue, WorkBudget};
    let capacity = Capacity::default();
    let entry = admit_with_capacity(&pair_variant_document(index(), true), capacity);
    let scalar = zkc_cpu::Value::Index(7);
    let work = scalar.retained_bytes() as u64;
    let ledger = ExecutionLedger::new(
        capacity.values,
        WorkBudget {
            logical_bytes: work,
            ..capacity.work
        },
    );
    let value = data::from_output(
        entry.host(),
        &entry.signature().parameters[0].schema,
        scalar.into(),
        &ledger,
    )
    .unwrap();
    let result = &entry.signature().result;
    let inner = data::pack(
        entry.host(),
        &result.alternatives[1].fields[0].schema,
        "One",
        vec![value],
        &ledger,
    )
    .unwrap();
    let held = ledger.snapshot().live_reserved_bytes;
    // The inner native variant is immutable. Its expanded retained bound must
    // be available without traversing its active payload before admission.
    assert_eq!(ledger.snapshot().logical_bytes, work);
    assert_eq!(
        data::pack(
            entry.host(),
            result,
            "Pair",
            vec![inner.clone(), inner.clone()],
            &ledger,
        )
        .unwrap_err(),
        "Limit"
    );
    let usage = ledger.snapshot();
    assert_eq!(usage.logical_bytes, work);
    assert_eq!(usage.live_reserved_bytes, held);
    assert_eq!(usage.pending_logical_bytes, 0);
    assert_eq!(usage.pending_value_bytes, 0);
    drop(inner);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn repeated_native_measurements_share_logical_work_before_walking() {
    use crate::execution::Capacity;
    use zkc_runtime::vm::{ExecutionLedger, Value as RuntimeValue, WorkBudget};
    let capacity = Capacity::default();
    let policy = capacity.backend();
    let scalar = zkc_cpu::Value::Field(zkc_cpu::Scalar::from(7));
    let inner = zkc_cpu::Value::Sequence(
        zkc_cpu::Sequence::new(
            zkc_runtime::vm::PhysicalType::default_for(
                zkc_runtime::vm::LogicalType::sequence(scalar.physical_type().logical().clone())
                    .unwrap(),
            )
            .unwrap(),
            vec![scalar; 32],
            &policy,
        )
        .unwrap(),
    );
    let native = zkc_cpu::Value::Sequence(
        zkc_cpu::Sequence::new(
            zkc_runtime::vm::PhysicalType::default_for(
                zkc_runtime::vm::LogicalType::sequence(inner.physical_type().logical().clone())
                    .unwrap(),
            )
            .unwrap(),
            vec![inner; 32],
            &policy,
        )
        .unwrap(),
    );
    let leaf = schema(
        "builtin",
        "NestedSequence",
        json!([native.physical_type().logical().spelling()]),
    );
    let wrapper = variant(
        "Measured",
        vec![("One", vec![("value", leaf.clone())])],
        true,
    );
    let doc = document(
        vec![("x", leaf)],
        wrapper.clone(),
        json!([{"op":"construct","alternative":"One","operands":[0],"results":[definition(1,wrapper)]}]),
        json!([1]),
    );
    let entry = admit_with_capacity(&doc, capacity);
    let work = native.retained_bytes() as u64;
    let ledger = ExecutionLedger::new(
        capacity.values,
        WorkBudget {
            logical_bytes: 3 * work,
            ..capacity.work
        },
    );
    let value = data::from_output(
        entry.host(),
        &entry.signature().parameters[0].schema,
        native.clone().into(),
        &ledger,
    )
    .unwrap();
    let held = ledger.snapshot().live_reserved_bytes;
    let output = || Value::Variant {
        alternative: "One".into(),
        fields: BTreeMap::from([("value".into(), native.clone().into())]),
    };
    for iteration in 1..=3 {
        let result = if iteration == 2 {
            data::from_output(entry.host(), &entry.signature().result, output(), &ledger)
        } else {
            data::pack(
                entry.host(),
                &entry.signature().result,
                "One",
                vec![value.clone()],
                &ledger,
            )
        }
        .unwrap();
        assert_eq!(ledger.snapshot().logical_bytes, iteration * work);
        drop(result);
        assert_eq!(ledger.snapshot().live_reserved_bytes, held);
    }
    // This owner would reject the payload during its recursive count scan.
    // Exhausted shared work must refuse first, through either Host path.
    let strict = admit_with_capacity(
        &doc,
        Capacity {
            elements: 1,
            ..capacity
        },
    );
    assert_eq!(
        data::backend(
            strict.host().options.limits.capacity,
            strict.cpu().clone(),
            strict.installation().clone()
        )
        .unwrap()
        .measure_native_value(&native)
        .unwrap_err()
        .to_string(),
        "native-wire-limit"
    );
    for host in [entry.host(), strict.host()] {
        for owned in [false, true] {
            let result = if owned {
                data::from_output(host, &entry.signature().result, output(), &ledger)
            } else {
                data::pack(
                    host,
                    &entry.signature().result,
                    "One",
                    vec![value.clone()],
                    &ledger,
                )
            };
            assert_eq!(result.unwrap_err(), "Limit");
            let usage = ledger.snapshot();
            assert_eq!(usage.logical_bytes, 3 * work);
            assert_eq!(usage.live_reserved_bytes, held);
            assert_eq!(usage.pending_logical_bytes, 0);
            assert_eq!(usage.pending_value_bytes, 0);
        }
    }
    drop(value);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);

    // A partial active-arm walk keeps its committed work on later refusal.
    let pair = admit_with_capacity(
        &pair_variant_document(
            doc["functions"][0]["signature"]["parameters"][0]["schema"].clone(),
            false,
        ),
        capacity,
    );
    let ledger = ExecutionLedger::new(
        capacity.values,
        WorkBudget {
            logical_bytes: work,
            ..capacity.work
        },
    );
    let result = data::from_output(
        pair.host(),
        &pair.signature().result,
        pair_value(&native, false),
        &ledger,
    );
    assert_eq!(result.unwrap_err(), "Limit");
    assert_eq!(ledger.snapshot().logical_bytes, work);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);

    // Pack scratch must be reserved before measurement, even when all payload
    // storage is shared and the live allowance is held by the existing leaf.
    let leaf = &entry.signature().parameters[0].schema;
    let ledger = ExecutionLedger::new(
        zkc_runtime::vm::ValueBudget {
            live_bytes: data::metadata(leaf) + native.retained_bytes(),
            ..capacity.values
        },
        capacity.work,
    );
    let value = data::from_output(entry.host(), leaf, native.clone().into(), &ledger).unwrap();
    let held = ledger.snapshot().live_reserved_bytes;
    let result = data::pack(
        entry.host(),
        &entry.signature().result,
        "One",
        vec![value.clone()],
        &ledger,
    );
    assert_eq!(result.unwrap_err(), "Limit");
    assert_eq!(ledger.snapshot().logical_bytes, 0);
    assert_eq!(ledger.snapshot().live_reserved_bytes, held);
    drop(value);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);

    // Output planning scratch fits, but retaining the result cannot. Completed
    // measurement work stays charged and neither scratch nor output stays live.
    let ledger = ExecutionLedger::new(
        zkc_runtime::vm::ValueBudget {
            live_bytes: data::metadata(&entry.signature().result),
            ..capacity.values
        },
        capacity.work,
    );
    let result = data::from_output(entry.host(), &entry.signature().result, output(), &ledger);
    assert_eq!(result.unwrap_err(), "Limit");
    let usage = ledger.snapshot();
    assert_eq!(usage.logical_bytes, work);
    assert_eq!(usage.live_reserved_bytes, 0);
    assert_eq!(usage.pending_logical_bytes, 0);
    assert_eq!(usage.pending_value_bytes, 0);
}

fn plonky3_installation() -> zkc_cpu::CpuInstallation {
    zkc_cpu::CpuInstallation::builder()
        .include(zkc_cpu::providers::Plonky3)
        .finish()
        .unwrap()
}
#[test]
fn selected_installation_checks_typed_and_encoded_inputs_without_numerical_calls() {
    let leaf = schema(
        "field",
        "field<bls12-381.fr>",
        json!(["field:bls12-381.fr"]),
    );
    let doc = document(vec![("x", leaf.clone())], leaf, json!([]), json!([0]));
    let entry = FunctionEntry::admit(
        capture(&doc),
        FunctionOptions::default().with_installation(plonky3_installation()),
        BTreeMap::new(),
    )
    .unwrap();
    let native = zkc_cpu::Value::Field(zkc_cpu::Scalar::from(7));
    let prepared = crate::execution::PreparedData::from_value(
        native.clone(),
        crate::execution::Capacity::default(),
    )
    .unwrap();
    for argument in [
        native.into(),
        crate::execution::InputValue::Wire(prepared.canonical_bytes().to_vec().into()).into(),
        crate::execution::InputValue::Prepared(prepared).into(),
    ] {
        assert!(
            admit(&doc)
                .unwrap()
                .prepare(request(vec![("x", data::duplicate(&argument))]))
                .unwrap()
                .execute()
                .is_success()
        );
        let failure = entry.prepare(request(vec![("x", argument)])).err().unwrap();
        assert_eq!(failure.phase, EntryPhase::Preparation);
        assert_eq!(failure.code(), "native-input-type");
    }
    assert_eq!(
        entry.check_result_encoding().unwrap_err().code(),
        "entry-output-codec"
    );
    assert_eq!(
        entry
            .interface()
            .check_result_encoding(entry.installation())
            .unwrap_err()
            .code(),
        "entry-output-codec"
    );
}
#[test]
fn selected_installation_checks_calculations_and_nested_children_before_execution() {
    assert!(admit(&numeric_document()).is_ok());
    let failure = FunctionEntry::admit(
        capture(&numeric_document()),
        FunctionOptions::default().with_installation(plonky3_installation()),
        BTreeMap::new(),
    )
    .err()
    .unwrap();
    assert_eq!(failure.phase, EntryPhase::Admission);
    assert_eq!(failure.code(), "Backend: installation-binding");

    let leaf = schema(
        "field",
        "field<bls12-381.fr>",
        json!(["field:bls12-381.fr"]),
    );
    let doc = joint_document_with_schema(leaf);
    let authority = || BTreeMap::from([("joint".into(), SetupAuthority::default())]);
    assert!(FunctionEntry::admit(capture(&doc), Default::default(), authority()).is_ok());
    let failure = FunctionEntry::admit(
        capture(&doc),
        FunctionOptions::default().with_installation(plonky3_installation()),
        authority(),
    )
    .err()
    .unwrap();
    assert_eq!(failure.phase, EntryPhase::Admission);
    assert_eq!(
        failure.code(),
        "run-Candidate(\"Representation: installation-type\")"
    );

    // The permitted numerical child still executes under the same selection.
    let entry = FunctionEntry::admit(
        capture(&joint_document()),
        FunctionOptions::default().with_installation(plonky3_installation()),
        authority(),
    )
    .unwrap();
    assert!(
        entry
            .prepare(joint_request())
            .unwrap()
            .execute()
            .is_success()
    );
}
#[test]
fn selected_installation_rejects_inactive_variant_payload_and_private_typed_results() {
    let leaf = schema(
        "field",
        "field<bls12-381.fr>",
        json!(["field:bls12-381.fr"]),
    );
    let mixed = variant(
        "Mixed",
        vec![("Empty", vec![]), ("Hidden", vec![("value", leaf)])],
        true,
    );
    let doc = document(vec![("x", mixed.clone())], mixed, json!([]), json!([0]));
    let entry = FunctionEntry::admit(
        capture(&doc),
        FunctionOptions::default().with_installation(plonky3_installation()),
        BTreeMap::new(),
    )
    .unwrap();
    let failure = entry
        .prepare(request(vec![(
            "x",
            Value::Variant {
                alternative: "Empty".into(),
                fields: BTreeMap::new(),
            },
        )]))
        .err()
        .unwrap();
    assert_eq!(failure.code(), "native-input-type");

    let polynomial = schema("builtin", "Polynomial", json!(["polynomial:koala-bear"]));
    let doc = document(
        vec![("x", polynomial.clone())],
        polynomial,
        json!([]),
        json!([0]),
    );
    let entry = FunctionEntry::admit(
        capture(&doc),
        FunctionOptions::default().with_installation(plonky3_installation()),
        BTreeMap::new(),
    )
    .unwrap();
    let ledger = zkc_runtime::vm::ExecutionLedger::new(Default::default(), Default::default());
    let value = zkc_cpu::Value::KoalaBearPolynomial(vec![zkc_cpu::KoalaBear::new(7)].into());
    // Typed result retention adds no codec check.
    assert!(
        data::from_output(
            entry.host(),
            &entry.signature().result,
            value.into(),
            &ledger
        )
        .is_ok()
    );
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn selected_installation_reaches_nested_proof_program_decoding() {
    let mut doc = proof_document(true);
    let mut child: Json =
        serde_json::from_str(doc["deployments"][0]["package"].as_str().unwrap()).unwrap();
    let mut artifact: Json = serde_json::from_str(child["artifact"].as_str().unwrap()).unwrap();
    let mut program: Json = serde_json::from_str(artifact[4].as_str().unwrap()).unwrap();
    let numeric: Json = serde_json::from_str(calculation()["program"].as_str().unwrap()).unwrap();
    program[1] = numeric[1].clone();
    program[2] = numeric[2].clone();
    artifact[4] = json!(program.to_string());
    artifact[3] = json!(crate::io::bytes::hash(
        &zkc_format::logical::encode_tree(&artifact[2]).unwrap()
    ));
    artifact[5] = json!(digest(artifact[4].as_str().unwrap()));
    child["artifact"] = json!(artifact.to_string());
    doc["deployments"][0]["package"] = json!(child.to_string());
    let authority = || BTreeMap::from([("proof".into(), SetupAuthority::default())]);
    let options = || FunctionOptions {
        binding: crate::entry::BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    assert!(FunctionEntry::admit(capture(&doc), options(), authority()).is_ok());
    let failure = FunctionEntry::admit(
        capture(&doc),
        options().with_installation(plonky3_installation()),
        authority(),
    )
    .err()
    .unwrap();
    assert_eq!(failure.phase, EntryPhase::Admission);
    assert_eq!(failure.code(), "Backend: installation-binding");
}
