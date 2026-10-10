//! Independently authored native carriers exercise the entire Entry/Host bridge.
use super::*;
use crate::entry::{
    self, BindingPolicy, ProofEntry, ProofOptions, RunEntry, RunRequest, SetupAuthority,
};
use crate::run::HostLimits;
use crate::source_names::encode_nominal_identity;
use std::collections::BTreeMap;
use zkc_runtime::interactive::{LogicalType, PhysicalType};

fn package(document: &Value, artifact: &str) -> Package {
    let bytes =
        json!({"format":"zkc.entry/0", "original":"original", "interface":document.to_string(),
        "artifact":artifact,"options":{"simplify":true,"release_storage":false,"fuse_vector_reductions":false},"assets":[]})
        .to_string();
    Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}
fn physical(logical: &str) -> String {
    PhysicalType::default_for(LogicalType::parse(logical).unwrap())
        .unwrap()
        .spelling()
}
fn rename(value: &mut Value, from: &str, to: &str) {
    match value {
        Value::String(s) if s == from => *s = to.to_owned(),
        Value::Array(values) => values.iter_mut().for_each(|v| rename(v, from, to)),
        Value::Object(values) => values.values_mut().for_each(|v| rename(v, from, to)),
        _ => (),
    }
}
fn escape_json(text: &str) -> String {
    let mut encoded = String::new();
    for c in text.chars() {
        if c.is_ascii() {
            encoded.push(c);
        } else {
            for unit in c.encode_utf16(&mut [0; 2]) {
                encoded.push_str(&format!("\\u{unit:04x}"));
            }
        }
    }
    encoded
}
fn unicode_document() -> Value {
    let mut doc = document();
    doc["entry"] = json!("数学::𐐀::検証₂");
    for (from, to) in [
        ("P", "証明者"),
        ("V", "検証者"),
        ("accepted", "成功"),
        ("knowledge", "知識"),
        ("s", "σ"),
        ("w", "ω"),
    ] {
        rename(&mut doc, from, to);
    }
    doc["protocols"][0]["inputs"][0]["name"] = json!("α");
    doc["protocols"][0]["inputs"][1]["name"] = json!("a\u{316}\u{315}");
    doc
}
#[test]
fn unicode_interface_names_admit_equivalent_raw_and_escaped_json() {
    let doc = unicode_document();
    let raw = read(&doc).unwrap();
    let escaped = read_text(&escape_json(&doc.to_string())).unwrap();
    assert_eq!(raw.describe(), escaped.describe());
    assert_eq!(raw.entry(), "数学::𐐀::検証₂");
    assert_eq!(raw.roles()[0].name, "証明者");
    assert_eq!(raw.roles()[0].native_name, "role00000000");
    for (path, bad) in [
        ("/entry", "数学::e\u{301}"),
        ("/protocols/0/inputs/0/name", "a\u{315}\u{316}"),
        ("/protocols/0/roles/0", "証\u{200d}明者"),
    ] {
        let mut bad_doc = doc.clone();
        *bad_doc.pointer_mut(path).unwrap() = json!(bad);
        assert!(read(&bad_doc).is_err(), "{path}");
    }
    for invalid in ["\\ud800", "\\udfff", "\\ud800x", "\\ud800\\u0041"] {
        let bad = doc.to_string().replace("α", invalid);
        assert_eq!(read_text(&bad).unwrap_err(), InterfaceError::Format);
    }
    let mut bytes = doc.to_string().into_bytes();
    let index = bytes.windows(2).position(|s| s == "α".as_bytes()).unwrap();
    bytes[index] = 0xff;
    assert!(serde_json::from_slice::<raw::Interface>(&bytes).is_err());
    for size in [64, 65] {
        let mut bounded = doc.clone();
        bounded["protocols"][0]["inputs"][0]["name"] = json!("α".repeat(size));
        assert_eq!(read(&bounded).is_ok(), size == 64, "UTF8 byte ceiling");
    }
}
fn variant_schema(key: &str, names: [&str; 2], encoded: &str, labels: [&str; 2]) -> Value {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let spelling = zkc_test_support::variants::encode_tree(json!([
        ["zkc.language", encoded],
        [[labels[0], []], [labels[1], ["bool"]]]
    ]));
    let mut ty = schema("variant", key, json!([spelling]));
    ty["alternatives"] = json!([
        {"name":names[0],"fields":[]},
        {"name":names[1],"fields":[{"name":"値","offset":0,"schema":boolean}]}
    ]);
    ty
}
#[test]
fn nominal_enum_identity_hashes_decoded_original_utf8_and_rejects_tampering() {
    // ASCII alternatives in a Unicode-qualified type still need nominal encoding.
    let key = "数学::𐐀::Choice";
    let encoded = encode_nominal_identity(key);
    let make = |hex: &str, labels: [&str; 2]| {
        run_with(port(
            "選択",
            0,
            json!([0]),
            json!(["P"]),
            variant_schema(key, ["Empty", "Flag"], hex, labels),
        ))
    };
    let doc = make(&encoded, ["case00000000", "case00000001"]);
    read(&doc).unwrap();
    read_text(&escape_json(&doc.to_string())).unwrap();
    for bad in [
        "".into(),
        key.into(),
        encoded.to_uppercase(),
        encoded[..encoded.len() - 1].into(),
        format!("{encoded}ff"),
        "eda080".into(),
        encode_nominal_identity("数学::𐐀::Other"),
    ] {
        assert_eq!(
            read(&make(&bad, ["case00000000", "case00000001"])).unwrap_err(),
            InterfaceError::Schema,
            "{bad}"
        );
    }
    for labels in [
        ["Empty", "Flag"],
        ["case00000001", "case00000000"],
        ["case00000000", "case00000002"],
        ["case00000000", "case0000000A"],
    ] {
        assert_eq!(
            read(&make(&encoded, labels)).unwrap_err(),
            InterfaceError::Schema
        );
    }
    for name in ["Empty", "a\u{200d}", "e\u{301}"] {
        let mut bad = doc.clone();
        bad["protocols"][0]["inputs"][0]["schema"]["alternatives"][1]["name"] = json!(name);
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Schema);
    }
    let mut wrong_digest = doc;
    wrong_digest["protocols"][0]["inputs"][0]["schema"]["identity"] = json!(digest(&encoded));
    assert_eq!(read(&wrong_digest).unwrap_err(), InterfaceError::Schema);
}
fn run_fixture(ty: &Value, names: &[&str], native_names: &[&str]) -> (Value, String) {
    let logical = ty["leaves"][0].as_str().unwrap();
    let physical = physical(logical);
    let mut participants = Vec::new();
    let mut entries = Vec::new();
    let mut steps = Vec::new();
    for (index, role) in native_names.iter().enumerate() {
        let function = format!("participant{index}");
        participants.push(json!([
            "participant",
            function,
            "root",
            role,
            [["x", physical]],
            [physical],
            [["return", ["x"]]],
            []
        ]));
        entries.push(json!([role, function]));
        steps.push(json!({"role":index,"instruction":0,"anchor":null}));
    }
    let carrier = json!([
        "zkc.program/0",
        [],
        [],
        participants,
        [["entry", "main", entries]]
    ]);
    let artifact = json!({"format":"zkc.run/0","candidate":carrier.to_string(),"entry":"main","roles":native_names,"steps":steps}).to_string();
    let doc = json!({"format":"zkc.language-interface/0","setups":[],"capture":digest("capture"),"original":digest("original"),
        "toolchain":"test-toolchain","entry":"数学::実行₂","protocol":"main","relations":[],"job":{"kind":"run"},
        "protocols":[{"symbol":"main","roles":names,"inputs":[port("入力",0,json!([0]),json!(names),ty.clone())],
        "outputs":[port("結果",0,json!([0]),json!(names),ty.clone())],"services":[],"clauses":[]}]});
    (doc, artifact)
}
#[test]
fn unicode_roles_enum_payloads_and_output_keys_round_trip_through_native_host() {
    let ty = variant_schema(
        "数学::Choice",
        ["空", "有値"],
        &encode_nominal_identity("数学::Choice"),
        ["case00000000", "case00000001"],
    );
    // A source name that resembles another role's native label stays distinct.
    let (doc, artifact) = run_fixture(
        &ty,
        &["role00000001", "検証者"],
        &["role00000000", "role00000001"],
    );
    let entry = RunEntry::admit(
        package(&doc, &artifact),
        HostLimits::default(),
        SetupAuthority::default(),
    )
    .unwrap();
    let request = json!({"format":"zkc.entry-run/0","session":"unicode", "roles":{
        "role00000001":{"inputs":{"入力":{"case":"有値","fields":{"値":true}}}},
        "検証者":{"inputs":{"入力":{"case":"空","fields":{}}}}
    }});
    for text in [request.to_string(), escape_json(&request.to_string())] {
        let report = entry
            .prepare(entry.interface().run_request(text.as_bytes()).unwrap())
            .unwrap()
            .execute();
        assert!(report.is_success(), "{:?}", report.output_error);
        let outputs = report.outputs.unwrap();
        let entry::Value::Variant {
            alternative,
            fields,
        } = &outputs["role00000001"]["結果"]
        else {
            panic!("variant")
        };
        assert_eq!(alternative, "有値");
        assert!(fields.contains_key("値"));
        let bytes =
            entry::files::run_outputs(&outputs, Default::default(), Default::default()).unwrap();
        let output: Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(output["roles"]["role00000001"]["結果"]["case"], "有値");
        assert_eq!(output["roles"]["検証者"]["結果"]["case"], "空");
    }
    let duplicate = request
        .to_string()
        .replace("\"検証者\":", "\"検証者\":{\"inputs\":{}},\"\\u691c証者\":");
    assert!(entry.interface().run_request(duplicate.as_bytes()).is_err());
    let mut bad = request.clone();
    bad["roles"]["検証者"]["inputs"]["入力"]["case"] = json!("case00000000");
    assert!(
        entry
            .interface()
            .run_request(bad.to_string().as_bytes())
            .is_err()
    );
    let mut bad = request;
    bad["roles"]["role00000000"] = bad["roles"]["role00000001"].take();
    bad["roles"].as_object_mut().unwrap().remove("role00000001");
    assert!(
        entry
            .interface()
            .run_request(bad.to_string().as_bytes())
            .is_err()
    );
    for native in [
        ["role00000001", "role00000000"],
        ["P", "V"],
        ["role00000000", "role00000002"],
    ] {
        let (doc, artifact) = run_fixture(&ty, &["role00000001", "検証者"], &native);
        let error = RunEntry::admit(
            package(&doc, &artifact),
            HostLimits::default(),
            SetupAuthority::default(),
        )
        .err()
        .unwrap();
        assert_eq!(error.to_string(), "entry-interface-native-binding");
    }
}
#[test]
fn unicode_setup_authority_and_material_translate_together() {
    let mut doc = setup_document();
    rename(&mut doc, "pcs", "鍵₂");
    rename(&mut doc, "P", "証明者");
    rename(&mut doc, "V", "検証者");
    let interface = read(&doc).unwrap();
    let authority = SetupAuthority {
        keys: [("鍵₂".into(), [7; 32])].into(),
    };
    let native = entry::setups::run_authority(&interface, authority.clone()).unwrap();
    assert_eq!(native.keys, [("setup00000000".into(), [7; 32])].into());
    assert_eq!(native.inputs[&("role00000001".into(), 0)], "setup00000000");
    let material = [("鍵₂".into(), vec![1, 2, 3])].into();
    let native_material =
        entry::setups::run_material(&interface, material, Default::default()).unwrap();
    assert_eq!(
        native_material,
        [("setup00000000".into(), vec![1, 2, 3])].into()
    );
    let proof = entry::setups::proof_authority(&interface, authority).unwrap();
    assert_eq!(proof.keys, [(0, [7; 32])].into());
    assert_eq!(proof.inputs, [(1, 0), (2, 0)].into());
    let material = [("鍵₂".into(), vec![1, 2, 3])].into();
    assert_eq!(
        entry::setups::public_keys(&interface, &material, Default::default()).unwrap(),
        [(0, &[1, 2, 3][..])].into()
    );
    for key in ["setup00000000", "鍵₃", "鍵₂\u{200d}"] {
        let authority = SetupAuthority {
            keys: [(key.into(), [7; 32])].into(),
        };
        assert_eq!(
            entry::setups::run_authority(&interface, authority.clone()).unwrap_err(),
            "entry-setup-authority"
        );
        assert!(entry::setups::proof_authority(&interface, authority).is_err());
        let material = [(key.into(), vec![1])].into();
        assert_eq!(
            entry::setups::run_material(&interface, material, Default::default()).unwrap_err(),
            "entry-setup-material"
        );
    }
}

#[test]
fn unicode_setup_material_reaches_native_admission_and_results() {
    let logical = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut ty = schema("builtin", logical, json!([logical]));
    ty["permissions"] = json!(["Copy", "Drop"]);
    let (mut doc, artifact) = run_fixture(&ty, &["受信者"], &["role00000000"]);
    doc["setups"] = json!([{"name":"鍵₂","inputs":[{"port":0,"path":[]}]}]);
    let capacity = crate::execution::Capacity::default();
    let keys =
        zkc_arkworks::Keys::setup_for_development(1, &capacity.backend().ark_bounds()).unwrap();
    let key = keys.verifier_key();
    let bytes = key.to_bytes(&capacity.backend().ark_bounds()).unwrap();
    let authority = SetupAuthority {
        keys: [("鍵₂".into(), key.metadata().key_id())].into(),
    };
    let entry = RunEntry::admit(
        package(&doc, &artifact),
        HostLimits::default(),
        authority.clone(),
    )
    .unwrap();
    let material: BTreeMap<_, _> = [("鍵₂".into(), bytes.clone())].into();
    let request = RunRequest {
        session: "unicode".into(),
        roles: [("受信者".into(), entry::RoleInputs::default())].into(),
        setups: material.clone(),
    };
    let report = entry.prepare(request).unwrap().execute();
    assert!(report.is_success());
    let outputs = report.outputs.unwrap();
    entry::files::output_setups(&material, &authority, capacity).unwrap();
    let entry::Value::Leaf(crate::execution::InputValue::Native(returned)) =
        &outputs["受信者"]["結果"]
    else {
        panic!("native key");
    };
    let zkc_backends::Value::VerifierKey(returned) = returned.as_ref() else {
        panic!("verifier key");
    };
    assert_eq!(returned.metadata().key_id(), key.metadata().key_id());
    for name in ["setup00000000", "鍵₃"] {
        let request = RunRequest {
            session: "unicode".into(),
            roles: [("受信者".into(), entry::RoleInputs::default())].into(),
            setups: [(name.into(), bytes.clone())].into(),
        };
        assert_eq!(
            entry.prepare(request).err().unwrap().to_string(),
            "entry-setup-material"
        );
    }
    let request = RunRequest {
        session: "unicode".into(),
        roles: [("受信者".into(), entry::RoleInputs::default())].into(),
        setups: [("鍵₂".into(), vec![0])].into(),
    };
    assert!(entry.prepare(request).is_err());
    let authority = SetupAuthority {
        keys: [("鍵₂".into(), [0; 32])].into(),
    };
    let entry =
        RunEntry::admit(package(&doc, &artifact), HostLimits::default(), authority).unwrap();
    let request = RunRequest {
        session: "unicode".into(),
        roles: [("受信者".into(), entry::RoleInputs::default())].into(),
        setups: material,
    };
    assert!(entry.prepare(request).is_err());
}
#[test]
fn distinct_setup_slots_preserve_authority_and_reject_swapped_material() {
    let logical = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut ty = schema("builtin", logical, json!([logical]));
    ty["permissions"] = json!(["Copy", "Drop"]);
    let (mut doc, artifact) = run_fixture(&ty, &["受信者"], &["role00000000"]);
    for (direction, name) in [("inputs", "入力₂"), ("outputs", "結果₂")] {
        doc["protocols"][0][direction]
            .as_array_mut()
            .unwrap()
            .push(port(name, 1, json!([1]), json!(["受信者"]), ty.clone()));
    }
    doc["setups"] = json!([
        {"name":"setup00000001","inputs":[{"port":0,"path":[]}]},
        {"name":"鍵₂","inputs":[{"port":1,"path":[]}]}
    ]);
    let mut artifact: Value = serde_json::from_str(&artifact).unwrap();
    let mut candidate: Value =
        serde_json::from_str(artifact["candidate"].as_str().unwrap()).unwrap();
    candidate[3][0][4]
        .as_array_mut()
        .unwrap()
        .push(json!(["y", physical(logical)]));
    candidate[3][0][5]
        .as_array_mut()
        .unwrap()
        .push(json!(physical(logical)));
    candidate[3][0][6] = json!([["return", ["x", "y"]]]);
    artifact["candidate"] = json!(candidate.to_string());
    let capacity = crate::execution::Capacity::default();
    let bounds = capacity.backend().ark_bounds();
    let keys = [
        zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap(),
        zkc_arkworks::Keys::setup_for_development(2, &bounds).unwrap(),
    ];
    let identities = keys
        .each_ref()
        .map(|key| key.verifier_key().metadata().key_id());
    assert_ne!(identities[0], identities[1]);
    let bytes = keys
        .each_ref()
        .map(|key| key.verifier_key().to_bytes(&bounds).unwrap());
    let authority = SetupAuthority {
        keys: [
            ("setup00000001".into(), identities[0]),
            ("鍵₂".into(), identities[1]),
        ]
        .into(),
    };
    let interface = read(&doc).unwrap();
    let native = entry::setups::run_authority(&interface, authority.clone()).unwrap();
    assert_eq!(
        native.keys,
        [
            ("setup00000000".into(), identities[0]),
            ("setup00000001".into(), identities[1])
        ]
        .into()
    );
    let entry = RunEntry::admit(
        package(&doc, &artifact.to_string()),
        HostLimits::default(),
        authority,
    )
    .unwrap();
    let request = |swapped: bool| RunRequest {
        session: "distinct_setups".into(),
        roles: [("受信者".into(), entry::RoleInputs::default())].into(),
        setups: [
            ("setup00000001".into(), bytes[usize::from(swapped)].clone()),
            ("鍵₂".into(), bytes[usize::from(!swapped)].clone()),
        ]
        .into(),
    };
    let report = entry.prepare(request(false)).unwrap().execute();
    assert!(report.is_success());
    let outputs = report.outputs.unwrap();
    for (name, identity) in [("結果", identities[0]), ("結果₂", identities[1])] {
        let entry::Value::Leaf(crate::execution::InputValue::Native(value)) =
            &outputs["受信者"][name]
        else {
            panic!("native key");
        };
        let zkc_backends::Value::VerifierKey(key) = value.as_ref() else {
            panic!("verifier key");
        };
        assert_eq!(key.metadata().key_id(), identity);
    }
    assert!(
        entry.prepare(request(true)).is_err(),
        "swapped material bypassed setup authority"
    );
}

fn proof_fixture() -> (Value, String) {
    let boolean = physical("bool");
    let candidate = json!([
        "zkc.program/0",
        [],
        [],
        [
            [
                "participant",
                "v",
                "root",
                "role00000000",
                [["x", boolean]],
                [boolean],
                [["return", ["x"]]],
                []
            ],
            [
                "participant",
                "p",
                "root",
                "role00000001",
                [["x", boolean], ["w", boolean]],
                [boolean],
                [["return", ["w"]]],
                []
            ]
        ],
        [[
            "entry",
            "main",
            [["role00000000", "v"], ["role00000001", "p"]]
        ]]
    ])
    .to_string();
    let descriptor = json!([
        "zkc.native-proof-descriptor/0",
        [
            "zkc.native-proof-policy/0",
            "main",
            "role00000001",
            "role00000000",
            "0",
            "",
            "",
            ["0"],
            []
        ],
        "zkc.native-origin/0",
        [],
        [["role00000000", "0", "bool", "zkcv.bool/0"]],
        []
    ]);
    let artifact = json!([
        "zkc.native-proof/0",
        digest("original"),
        descriptor,
        crate::host::inputs::hash(&zkc_runtime::logical::encode_tree(&descriptor).unwrap()),
        candidate,
        digest(&candidate),
        [
            [
                "role00000000",
                "v",
                [["0", "bool"]],
                [["0", "bool"]],
                [],
                "0"
            ],
            [
                "role00000001",
                "p",
                [["0", "bool"], ["1", "bool"]],
                [["1", "bool"]],
                [],
                ""
            ]
        ],
        ["true", "false", "false"],
        []
    ])
    .to_string();
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let doc = json!({"format":"zkc.language-interface/0","setups":[],"capture":digest("capture"),"original":digest("original"),
        "toolchain":"test-toolchain","entry":"数学::証明₂","protocol":"main","relations":[],
        "protocols":[{"symbol":"main","roles":["検証者","証明者"],"services":[],"clauses":[],
            "inputs":[port("公開",0,json!([0]),json!(["検証者","証明者"]),boolean.clone()),port("秘密",1,json!([1]),json!(["証明者"]),boolean.clone())],
            "outputs":[port("受理",0,json!([0]),json!(["検証者"]),boolean.clone()),port("結果",1,json!([1]),json!(["証明者"]),boolean)]}],
        "job":{"kind":"proof","prover":"証明者","verifier":"検証者","public":[0],"acceptance":selector("output",0,"検証者"),"completion":null,"target":null,"construction":{"kind":"authored"}}});
    (doc, artifact)
}
#[test]
fn unicode_proof_requests_bind_the_selected_prover_and_verifier_roster_indices() {
    let (doc, artifact) = proof_fixture();
    let code = entry::bindings::rust(&package(&doc, &artifact)).unwrap();
    assert!(code.contains("PROVER: &::core::primitive::str = \"証明者\""));
    assert!(code.contains("VERIFIER: &::core::primitive::str = \"検証者\""));
    let options = ProofOptions {
        binding: BindingPolicy::AllowHeaderOnly,
        ..Default::default()
    };
    let prover =
        ProofEntry::admit(package(&doc, &artifact), options, SetupAuthority::default()).unwrap();
    let verifier =
        ProofEntry::admit(package(&doc, &artifact), options, SetupAuthority::default()).unwrap();
    let request =
        json!({"format":"zkc.entry-proof/0","public":{"公開":true},"inputs":{"秘密":false}})
            .to_string();
    let request = prover
        .interface()
        .proof_request(escape_json(&request).as_bytes(), true)
        .unwrap();
    let report = prover.prove(request).unwrap();
    assert!(report.is_success(), "{:?}", report.native.outcome);
    assert!(!bool::try_from(report.outputs.unwrap().remove("結果").unwrap()).unwrap());
    let proof = report.native.outcome.unwrap();
    let request = json!({"format":"zkc.entry-proof/0","public":{"公開":true}}).to_string();
    let report = verifier
        .verify(
            verifier
                .interface()
                .proof_request(request.as_bytes(), false)
                .unwrap(),
            &proof,
        )
        .unwrap();
    assert!(report.is_success(), "{:?}", report.native.outcome);
    assert!(bool::try_from(report.outputs.unwrap().remove("受理").unwrap()).unwrap());
    let private =
        json!({"format":"zkc.entry-proof/0","public":{"公開":true},"inputs":{"秘密":true}})
            .to_string();
    assert!(
        verifier
            .interface()
            .proof_request(private.as_bytes(), false)
            .is_err()
    );
    for swapped in [true, false] {
        let mut bad = doc.clone();
        if swapped {
            bad["protocols"][0]["roles"] = json!(["証明者", "検証者"]);
            bad["protocols"][0]["inputs"][0]["roles"] = json!(["証明者", "検証者"]);
        } else {
            rename(&mut bad, "証明者", "role00000000");
            rename(&mut bad, "検証者", "role00000001");
            // Source spellings that resemble labels are harmless: roster wins.
        }
        let result =
            ProofEntry::admit(package(&bad, &artifact), options, SetupAuthority::default());
        if swapped {
            assert_eq!(
                result.err().unwrap().to_string(),
                "entry-interface-native-binding"
            );
        } else {
            assert!(result.is_ok());
        }
    }
}

#[test]
fn unicode_setup_material_is_injected_into_both_independent_proof_requests() {
    let (mut doc, artifact) = proof_fixture();
    let vk = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut artifact: Value = serde_json::from_str(&artifact).unwrap();
    let mut candidate: Value = serde_json::from_str(artifact[4].as_str().unwrap()).unwrap();
    candidate[3][0][4]
        .as_array_mut()
        .unwrap()
        .push(json!(["key", physical(vk)]));
    let candidate = candidate.to_string();
    artifact[4] = json!(candidate);
    artifact[5] = json!(digest(&candidate));
    artifact[2][1][7] = json!(["0", "2"]);
    artifact[2][4].as_array_mut().unwrap().push(json!([
        "role00000000",
        "2",
        vk,
        "zkc.native-verifier-key/0"
    ]));
    artifact[3] = json!(crate::host::inputs::hash(
        &zkc_runtime::logical::encode_tree(&artifact[2]).unwrap()
    ));
    artifact[6][0][2]
        .as_array_mut()
        .unwrap()
        .push(json!(["2", vk]));
    let mut key_schema = schema("builtin", vk, json!([vk]));
    key_schema["permissions"] = json!(["Copy", "Drop"]);
    doc["protocols"][0]["inputs"]
        .as_array_mut()
        .unwrap()
        .push(port("検証鍵", 2, json!([2]), json!(["検証者"]), key_schema));
    doc["job"]["public"] = json!([0, 2]);
    doc["setups"] = json!([{"name":"鍵₂","inputs":[{"port":2,"path":[]}]}]);
    let options = ProofOptions {
        binding: BindingPolicy::AllowHeaderOnly,
        ..Default::default()
    };
    let keys =
        zkc_arkworks::Keys::setup_for_development(1, &options.capacity.backend().ark_bounds())
            .unwrap();
    let bytes = keys
        .verifier_key()
        .to_bytes(&options.capacity.backend().ark_bounds())
        .unwrap();
    let authority = SetupAuthority {
        keys: [("鍵₂".into(), keys.verifier_key().metadata().key_id())].into(),
    };
    let entry =
        ProofEntry::admit(package(&doc, &artifact.to_string()), options, authority).unwrap();
    let request = |producer: bool, key: &str, material: &[u8]| {
        let text = json!({"format":"zkc.entry-proof/0","public":{"公開":true},
            "inputs":if producer { json!({"秘密":false}) } else {json!({})},
            "setups":{key:crate::host::inputs::hex(material)}})
        .to_string();
        entry
            .interface()
            .proof_request(escape_json(&text).as_bytes(), producer)
            .unwrap()
    };
    let produced = entry.prove(request(true, "鍵₂", &bytes)).unwrap();
    assert!(produced.is_success(), "{:?}", produced.native.outcome);
    let proof = produced.native.outcome.unwrap();
    let checked = entry.verify(request(false, "鍵₂", &bytes), &proof).unwrap();
    assert!(checked.is_success(), "{:?}", checked.native.outcome);
    for producer in [true, false] {
        let bad = request(producer, "setup00000000", &bytes);
        let result = if producer {
            entry.prove(bad)
        } else {
            entry.verify(bad, &proof)
        };
        assert_eq!(result.err().unwrap().to_string(), "entry-setup-material");
        let bad = request(producer, "鍵₂", &[0]);
        assert!(
            if producer {
                entry.prove(bad)
            } else {
                entry.verify(bad, &proof)
            }
            .is_err()
        );
    }
}

#[test]
fn proof_package_binds_every_compilation_choice_to_the_deployment() {
    let (doc, artifact) = proof_fixture();
    let original = package(&doc, &artifact);
    for key in ["simplify", "release_storage", "fuse_vector_reductions"] {
        let mut frame: Value = serde_json::from_slice(original.bytes()).unwrap();
        frame["options"][key] = json!(!frame["options"][key].as_bool().unwrap());
        let raw = frame.to_string();
        let changed = Package::capture(
            raw.as_bytes(),
            &Sha256::digest(raw.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        let options = ProofOptions {
            binding: BindingPolicy::AllowHeaderOnly,
            ..Default::default()
        };
        let refused = ProofEntry::admit(changed, options, SetupAuthority::default());
        assert_eq!(
            refused.err().unwrap().to_string(),
            "entry-interface-native-binding",
            "{key}"
        );
    }
    let mut frame: Value = serde_json::from_slice(original.bytes()).unwrap();
    frame["options"]["fuse_vector_reductions"] = json!(true);
    let mut deployment: Value = serde_json::from_str(&artifact).unwrap();
    deployment[7][2] = json!("true");
    frame["artifact"] = json!(deployment.to_string());
    let raw = frame.to_string();
    let changed = Package::capture(
        raw.as_bytes(),
        &Sha256::digest(raw.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap();
    let options = ProofOptions {
        binding: BindingPolicy::AllowHeaderOnly,
        ..Default::default()
    };
    assert!(ProofEntry::admit(changed, options, SetupAuthority::default()).is_ok());
}
