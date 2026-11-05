use super::*;
use crate::entry::{BoundInterface, InterfaceLimits, Package};
use serde_json::json;
use std::collections::BTreeMap;

fn schema(kind: &str, name: &str, leaves: Value) -> Value {
    json!({"kind":kind,"identity":hash(name.as_bytes()),"type":name,
        "generated":null,"custody":0,"sealed":false,"roles":[],"element":null,
        "constructible":true,"permissions":["Copy","Drop"],"fields":[],
        "alternatives":[],"leaves":leaves})
}
fn field(name: &str, offset: u32, schema: Value) -> Value {
    json!({"name":name,"offset":offset,"public":true,"placement":null,"schema":schema})
}
fn product() -> Value {
    let mut pair = schema("tuple", "(bool,index)", json!(["bool", "index"]));
    pair["fields"] = json!([
        field("0", 0, schema("boolean", "bool", json!(["bool"]))),
        field("1", 1, schema("index", "index", json!(["index"])))
    ]);
    pair
}
fn port(name: &str, index: u32, native: &[u32], schema: Value) -> Value {
    fn components(schema: &Value, path: &mut Vec<u32>, next: &mut u32, out: &mut Vec<Value>) {
        let fields = schema["fields"].as_array().unwrap();
        if fields.is_empty() {
            for leaf in 0..schema["leaves"].as_array().unwrap().len() {
                out.push(json!({"path":path,"leaf":leaf,"role":1,"facet":"data","native":*next}));
                *next += 1;
            }
        } else {
            for (i, field) in fields.iter().enumerate() {
                path.push(i as u32);
                components(&field["schema"], path, next, out);
                path.pop();
            }
        }
    }
    let mut items = Vec::new();
    components(
        &schema,
        &mut Vec::new(),
        &mut native.first().copied().unwrap_or(0),
        &mut items,
    );
    json!({"name":name,"index":index,"native":native,"schema":schema,
        "type":schema["type"],"placement":{"kind":"data","roles":[1]},"components":items})
}
fn document(inputs: Vec<Value>, public: Value) -> Value {
    json!({"format":"zkc.language-interface/0","original":hash(b"original"),
        "capture":hash(b"capture"),"toolchain":hash(b"compiler"),
        "entry":"example::Proof","protocol":"main","setups":[],"relations":[],
        "protocols":[{"symbol":"main","roles":["P","V"],"inputs":inputs,
            "outputs":[port("accepted",0,&[0],schema("boolean","bool",json!(["bool"])))],
            "services":[],"clauses":[],"common_input_requirements":[]}],
        "job":{"kind":"proof","prover":"P","verifier":"V","public":public,
            "acceptance":{"direction":"output","port":0,"path":[],"role":"V"},
            "completion":null,"target":null,"gates":[],
            "construction":{"kind":"authored","format":"zkc.framed/0"}}})
}
fn selection(port: u32, path: &[u32]) -> Value {
    json!({"port":port,"path":path,"role":"V"})
}
fn interface(doc: &Value) -> BoundInterface {
    let bytes = json!({"format":"zkc.entry/0","original":"original",
        "interface":doc.to_string(),"artifact":"not admitted by the metadata reader",
        "options":Options::default().compile,"assets":[]})
    .to_string()
    .into_bytes();
    let package =
        Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap();
    BoundInterface::read(&package, InterfaceLimits::DEFAULT).unwrap()
}
fn source_record(doc: &Value, public: &[(u32, &str)]) -> Value {
    let mut record = crate::evm::tests::source_record("example::Proof", "fixture Yul");
    for key in ["original", "capture"] {
        record[key] = doc[key].clone();
    }
    record["compiler"] = doc["toolchain"].clone();
    record["policy"][1] = doc["protocol"].clone();
    record["policy"][2] = json!("role00000000");
    record["policy"][3] = json!("role00000001");
    record["policy"][5] = json!("");
    record["policy"][6] = json!([]);
    record["policy"][7] = json!(
        public
            .iter()
            .map(|(n, _)| n.to_string())
            .collect::<Vec<_>>()
    );
    record["policy"][8] = json!([]);
    record["descriptor"][1] = record["policy"].clone();
    record["descriptor"][3] = json!([]);
    record["descriptor"][4] = json!(
        public
            .iter()
            .map(|(n, ty)| {
                // Fixture codec annotations are compiler-owned; no SDK codec is run.
                json!(["role00000001", n.to_string(), ty, "zkc.native-data/0"])
            })
            .collect::<Vec<_>>()
    );
    record["descriptor"][5] = json!([]);
    record
}
fn artifact(record: &Value) -> Artifact {
    let source = Source::capture(&encode(record).unwrap()).unwrap();
    let files: BTreeMap<String, Vec<u8>> = BTreeMap::from([
        ("source.json".into(), source.bytes().to_vec()),
        ("verifier.yul".into(), source.yul().as_bytes().to_vec()),
        ("abi.json".into(), encode(source.abi()).unwrap()),
        (
            "solc-input.json".into(),
            encode(&solc::input(&source)).unwrap(),
        ),
        ("creation.bin".into(), vec![0]),
        ("runtime.bin".into(), vec![0]),
    ]);
    let compiler = hash(b"compiler executable");
    let solc = hash(b"solc executable");
    let manifest = Manifest {
        format: FORMAT.into(),
        build_key: solc::build_key(&source, &compiler, &solc).unwrap(),
        compiler_sha256: compiler,
        solc_sha256: solc,
        solc_version: SOLC_VERSION.into(),
        evm_version: source.fork(),
        files: files
            .iter()
            .map(|(name, bytes)| (name.clone(), hash(bytes)))
            .collect(),
    };
    Artifact::new(manifest, files).unwrap()
}
fn basic() -> (Value, Value) {
    let doc = document(
        vec![
            port("statement", 0, &[0, 1], product()),
            port("empty", 1, &[], schema("unit", "()", json!([]))),
        ],
        json!([selection(0, &[]), selection(1, &[])]),
    );
    let record = source_record(&doc, &[(0, "bool"), (1, "index")]);
    (doc, record)
}
fn refusal(result: Result<Vec<u8>>, code: &str) {
    assert_eq!(result.unwrap_err().0, code);
}

#[test]
fn products_and_empty_inputs_use_descriptor_order_and_existing_abi() {
    let (doc, record) = basic();
    let bound = interface(&doc);
    let artifact = artifact(&record);
    let wires: &[&[u8]] = &[b"first native frame", b"second native frame"];
    let named = artifact
        .calldata_named(
            &bound,
            &[("empty", &[]), ("statement", wires)],
            b"ctx",
            b"proof",
        )
        .unwrap();
    assert_eq!(
        named,
        artifact
            .calldata(Invocation {
                public_inputs: wires,
                context: b"ctx",
                proof: b"proof"
            })
            .unwrap()
    );
    // Independent ABI observation: no synthetic native frame for the empty input.
    let word = |at: usize| u64::from_be_bytes(named[at + 24..at + 32].try_into().unwrap());
    assert_eq!(word(100), 2);
    assert_eq!(word(132), 64);
    assert_eq!(word(164), 128);
    assert_eq!(&named[228..246], b"first native frame");
    assert_eq!(&named[292..311], b"second native frame");
}

#[test]
fn exact_names_duplicates_and_native_widths_are_required() {
    let (doc, record) = basic();
    let bound = interface(&doc);
    let artifact = artifact(&record);
    let pair: &[&[u8]] = &[b"a", b"b"];
    for entries in [
        vec![("statement", pair)],
        vec![("statement", pair), ("empty", &[][..]), ("extra", &[][..])],
        vec![("statement", pair), ("statement", &[][..])],
        vec![("statement", pair), ("Empty", &[][..])],
        vec![("statement", pair), ("0", &[][..])],
    ] {
        refusal(
            artifact.calldata_named(&bound, &entries, b"", b""),
            "evm-calldata-names",
        );
    }
    for entries in [
        vec![("statement", &pair[..1]), ("empty", &pair[1..])],
        vec![("statement", &pair[..1]), ("empty", &[][..])],
        vec![("statement", pair), ("empty", &pair[..1])],
    ] {
        refusal(
            artifact.calldata_named(&bound, &entries, b"", b""),
            "evm-calldata-width",
        );
    }
}

#[test]
fn selected_children_use_admitted_collision_resolved_aliases() {
    let mut doc = document(
        vec![
            port("item", 0, &[0, 1], product()),
            port(
                "item_0",
                1,
                &[2],
                schema("boolean", "bool", json!(["bool"])),
            ),
        ],
        json!([selection(0, &[0]), selection(0, &[1]), selection(1, &[])]),
    );
    let bound = interface(&doc);
    let names: Vec<_> = bound
        .ordinary_inputs("V")
        .unwrap()
        .into_iter()
        .map(|p| p.name().unwrap().to_owned())
        .collect();
    assert_eq!(names, ["item_0_2", "item_1", "item_0"]);
    let record = source_record(&doc, &[(0, "bool"), (1, "index"), (2, "bool")]);
    let artifact = artifact(&record);
    let ordered: &[&[u8]] = &[b"a", b"b", b"c"];
    let named = artifact
        .calldata_named(
            &bound,
            &[
                ("item_0", &ordered[2..]),
                ("item_1", &ordered[1..2]),
                ("item_0_2", &ordered[..1]),
            ],
            b"",
            b"",
        )
        .unwrap();
    assert_eq!(
        named,
        artifact
            .calldata(Invocation {
                public_inputs: ordered,
                context: b"",
                proof: b""
            })
            .unwrap()
    );
    refusal(
        artifact.calldata_named(
            &bound,
            &[
                ("item", &ordered[..1]),
                ("item_1", &ordered[1..2]),
                ("item_0", &ordered[2..]),
            ],
            b"",
            b"",
        ),
        "evm-calldata-names",
    );
    // The same source subject must also independently agree with the public map.
    doc["job"]["public"] = json!([selection(0, &[]), selection(1, &[])]);
    let whole = interface(&doc);
    assert!(
        artifact
            .calldata_named(
                &whole,
                &[("item", &ordered[..2]), ("item_0", &ordered[2..])],
                b"",
                b""
            )
            .is_ok()
    );
}

#[test]
fn logical_root_does_not_grant_unselected_private_authority() {
    let mut root = schema("logical_record", "State", json!([]));
    root["roles"] = json!(["P", "V"]);
    root["constructible"] = json!(false);
    root["fields"] = json!([
        field("statement", 0, product()),
        field("secret", 2, schema("boolean", "bool", json!(["bool"]))),
        field("empty", 3, schema("unit", "()", json!([])))
    ]);
    for (i, roles) in [(0, json!([1])), (1, json!([0])), (2, json!([1]))] {
        root["fields"][i]["placement"] = json!({"kind":"data","roles":roles});
    }
    let mut p = port("state", 0, &[0, 1, 2], root.clone());
    p["placement"] = json!({"kind":"product","instance":root["identity"],"arguments":[0,1],
        "fields":[{"kind":"data","roles":[1]},{"kind":"data","roles":[0]},{"kind":"data","roles":[1]}]});
    p["components"][2]["role"] = json!(0);
    let doc = document(vec![p], json!([selection(0, &[0]), selection(0, &[2])]));
    let bound = interface(&doc);
    let record = source_record(&doc, &[(0, "bool"), (1, "index")]);
    let artifact = artifact(&record);
    let pair: &[&[u8]] = &[b"a", b"b"];
    assert!(
        artifact
            .calldata_named(
                &bound,
                &[("state_statement", pair), ("state_empty", &[])],
                b"",
                b""
            )
            .is_ok()
    );
    refusal(
        artifact.calldata_named(&bound, &[("state", pair), ("state_empty", &[])], b"", b""),
        "evm-calldata-names",
    );
    refusal(
        artifact.calldata_named(
            &bound,
            &[("state_statement", pair), ("state_secret", &[])],
            b"",
            b"",
        ),
        "evm-calldata-names",
    );
}

#[test]
fn nested_selected_products_preserve_empty_paths_and_leaf_order() {
    let mut nested = schema("tuple", "(unit,(bool,index))", json!(["bool", "index"]));
    nested["fields"] = json!([
        field("0", 0, schema("unit", "()", json!([]))),
        field("1", 0, product())
    ]);
    for public in [
        json!([selection(0, &[0]), selection(0, &[1])]),
        json!([
            selection(0, &[0]),
            selection(0, &[1, 0]),
            selection(0, &[1, 1])
        ]),
    ] {
        let doc = document(vec![port("nested", 0, &[0, 1], nested.clone())], public);
        let bound = interface(&doc);
        let artifact = artifact(&source_record(&doc, &[(0, "bool"), (1, "index")]));
        let wires: &[&[u8]] = &[b"a", b"b"];
        let names = bound.ordinary_inputs("V").unwrap();
        let named: Vec<_> = names
            .iter()
            .rev()
            .map(|p| {
                let at = p.native().first().copied().unwrap_or(0) as usize;
                (p.name().unwrap(), &wires[at..at + p.native().len()])
            })
            .collect();
        assert_eq!(
            artifact.calldata_named(&bound, &named, b"", b"").unwrap(),
            artifact
                .calldata(Invocation {
                    public_inputs: wires,
                    context: b"",
                    proof: b""
                })
                .unwrap()
        );
        assert_eq!(names[0].name(), Some("nested_0"));
        assert!(names[0].native().is_empty());
        refusal(
            artifact.calldata_named(&bound, &named[..named.len() - 1], b"", b""),
            "evm-calldata-names",
        );
    }
}

#[test]
fn initialized_public_keys_retain_their_existing_alias() {
    // Transport coverage only: this fixture does not assert EVM target support
    // for KZG key realization or encode a key.
    let leaf = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut key = schema("builtin", leaf, json!([leaf]));
    key["constructible"] = json!(false);
    let mut doc = document(vec![port("vk", 0, &[0], key)], json!([selection(0, &[])]));
    doc["setups"] = json!([{"name":"pcs","inputs":[{"port":0,"path":[]}]}]);
    let bound = interface(&doc);
    assert!(bound.input_groups()[0].is_empty());
    let artifact = artifact(&source_record(&doc, &[(0, leaf)]));
    assert!(
        artifact
            .calldata_named(&bound, &[("vk", &[b"existing key frame"])], b"", b"")
            .is_ok()
    );
    refusal(
        artifact.calldata_named(&bound, &[], b"", b""),
        "evm-calldata-names",
    );
}

#[test]
fn source_subject_and_interface_identity_are_checked_independently() {
    let (doc, record) = basic();
    let bound = interface(&doc);
    for (key, wrong) in [
        ("original", json!(hash(b"wrong original"))),
        ("capture", json!(hash(b"wrong capture"))),
        ("compiler", json!(hash(b"wrong compiler"))),
        ("entry", json!("other::Proof")),
    ] {
        let mut wrong_record = record.clone();
        wrong_record[key] = wrong;
        refusal(
            artifact(&wrong_record).calldata_named(&bound, &[], b"", b""),
            "evm-calldata-subject",
        );
    }
}

#[test]
fn policy_and_descriptor_cannot_reassign_public_arguments() {
    let (doc, record) = basic();
    let bound = interface(&doc);
    let inputs: &[(&str, &[&[u8]])] = &[("statement", &[b"a", b"b"]), ("empty", &[])];
    for (slot, value) in [
        (1, json!("other")),
        (2, json!("other_prover")),
        (3, json!("other_verifier")),
        (4, json!("1")),
    ] {
        let mut changed = record.clone();
        changed["policy"][slot] = value;
        if slot == 3 {
            for row in changed["descriptor"][4].as_array_mut().unwrap() {
                row[0] = json!("other_verifier");
            }
        }
        changed["descriptor"][1] = changed["policy"].clone();
        refusal(
            artifact(&changed).calldata_named(&bound, inputs, b"", b""),
            "evm-calldata-policy",
        );
    }
    for (ports, rows) in [
        (
            json!(["0", "2"]),
            json!([
                ["role00000001", "0", "bool", "zkc.native-data/0"],
                ["role00000001", "2", "index", "zkc.native-data/0"]
            ]),
        ),
        (
            json!(["0", "1"]),
            json!([
                ["role00000001", "0", "index", "zkc.native-data/0"],
                ["role00000001", "1", "bool", "zkc.native-data/0"]
            ]),
        ),
    ] {
        let mut changed = record.clone();
        changed["policy"][7] = ports;
        changed["descriptor"][1] = changed["policy"].clone();
        changed["descriptor"][4] = rows;
        refusal(
            artifact(&changed).calldata_named(&bound, inputs, b"", b""),
            "evm-calldata-descriptor",
        );
    }
    for rows in [
        json!([
            ["role00000000", "0", "bool", "zkc.native-data/0"],
            ["role00000001", "1", "index", "zkc.native-data/0"]
        ]),
        json!([
            ["role00000001", "1", "index", "zkc.native-data/0"],
            ["role00000001", "0", "bool", "zkc.native-data/0"]
        ]),
    ] {
        let mut changed = record.clone();
        changed["descriptor"][4] = rows;
        assert_eq!(
            Source::capture(&encode(&changed).unwrap()).unwrap_err().0,
            "evm-source-identity"
        );
    }
}

#[test]
fn suite_service_gate_and_construction_associations_are_checked() {
    let (mut doc, mut record) = basic();
    let suite = "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0";
    let path = ["outer".to_owned(), "β".to_owned(), "challenge".to_owned()];
    let site = crate::source_names::native_site_path(&path);
    doc["protocols"][0]["services"] = json!([{
        "name":"coins", "contract":"random.koala-bear.ext4-binomial3/0", "owner":"V", "native":2
    }]);
    doc["job"]["construction"] =
        json!({"kind":"fiat_shamir", "format":"zkc.framed/0", "suite":suite, "services":[0]});
    doc["job"]["gates"] = json!([{"path":path,"bits":3}]);
    record["policy"][5] = json!(suite);
    record["policy"][6] = json!(["2"]);
    record["policy"][8] = json!([[site, "delivery"]]);
    record["policy"][11] = json!([[site, "3"]]);
    record["descriptor"][1] = record["policy"].clone();
    let bound = interface(&doc);
    let names: &[(&str, &[&[u8]])] = &[("statement", &[b"a", b"b"]), ("empty", &[])];
    assert!(
        artifact(&record)
            .calldata_named(&bound, names, b"", b"")
            .is_ok()
    );
    // Both a matching and a mismatched gate policy must reach caller bounds
    // before policy association allocates its service/path temporaries.
    let mut mismatched = record.clone();
    mismatched["policy"][11][0][1] = json!("4");
    mismatched["descriptor"][1] = mismatched["policy"].clone();
    for bounded in [&record, &mismatched] {
        let target = artifact(bounded);
        refusal(
            target.calldata_named(&bound, &[], b"", b""),
            "evm-calldata-names",
        );
        let large_name = "n".repeat(crate::entry::inputs::MAX_REQUEST_BYTES + 1);
        refusal(
            target.calldata_named(
                &bound,
                &[(large_name.as_str(), &[b"a", b"b"]), ("empty", &[])],
                b"",
                b"",
            ),
            "evm-calldata-limit",
        );
        let context = vec![0; bounded["limits"]["context_bytes"].as_u64().unwrap() as usize + 1];
        refusal(
            target.calldata_named(&bound, names, &context, b""),
            "evm-calldata-limit",
        );
        let proof = vec![0; bounded["limits"]["proof_bytes"].as_u64().unwrap() as usize + 1];
        refusal(
            target.calldata_named(&bound, names, b"", &proof),
            "evm-calldata-limit",
        );
        let mut lowered = bounded.clone();
        lowered["limits"]["calldata_bytes"] = json!(1024);
        let payload = vec![0; 1024];
        refusal(
            artifact(&lowered).calldata_named(
                &bound,
                &[("statement", &[payload.as_slice(), b"b"]), ("empty", &[])],
                b"",
                b"",
            ),
            "evm-calldata-limit",
        );
    }
    for (slot, value) in [
        (
            5,
            json!("hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0"),
        ),
        (6, json!(["3"])),
        (11, json!([[site, "4"]])),
    ] {
        let mut changed = record.clone();
        changed["policy"][slot] = value;
        changed["descriptor"][1] = changed["policy"].clone();
        refusal(
            artifact(&changed).calldata_named(&bound, names, b"", b""),
            "evm-calldata-policy",
        );
    }
    for wrong_site in [
        site.replacen("apply_", "apply_0", 1),
        "apply_1_x_label_00".into(),
        format!("{site}_"),
        crate::source_names::native_site_path(&["outer".into(), "challenge".into()]),
    ] {
        let mut changed = record.clone();
        changed["policy"][8][0][0] = json!(wrong_site);
        changed["policy"][11][0][0] = json!(wrong_site);
        changed["descriptor"][1] = changed["policy"].clone();
        refusal(
            artifact(&changed).calldata_named(&bound, names, b"", b""),
            "evm-calldata-policy",
        );
    }
    doc["job"]["construction"] = json!({"kind":"derived", "symbol":"selected_construction", "suite":suite,"format":"zkc.framed/0","services":[0]});
    doc["job"]["gates"] = json!([]);
    refusal(
        artifact(&record).calldata_named(&interface(&doc), names, b"", b""),
        "evm-calldata-policy",
    );
    let (mut run, _) = basic();
    run["job"] = json!({"kind":"run"});
    refusal(
        artifact(&record).calldata_named(&interface(&run), names, b"", b""),
        "evm-calldata-policy",
    );
}

#[test]
fn raw_and_named_abi_padding_share_the_same_exact_size_gate() {
    let (doc, record) = basic();
    let bound = interface(&doc);
    for length in [0usize, 1, 31, 32, 33, 63, 64, 65] {
        let bytes = vec![0xab; length];
        let wires: &[&[u8]] = &[&bytes, &bytes];
        let size = 196 + 128 + 4 * ((length + 31) & !31);
        let mut exact = record.clone();
        exact["limits"]["calldata_bytes"] = json!(size);
        let compiled = artifact(&exact);
        let named = [("empty", &[][..]), ("statement", wires)];
        let call = compiled
            .calldata_named(&bound, &named, &bytes, &bytes)
            .unwrap();
        assert_eq!(call.len(), size);
        assert_eq!(
            call,
            compiled
                .calldata(Invocation {
                    public_inputs: wires,
                    context: &bytes,
                    proof: &bytes
                })
                .unwrap()
        );
        exact["limits"]["calldata_bytes"] = json!(size - 1);
        let lowered = artifact(&exact);
        refusal(
            lowered.calldata_named(&bound, &named, &bytes, &bytes),
            "evm-calldata-limit",
        );
        refusal(
            lowered.calldata(Invocation {
                public_inputs: wires,
                context: &bytes,
                proof: &bytes,
            }),
            "evm-calldata-limit",
        );
    }
}

#[test]
fn empty_rosters_and_all_zero_width_rosters_remain_distinct() {
    for count in [0, 2] {
        let doc = document(
            (0..count)
                .map(|i| {
                    port(
                        if i == 0 { "first" } else { "second" },
                        i,
                        &[],
                        schema("unit", "()", json!([])),
                    )
                })
                .collect(),
            json!((0..count).map(|i| selection(i, &[])).collect::<Vec<_>>()),
        );
        let bound = interface(&doc);
        let artifact = artifact(&source_record(&doc, &[]));
        let names: &[(&str, &[&[u8]])] = if count == 0 {
            &[]
        } else {
            &[("second", &[]), ("first", &[])]
        };
        let bytes = artifact.calldata_named(&bound, names, b"", b"").unwrap();
        assert_eq!(bytes.len(), 196);
        if count != 0 {
            refusal(
                artifact.calldata_named(&bound, &[], b"", b""),
                "evm-calldata-names",
            );
        }
    }
}

#[test]
fn lowered_deployment_caps_are_applied_before_transport_allocation() {
    let (doc, record) = basic();
    let bound = interface(&doc);
    let pair: &[&[u8]] = &[b"a", b"b"];
    let names: &[(&str, &[&[u8]])] = &[("statement", pair), ("empty", &[])];
    for (key, cap, context, proof) in [
        ("public_bytes", 1, &b""[..], &b""[..]),
        ("context_bytes", 1, &b"cc"[..], &b""[..]),
        ("proof_bytes", 1, &b""[..], &b"pp"[..]),
        ("calldata_bytes", 387, &b""[..], &b""[..]),
    ] {
        let mut lowered = record.clone();
        lowered["limits"][key] = json!(cap);
        refusal(
            artifact(&lowered).calldata_named(&bound, names, context, proof),
            "evm-calldata-limit",
        );
    }
    let mut exact = record.clone();
    exact["limits"]["public_bytes"] = json!(2);
    exact["limits"]["calldata_bytes"] = json!(388);
    assert_eq!(
        artifact(&exact)
            .calldata_named(&bound, names, b"", b"")
            .unwrap()
            .len(),
        388
    );
    let too_long = "x".repeat(crate::entry::inputs::MAX_REQUEST_BYTES + 1);
    refusal(
        artifact(&record).calldata_named(
            &bound,
            &[(too_long.as_str(), pair), ("empty", &[])],
            b"",
            b"",
        ),
        "evm-calldata-limit",
    );
}
