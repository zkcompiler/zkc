use super::*;

// This is actual defaultFRI fullmodule output, retained verbatim as an external
// producer fixture. It includes every closed protocol, not just the proof root.
const FRI: &[u8] = include_bytes!("fixtures/fri-interface.json");

fn handle(row: &str, rows: Option<&str>, capacity: Option<&str>) -> Value {
    let data = if let Some(field) = row.strip_prefix("field:") {
        format!("vector:{field}")
    } else if let Some(group) = row.strip_prefix("group:") {
        format!("groups:{group}")
    } else if row == "index" {
        "indices".into()
    } else {
        format!("sequence<{row}>")
    };
    let data = if capacity.is_some() {
        format!("sequence<{data}>")
    } else {
        data
    };
    let ty = format!("Handle<{row},{rows:?},{capacity:?}>");
    let mut result = schema(
        if capacity.is_some() {
            "oracle_sequence"
        } else {
            "oracle"
        },
        &ty,
        json!([]),
    );
    result["constructible"] = json!(false);
    result["oracle"] = json!({"kind":"table","arguments":[["type",row]]});
    if let Some(rows) = rows {
        result["oracle"]["arguments"]
            .as_array_mut()
            .unwrap()
            .push(json!(["nat", rows]));
    }
    if let Some(capacity) = capacity {
        result["maximum"] = json!(capacity);
    }
    result["data_schema"] = schema("builtin", &data, json!([data]));
    result
}
fn logical_port(value: Value, maximum: Value) -> Value {
    let mut p = port("word", 0, json!([0, 1]), json!(["P", "V"]), value);
    p["holder"] = json!("P");
    p["maximum_rows"] = maximum;
    p
}
fn retained(p: Value) -> Value {
    let mut d = document();
    d["protocols"]
        .as_array_mut()
        .unwrap()
        .push(json!({"symbol":"internal","roles":["P","V"],
        "inputs":[p],"outputs":[],"services":[],"clauses":[]}));
    d
}
fn record() -> Value {
    let mut r = schema("logical_record", "State", json!([]));
    r["constructible"] = json!(false);
    r["fields"] = json!([
        {"name":"empty","offset":0,"schema":schema("unit","()",json!([]))},
        {"name":"word","offset":0,"maximum_rows":"0","schema":handle("field:koala-bear",None,None)},
        {"name":"count","offset":1,"schema":schema("index","index",json!(["index"]))},
        {"name":"layers","offset":2,"schema":handle("bool",Some("0"),Some("0"))},
        {"name":"tail","offset":3,"schema":schema("index","index",json!(["index"]))}
    ]);
    r
}
fn record_port() -> Value {
    let mut p = port(
        "state",
        0,
        json!([0, 1, 2, 3, 4, 5]),
        json!(["P", "V"]),
        record(),
    );
    p["holder"] = json!("P");
    p
}
fn replace(d: &Value, path: &str, value: Value) -> Value {
    let mut d = d.clone();
    *d.pointer_mut(path).unwrap() = value;
    d
}
fn refuses(d: &Value, cases: &[(&str, Value)]) {
    for (path, value) in cases {
        assert!(
            read(&replace(d, path, value.clone())).is_err(),
            "accepted {path} = {value}"
        );
    }
}

#[test]
fn actual_fri_retains_internal_state_metadata() {
    let view = Interface::decode(FRI, None).unwrap();
    assert_eq!(view.document.protocols.len(), 6);
    assert_eq!(view.document.relations.len(), 1);
    view.check_executable_ports().unwrap();
    let p = view
        .document
        .protocols
        .iter()
        .flat_map(|p| &p.inputs)
        .find(|p| p.schema.kind == raw::Kind::LogicalRecord)
        .unwrap();
    assert!(p.display_type.starts_with("fri::State<"));
    assert_eq!(p.holder.get().map(String::as_str), Some("P"));
    assert_eq!(p.native, (0..12).collect::<Vec<_>>());
    assert!(p.schema.leaves.is_empty());
    assert_eq!(
        p.schema
            .fields
            .iter()
            .map(|f| (f.name.as_str(), f.offset))
            .collect::<Vec<_>>(),
        [
            ("initial", 0),
            ("layers", 1),
            ("folds", 2),
            ("geometry", 3),
            ("coefficients", 5),
            ("positions", 6),
            ("round_count", 7),
            ("query_count", 8)
        ]
    );
    assert_eq!(
        p.schema.fields[0].maximum_rows.get(),
        Some(&raw::Unsigned(32))
    );
    assert_eq!(
        p.schema.fields[1].schema.maximum.get(),
        Some(&raw::Unsigned(3))
    );
    // Body offset 3 follows three handles and therefore starts at native slot 6.
    let (geometry, slots) = validate::project(p, &[3]).unwrap();
    assert_eq!(slots, [6, 7]);
    assert_eq!(
        geometry.leaves,
        ["field:koala-bear.ext8-binomial3", "index"]
    );
}

#[test]
fn direct_handles_and_sequences_preserve_unsigned_bounds_and_associations() {
    for row in [
        "field:koala-bear",
        "group:ristretto255.group",
        "index",
        "bool",
        "sequence<bool>",
        "field_array<koala-bear,4>",
    ] {
        for rows in [None, Some("0"), Some("18446744073709551615")] {
            for capacity in [None, Some("0"), Some("18446744073709551615")] {
                let maximum = if rows.is_none() {
                    json!("0")
                } else {
                    Value::Null
                };
                let d = retained(logical_port(handle(row, rows, capacity), maximum));
                let view = read(&d).unwrap();
                assert_eq!(view.document.protocols[1].inputs[0].native, [0, 1]);
                assert_eq!(
                    view.document.protocols[1].inputs[0]
                        .schema
                        .maximum
                        .get()
                        .map(|v| v.0),
                    capacity.map(|s| s.parse().unwrap())
                );
            }
        }
    }
    let d = retained(record_port());
    let view = read(&d).unwrap();
    let p = &view.document.protocols[1].inputs[0];
    assert!(validate::project(p, &[0]).unwrap().1.is_empty());
    assert_eq!(validate::project(p, &[2]).unwrap().1, [2]);
    assert_eq!(validate::project(p, &[4]).unwrap().1, [5]);
    assert!(validate::project(p, &[1]).is_err());
}

#[test]
fn exact_conditional_fields_and_objects_refuse_omission_null_and_extras() {
    let d = retained(logical_port(handle("bool", None, Some("0")), json!("0")));
    for path in [
        "/protocols/1/inputs/0/holder",
        "/protocols/1/inputs/0/maximum_rows",
        "/protocols/1/inputs/0/schema/oracle",
        "/protocols/1/inputs/0/schema/data_schema",
        "/protocols/1/inputs/0/schema/maximum",
    ] {
        let mut missing = d.clone();
        let (parent, key) = path.rsplit_once('/').unwrap();
        missing
            .pointer_mut(parent)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove(key);
        assert!(read(&missing).is_err(), "missing {path}");
        assert!(
            read(&replace(&d, path, Value::Null)).is_err(),
            "null {path}"
        );
    }
    for path in [
        "/protocols/1/inputs/0",
        "/protocols/1/inputs/0/schema",
        "/protocols/1/inputs/0/schema/oracle",
        "/protocols/1/inputs/0/schema/data_schema",
    ] {
        let mut unknown = d.clone();
        unknown.pointer_mut(path).unwrap()["extra"] = json!(null);
        assert_eq!(read(&unknown).unwrap_err(), InterfaceError::Format);
    }
    let mut ordinary = document();
    for key in ["holder", "maximum_rows"] {
        ordinary["protocols"][0]["inputs"][0][key] = json!(null);
        assert!(read(&ordinary).is_err());
        ordinary["protocols"][0]["inputs"][0]
            .as_object_mut()
            .unwrap()
            .remove(key);
    }
    for key in ["oracle", "data_schema", "maximum"] {
        ordinary["protocols"][0]["inputs"][0]["schema"][key] = json!(null);
        assert!(read(&ordinary).is_err());
        ordinary["protocols"][0]["inputs"][0]["schema"]
            .as_object_mut()
            .unwrap()
            .remove(key);
    }
    let mut record = retained(record_port());
    record["protocols"][1]["inputs"][0]["maximum_rows"] = json!(null);
    assert!(read(&record).is_err());
}

#[test]
fn oracle_kind_data_shape_and_family_are_checked() {
    let d = retained(logical_port(
        handle("field:koala-bear", None, Some("0")),
        json!("0"),
    ));
    refuses(
        &d,
        &[
            ("/protocols/1/inputs/0/holder", json!("unknown")),
            ("/protocols/1/inputs/0/roles", json!(["P"])),
            ("/protocols/1/inputs/0/roles", json!(["V", "P"])),
            ("/protocols/1/inputs/0/roles", json!(["P", "P"])),
            ("/protocols/1/inputs/0/roles", json!(["P", "X"])),
            ("/protocols/1/inputs/0/native", json!([0])),
            ("/protocols/1/inputs/0/native", json!([1, 0])),
            ("/protocols/1/inputs/0/schema/constructible", json!(true)),
            ("/protocols/1/inputs/0/schema/custody", json!(true)),
            ("/protocols/1/inputs/0/schema/leaves", json!(["bool"])),
            ("/protocols/1/inputs/0/schema/permissions", json!(["Drop"])),
            (
                "/protocols/1/inputs/0/schema/oracle/kind",
                json!("oracle.table"),
            ),
            ("/protocols/1/inputs/0/schema/oracle/arguments", json!([])),
            (
                "/protocols/1/inputs/0/schema/oracle/arguments",
                json!([["nat", "1"]]),
            ),
            (
                "/protocols/1/inputs/0/schema/oracle/arguments",
                json!([["type", "bool"], ["type", "bool"]]),
            ),
            (
                "/protocols/1/inputs/0/schema/oracle/arguments",
                json!([["type", "bool"], ["nat", "0"], ["nat", "0"]]),
            ),
            (
                "/protocols/1/inputs/0/schema/data_schema/leaves",
                json!(["sequence<vector:bls12-381.fr>"]),
            ),
            (
                "/protocols/1/inputs/0/schema/data_schema/kind",
                json!("record"),
            ),
            (
                "/protocols/1/inputs/0/schema/data_schema/permissions",
                json!(["Drop"]),
            ),
        ],
    );
    for row in [
        "field:unknown",
        "field:bn254.g1",
        "resource_unit:Slot",
        "rng:bls12-381.fr",
        "groups:bn254.gt",
        "groups:bls12-381.gt",
        "group:bn254.gt",
        "group:bls12-381.gt",
        "verifier_key:multilinear.kzg.bls12-381/0",
        "opening_state:multilinear.kzg.bls12-381/0",
        "bool@physical",
        "sequence< bool>",
        "fixed_vector<bool,1048577>",
    ] {
        let invalid = retained(logical_port(handle(row, None, Some("0")), json!("0")));
        assert!(read(&invalid).is_err(), "{row}");
    }
    for number in [
        json!(0),
        json!(""),
        json!("00"),
        json!("-1"),
        json!("+1"),
        json!("1e2"),
        json!("18446744073709551616"),
    ] {
        for path in [
            "/protocols/1/inputs/0/schema/maximum",
            "/protocols/1/inputs/0/maximum_rows",
        ] {
            assert!(
                read(&replace(&d, path, number.clone())).is_err(),
                "{path}: {number}"
            );
        }
    }
    let sized = retained(logical_port(handle("bool", Some("0"), None), json!(null)));
    assert!(
        read(&replace(
            &sized,
            "/protocols/1/inputs/0/maximum_rows",
            json!("0")
        ))
        .is_err()
    );
}

#[test]
fn logical_field_bounds_offsets_and_ordinary_products_are_exact() {
    let d = retained(record_port());
    refuses(
        &d,
        &[
            ("/protocols/1/inputs/0/schema/fields/2/offset", json!(2)),
            ("/protocols/1/inputs/0/schema/fields/4/offset", json!(5)),
            ("/protocols/1/inputs/0/schema/fields/3/name", json!("word")),
            ("/protocols/1/inputs/0/schema/fields/3/schema", record()),
            (
                "/protocols/1/inputs/0/schema/fields/2/schema",
                schema(
                    "builtin",
                    "key",
                    json!(["verifier_key:multilinear.kzg.bls12-381/0"]),
                ),
            ),
            (
                "/protocols/1/inputs/0/schema/fields/2/schema/permissions",
                json!(["Drop"]),
            ),
        ],
    );
    for (field, bound) in [
        (0, json!("0")),
        (1, json!(null)),
        (2, json!("0")),
        (3, json!("0")),
    ] {
        let mut bad = d.clone();
        bad["protocols"][1]["inputs"][0]["schema"]["fields"][field]["maximum_rows"] = bound;
        assert!(read(&bad).is_err());
    }
    let mut missing = d.clone();
    missing["protocols"][1]["inputs"][0]["schema"]["fields"][1]
        .as_object_mut()
        .unwrap()
        .remove("maximum_rows");
    assert!(read(&missing).is_err());
    let mut ordinary = schema("record", "Hidden", json!([]));
    ordinary["fields"] = json!([{"name":"word","offset":0,"schema":handle("bool",Some("0"),None)}]);
    assert!(
        read(&retained(port(
            "hidden",
            0,
            json!([]),
            json!(["P"]),
            ordinary
        )))
        .is_err()
    );
}

#[test]
fn reordered_objects_accept_but_duplicate_and_unknown_logical_fields_refuse() {
    let d = retained(record_port());
    fn reversed(v: &Value) -> String {
        match v {
            Value::Object(m) => format!(
                "{{{}}}",
                m.iter()
                    .rev()
                    .map(|(k, v)| format!("{}:{}", json!(k), reversed(v)))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Value::Array(a) => {
                format!("[{}]", a.iter().map(reversed).collect::<Vec<_>>().join(","))
            }
            _ => v.to_string(),
        }
    }
    read_text(&reversed(&d)).unwrap();
    let text = d.to_string();
    for (key, value) in [
        ("holder", json!("P")),
        ("maximum_rows", json!("0")),
        ("maximum", json!("0")),
        ("arguments", json!([["type", "bool"], ["nat", "0"]])),
        (
            "oracle",
            d["protocols"][1]["inputs"][0]["schema"]["fields"][1]["schema"]["oracle"].clone(),
        ),
    ] {
        let field = format!("\"{key}\":{value}");
        let duplicate = text.replacen(
            &field,
            &format!(
                "{field},\"\\u{:04x}{}\":{value}",
                key.as_bytes()[0],
                &key[1..]
            ),
            1,
        );
        assert_ne!(duplicate, text, "{key}");
        assert_eq!(
            read_text(&duplicate).unwrap_err(),
            InterfaceError::Format,
            "{key}"
        );
    }
}

#[test]
fn anchor_selectors_match_complete_data_and_derive_expanded_prefixes() {
    let mut d = retained(record_port());
    let data =
        d["protocols"][1]["inputs"][0]["schema"]["fields"][1]["schema"]["data_schema"].clone();
    d["relations"].as_array_mut().unwrap().push(json!({"symbol":"OraclePredicate","static_arguments":[],
        "inputs":[{"name":"data","purpose":"witness","native":[0],"schema":data}],"definition":{"kind":"opaque"}}));
    let operand = json!({"direction":"input","port":0,"role":null,"path":[1]});
    d["protocols"][1]["clauses"] = json!([{"name":"requires","kind":"input","subject":{"relation":"OraclePredicate","operands":[operand]},"residual":null,"decision":null}]);
    let view = read(&d).unwrap();
    let p = &view.document.protocols[1];
    let selected = validate::select(p, &p.clauses[0].subject.operands[0]).unwrap();
    assert_eq!(selected.0.leaves, ["vector:koala-bear"]);
    assert_eq!(selected.1, [1]);
    refuses(
        &d,
        &[
            ("/protocols/1/clauses/0/subject/operands/0/role", json!("P")),
            (
                "/protocols/1/clauses/0/subject/operands/0/role",
                json!("unknown"),
            ),
            ("/protocols/1/clauses/0/subject/operands/0/path", json!([])),
            ("/protocols/1/clauses/0/subject/operands/0/path", json!([3])),
            ("/protocols/1/clauses/0/subject/operands/0/path", json!([2])),
            (
                "/relations/1/inputs/0/schema/identity",
                json!(digest("other logical Data")),
            ),
        ],
    );
    // The ordinary metadata after a handle uses expanded offsets, even though
    // the relation formal is not an oracle Data association.
    let mut ordinary = d.clone();
    ordinary["protocols"][1]["clauses"][0]["subject"]["operands"][0] =
        json!({"direction":"input","port":0,"role":"V","path":[4]});
    ordinary["relations"][1]["inputs"][0]["schema"] = schema("index", "index", json!(["index"]));
    read(&ordinary).unwrap();
}

#[test]
fn repeated_logical_identity_includes_bounds_kind_capacity_and_data_schema() {
    let d = retained(record_port());
    let mut repeated = d.clone();
    repeated["protocols"][1]["outputs"] = json!([record_port()]);
    read(&repeated).unwrap();
    refuses(
        &repeated,
        &[
            (
                "/protocols/1/outputs/0/schema/fields/1/maximum_rows",
                json!("1"),
            ),
            (
                "/protocols/1/outputs/0/schema/fields/3/schema/maximum",
                json!("1"),
            ),
            (
                "/protocols/1/outputs/0/schema/fields/1/schema/data_schema/identity",
                json!(digest("another Data")),
            ),
            (
                "/protocols/1/outputs/0/schema/fields/3/schema/oracle/arguments/1/1",
                json!("1"),
            ),
        ],
    );
}

#[test]
fn logical_width_and_kind_nesting_limits_include_zero_capacity_handles() {
    for count in [512usize, 513] {
        let mut r = schema("logical_record", "WideState", json!([]));
        r["constructible"] = json!(false);
        r["fields"] = json!(
            (0..count)
                .map(|i| json!({"name":format!("word_{i}"),"offset":i,
            "schema":handle("bool",Some("0"),Some("0"))}))
                .collect::<Vec<_>>()
        );
        let mut p = port(
            "state",
            0,
            json!((0..2 * count).collect::<Vec<_>>()),
            json!(["P", "V"]),
            r,
        );
        p["holder"] = json!("P");
        let result = read(&retained(p));
        if count == 512 {
            result.unwrap();
        } else {
            assert_eq!(result.unwrap_err(), InterfaceError::Limit);
        }
    }
    // Both the row and the associated collection must fit the native grammar.
    let row = "sequence<".repeat(7) + "bool" + &">".repeat(7);
    read(&retained(logical_port(
        handle(&row, Some("0"), None),
        json!(null),
    )))
    .unwrap();
    assert!(
        read(&retained(logical_port(
            handle(&row, Some("0"), Some("0")),
            json!(null)
        )))
        .is_err()
    );
    let row = "sequence<".repeat(9) + "bool" + &">".repeat(9);
    assert!(
        read(&retained(logical_port(
            handle(&row, Some("0"), None),
            json!(null)
        )))
        .is_err()
    );
}

#[test]
fn maliciously_selected_logical_ports_remain_inspectable_and_refuse_execution() {
    for logical in [
        logical_port(handle("bool", None, None), json!("0")),
        logical_port(handle("bool", Some("0"), Some("0")), json!(null)),
        record_port(),
    ] {
        for output in [false, true] {
            let mut d = retained(logical.clone());
            d["protocol"] = json!("internal");
            d["job"] = json!({"kind":"run"});
            if output {
                d["protocols"][1]["outputs"] = json!([logical.clone()]);
                d["protocols"][1]["inputs"] = json!([]);
            }
            let view = read(&d).unwrap();
            assert_eq!(
                view.check_executable_ports().unwrap_err(),
                InterfaceError::NativeBinding
            );
            let p = &view.document.protocols[1];
            let schema = &if output { &p.outputs } else { &p.inputs }[0].schema;
            assert_eq!(
                schemas::check_import(schema).unwrap_err(),
                "entry-input-constructor"
            );
            assert_eq!(
                schemas::check_export(schema).unwrap_err(),
                "entry-output-custody"
            );
            #[cfg(feature = "cpu")]
            {
                assert_eq!(
                    crate::entry::arguments::check_ports(&view).unwrap_err(),
                    "entry-interface-native-binding"
                );
                assert_eq!(
                    crate::entry::arguments::check_host_ports(&view, None).unwrap_err(),
                    "entry-interface-native-binding"
                );
                let mut empty = std::iter::empty();
                assert_eq!(
                    crate::entry::value::collect(schema, &mut empty).unwrap_err(),
                    "entry-output-custody"
                );
            }
            view.describe();
        }
    }
}
