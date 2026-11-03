use super::*;

#[test]
fn generated_family_identity_is_required_nullable_and_nominal() {
    let mut generated = schema("record", "Generated", json!([]));
    generated["generated"] = json!(digest("family"));
    let original = run_with(port("generated", 0, json!([]), json!([0]), generated));
    assert!(read(&original).is_ok());
    let pointer = "/protocols/0/inputs/0/schema";
    let mut missing = original.clone();
    missing
        .pointer_mut(pointer)
        .unwrap()
        .as_object_mut()
        .unwrap()
        .remove("generated");
    assert!(read(&missing).is_err());
    for invalid in [json!(""), json!("A".repeat(64)), json!(false), json!(0)] {
        let mut bad = original.clone();
        bad.pointer_mut(pointer).unwrap()["generated"] = invalid;
        assert!(read(&bad).is_err());
    }
    let mut scalar = document();
    scalar["protocols"][0]["inputs"][0]["schema"]["generated"] = json!(digest("scalar"));
    assert_eq!(read(&scalar).unwrap_err(), InterfaceError::Schema);
    let mut changed = original.clone();
    changed["protocols"][0]["outputs"] = original["protocols"][0]["inputs"].clone();
    assert!(read(&changed).is_ok());
    changed["protocols"][0]["outputs"][0]["schema"]["generated"] =
        json!(digest("different family"));
    assert_eq!(read(&changed).unwrap_err(), InterfaceError::Schema);
}

#[test]
fn ordinary_structural_schemas_preserve_independent_product_placement() {
    let mut tuple = schema("tuple", "(index,bool)", json!(["index", "bool"]));
    tuple["fields"] = json!([
        field(
            "0",
            0,
            true,
            Value::Null,
            schema("index", "index", json!(["index"]))
        ),
        field(
            "1",
            1,
            true,
            Value::Null,
            schema("boolean", "bool", json!(["bool"]))
        )
    ]);
    let placement = product_placement(
        &tuple,
        json!([0, 1]),
        json!([
            {"kind":"data","roles":[0]}, {"kind":"data","roles":[1]}
        ]),
    );
    let mut document = run_with(placed_port(
        "pair",
        0,
        json!([0, 1]),
        placement,
        tuple.clone(),
    ));
    // The same static type can be locally placed without acquiring a different
    // schema or granting the distributed pair an aggregate owner.
    document["protocols"][0]["outputs"] =
        json!([port("local", 0, json!([0, 1]), json!([0]), tuple)]);
    let view = read(&document).unwrap();
    assert_eq!(view.ordinary_input(0, &[0], "P").unwrap().native(), [0]);
    assert_eq!(view.ordinary_input(0, &[1], "V").unwrap().native(), [1]);
    assert!(view.ordinary_input(0, &[1], "P").is_err());
    assert!(view.ordinary_input(0, &[], "P").is_err());
    view.check_executable_ports().unwrap();
    for roles in [json!([1, 0]), json!([0]), json!([0, 0])] {
        let mut bad = document.clone();
        bad["protocols"][0]["inputs"][0]["placement"]["arguments"] = roles;
        assert!(read(&bad).is_err());
    }
    let mut forged = document.clone();
    forged["protocols"][0]["inputs"][0]["components"][1]["role"] = json!(0);
    assert!(read(&forged).is_err());
}

#[test]
fn zero_ordinary_array_retains_its_product_element_placement() {
    let mut array = schema("array", "[index;0]", json!([]));
    array["element"] = schema("index", "index", json!(["index"]));
    let placement = product_placement(&array, json!([1]), json!([{"kind":"data","roles":[1]}]));
    let document = run_with(placed_port("empty", 0, json!([]), placement, array));
    read(&document).unwrap();
    for fields in [json!([]), json!([{"kind":"data","roles":[0]}])] {
        let mut bad = document.clone();
        bad["protocols"][0]["inputs"][0]["placement"]["fields"] = fields;
        assert!(read(&bad).is_err());
    }
}

fn field(name: &str, offset: u32, public: bool, placement: Value, schema: Value) -> Value {
    json!({"name":name,"offset":offset,"public":public,"placement":placement,"schema":schema})
}
fn product(name: &str, roles: Value, fields: Value, custody: u32) -> Value {
    let mut s = schema("logical_record", name, json!([]));
    s["constructible"] = json!(false);
    s["roles"] = roles;
    s["fields"] = fields;
    s["custody"] = json!(custody);
    if custody != 0 {
        s["permissions"] = json!([]);
    }
    s
}
fn product_placement(schema: &Value, arguments: Value, fields: Value) -> Value {
    json!({"kind":"product","instance":schema["identity"],"arguments":arguments,"fields":fields})
}
fn recursive_port() -> Value {
    let oracle = logical::handle("bool", Some("0"), None);
    let left = json!({"kind":"oracle","holder":0,"receivers":[2]});
    let right = json!({"kind":"oracle","holder":1,"receivers":[2]});
    let empty = schema("unit", "()", json!([]));
    let inner = product(
        "Inner<phantom>",
        json!(["A", "B", "V"]),
        json!([
            field("left", 0, true, left.clone(), oracle.clone()),
            field("right", 1, true, right.clone(), oracle),
            field("empty", 2, false, data_placement(json!([0])), empty)
        ]),
        0,
    );
    let inner_formula = product_placement(
        &inner,
        json!([1, 0, 2]),
        json!([
            {"kind":"oracle","holder":1,"receivers":[2]},
            {"kind":"oracle","holder":0,"receivers":[2]},
            {"kind":"data","roles":[1]}
        ]),
    );
    let outer = product(
        "Outer",
        json!(["X", "Y", "Z"]),
        json!([
            field("nested", 0, true, inner_formula.clone(), inner),
            field(
                "count",
                2,
                true,
                data_placement(json!([2])),
                schema("index", "index", json!(["index"]))
            )
        ]),
        0,
    );
    let placed = product_placement(
        &outer,
        json!([0, 1, 2]),
        json!([inner_formula,{"kind":"data","roles":[2]}]),
    );
    placed_port("state", 0, json!([0, 1, 2, 3, 4]), placed, outer)
}
fn recursive_document(port: Value) -> Value {
    let mut d = run_with(port);
    d["protocols"][0]["roles"] = json!(["A", "B", "V"]);
    d["protocols"][0]["outputs"] = json!([]);
    d
}
#[test]
fn nested_products_keep_ordered_role_maps_independent_holders_and_private_empty_fields() {
    let d = recursive_document(recursive_port());
    let view = read(&d).unwrap();
    let p = &view.selected_protocol().inputs[0];
    assert_eq!(
        p.components
            .iter()
            .map(|c| (c.path.clone(), c.role, c.native))
            .collect::<Vec<_>>(),
        [
            (vec![0, 0], 1, 0),
            (vec![0, 0], 2, 1),
            (vec![0, 1], 0, 2),
            (vec![0, 1], 2, 3),
            (vec![1], 2, 4)
        ]
    );
    let selected = view.ordinary_input(0, &[1], "V").unwrap();
    assert_eq!(selected.native(), [4]);
    assert_eq!(selected.path(), [1]);
    assert!(view.ordinary_input(0, &[1], "A").is_err());
    assert!(view.ordinary_input(0, &[0, 2], "B").is_err());
    assert!(view.ordinary_input(0, &[], "V").is_err());
    assert_eq!(
        view.check_executable_ports(),
        Err(InterfaceError::NativeBinding)
    );
    for (path, value) in [
        (
            "/protocols/0/inputs/0/placement/arguments",
            json!([0, 0, 2]),
        ),
        (
            "/protocols/0/inputs/0/placement/fields/0/arguments",
            json!([0, 1, 2]),
        ),
        (
            "/protocols/0/inputs/0/placement/fields/0/fields/0/holder",
            json!(0),
        ),
        (
            "/protocols/0/inputs/0/placement/instance",
            json!("12:internal-type-enum"),
        ),
        (
            "/protocols/0/inputs/0/placement/fields/0/fields/0/receivers",
            json!([2, 2]),
        ),
        (
            "/protocols/0/inputs/0/schema/fields/0/schema/fields/2/placement/roles",
            json!([3]),
        ),
    ] {
        let mut bad = d.clone();
        *bad.pointer_mut(path).unwrap() = value;
        assert!(read(&bad).is_err(), "{path}");
    }
}
#[test]
fn components_reject_omitted_repeated_reordered_wrong_facets_paths_roles_and_native_indices() {
    let d = recursive_document(recursive_port());
    read(&d).unwrap();
    for field in ["path", "leaf", "role", "facet", "native"] {
        let mut bad = d.clone();
        bad["protocols"][0]["inputs"][0]["components"][0][field] = match field {
            "path" => json!([0, 1]),
            "leaf" => json!(1),
            "role" => json!(0),
            "facet" => json!("data"),
            _ => json!(1),
        };
        assert!(read(&bad).is_err(), "{field}");
    }
    for mode in 0..3 {
        let mut bad = d.clone();
        let cs = bad["protocols"][0]["inputs"][0]["components"]
            .as_array_mut()
            .unwrap();
        match mode {
            0 => {
                cs.remove(0);
            }
            1 => {
                cs.push(cs[0].clone());
            }
            _ => cs.swap(0, 1),
        }
        assert!(read(&bad).is_err());
    }
}
fn zero_array(element: Value) -> Value {
    let mut s = schema("array", "[Inner;0]", json!([]));
    s["element"] = element;
    s["constructible"] = json!(false);
    s
}
#[test]
fn zero_arrays_keep_element_category_and_template_without_physical_components() {
    let element = recursive_port()["schema"].clone();
    let element_placement = recursive_port()["placement"].clone();
    let array = zero_array(element);
    let placed = product_placement(&array, json!([0, 1, 2]), json!([element_placement]));
    let d = recursive_document(placed_port("empty", 0, json!([]), placed, array));
    let view = read(&d).unwrap();
    assert!(view.selected_protocol().inputs[0].schema.is_logical());
    assert!(view.selected_protocol().inputs[0].components.is_empty());
    assert!(view.ordinary_input(0, &[], "A").is_err());
    for (path, value) in [
        ("/protocols/0/inputs/0/schema/element", Value::Null),
        ("/protocols/0/inputs/0/placement/fields", json!([])),
        (
            "/protocols/0/inputs/0/placement",
            data_placement(json!([0])),
        ),
        ("/protocols/0/inputs/0/schema/element/roles", json!([])),
    ] {
        let mut bad = d.clone();
        *bad.pointer_mut(path).unwrap() = value;
        assert!(read(&bad).is_err(), "{path}");
    }
}
#[test]
fn empty_distributed_custody_keeps_every_fragment_and_blocks_ingress() {
    let s = product("Guard", json!(["A", "B", "V"]), json!([]), 3);
    let p = product_placement(&s, json!([2, 0, 1]), json!([]));
    let d = recursive_document(placed_port("guard", 0, json!([0, 1, 2]), p, s));
    let view = read(&d).unwrap();
    let cs = &view.selected_protocol().inputs[0].components;
    assert_eq!(
        cs.iter()
            .map(|c| (c.leaf, c.role, c.native))
            .collect::<Vec<_>>(),
        [(0, 2, 0), (1, 0, 1), (2, 1, 2)]
    );
    assert!(cs.iter().all(|c| c.facet == raw::Facet::Custody));
    assert!(view.ordinary_input(0, &[], "V").is_err());
    for value in [
        json!(0),
        json!(1),
        json!(2),
        json!(4),
        json!(1025),
        json!(true),
    ] {
        let mut bad = d.clone();
        bad["protocols"][0]["inputs"][0]["schema"]["custody"] = value;
        assert!(read(&bad).is_err());
    }
}
#[test]
fn repeated_identity_includes_private_zero_fields_formulas_and_element_policy() {
    let mut d = recursive_document(recursive_port());
    d["protocols"][0]["outputs"] = json!([recursive_port()]);
    read(&d).unwrap();
    for (path, value) in [
        (
            "/protocols/0/outputs/0/schema/fields/0/schema/fields/2/public",
            json!(true),
        ),
        (
            "/protocols/0/outputs/0/schema/fields/0/schema/fields/2/placement/roles",
            json!([1]),
        ),
        (
            "/protocols/0/outputs/0/schema/fields/0/schema/type",
            json!("Other<phantom>"),
        ),
    ] {
        let mut bad = d.clone();
        *bad.pointer_mut(path).unwrap() = value;
        assert!(read(&bad).is_err(), "{path}");
    }
}
#[test]
fn required_nullable_unknown_duplicate_and_escaped_placement_keys_refuse() {
    let d = recursive_document(recursive_port());
    for path in [
        "/protocols/0/inputs/0/schema/element",
        "/protocols/0/inputs/0/schema/fields/0/placement",
        "/protocols/0/inputs/0/schema/fields/0/public",
        "/protocols/0/inputs/0/placement",
        "/protocols/0/inputs/0/components",
    ] {
        let mut bad = d.clone();
        let (parent, key) = path.rsplit_once('/').unwrap();
        bad.pointer_mut(parent)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove(key);
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Format, "{path}");
    }
    let text = d.to_string();
    for (key, value) in [
        ("arguments", json!([0, 1, 2])),
        ("holder", json!(1)),
        ("receivers", json!([2])),
        ("element", Value::Null),
        (
            "placement",
            d["protocols"][0]["inputs"][0]["placement"].clone(),
        ),
    ] {
        let field = format!("\"{key}\":{value}");
        let escaped = format!("\\u{:04x}{}", key.as_bytes()[0], &key[1..]);
        let bad = text.replacen(&field, &format!("{field},\"{escaped}\":{value}"), 1);
        assert_ne!(bad, text);
        assert_eq!(
            read_text(&bad).unwrap_err(),
            InterfaceError::Format,
            "{key}"
        );
    }
}

#[test]
fn structural_products_use_canonical_union_and_array_element_template_paths() {
    let p = recursive_port();
    let inner = p["schema"].clone();
    let placed = p["placement"].clone();
    let mut array = schema("array", "[Outer;2]", json!([]));
    array["constructible"] = json!(false);
    array["element"] = inner.clone();
    array["fields"] = json!([
        field("0", 0, true, Value::Null, inner.clone()),
        field("1", 3, true, Value::Null, inner)
    ]);
    let template = product_placement(&array, json!([0, 1, 2]), json!([placed]));
    let d = recursive_document(placed_port(
        "array",
        0,
        json!((0..10).collect::<Vec<_>>()),
        template,
        array,
    ));
    let view = read(&d).unwrap();
    assert_eq!(view.ordinary_input(0, &[1, 1], "V").unwrap().native(), [9]);
    for (path, value) in [
        (
            "/protocols/0/inputs/0/placement/arguments",
            json!([1, 0, 2]),
        ),
        ("/protocols/0/inputs/0/schema/fields/1/offset", json!(5)),
        (
            "/protocols/0/inputs/0/schema/fields/1/placement",
            data_placement(json!([0])),
        ),
        ("/protocols/0/inputs/0/schema/fields/1/public", json!(false)),
    ] {
        let mut bad = d.clone();
        *bad.pointer_mut(path).unwrap() = value;
        assert!(read(&bad).is_err(), "{path}");
    }
}

#[test]
fn ordinary_children_decode_without_supplying_other_logical_obligations() {
    let view = read(&recursive_document(recursive_port())).unwrap();
    let selected = view.ordinary_input(0, &[1], "V").unwrap();
    assert_eq!(selected.port(), 0);
    assert_eq!(selected.role(), "V");
    assert_eq!(selected.schema().kind, raw::Kind::Index);
    #[cfg(feature = "cpu")]
    {
        let group = selected.input_group("selected");
        let mut decoder = crate::entry::inputs::Decoder::new(Default::default()).unwrap();
        let values = decoder.decode(&group, br#"{"value":"7"}"#, None).unwrap();
        assert_eq!(values.len(), 1);
        assert!(
            decoder
                .decode(&group, br#"{"value":"7","anchor":"0"}"#, None)
                .is_err()
        );
        assert!(crate::entry::arguments::check_ports(&view).is_err());
    }
}

#[test]
fn native_binding_selects_each_ordinary_component_at_its_own_role() {
    let s = product(
        "OrdinaryOnly",
        json!(["A", "B", "V"]),
        json!([
            field(
                "flag",
                0,
                true,
                data_placement(json!([0])),
                schema("boolean", "bool", json!(["bool"]))
            ),
            field(
                "count",
                1,
                true,
                data_placement(json!([1, 2])),
                schema("index", "index", json!(["index"]))
            )
        ]),
        0,
    );
    let placed = product_placement(
        &s,
        json!([2, 0, 1]),
        json!([
            {"kind":"data","roles":[2]},{"kind":"data","roles":[0,1]}
        ]),
    );
    let view = read(&recursive_document(placed_port(
        "data",
        0,
        json!([0, 1]),
        placed,
        s,
    )))
    .unwrap();
    let p = &view.selected_protocol().inputs[0];
    #[cfg(feature = "cpu")]
    {
        assert_eq!(
            super::super::binding::leaves(std::iter::once(p), Some(0)).unwrap(),
            [(1, "index")]
        );
        assert_eq!(
            super::super::binding::leaves(std::iter::once(p), Some(1)).unwrap(),
            [(1, "index")]
        );
        assert_eq!(
            super::super::binding::leaves(std::iter::once(p), Some(2)).unwrap(),
            [(0, "bool")]
        );
    }
    assert_eq!(p.components.len(), 3);
}

#[test]
fn ordinary_custody_specification_observation_does_not_grant_ingress() {
    for permissions in [json!([]), json!(["Drop"])] {
        let mut s = schema(
            "record",
            "Guard<1>",
            json!([
                format!("resource_unit:zkl_resource_{}", digest("Guard<1>")),
                "bool"
            ]),
        );
        s["custody"] = json!(1);
        s["constructible"] = json!(false);
        s["permissions"] = permissions;
        s["fields"] = json!([field(
            "value",
            1,
            true,
            Value::Null,
            schema("boolean", "bool", json!(["bool"]))
        )]);
        let mut d = run_with(port("guard", 0, json!([0, 1]), json!([0]), s));
        d["relations"] = document()["relations"].clone();
        d["relations"][0]["inputs"].as_array_mut().unwrap().pop();
        d["protocols"][0]["clauses"] = document()["protocols"][0]["clauses"].clone();
        d["protocols"][0]["clauses"][0]["subject"]["operands"] =
            json!([{"direction":"input","port":0,"role":"P","path":[0]}]);
        let view = read(&d).unwrap();
        assert!(view.ordinary_input(0, &[0], "P").is_err());
        let mut bad = d.clone();
        bad["protocols"][0]["inputs"][0]["schema"]["custody"] = json!(0);
        assert!(read(&bad).is_err());
        let mut bad = d;
        bad["protocols"][0]["inputs"][0]["schema"]["leaves"] = json!(["bool"]);
        assert!(read(&bad).is_err());
    }
}

#[test]
fn whole_logical_public_selection_refuses_even_when_a_valid_child_is_ordinary() {
    let p = recursive_port();
    let mut s = p["schema"].clone();
    // A two-role ordinary-only logical product is inspectable, but whole input
    // ordinals cannot express its separate ordinary public-component roster.
    s["roles"] = json!(["A", "V"]);
    s["fields"] = json!([
        field(
            "flag",
            0,
            true,
            data_placement(json!([0])),
            schema("boolean", "bool", json!(["bool"]))
        ),
        field(
            "count",
            1,
            true,
            data_placement(json!([1])),
            schema("index", "index", json!(["index"]))
        )
    ]);
    let placed = product_placement(
        &s,
        json!([0, 1]),
        json!([{"kind":"data","roles":[0]},{"kind":"data","roles":[1]}]),
    );
    let mut d = document();
    d["relations"] = json!([]);
    d["protocols"][0]["clauses"] = json!([]);
    d["job"]["target"] = Value::Null;
    d["protocols"][0]["inputs"] = json!([placed_port("root", 0, json!([0, 1]), placed, s)]);
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
    d["job"]["public"] = json!([]);
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
}

#[test]
fn retained_recursive_fixture_matches_the_reviewed_schema_and_component_coordinates() {
    let fixture: Value =
        serde_json::from_slice(include_bytes!("fixtures/recursive-interface.json")).unwrap();
    assert_eq!(fixture, recursive_document(recursive_port()));
    Interface::decode(
        include_bytes!("fixtures/recursive-interface.json"),
        None,
        InterfaceLimits::DEFAULT,
    )
    .unwrap();
}

#[test]
fn nested_empty_ordinary_arrays_retain_participant_and_constructor_policy() {
    let spelling = "verifier_key:multilinear.kzg.bls12-381/0";
    let mut key = schema("builtin", spelling, json!([spelling]));
    key["constructible"] = json!(false);
    let mut array = schema("array", "[Key;0]", json!([]));
    array["element"] = key;
    let mut root = schema("record", "NestedEmpty", json!([]));
    root["fields"] = json!([field("empty", 0, true, Value::Null, array)]);
    let d = run_with(port("root", 0, json!([]), json!([0]), root.clone()));
    let view = read(&d).unwrap();
    assert!(view.ordinary_input(0, &[], "P").is_err());
    let d = run_with(port("root", 0, json!([]), json!([0, 1]), root));
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Schema);
}

#[test]
fn role_telescope_custody_and_metadata_work_limits_include_zero_storage() {
    // One custody leaf per telescope role: the telescope and the custody
    // prefix are both bounded at 1,024.
    for count in [16usize, 17, 1024, 1025] {
        let roles: Vec<_> = (0..count).map(|i| format!("Role{i}")).collect();
        let schema = product("EmptyRoles", json!(roles), json!([]), count as u32);
        let p = product_placement(
            &schema,
            json!((0..count).rev().collect::<Vec<_>>()),
            json!([]),
        );
        let mut d = run_with(placed_port(
            "empty",
            0,
            json!((0..count).collect::<Vec<_>>()),
            p,
            schema,
        ));
        d["protocols"][0]["roles"] = json!(roles[..count.min(1024)]);
        d["protocols"][0]["outputs"] = json!([]);
        if count <= 1024 {
            read(&d).unwrap();
        } else {
            assert_eq!(read(&d).unwrap_err(), InterfaceError::Limit);
        }
    }
    let mut d = recursive_document(recursive_port());
    d["protocols"][0]["inputs"][0]["components"] = json!(vec![
        json!({"path":[],"leaf":0,"role":0,"facet":"data","native":0});
        20_000
    ]);
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Limit);
}

/// A run over `roles` protocol roles R0.. (at most the roster limit) whose one
/// input is a distributed record of `roles` parameters A0.. with an index
/// field at each of its first `fields` parameters. Telescope position i is
/// applied to protocol role `order[i]`.
fn telescope(roles: usize, fields: usize, order: &[u32]) -> Value {
    let parameters: Vec<_> = (0..roles).map(|i| format!("A{i}")).collect();
    let index = schema("index", "index", json!(["index"]));
    let declared: Vec<_> = (0..fields)
        .map(|i| {
            let placed = data_placement(json!([i]));
            field(&format!("f{i}"), i as u32, true, placed, index.clone())
        })
        .collect();
    let record = product(
        &format!("Wide{roles}"),
        json!(parameters),
        json!(declared),
        0,
    );
    let applied: Vec<_> = order[..fields]
        .iter()
        .map(|role| data_placement(json!([role])))
        .collect();
    let p = product_placement(&record, json!(order), json!(applied));
    let native: Vec<_> = (0..fields).collect();
    let mut d = run_with(placed_port("w", 0, json!(native), p, record));
    let participants: Vec<_> = (0..roles.min(1024)).map(|i| format!("R{i}")).collect();
    d["protocols"][0]["roles"] = json!(participants);
    d["protocols"][0]["outputs"] = json!([]);
    d
}
#[test]
fn record_telescopes_have_their_own_catalog_limit() {
    // The record telescope limit is separate from the protocol roster limit;
    // both are 1,024 roles.
    for (roles, accepted) in [(16, true), (17, true), (1024, true), (1025, false)] {
        let order: Vec<u32> = (0..roles as u32).rev().collect();
        let d = telescope(roles, 1, &order);
        if accepted {
            let view = read(&d).unwrap();
            let last = format!("R{}", roles - 1);
            assert_eq!(view.ordinary_input(0, &[0], &last).unwrap().native(), [0]);
        } else {
            assert_eq!(read(&d).unwrap_err(), InterfaceError::Limit, "{roles}");
        }
    }
}
#[test]
fn permuted_wide_telescopes_place_each_field_at_its_substituted_role() {
    // Telescope position i is applied to protocol role (i + 16) mod 17, so
    // the arguments are an ordered substitution, not a sorted set. Each
    // participant's supply view holds exactly the field placed at the
    // telescope parameter that names it.
    let order: Vec<u32> = (0..17).map(|i| (i + 16) % 17).collect();
    let d = telescope(17, 17, &order);
    let view = read(&d).unwrap();
    assert_eq!(
        view.selected_protocol().inputs[0].placement.describe()["arguments"],
        json!(order)
    );
    let roles = view.roles();
    for (position, &role) in order.iter().enumerate() {
        let position = position as u32;
        let placed: Vec<_> = view
            .input_ports(&roles[role as usize])
            .map(|p| (p.index, p.path.to_vec(), p.role))
            .collect();
        assert_eq!(placed, [(0, vec![position], role)], "R{role}");
        let selected = view.ordinary_input(0, &[position], &format!("R{role}"));
        assert_eq!(selected.unwrap().native(), [position], "R{role}");
    }
}

#[test]
fn substitution_sorts_structural_scope_without_sorting_nominal_role_arguments() {
    let mut tuple = schema("tuple", "(Handle,index)", json!([]));
    tuple["constructible"] = json!(false);
    tuple["fields"] = json!([
        field(
            "0",
            0,
            true,
            Value::Null,
            logical::handle("bool", Some("0"), None)
        ),
        field(
            "1",
            1,
            true,
            Value::Null,
            schema("index", "index", json!(["index"]))
        )
    ]);
    let formula = product_placement(
        &tuple,
        json!([0, 1]),
        json!([
            {"kind":"oracle","holder":0,"receivers":[1]},{"kind":"data","roles":[0]}
        ]),
    );
    let actual = product_placement(
        &tuple,
        json!([0, 1]),
        json!([
            {"kind":"oracle","holder":1,"receivers":[0]},{"kind":"data","roles":[1]}
        ]),
    );
    let root = product(
        "StructuralChild",
        json!(["H", "R"]),
        json!([field("tuple", 0, true, formula, tuple)]),
        0,
    );
    let p = product_placement(&root, json!([1, 0]), json!([actual]));
    let d = run_with(placed_port("root", 0, json!([0, 1, 2]), p, root));
    let view = read(&d).unwrap();
    assert_eq!(view.ordinary_input(0, &[0, 1], "V").unwrap().native(), [2]);
    let mut bad = d;
    bad["protocols"][0]["inputs"][0]["placement"]["fields"][0]["arguments"] = json!([1, 0]);
    assert!(read(&bad).is_err());
}

#[test]
fn ordinary_specification_custody_allowance_does_not_open_distributed_resources() {
    let s = product(
        "DistributedGuard",
        json!(["P", "V"]),
        json!([field(
            "flag",
            2,
            true,
            data_placement(json!([0])),
            schema("boolean", "bool", json!(["bool"]))
        )]),
        2,
    );
    let placed = product_placement(&s, json!([0, 1]), json!([{"kind":"data","roles":[0]}]));
    let mut d = run_with(placed_port("guard", 0, json!([0, 1, 2]), placed, s));
    d["relations"] = document()["relations"].clone();
    d["relations"][0]["inputs"].as_array_mut().unwrap().pop();
    d["protocols"][0]["clauses"] = json!([{"name":"requires","kind":"input","subject":{"relation":"Predicate",
        "operands":[{"direction":"input","port":0,"role":"P","path":[0]}]},"residual":null,"decision":null}]);
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
}

#[test]
fn oracle_component_participants_are_ordered_independently_of_native_facet_offsets() {
    let p = placed_port(
        "handle",
        0,
        json!([0, 1]),
        json!({"kind":"oracle","holder":2,"receivers":[0,1]}),
        logical::handle("index", Some("4"), None),
    );
    let mut p = p;
    p["maximum_rows"] = Value::Null;
    let d = recursive_document(p);
    let view = read(&d).unwrap();
    let port = view.protocol_inputs().next().unwrap();
    assert_eq!(view.participants(), ["A", "B", "V"]);
    assert_eq!(
        port.components
            .iter()
            .map(|c| (c.role, c.native, c.facet))
            .collect::<Vec<_>>(),
        [
            (0, 1, raw::Facet::OracleAnchor),
            (1, 1, raw::Facet::OracleAnchor),
            (2, 0, raw::Facet::OracleData)
        ]
    );
    let mut bad = d;
    bad["protocols"][0]["inputs"][0]["components"]
        .as_array_mut()
        .unwrap()
        .rotate_right(1);
    assert_eq!(read(&bad).unwrap_err(), InterfaceError::Schema);
}
