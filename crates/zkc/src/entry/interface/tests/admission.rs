//! Independent regressions for operation-scoped ingress and component selection.
use super::*;

fn tuple(empty: bool) -> Value {
    let mut s = schema("tuple", "(bool,unit)", json!(["bool"]));
    s["fields"] = json!([
        {"name":"0","offset":0,"public":true,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))}
    ]);
    if empty {
        s["fields"].as_array_mut().unwrap().push(json!({"name":"1","offset":1,"public":true,"placement":null,"schema":schema("unit","()",json!([]))}));
    }
    s
}
fn product(s: &Value, roles: &[Value]) -> Value {
    json!({"kind":"product","instance":s["identity"],"arguments":[0,1],"fields":roles.iter().cloned().map(data_placement).collect::<Vec<_>>()})
}
#[test]
fn ordinary_product_target_visibility_uses_the_selected_role_intersection() {
    for empty in [false, true] {
        let s = tuple(empty);
        let roles = vec![json!([0, 1]); if empty { 2 } else { 1 }];
        let mut d = document();
        d["protocols"][0]["inputs"][0] =
            placed_port("statement", 0, json!([0]), product(&s, &roles), s.clone());
        d["relations"][0]["inputs"][0]["schema"] = s;
        read(&d).expect("ordinary verifier Product is a statement, including its empty descendant");
        d["relations"][0]["inputs"][0]["purpose"] = json!("witness");
        assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
    }
}
#[test]
fn uneven_product_roles_supply_the_whole_to_prover_and_only_child_to_verifier() {
    let mut s = tuple(true);
    s["type"] = json!("(index,index)");
    s["identity"] = json!(digest("(index,index)"));
    for field in s["fields"].as_array_mut().unwrap() {
        field["schema"] = schema("index", "index", json!(["index"]));
    }
    s["leaves"] = json!(["index", "index"]);
    let mut d = document();
    d["protocols"][0]["inputs"] = json!([placed_port(
        "pair",
        0,
        json!([0, 1]),
        product(&s, &[json!([0, 1]), json!([0])]),
        s
    )]);
    d["protocols"][0]["clauses"] = json!([]);
    d["job"]["target"] = Value::Null;
    d["job"]["public"] = json!([{"port":0,"path":[0],"role":"V"}]);
    // Run has no public selector forcing P to split its maximal tuple.
    let mut run = d.clone();
    run["job"] = json!({"kind":"run"});
    let view = read(&run).unwrap();
    assert_eq!(
        view.input_ports(&view.roles()[0])
            .map(|p| p.path.to_vec())
            .collect::<Vec<_>>(),
        [Vec::<u32>::new()]
    );
    assert_eq!(
        view.input_ports(&view.roles()[1])
            .map(|p| p.path.to_vec())
            .collect::<Vec<_>>(),
        [vec![0]]
    );
    assert!(view.ordinary_input(0, &[], "V").is_err());
    view.check_executable_ports().unwrap();
    read(&d).unwrap().check_executable_ports().unwrap();
}

fn zero_storage_roster(count: usize) -> Value {
    let mut root = schema("logical_record", "EmptyRoster", json!([]));
    root["constructible"] = json!(false);
    root["roles"] = json!(["P", "V"]);
    root["fields"] = json!((0..count).map(|i|json!({"name":format!("unit{i}"),"offset":0,"public":true,"placement":data_placement(json!([1])),"schema":schema("unit","()",json!([]))})).collect::<Vec<_>>());
    let p = product(&root, &vec![json!([1]); count]);
    let mut d = document();
    d["protocols"][0]["inputs"] = json!([placed_port("state", 0, json!([]), p, root)]);
    d["protocols"][0]["clauses"] = json!([]);
    d["job"]["target"] = Value::Null;
    d["job"]["public"] = json!(
        (0..count)
            .map(|i| json!({"port":0,"path":[i],"role":"V"}))
            .collect::<Vec<_>>()
    );
    d
}
#[test]
fn zero_storage_public_roster_retains_every_semantic_selection() {
    let d = zero_storage_roster(2000);
    assert!(d.to_string().len() < 4 * 1024 * 1024);
    let view = read(&d).unwrap();
    assert_eq!(view.public_ports().count(), 2000);
    assert!(view.public_ports().all(|p| p.native.is_empty()));
    view.check_executable_ports().unwrap();
    let mut missing = d;
    missing["job"]["public"].as_array_mut().unwrap().pop();
    assert_eq!(read(&missing).unwrap_err(), InterfaceError::Selection);
}

#[cfg(feature = "cpu")]
#[test]
fn opaque_prover_witness_does_not_require_a_verifier_constructor() {
    let (mut d, artifact) = unicode::proof_fixture();
    let mut opaque = schema("associated", "PrivateBool", json!(["bool"]));
    opaque["constructible"] = json!(false);
    opaque["fields"] = json!([{"name":"value","offset":0,"public":true,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))}]);
    let witness = &mut d["protocols"][0]["inputs"][1];
    witness["schema"] = opaque;
    witness["type"] = json!("PrivateBool");
    refresh_components(witness);
    let package = || {
        let frame = json!({"format":"zkc.entry/0","original":"original","interface":d.to_string(),"artifact":artifact,"assets":[],"options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":crate::entry::OracleSelection::default()}}).to_string();
        Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap()
    };
    let options = crate::entry::ProofOptions {
        binding: crate::entry::BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    crate::entry::ProofEntry::admit_operation(
        package(),
        options.clone(),
        Default::default(),
        crate::entry::ProofOperation::Verify,
    )
    .expect("verification consumes no opaque prover witness");
    let refused = crate::entry::ProofEntry::admit_operation(
        package(),
        options,
        Default::default(),
        crate::entry::ProofOperation::Prove,
    )
    .err()
    .expect("external construction stays private");
    assert_eq!(refused.code(), "entry-input-constructor");
}

#[cfg(feature = "cpu")]
#[test]
fn setup_variant_remains_a_supplied_operand_for_every_alternative() {
    let mut d = components::nested_setup();
    let commitment = d["protocols"][0]["inputs"][0]["schema"]["fields"][2]["schema"].clone();
    let key = json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity("SetupChoice")
        ],
        [
            ["case00000000", []],
            ["case00000001", ["commitment:multilinear.kzg.bls12-381/0"]]
        ]
    ]);
    let spelling = zkc_test_support::variants::encode_tree(key);
    let mut variant = schema("variant", "SetupChoice", json!([spelling]));
    variant["alternatives"] = json!([
        {"name":"Empty","fields":[]},
        {"name":"Commitment","fields":[{"name":"value","offset":0,"public":true,"placement":null,"schema":commitment}]}
    ]);
    d["protocols"][0]["inputs"][0]["schema"]["fields"][2]["schema"] = variant;
    refresh_components(&mut d["protocols"][0]["inputs"][0]);
    let view =
        read(&d).expect("setup-bearing variants do not disappear through empty product fields");
    view.check_executable_ports().unwrap();
    use ark_std::rand::SeedableRng;
    let policy = zkc_cpu::Policy::default();
    let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        1,
        &mut ark_std::rand::rngs::StdRng::from_seed([7; 32]),
        &policy.ark_bounds(),
    )
    .unwrap();
    let pin = keys.verifier_key().metadata().key_id();
    let key_bytes = keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap();
    let table = zkc_kernels::arkworks::bls12_381::Table::from_logical(
        &[zkc_cpu::Scalar::from(2u64), zkc_cpu::Scalar::from(5u64)],
        &policy.ark_bounds(),
    )
    .unwrap();
    let committed = keys.prover_key().commit(&table).unwrap();
    let authority = crate::entry::SetupAuthority {
        keys: [("pcs".into(), pin)].into(),
    };
    let native = crate::entry::setups::proof_authority(&view, authority).unwrap();
    assert_eq!(native.keys, [(0, pin)].into());
    assert_eq!(native.inputs, [(1, 0), (2, 0)].into());
    assert!(
        view.input_ports(&view.roles()[0])
            .any(|p| p.name == "setup_nonce")
    );
    let vk = [(0, key_bytes.as_slice())].into();
    for (alternative, fields) in [
        ("Empty", Default::default()),
        (
            "Commitment",
            [(
                "value".into(),
                zkc_cpu::Value::Commitment(std::sync::Arc::new(committed.commitment().clone()))
                    .into(),
            )]
            .into(),
        ),
    ] {
        let supplied = [
            (
                "setup_statement".into(),
                crate::entry::Value::Variant {
                    alternative: alternative.into(),
                    fields,
                },
            ),
            ("setup_unit".into(), crate::entry::Value::Unit),
        ]
        .into();
        let values =
            crate::entry::arguments::values(view.public_ports(), supplied, Some(&vk)).unwrap();
        assert_eq!(values.len(), 2);
        let crate::execution::InputValue::Wire(bytes) = &values[0] else {
            panic!("initialized key")
        };
        assert_eq!(bytes.as_slice(), key_bytes.as_slice());
    }
    // Neither setup metadata nor the inactive Empty alternative supplies a value.
    let missing = [("setup_unit".into(), crate::entry::Value::Unit)].into();
    assert_eq!(
        crate::entry::arguments::values(view.public_ports(), missing, Some(&vk)).unwrap_err(),
        "entry-input-names"
    );
}

#[cfg(feature = "cpu")]
#[test]
fn whole_sealed_ordinary_values_pass_typed_transport_but_never_ingress_or_projection() {
    let mut sealed = schema("record", "Sealed", json!(["bool"]));
    sealed["sealed"] = json!(true);
    sealed["constructible"] = json!(false);
    sealed["fields"] = json!([{"name":"secret","offset":0,"public":false,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))}]);
    let mut d = document();
    d["job"] = json!({"kind":"run"});
    d["protocols"][0]["clauses"] = json!([]);
    d["protocols"][0]["inputs"] =
        json!([port("sealed", 0, json!([0]), json!([0]), sealed.clone())]);
    d["protocols"][0]["outputs"] = d["protocols"][0]["inputs"].clone();
    let view = read(&d).unwrap();
    crate::entry::arguments::check_host_ports(&view, None)
        .expect("whole typed Copy value transport");
    assert_eq!(
        crate::entry::arguments::check_ports(&view).unwrap_err(),
        "entry-input-constructor"
    );
    assert!(view.ordinary_input(0, &[], "P").is_err());
    assert!(view.ordinary_input(0, &[0], "P").is_err());
    assert!(view.output_ports(&view.roles()[0]).any(|p| p.schema.sealed));
}

#[test]
fn indexed_public_selection_charges_bounded_cumulative_work_even_without_native_slots() {
    let mut previous = 0;
    for count in [1000, 2000] {
        let d = zero_storage_roster(count);
        let view = read(&d).unwrap();
        let mut work = boundary::Work::new(InterfaceLimits::DEFAULT);
        ports::Ports::with_work(
            &view.document,
            view.selected,
            &view.types,
            &view.setups,
            &mut work,
        )
        .unwrap();
        let used = InterfaceLimits::DEFAULT.work - work.remaining;
        eprintln!("{count} public unit fields: {used} reconstruction work");
        assert!(used < InterfaceLimits::DEFAULT.work);
        if previous != 0 {
            assert!(used < previous * 5 / 2);
        }
        previous = used;
        let mut exhausted = boundary::Work::new(InterfaceLimits {
            work: used - 1,
            ..InterfaceLimits::DEFAULT
        });
        assert!(matches!(
            ports::Ports::with_work(
                &view.document,
                view.selected,
                &view.types,
                &view.setups,
                &mut exhausted
            ),
            Err(InterfaceError::WorkLimit)
        ));
    }
}

#[cfg(feature = "cpu")]
#[test]
fn structural_residuals_apply_only_to_the_consumed_participant() {
    let mut d = components::document_components();
    d["protocols"][0]["inputs"][0]["schema"]["fields"][1]["public"] = json!(false);
    let view = read(&d).unwrap();
    assert!(
        view.outstanding_requirements()
            .iter()
            .all(|r| r.role == "P" && r.reason == "hidden")
    );
    view.check_executable_role(Some("V")).unwrap();
    assert!(
        crate::entry::EntryError::boundary_for_role(
            crate::entry::EntryPhase::Interface,
            "entry-input-codec",
            &view,
            Some("V")
        )
        .path()
        .is_none()
    );
    assert!(
        crate::entry::EntryError::boundary_for_role(
            crate::entry::EntryPhase::Interface,
            "entry-input-constructor",
            &view,
            Some("P")
        )
        .path()
        .unwrap()
        .contains("@P:hidden")
    );
    assert!(view.check_executable_ports().is_err());
    crate::entry::arguments::check_proof_ports(&view, crate::entry::ProofOperation::Verify)
        .unwrap();
    crate::entry::arguments::check_host_ports(&view, Some(crate::entry::ProofOperation::Verify))
        .unwrap();
    assert_eq!(
        crate::entry::arguments::check_proof_ports(&view, crate::entry::ProofOperation::Prove)
            .unwrap_err(),
        "entry-input-constructor"
    );
    assert_eq!(
        crate::entry::arguments::check_host_ports(&view, Some(crate::entry::ProofOperation::Prove))
            .unwrap_err(),
        "entry-input-constructor"
    );
}

#[cfg(feature = "cpu")]
#[test]
fn retained_public_data_requires_a_codec_and_external_context_keeps_constructor_checks() {
    let mut d = document();
    let mut opaque = schema("associated", "OpaqueStatement", json!(["bool"]));
    opaque["constructible"] = json!(false);
    opaque["fields"] = json!([{"name":"value","offset":0,"public":true,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))}]);
    d["protocols"][0]["inputs"][0]["schema"] = opaque.clone();
    d["protocols"][0]["inputs"][0]["type"] = opaque["type"].clone();
    refresh_components(&mut d["protocols"][0]["inputs"][0]);
    d["relations"][0]["inputs"][0]["schema"] = opaque;
    let view = read(&d).unwrap();
    for operation in [
        crate::entry::ProofOperation::Prove,
        crate::entry::ProofOperation::Verify,
    ] {
        crate::entry::arguments::check_host_ports(&view, Some(operation)).unwrap();
        assert_eq!(
            crate::entry::arguments::check_proof_ports(&view, operation).unwrap_err(),
            "entry-input-constructor"
        );
    }
    let mut context = setup_document();
    context["protocols"][0]["inputs"][2]["schema"]["constructible"] = json!(false);
    let view = read(&context).unwrap();
    assert_eq!(
        crate::entry::arguments::check_host_ports(&view, Some(crate::entry::ProofOperation::Prove))
            .unwrap_err(),
        "entry-input-constructor"
    );
}

#[test]
fn an_empty_prover_only_child_restricts_whole_product_target_visibility() {
    let s = tuple(true);
    let mut d = document();
    d["protocols"][0]["inputs"][1] = placed_port(
        "witness",
        1,
        json!([1]),
        product(&s, &[json!([0, 1]), json!([0])]),
        s.clone(),
    );
    d["relations"][0]["inputs"][1]["schema"] = s;
    d["job"]["public"] = json!([
        {"port":0,"path":[],"role":"V"}, {"port":1,"path":[0],"role":"V"}
    ]);
    read(&d).expect("the verifier's physical bool does not include the prover's empty child");
    d["relations"][0]["inputs"][1]["purpose"] = json!("statement");
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
}
