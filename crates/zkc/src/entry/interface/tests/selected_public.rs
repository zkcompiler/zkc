//! Selected public storage through authenticated named and positional proof calls.
use super::*;
use crate::{
    entry::{
        self, BindingPolicy, ProofEntry, ProofOperation, ProofOptions, ProofRequest, RoleInputs,
    },
    execution::{Capacity, InputValue, PreparedData},
    proof::{Invocation, NativeDeployment, ProofInputs},
};
use zkc_kernels::blst::bls12_381 as kernel;
use zkc_native::{Policy, Sequence, Value as NativeValue, native_contracts};
use zkc_runtime::vm::{LogicalType, PhysicalType, Representation, Value as _};

fn sequence(number: u64) -> (Value, NativeValue) {
    let child = native_contracts()
        .physical_type("field:bls12-381.fr@blst/fr")
        .unwrap();
    let logical = LogicalType::sequence(child.logical().clone()).unwrap();
    let ty = native_contracts()
        .aggregate_type(logical.clone(), Representation::Sequence, vec![child])
        .unwrap();
    let value = NativeValue::Sequence(
        Sequence::new(
            ty,
            vec![NativeValue::BlstField(kernel::Scalar::from(number))],
            &Policy::default(),
        )
        .unwrap(),
    );
    (
        schema("builtin", "Scalars", json!([logical.spelling()])),
        value,
    )
}

fn variant() -> (Value, NativeValue) {
    let children: Vec<_> = [
        "field:bls12-381.fr@blst/fr",
        "vector:bls12-381.fr@blst/fr",
        "group:bls12-381.g1@blst/g1",
        "groups:bls12-381.g1@blst/g1",
        "group:bls12-381.g2@blst/g2",
        "groups:bls12-381.g2@blst/g2",
    ]
    .iter()
    .map(|s| native_contracts().physical_type(s).unwrap())
    .collect();
    let leaves: Vec<_> = children.iter().map(|t| t.logical().spelling()).collect();
    let spelling = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity("sample::Statement")
        ],
        [
            ["case00000000", []],
            ["case00000001", []],
            ["case00000002", leaves]
        ]
    ]));
    let mut source = schema("variant", "sample::Statement", json!([spelling]));
    let fields: Vec<_> = children
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            let logical = ty.logical();
            let kind = match logical.kind() {
                zkc_runtime::vm::Type::Field => "field",
                zkc_runtime::vm::Type::Group => "group",
                _ => "builtin",
            };
            json!({"name":i.to_string(),"offset":i,
            "schema":schema(kind, &logical.spelling(), json!([logical.spelling()]))})
        })
        .collect();
    source["alternatives"] = json!([
        {"name":"Empty","fields":[]}, {"name":"Other","fields":[]},
        {"name":"Payload","fields":fields}
    ]);
    let ty = native_contracts()
        .aggregate_type(
            LogicalType::parse(&spelling).unwrap(),
            Representation::Variant,
            children,
        )
        .unwrap();
    (source, NativeValue::pack_variant(ty, 0, vec![]).unwrap())
}

fn seal(artifact: &mut Value) {
    artifact[3] = json!(crate::host::inputs::hash(
        &zkc_runtime::logical::encode_tree(&artifact[2]).unwrap(),
    ));
    artifact[5] = json!(digest(artifact[4].as_str().unwrap()));
}

fn fixture(source: &Value, ty: &PhysicalType) -> (Value, Value) {
    let (mut doc, artifact) = unicode::proof_fixture();
    doc["protocols"][0]["inputs"]
        .as_array_mut()
        .unwrap()
        .push(port(
            "selected",
            2,
            json!([2]),
            json!(["検証者", "証明者"]),
            source.clone(),
        ));
    doc["job"]["public"] = json!([0, 2]);
    let mut artifact: Value = serde_json::from_str(&artifact).unwrap();
    let mut program: Value = serde_json::from_str(artifact[4].as_str().unwrap()).unwrap();
    for i in 0..2 {
        program[3][i][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["selected", ty.spelling()]));
        artifact[6][i][2]
            .as_array_mut()
            .unwrap()
            .push(json!(["2", ty.logical().spelling()]));
    }
    // Exercise the proof driver and selected message decoder as well as ingress.
    program[3][1][6].as_array_mut().unwrap().insert(
        0,
        json!(["send", "selected", "selected", "role00000000", "selected"]),
    );
    program[3][0][6].as_array_mut().unwrap().insert(
        0,
        json!([
            "receive",
            "selected",
            "selected",
            "role00000001",
            "received",
            ty.spelling()
        ]),
    );
    let origin = crate::host::inputs::hex(
        &zkc_runtime::logical::encode_tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            [
                "message",
                "protocol",
                "selected",
                "selected",
                "role00000001",
                "role00000000"
            ]
        ]))
        .unwrap(),
    );
    artifact[2][3] = json!([["message", origin]]);
    artifact[2][5] = json!([[origin, ty.logical().spelling(), "zkc.native-data/0"]]);
    artifact[8] = json!([[origin, "selected"]]);
    artifact[4] = json!(program.to_string());
    artifact[2][1][7] = json!(["0", "2"]);
    artifact[2][4].as_array_mut().unwrap().push(json!([
        "role00000000",
        "2",
        ty.logical().spelling(),
        "zkc.native-data/0"
    ]));
    seal(&mut artifact);
    (doc, artifact)
}

fn package(doc: &Value, artifact: &Value) -> Package {
    let frame = json!({"format":"zkc.entry/0","original":"original",
        "interface":doc.to_string(),"artifact":artifact.to_string(),
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
            "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true},
        "assets":[]})
    .to_string();
    Package::capture(
        frame.as_bytes(),
        &Sha256::digest(frame.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}

fn deployment(artifact: &Value) -> std::result::Result<NativeDeployment, String> {
    let bytes = artifact.to_string();
    NativeDeployment::admit(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Default::default(),
    )
}

fn input(value: &NativeValue, form: &str) -> InputValue {
    let data = PreparedData::from_value(value.clone(), Capacity::default()).unwrap();
    match form {
        "native" => value.clone().into(),
        "prepared" => data.into(),
        "wire" => InputValue::Wire(data.canonical_bytes().to_vec().into()),
        _ => panic!("unknown test input form"),
    }
}

fn positional(
    value: &NativeValue,
    producer: bool,
    public_form: &str,
    role_form: &str,
) -> ProofInputs {
    let mut inputs = vec![NativeValue::Bool(true).into()];
    if producer {
        inputs.push(NativeValue::Bool(false).into());
    }
    inputs.push(input(value, role_form));
    ProofInputs {
        public: vec![NativeValue::Bool(true).into(), input(value, public_form)],
        inputs,
        context: b"selected public".to_vec(),
        services: vec![],
        transcript_budget: 0,
    }
}

fn named(selected: entry::Value, producer: bool) -> ProofRequest {
    ProofRequest {
        public: [("公開".into(), true.into()), ("selected".into(), selected)].into(),
        private: RoleInputs {
            inputs: if producer {
                [("秘密".into(), false.into())].into()
            } else {
                Default::default()
            },
            ..Default::default()
        },
        context: b"selected public".to_vec(),
        ..Default::default()
    }
}

fn entry(doc: &Value, artifact: &Value) -> ProofEntry {
    ProofEntry::admit(
        package(doc, artifact),
        ProofOptions {
            binding: BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        Default::default(),
    )
    .unwrap()
}

#[test]
fn selected_public_positional_proofs_agree_for_native_prepared_and_wire() {
    for (source, value) in [sequence(7), variant()] {
        let (_, artifact) = fixture(&source, &value.physical_type());
        let host = deployment(&artifact).unwrap();
        assert_eq!(host.public_types()[1], value.physical_type());
        let mut expected = None;
        for public_form in ["native", "prepared", "wire"] {
            for role_form in ["native", "prepared", "wire"] {
                let report = host
                    .execute(
                        &positional(&value, true, public_form, role_form),
                        Invocation::Prove,
                    )
                    .unwrap();
                assert!(report.cleanup_errors.is_empty());
                assert_eq!(report.messages, 1);
                let proof = report.outcome.unwrap();
                assert!(proof.len() > 40);
                let actual = (report.binding, proof.clone());
                assert_eq!(expected.get_or_insert_with(|| actual.clone()), &actual);
                let checked = host
                    .execute(
                        &positional(&value, false, role_form, public_form),
                        Invocation::Verify(&proof),
                    )
                    .unwrap();
                assert_eq!(checked.verification_result(), Some(true));
                assert_eq!(checked.messages, 1);
                assert_eq!(checked.binding, actual.0);
                assert!(checked.cleanup_errors.is_empty());
            }
        }
    }
}

#[test]
fn selected_public_named_sequence_proofs_keep_canonical_binding() {
    let (source, value) = sequence(7);
    let (doc, artifact) = fixture(&source, &value.physical_type());
    let entry = entry(&doc, &artifact);
    let positional = deployment(&artifact)
        .unwrap()
        .execute(&positional(&value, true, "wire", "wire"), Invocation::Prove)
        .unwrap();
    for form in ["native", "prepared", "wire"] {
        let report = entry
            .prove(named(input(&value, form).into(), true))
            .unwrap();
        assert!(report.is_success());
        assert_eq!(report.native.binding, positional.binding);
        let proof = report.native.outcome.unwrap();
        assert_eq!(proof, *positional.outcome.as_ref().unwrap());
        let checked = entry
            .verify(named(input(&value, form).into(), false), &proof)
            .unwrap();
        assert!(checked.is_success());
        assert_eq!(checked.verification_result(), Some(true));
    }
}

#[test]
fn selected_public_named_empty_variant_preserves_all_inactive_children() {
    let (source, value) = variant();
    let (doc, artifact) = fixture(&source, &value.physical_type());
    let entry = entry(&doc, &artifact);
    let selected = || entry::Value::Variant {
        alternative: "Empty".into(),
        fields: Default::default(),
    };
    let report = entry.prove(named(selected(), true)).unwrap();
    assert!(report.is_success());
    let proof = report.native.outcome.unwrap();
    let checked = entry.verify(named(selected(), false), &proof).unwrap();
    assert_eq!(checked.verification_result(), Some(true));
    for form in ["native", "prepared", "wire"] {
        let report = deployment(&artifact)
            .unwrap()
            .execute(&positional(&value, true, form, form), Invocation::Prove)
            .unwrap();
        assert_eq!(report.binding, checked.native.binding);
        assert_eq!(report.outcome.unwrap(), proof);
    }
    // Nominal source variants keep their schema-directed constructor boundary.
    assert_eq!(
        entry
            .prove(named(input(&value, "native").into(), true))
            .err()
            .unwrap()
            .to_string(),
        "entry-input-shape"
    );
}

#[test]
fn selected_public_exact_types_and_canonical_statement_equality_are_required() {
    for (source, value) in [sequence(7), variant()] {
        let (doc, artifact) = fixture(&source, &value.physical_type());
        let host = deployment(&artifact).unwrap();
        let default = PreparedData::from_wire(
            PhysicalType::default_for(value.physical_type().logical().clone()).unwrap(),
            PreparedData::from_value(value.clone(), Capacity::default())
                .unwrap()
                .canonical_bytes()
                .to_vec(),
            Capacity::default(),
        )
        .unwrap();
        for producer in [true, false] {
            let invocation = if producer {
                Invocation::Prove
            } else {
                Invocation::Verify(&[])
            };
            for public in [true, false] {
                for wrong in [default.value().clone(), NativeValue::Index(0)] {
                    for form in ["native", "prepared"] {
                        let mut request = positional(&value, producer, "native", "native");
                        if public {
                            request.public[1] = input(&wrong, form);
                        } else {
                            *request.inputs.last_mut().unwrap() = input(&wrong, form);
                        }
                        assert_eq!(
                            host.execute(&request, invocation).err().unwrap(),
                            "native-input-type"
                        );
                    }
                }
            }
            if source["kind"] == "builtin" {
                for form in ["native", "prepared"] {
                    assert_eq!(
                        entry(&doc, &artifact)
                            .check_inputs(
                                named(input(default.value(), form).into(), producer),
                                if producer {
                                    ProofOperation::Prove
                                } else {
                                    ProofOperation::Verify
                                },
                                None,
                            )
                            .unwrap_err()
                            .to_string(),
                        "native-input-type"
                    );
                }
            }
            let changed = if source["kind"] == "builtin" {
                sequence(8).1
            } else {
                NativeValue::pack_variant(value.physical_type(), 1, vec![]).unwrap()
            };
            for public_form in ["native", "prepared", "wire"] {
                for role_form in ["native", "prepared", "wire"] {
                    let mut request = positional(&value, producer, public_form, role_form);
                    *request.inputs.last_mut().unwrap() = input(&changed, role_form);
                    assert_eq!(
                        host.execute(&request, invocation).err().unwrap(),
                        "native-proof-shared-public-input"
                    );
                }
            }
            let proof = host
                .execute(
                    &positional(&value, true, "native", "native"),
                    Invocation::Prove,
                )
                .unwrap()
                .outcome
                .unwrap();
            let changed = host
                .execute(
                    &positional(&changed, false, "wire", "native"),
                    Invocation::Verify(&proof),
                )
                .unwrap();
            assert_eq!(changed.outcome.unwrap_err(), "proof-header");
        }
    }
}

#[test]
fn selected_public_role_disagreement_in_inactive_children_is_rejected() {
    for (source, value) in [sequence(7), variant()] {
        let ty = value.physical_type();
        let (doc, artifact) = fixture(&source, &ty);
        let children = if source["kind"] == "variant" {
            ty.variant_payload(2).unwrap().to_vec()
        } else {
            vec![ty.sequence_element().unwrap().clone()]
        };
        for index in 0..children.len() {
            let mut changed = children.clone();
            changed[index] = PhysicalType::default_for(changed[index].logical().clone()).unwrap();
            let wrong = native_contracts()
                .aggregate_type(ty.logical().clone(), ty.representation(), changed)
                .unwrap();
            assert_ne!(wrong, ty);
            let mut bad = artifact.clone();
            let mut program: Value = serde_json::from_str(bad[4].as_str().unwrap()).unwrap();
            // Isolate ingress agreement from Program message-schema agreement.
            for i in 0..2 {
                program[3][i][6].as_array_mut().unwrap().remove(0);
            }
            bad[2][3] = json!([]);
            bad[2][5] = json!([]);
            bad[8] = json!([]);
            program[3][1][4][2][1] = json!(wrong.spelling());
            bad[4] = json!(program.to_string());
            seal(&mut bad);
            assert_eq!(
                deployment(&bad).unwrap_err(),
                "native-proof-shared-port-type"
            );
            assert_eq!(
                ProofEntry::admit(
                    package(&doc, &bad),
                    ProofOptions {
                        binding: BindingPolicy::AllowAuthored,
                        ..Default::default()
                    },
                    Default::default()
                )
                .err()
                .unwrap()
                .to_string(),
                "native-proof-shared-port-type"
            );
            if source["kind"] == "variant" {
                let forged = NativeValue::pack_variant(wrong, 0, vec![]).unwrap();
                for form in ["native", "prepared"] {
                    let mut request = positional(&value, true, "native", "native");
                    request.public[1] = input(&forged, form);
                    assert_eq!(
                        deployment(&artifact)
                            .unwrap()
                            .execute(&request, Invocation::Prove)
                            .err()
                            .unwrap(),
                        "native-input-type"
                    );
                }
            }
        }
    }
}

#[test]
fn selected_public_operation_specific_packages_resolve_present_role_ports() {
    for (source, value) in [sequence(7), variant()] {
        let (doc, artifact) = fixture(&source, &value.physical_type());
        for projected in [false, true] {
            let admit = |producer| {
                let mut artifact = artifact.clone();
                if projected {
                    let role = if producer {
                        "role00000001"
                    } else {
                        "role00000000"
                    };
                    let mut program: Value =
                        serde_json::from_str(artifact[4].as_str().unwrap()).unwrap();
                    program[3].as_array_mut().unwrap().retain(|p| p[3] == role);
                    program[4][0][2]
                        .as_array_mut()
                        .unwrap()
                        .retain(|p| p[0] == role);
                    artifact[6].as_array_mut().unwrap().retain(|m| m[0] == role);
                    artifact[4] = json!(program.to_string());
                    seal(&mut artifact);
                }
                ProofEntry::admit_operation(
                    package(&doc, &artifact),
                    ProofOptions {
                        binding: BindingPolicy::AllowAuthored,
                        ..Default::default()
                    },
                    Default::default(),
                    if producer {
                        ProofOperation::Prove
                    } else {
                        ProofOperation::Verify
                    },
                )
                .unwrap()
            };
            let selected = || {
                if source["kind"] == "variant" {
                    entry::Value::Variant {
                        alternative: "Empty".into(),
                        fields: Default::default(),
                    }
                } else {
                    input(&value, "prepared").into()
                }
            };
            let produced = admit(true).prove(named(selected(), true)).unwrap();
            assert!(produced.is_success());
            let checked = admit(false)
                .verify(named(selected(), false), &produced.native.outcome.unwrap())
                .unwrap();
            assert_eq!(checked.verification_result(), Some(true));
        }
    }
}

#[test]
fn selected_public_named_mismatch_and_nested_constructor_controls() {
    for (source, value) in [sequence(7), variant()] {
        let (doc, artifact) = fixture(&source, &value.physical_type());
        let entry = entry(&doc, &artifact);
        let selected = if source["kind"] == "variant" {
            entry::Value::Variant {
                alternative: "Empty".into(),
                fields: Default::default(),
            }
        } else {
            input(&value, "native").into()
        };
        let proof = entry
            .prove(named(selected, true))
            .unwrap()
            .native
            .outcome
            .unwrap();
        let changed = if source["kind"] == "variant" {
            entry::Value::Variant {
                alternative: "Other".into(),
                fields: Default::default(),
            }
        } else {
            input(&sequence(8).1, "prepared").into()
        };
        let rejected = entry.verify(named(changed, false), &proof).unwrap();
        assert_eq!(rejected.native.outcome.unwrap_err(), "proof-header");
        let mut restricted = doc.clone();
        if source["kind"] == "variant" {
            // Inactive fields retain their source constructor restrictions.
            restricted["protocols"][0]["inputs"][2]["schema"]["alternatives"][2]["fields"][0]["schema"]
                ["constructible"] = json!(false);
        } else {
            restricted["protocols"][0]["inputs"][2]["schema"]["constructible"] = json!(false);
        }
        assert_eq!(
            ProofEntry::admit(
                package(&restricted, &artifact),
                ProofOptions {
                    binding: BindingPolicy::AllowAuthored,
                    ..Default::default()
                },
                Default::default()
            )
            .err()
            .unwrap()
            .to_string(),
            "entry-input-constructor"
        );
        let mut wrong_source = doc.clone();
        wrong_source["protocols"][0]["inputs"][2]["schema"] =
            schema("boolean", "bool", json!(["bool"]));
        wrong_source["protocols"][0]["inputs"][2]["type"] = json!("bool");
        assert_eq!(
            ProofEntry::admit(
                package(&wrong_source, &artifact),
                ProofOptions {
                    binding: BindingPolicy::AllowAuthored,
                    ..Default::default()
                },
                Default::default()
            )
            .err()
            .unwrap()
            .to_string(),
            "entry-interface-native-binding"
        );
    }
}

#[test]
fn selected_public_foreign_child_grants_cannot_impersonate_native_storage() {
    use zkc_runtime::vm::ContractsBuilder;
    let (source, value) = variant();
    let ty = value.physical_type();
    let (_, artifact) = fixture(&source, &ty);
    let mut foreign = ContractsBuilder::standard();
    let children = ty
        .variant_payload(2)
        .unwrap()
        .iter()
        .zip([
            "blst/fr", "blst/fr", "blst/g1", "blst/g1", "blst/g2", "blst/g2",
        ])
        .map(|(child, layout)| {
            // Same names and logical types still belong to a different catalog.
            foreign
                .add_representation(layout, child.logical().clone())
                .unwrap()
        })
        .collect();
    let foreign_type = foreign
        .aggregate_type(ty.logical().clone(), Representation::Variant, children)
        .unwrap();
    assert_eq!(foreign_type.spelling(), ty.spelling());
    assert_ne!(foreign_type, ty);
    let forged = NativeValue::pack_variant(foreign_type, 0, vec![]).unwrap();
    let host = deployment(&artifact).unwrap();
    for producer in [true, false] {
        for public in [true, false] {
            let mut request = positional(&value, producer, "native", "native");
            if public {
                request.public[1] = forged.clone().into();
            } else {
                *request.inputs.last_mut().unwrap() = forged.clone().into();
            }
            assert_eq!(
                host.execute(
                    &request,
                    if producer {
                        Invocation::Prove
                    } else {
                        Invocation::Verify(&[])
                    }
                )
                .err()
                .unwrap(),
                "native-input-type"
            );
        }
    }
    // Preparation cannot bless a foreign inactive selection either.
    assert!(PreparedData::from_value(forged, Capacity::default()).is_err());
}

#[test]
fn selected_public_positional_byte_transport_uses_the_admitted_selection() {
    for (source, value) in [sequence(7), variant()] {
        let (_, artifact) = fixture(&source, &value.physical_type());
        let host = deployment(&artifact).unwrap();
        let encode = |value| {
            crate::host::inputs::hex(
                PreparedData::from_value(value, Capacity::default())
                    .unwrap()
                    .canonical_bytes(),
            )
        };
        let yes = encode(NativeValue::Bool(true));
        let no = encode(NativeValue::Bool(false));
        let selected = encode(value.clone());
        let mut proof = vec![];
        for producer in [true, false] {
            let mut role = vec![json!(["0", ["wire", yes]])];
            if producer {
                role.push(json!(["1", ["wire", no]]));
            }
            role.push(json!(["2", ["wire", selected]]));
            let bytes = json!([
                "zkc.native-proof-inputs/0",
                [["role00000000", "0", yes], ["role00000000", "2", selected]],
                role,
                crate::host::inputs::hex(b"selected public"),
                [],
                "0"
            ])
            .to_string();
            let invocation = if producer {
                Invocation::Prove
            } else {
                Invocation::Verify(&proof)
            };
            let decoded = ProofInputs::decode_bytes(&host, bytes.as_bytes(), invocation).unwrap();
            let report = host.execute(&decoded, invocation).unwrap();
            assert_eq!(report.messages, 1);
            assert!(report.cleanup_errors.is_empty());
            if producer {
                proof = report.outcome.unwrap();
            } else {
                assert_eq!(report.verification_result(), Some(true));
            }
        }
    }
}

#[test]
fn public_default_storage_remains_supported_by_both_proof_paths() {
    for (source, selected) in [sequence(7), variant()] {
        let data = PreparedData::from_wire(
            PhysicalType::default_for(selected.physical_type().logical().clone()).unwrap(),
            PreparedData::from_value(selected, Capacity::default())
                .unwrap()
                .canonical_bytes()
                .to_vec(),
            Capacity::default(),
        )
        .unwrap();
        let value = data.value();
        let (doc, artifact) = fixture(&source, data.physical_type());
        let host = deployment(&artifact).unwrap();
        let entry = entry(&doc, &artifact);
        for form in ["native", "prepared", "wire"] {
            let produced = host
                .execute(&positional(value, true, form, form), Invocation::Prove)
                .unwrap();
            let proof = produced.outcome.unwrap();
            let checked = host
                .execute(
                    &positional(value, false, form, form),
                    Invocation::Verify(&proof),
                )
                .unwrap();
            assert_eq!(checked.verification_result(), Some(true));
            let named_value = || {
                if source["kind"] == "variant" {
                    entry::Value::Variant {
                        alternative: "Empty".into(),
                        fields: Default::default(),
                    }
                } else {
                    input(value, form).into()
                }
            };
            let produced = entry.prove(named(named_value(), true)).unwrap();
            assert!(produced.is_success());
            assert_eq!(produced.native.outcome.unwrap(), proof);
            let checked = entry.verify(named(named_value(), false), &proof).unwrap();
            assert_eq!(checked.verification_result(), Some(true));
        }
    }
}
