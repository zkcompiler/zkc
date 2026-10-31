//! Complete selected layouts through native construction, codecs and preparation.
use serde_json::{Value as Json, json};
use std::{collections::HashSet, sync::Arc};
use zkc_cpu::{
    CpuBackend, Domain, EntryPolicy, FieldArray, FixedVector, Policy, Sequence, SetupRegistry,
    Value, Variant, cpu_contracts, has_native_wire,
};
use zkc_kernels::blst::bls12_381 as kernel;
use zkc_runtime::{
    interpreter::Runner,
    vm::{
        Action, Backend, Backing, ContractsBuilder, Identity, InstalledOperation, LogicalType,
        OperationBinding, PhysicalType, PreparationLimits, PreparedComputations, Program,
        Representation, Stop, Type, Usage, Value as _, ValueBudget, WireCodec, WorkBudget,
    },
};

fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        SetupRegistry::default(),
    )
    .unwrap()
}
fn physical(spelling: &str) -> PhysicalType {
    cpu_contracts().physical_type(spelling).unwrap()
}
fn scalar() -> PhysicalType {
    physical("field:bls12-381.fr@blst/fr")
}
fn sequence(element: &PhysicalType) -> PhysicalType {
    cpu_contracts()
        .aggregate_type(
            LogicalType::sequence(element.logical().clone()).unwrap(),
            Representation::Sequence,
            vec![element.clone()],
        )
        .unwrap()
}
fn dense(kind: Type, length: usize) -> PhysicalType {
    let logical = match kind {
        Type::FieldArray => format!("field_array<bls12-381.fr,{length}>"),
        Type::FixedVector => format!("fixed_vector<field:bls12-381.fr,{length}>"),
        _ => panic!("dense constructor"),
    };
    let storage = if kind == Type::FieldArray {
        "blst/field-array"
    } else {
        "blst/fixed-vector"
    };
    physical(&format!("{logical}@{storage}[blst/fr]"))
}
fn variant(name: &str, alternatives: Json, children: Vec<PhysicalType>) -> PhysicalType {
    let logical =
        LogicalType::parse(&zkc_test_support::variants::logical(name, alternatives)).unwrap();
    cpu_contracts()
        .aggregate_type(logical, Representation::Variant, children)
        .unwrap()
}
fn binding(
    operation: &str,
    arguments: Vec<String>,
    implementation: &str,
    selected: &PhysicalType,
) -> OperationBinding {
    OperationBinding {
        contract: operation.into(),
        arguments,
        implementation: implementation.into(),
        physical_arguments: vec![selected.spelling()],
    }
}
fn bytes(bindings: Vec<Json>, ports: Vec<Json>, outputs: Vec<String>, body: Vec<Json>) -> Vec<u8> {
    let inputs: Vec<_> = ports.iter().map(|p| p[0].clone()).collect();
    let names: Vec<_> = outputs
        .iter()
        .enumerate()
        .map(|(i, _)| format!("r{i}"))
        .collect();
    serde_json::to_vec(&json!([
        "zkc.program/0",
        bindings,
        [["function", "f", ports, outputs, body, ["f", []]]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            ports,
            outputs,
            [["local", "run", "f", inputs, names], ["return", names]],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}
fn row(name: &str, b: &OperationBinding) -> Json {
    json!([
        name,
        b.contract,
        b.arguments,
        b.implementation,
        b.physical_arguments
    ])
}
fn execute(mut runner: Runner<CpuBackend>) -> (Result<Vec<Value>, Stop>, Usage) {
    loop {
        while runner.advance_local_control().unwrap() {}
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
            Action::Returned(values) => return (Ok(values), runner.usage()),
            Action::Stopped(stop) => return (Err(stop), runner.usage()),
            other => panic!("unexpected {other:?}"),
        }
    }
}
fn call(b: OperationBinding, attributes: &[&str], args: Vec<Value>) -> Value {
    let native = backend();
    let actual = native.prepare_binding(&b).unwrap();
    let expected = cpu_contracts().resolve(b.clone()).unwrap();
    assert_eq!(actual.signature(), expected.signature());
    let ports: Vec<_> = actual
        .signature()
        .inputs
        .iter()
        .enumerate()
        .map(|(i, t)| json!([format!("a{i}"), t.spelling()]))
        .collect();
    let names: Vec<_> = ports.iter().map(|p| p[0].clone()).collect();
    let program = Program::decode(
        &bytes(
            vec![row("b", &b)],
            ports,
            actual
                .signature()
                .outputs
                .iter()
                .map(PhysicalType::spelling)
                .collect(),
            vec![
                json!(["op", "call", "b", attributes, names, ["out"]]),
                json!(["return", ["out"]]),
            ],
        ),
        cpu_contracts(),
    )
    .unwrap();
    program.check_installation(&native).unwrap();
    let runner = Runner::new(&program, "main", "P", "session", native, args)
        .unwrap_or_else(|e| panic!("{}", e.error));
    execute(runner).0.unwrap().remove(0)
}
fn resident(values: &[u64]) -> Arc<kernel::ScalarVector> {
    Arc::new(
        kernel::ScalarVector::try_from_fn(values.len(), |i| Ok(kernel::Scalar::from(values[i])))
            .unwrap(),
    )
}
fn parts(value: &Value) -> (usize, Vec<Backing>) {
    let mut seen = HashSet::new();
    let mut shared = Vec::new();
    let owned = value.retained_parts(&mut |b| {
        if !seen.insert(b) {
            return false;
        }
        shared.push(b);
        true
    });
    (owned, shared)
}

#[test]
fn complete_inactive_layout_and_nested_resident_children_survive_pack_and_access() {
    let field = scalar();
    let vector = physical("vector:bls12-381.fr@blst/fr");
    let g1 = physical("group:bls12-381.g1@blst/g1");
    let g2 = physical("group:bls12-381.g2@blst/g2");
    let ty = variant(
        "SelectedChildren",
        json!([
            ["empty", []],
            [
                "values",
                [
                    field.logical().spelling(),
                    vector.logical().spelling(),
                    g1.logical().spelling(),
                    g2.logical().spelling()
                ]
            ]
        ]),
        vec![field, vector, g1, g2],
    );
    let empty = Value::pack_variant(ty.clone(), 0, vec![]).unwrap();
    let default = PhysicalType::default_for(ty.logical().clone()).unwrap();
    assert_ne!(empty.physical_type(), default);
    assert_eq!(empty.unpack_variant().unwrap().0, ty);
    assert!(
        Value::pack_variant(
            default,
            1,
            vec![
                Value::BlstField(kernel::Scalar::ONE),
                Value::BlstVector(resident(&[3])),
                Value::BlstG1(kernel::G1::generator()),
                Value::BlstG2(Arc::new(kernel::G2::generator()))
            ]
        )
        .is_err()
    );
    let selected = sequence(&ty);
    let b = |op: &str| {
        binding(
            &format!("sequence.{op}"),
            vec![ty.logical().spelling()],
            &format!("native/sequence.{op}"),
            &selected,
        )
    };
    let values = call(b("empty"), &[], vec![]);
    assert_eq!(values.physical_type(), selected);
    let values = call(b("append"), &[], vec![values, empty]);
    assert!(matches!(
        call(b("length"), &[], vec![values.clone()]),
        Value::Index(1)
    ));
    let value = call(b("at"), &[], vec![values, Value::Index(0)]);
    assert_eq!(value.unpack_variant().unwrap().0, ty);
}

#[test]
fn dense_storage_shares_capacity_and_exact_backing_through_every_operation() {
    for n in [0, 4] {
        let mut upstream = Vec::with_capacity(n + 13);
        upstream.extend((0..n).map(|i| kernel::Scalar::from(i as u64 + 1).into_element()));
        let payload_bytes =
            upstream.capacity() * std::mem::size_of_val(&kernel::Scalar::ONE.into_element());
        let carrier = Arc::new(kernel::ScalarVector::from_elements(upstream));
        let vector = Value::BlstVector(carrier.clone());
        assert_eq!(vector.retained_bytes(), 256 + payload_bytes);
        let source_backing = parts(&vector).1;
        assert_eq!(source_backing[0].bytes(), 256 + payload_bytes);
        for kind in [Type::FieldArray, Type::FixedVector] {
            let ty = dense(kind, n);
            let family = if kind == Type::FieldArray {
                "field_array"
            } else {
                "fixed_vector"
            };
            let b = |op: &str| {
                binding(
                    &format!("{family}.{op}"),
                    vec!["bls12-381.fr".into(), n.to_string()],
                    &format!("blst/resident/{family}.{op}"),
                    &ty,
                )
            };
            let value = call(b("from_vector"), &[], vec![vector.clone()]);
            assert_eq!(value.physical_type(), ty);
            let (owned, backing) = parts(&value);
            assert_eq!(backing.len(), 3);
            assert!(backing.contains(&source_backing[0]));
            assert_eq!(
                owned + backing.iter().map(Backing::bytes).sum::<usize>(),
                value.retained_bytes()
            );
            assert_eq!(owned, 1024);
            assert_eq!(
                backing
                    .iter()
                    .filter(|b| !source_backing.contains(b))
                    .map(Backing::bytes)
                    .sum::<usize>(),
                ty.descriptor_bytes()
            );
            assert_eq!(parts(&value.clone()), parts(&value));
            match &value {
                Value::FieldArray(v) => {
                    assert!(Arc::ptr_eq(v.resident_elements().unwrap(), &carrier));
                    if n > 0 {
                        assert!(
                            matches!(call(b("at"), &["0"], vec![value.clone()]), Value::BlstField(v) if v == kernel::Scalar::ONE)
                        );
                        assert!(
                            matches!(call(b("get"), &[], vec![value.clone(), Value::Index(1)]), Value::BlstField(v) if v == kernel::Scalar::from(2))
                        );
                    }
                }
                Value::FixedVector(v) => {
                    assert!(Arc::ptr_eq(v.resident_elements().unwrap(), &carrier));
                    let Value::BlstVector(back) = call(b("to_vector"), &[], vec![value.clone()])
                    else {
                        panic!("resident vector")
                    };
                    assert!(Arc::ptr_eq(&back, &carrier));
                    let Value::BlstField(dot) =
                        call(b("dot"), &[], vec![value.clone(), value.clone()])
                    else {
                        panic!("resident dot")
                    };
                    assert_eq!(dot, carrier.dot(&carrier).unwrap());
                }
                _ => panic!("dense value"),
            }
        }
        assert!(
            FieldArray::from_resident(dense(Type::FieldArray, n + 1), carrier.clone()).is_err()
        );
        assert!(FixedVector::from_resident(dense(Type::FixedVector, n + 1), carrier).is_err());
    }
    const {
        assert!(std::mem::size_of::<Value>() <= 512);
    }
}

#[test]
fn nested_selected_codec_uses_identical_frames_and_decodes_directly() {
    let array = dense(Type::FieldArray, 3);
    let seq = sequence(&array);
    let ty = variant(
        "NestedSelectedWire",
        json!([["empty", []], ["values", [seq.logical().spelling()]]]),
        vec![seq.clone()],
    );
    let value = Value::Variant(
        Variant::new(
            ty.clone(),
            1,
            vec![Value::Sequence(
                Sequence::new(
                    seq,
                    vec![Value::FieldArray(
                        FieldArray::from_resident(array, resident(&[1, 4, 9])).unwrap(),
                    )],
                    &Policy::default(),
                )
                .unwrap(),
            )],
        )
        .unwrap(),
    );
    let native = backend();
    assert!(has_native_wire(&ty));
    assert!(cpu_contracts().permits_wire(&ty, WireCodec::Native));
    let bytes = native.encode_native_value(&value).unwrap();
    let selected = native.decode_native_value(&ty, &bytes).unwrap();
    let default = native
        .decode_native_value(
            &PhysicalType::default_for(ty.logical().clone()).unwrap(),
            &bytes,
        )
        .unwrap();
    assert_eq!(native.encode_native_value(&default).unwrap(), bytes);
    assert_eq!(native.encode_native_value(&selected).unwrap(), bytes);
    let mut invalid = bytes.clone();
    let last = invalid.len() - 32;
    invalid[last..].fill(255);
    assert_eq!(
        native.decode_native_value(&ty, &invalid).unwrap_err(),
        zkc_cpu::NativeWireError::Invalid(zkc_runtime::vm::DecodeReason::Scalar)
    );
    assert_eq!(selected.physical_type(), ty);
    let (_, _, values) = selected.unpack_variant().unwrap();
    let Value::Sequence(seq) = &values[0] else {
        panic!("sequence")
    };
    let Value::FieldArray(array) = seq.get(0).unwrap() else {
        panic!("array")
    };
    assert!(array.ark_elements().is_none());
    assert_eq!(
        array.resident_elements().unwrap().get(2),
        Some(kernel::Scalar::from(9))
    );
    let child_size = native.measure_native_value(&values[0]).unwrap();
    assert!(native.measure_native_variant(&ty, 1, &[child_size]).is_ok());
    let wrong = native.measure_native_value(&Value::Index(0)).unwrap();
    assert!(native.measure_native_variant(&ty, 1, &[wrong]).is_err());
}

#[test]
fn nested_frames_preserve_every_selected_resident_leaf_without_conversion() {
    let children = vec![
        scalar(),
        physical("vector:bls12-381.fr@blst/fr"),
        physical("group:bls12-381.g1@blst/g1"),
        physical("groups:bls12-381.g1@blst/g1"),
        physical("group:bls12-381.g2@blst/g2"),
        physical("groups:bls12-381.g2@blst/g2"),
    ];
    let logical: Vec<_> = children.iter().map(|ty| ty.logical().spelling()).collect();
    let ty = variant(
        "ResidentWireLeaves",
        json!([["empty", []], ["values", logical]]),
        children.clone(),
    );
    let native = backend();
    for alternative in [0, 1] {
        let payload = if alternative == 0 {
            vec![]
        } else {
            vec![
                Value::BlstField(kernel::Scalar::from(13)),
                Value::BlstVector(resident(&[2, 7])),
                Value::BlstG1(kernel::G1::generator()),
                Value::BlstG1Vector(Arc::new(
                    kernel::G1Vector::try_from_fn(2, |_| Ok(kernel::G1::generator())).unwrap(),
                )),
                Value::BlstG2(Arc::new(kernel::G2::generator())),
                Value::BlstG2Vector(Arc::new(
                    kernel::G2Vector::try_from_fn(2, |_| Ok(kernel::G2::generator())).unwrap(),
                )),
            ]
        };
        let value = Value::pack_variant(ty.clone(), alternative, payload).unwrap();
        let bytes = native.encode_native_value(&value).unwrap();
        let decoded = native.decode_native_value(&ty, &bytes).unwrap();
        assert_eq!(decoded.physical_type(), ty);
        assert_eq!(native.encode_native_value(&decoded).unwrap(), bytes);
        let canonical = native
            .decode_native_value(
                &PhysicalType::default_for(ty.logical().clone()).unwrap(),
                &bytes,
            )
            .unwrap();
        assert_eq!(native.encode_native_value(&canonical).unwrap(), bytes);
        if alternative == 1 {
            let (_, _, payload) = decoded.unpack_variant().unwrap();
            assert_eq!(
                payload.iter().map(Value::physical_type).collect::<Vec<_>>(),
                children
            );
            assert!(matches!(payload[1], Value::BlstVector(_)));
            assert!(matches!(payload[3], Value::BlstG1Vector(_)));
            assert!(matches!(payload[5], Value::BlstG2Vector(_)));
        }
    }
}

#[test]
fn inactive_local_only_layout_denies_wire_without_denying_immutable_preparation() {
    let fixed = dense(Type::FixedVector, 0);
    let ty = variant(
        "LocalSelected",
        json!([["empty", []], ["fixed", [fixed.logical().spelling()]]]),
        vec![fixed],
    );
    let value = Value::pack_variant(ty.clone(), 0, vec![]).unwrap();
    assert!(!has_native_wire(&ty));
    assert!(!cpu_contracts().permits_wire(&ty, WireCodec::Native));
    assert!(value.preparation_output());
    assert!(backend().encode_native_value(&value).is_err());
    let private = LogicalType::parse("prover_key:multilinear.kzg.bls12-381/0").unwrap();
    let ty = variant(
        "PrivateAlternative",
        json!([["empty", []], ["private", [private.spelling()]]]),
        vec![PhysicalType::default_for(private).unwrap()],
    );
    assert!(
        !Value::pack_variant(ty, 0, vec![])
            .unwrap()
            .preparation_output()
    );
}

fn prepared_program() -> Program {
    let ty = dense(Type::FixedVector, 4);
    let field = PhysicalType::default_for(scalar().logical().clone()).unwrap();
    let convert = OperationBinding {
        contract: "representation.convert".into(),
        arguments: vec![field.logical().spelling()],
        implementation: "native/representation.convert".into(),
        physical_arguments: vec![field.spelling(), scalar().spelling()],
    };
    let fill = OperationBinding {
        contract: "vector.fill".into(),
        arguments: vec!["bls12-381.fr".into()],
        implementation: "blst/resident/vector.fill".into(),
        physical_arguments: vec![],
    };
    let fixed = binding(
        "fixed_vector.from_vector",
        vec!["bls12-381.fr".into(), "4".into()],
        "blst/resident/fixed_vector.from_vector",
        &ty,
    );
    Program::decode(
        &bytes(
            vec![
                row("convert", &convert),
                row("fill", &fill),
                row("fixed", &fixed),
                json!(["count", "index.constant", [], "native/index.constant", []]),
            ],
            vec![json!(["x", field.spelling()])],
            vec![ty.spelling()],
            vec![
                json!(["op", "count", "count", ["4"], [], ["n"]]),
                json!(["op", "convert", "convert", [], ["x"], ["selected"]]),
                json!(["op", "fill", "fill", [], ["selected", "n"], ["v"]]),
                json!(["op", "fixed", "fixed", [], ["v"], ["out"]]),
                json!(["return", ["out"]]),
            ],
        ),
        cpu_contracts(),
    )
    .unwrap()
}
fn prepared_run(
    program: &Program,
    cache: &PreparedComputations<CpuBackend>,
    public: &[usize],
    values: ValueBudget,
    work: WorkBudget,
) -> (Result<Vec<Value>, Stop>, Usage) {
    let mut runner = Runner::new_with_budgets(
        program,
        "main",
        "P",
        "session",
        backend(),
        vec![Value::Field(zkc_cpu::Scalar::from(7))],
        values,
        work,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    runner.prepare_computations(cache.clone(), public).unwrap();
    execute(runner)
}
#[test]
fn public_scalar_prepares_local_only_aggregate_with_equal_warm_charges() {
    let program = prepared_program();
    program.check_installation(&backend()).unwrap();
    let cache = PreparedComputations::new(&program, PreparationLimits::default());
    let (cold, cold_usage) = prepared_run(
        &program,
        &cache,
        &[0],
        Default::default(),
        Default::default(),
    );
    let cold = cold.unwrap();
    assert_eq!(cache.stats().entries, 1);
    let (warm, warm_usage) = prepared_run(
        &program,
        &cache,
        &[0],
        Default::default(),
        Default::default(),
    );
    let warm = warm.unwrap();
    assert_eq!(cache.stats().hits, 1);
    assert_eq!(cold_usage, warm_usage);
    let (Value::FixedVector(a), Value::FixedVector(b)) = (&cold[0], &warm[0]) else {
        panic!("fixed results")
    };
    assert!(Arc::ptr_eq(
        a.resident_elements().unwrap(),
        b.resident_elements().unwrap()
    ));
    let cache_bytes = cache.stats().bytes;
    for (bytes, entries) in [(cache_bytes - 1, 0), (cache_bytes, 1)] {
        let bounded = PreparedComputations::new(&program, PreparationLimits { entries: 1, bytes });
        for _ in 0..2 {
            let (result, usage) = prepared_run(
                &program,
                &bounded,
                &[0],
                Default::default(),
                Default::default(),
            );
            result.unwrap();
            assert_eq!(usage, cold_usage);
        }
        assert_eq!(bounded.stats().entries, entries);
        assert_eq!(bounded.stats().hits, entries as u64);
    }
    let private = PreparedComputations::new(&program, PreparationLimits::default());
    assert!(
        prepared_run(
            &program,
            &private,
            &[],
            Default::default(),
            Default::default()
        )
        .0
        .is_ok()
    );
    assert_eq!(private.stats().entries, 0);
    for (values, work) in [
        (
            ValueBudget {
                total_bytes: cold_usage.total_value_bytes - 1,
                ..Default::default()
            },
            WorkBudget::default(),
        ),
        (
            ValueBudget::default(),
            WorkBudget {
                logical_bytes: cold_usage.logical_bytes - 1,
                ..Default::default()
            },
        ),
        (
            ValueBudget {
                live_bytes: 2048,
                ..Default::default()
            },
            WorkBudget::default(),
        ),
        (
            ValueBudget::default(),
            WorkBudget {
                instructions: cold_usage.instructions - 1,
                ..Default::default()
            },
        ),
    ] {
        let empty = PreparedComputations::new(
            &program,
            PreparationLimits {
                entries: 0,
                bytes: 0,
            },
        );
        let cached = prepared_run(&program, &cache, &[0], values, work);
        let uncached = prepared_run(&program, &empty, &[0], values, work);
        assert!(cached.0.is_err());
        assert_eq!(cached.0.unwrap_err(), uncached.0.unwrap_err());
        assert_eq!(cached.1, uncached.1);
    }
}

#[test]
fn family_actual_metadata_refuses_wrong_complete_parameters_and_lifted_conversions() {
    let ty = sequence(&scalar());
    let good = binding(
        "sequence.append",
        vec!["field:bls12-381.fr".into()],
        "native/sequence.append",
        &ty,
    );
    assert!(backend().prepare_binding(&good).is_some());
    for physical_arguments in [
        vec![scalar().spelling()],
        vec![ty.spelling(), ty.spelling()],
    ] {
        let bad = OperationBinding {
            physical_arguments,
            ..good.clone()
        };
        assert!(backend().prepare_binding(&bad).is_none());
        assert!(cpu_contracts().resolve(bad).is_err());
    }
    let default = PhysicalType::default_for(ty.logical().clone()).unwrap();
    let conversion = OperationBinding {
        contract: "representation.convert".into(),
        arguments: vec![ty.logical().spelling()],
        implementation: "native/representation.convert".into(),
        physical_arguments: vec![default.spelling(), ty.spelling()],
    };
    assert!(backend().prepare_binding(&conversion).is_none());
    assert!(cpu_contracts().resolve(conversion).is_err());
}

#[test]
fn inactive_foreign_layout_cannot_borrow_native_catalog_authority() {
    let mut foreign = ContractsBuilder::standard();
    let child = foreign
        .add_representation("blst/fr", scalar().logical().clone())
        .unwrap();
    assert_ne!(child, scalar());
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "ForeignInactive",
        json!([["empty", []], ["value", [child.logical().spelling()]]]),
    ))
    .unwrap();
    let ty = foreign
        .aggregate_type(logical, Representation::Variant, vec![child])
        .unwrap();
    let value = Value::pack_variant(ty.clone(), 0, vec![]).unwrap();
    assert!(!has_native_wire(&ty));
    assert!(!cpu_contracts().permits_wire(&ty, WireCodec::Native));
    assert!(!value.preparation_output());
    assert!(backend().measure_native_value(&value).is_err());
    assert!(backend().measure_native_variant(&ty, 0, &[]).is_err());
}

#[test]
fn selected_nested_resources_are_revalidated_without_reissuing_authority() {
    let mut native = backend();
    let rng = native
        .issue_rng_for(
            Identity::Bls12381Fr,
            Domain::new("P", "session", "main", None),
            1,
        )
        .unwrap();
    let Value::Rng(token) = &rng else {
        panic!("rng")
    };
    let token = token.clone();
    let ty = variant(
        "SelectedResource",
        json!([
            ["resource", [rng.physical_type().logical().spelling()]],
            ["scalar", [scalar().logical().spelling()]]
        ]),
        vec![rng.physical_type(), scalar()],
    );
    let value = Value::pack_variant(ty.clone(), 0, vec![rng]).unwrap();
    assert_eq!(value.physical_type(), ty);
    assert!(value.validation_backing().is_none());
    assert!(!value.preparation_output());
    native.validate_value(&value).unwrap();
    let (_, _, payload) = value.unpack_variant().unwrap();
    let Value::Rng(unpacked) = &payload[0] else {
        panic!("rng")
    };
    assert_eq!(unpacked.issued_id(), token.issued_id());
    assert_eq!(unpacked.identity(), token.identity());
    native.retire(&token).unwrap();
    assert_eq!(
        native.validate_value(&value).unwrap_err().code,
        "refused:capability-unissued"
    );
    assert_eq!(
        native.validate_value(&value.clone()).unwrap_err().code,
        "refused:capability-unissued"
    );
}

#[test]
fn native_match_preserves_every_resident_payload_port_and_empty_alternative() {
    let children = vec![
        scalar(),
        physical("vector:bls12-381.fr@blst/fr"),
        physical("group:bls12-381.g1@blst/g1"),
        physical("group:bls12-381.g2@blst/g2"),
    ];
    let logical: Vec<_> = children.iter().map(|t| t.logical().spelling()).collect();
    let ty = variant(
        "MatchedResident",
        json!([["empty", []], ["values", logical]]),
        children.clone(),
    );
    let names = ["s", "v", "g1", "g2"];
    let ports: Vec<_> = names
        .iter()
        .zip(&children)
        .map(|(n, t)| json!([n, t.spelling()]))
        .collect();
    for (alternative, payload) in [("empty", json!([])), ("values", json!(names))] {
        let program = Program::decode(
            &bytes(
                vec![],
                ports.clone(),
                children.iter().map(PhysicalType::spelling).collect(),
                vec![
                    json!([
                        "variant",
                        "pack",
                        ty.spelling(),
                        alternative,
                        payload,
                        "packed"
                    ]),
                    json!([
                        "match",
                        "unpack",
                        "packed",
                        names,
                        [
                            ["empty", [], [["yield", names]]],
                            [
                                "values",
                                ["p0", "p1", "p2", "p3"],
                                [["yield", ["p0", "p1", "p2", "p3"]]]
                            ]
                        ],
                        ["o0", "o1", "o2", "o3"]
                    ]),
                    json!(["return", ["o0", "o1", "o2", "o3"]]),
                ],
            ),
            cpu_contracts(),
        )
        .unwrap();
        let args = vec![
            Value::BlstField(kernel::Scalar::from(3)),
            Value::BlstVector(resident(&[5, 7])),
            Value::BlstG1(kernel::G1::generator()),
            Value::BlstG2(Arc::new(kernel::G2::generator())),
        ];
        let runner = Runner::new(&program, "main", "P", "session", backend(), args)
            .unwrap_or_else(|e| panic!("{}", e.error));
        let output = execute(runner).0.unwrap();
        assert_eq!(
            output.iter().map(Value::physical_type).collect::<Vec<_>>(),
            children
        );
    }
}
