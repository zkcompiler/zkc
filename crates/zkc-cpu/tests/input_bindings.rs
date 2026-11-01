//! Hand-authored runtime subjects with actual CPU values; no source certification.
use serde_json::json;
use sha2::{Digest, Sha256};
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Scalar, Sequence, SetupRegistry, Value};
use zkc_runtime::{
    host::{
        input_binding::{
            BindingError, InputBindings, InputComponent, InputRequirement, Observation,
        },
        wire::WireBackend,
    },
    vm::{LogicalType, PhysicalType, Program, Value as _},
};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
/// A default-capacity invocation ledger for one inspection.
fn ledger() -> zkc_runtime::vm::ExecutionLedger {
    zkc_runtime::vm::ExecutionLedger::new(Default::default(), Default::default())
}
fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        SetupRegistry::default(),
    )
    .unwrap()
}
fn pinned(ty: PhysicalType, observation: Observation, expected: &[u8]) -> InputBindings {
    let participants: Vec<_> = ["P", "V"]
        .iter()
        .map(|role| {
            json!([
                "participant",
                role,
                "root",
                role,
                [["x", ty.spelling()]],
                [],
                [["return", []]],
                []
            ])
        })
        .collect();
    let program = Program::decode(
        json!([
            "zkc.program/0",
            [],
            [],
            participants,
            [["entry", "main", [["P", "P"], ["V", "V"]]]]
        ])
        .to_string()
        .as_bytes(),
        zkc_cpu::cpu_contracts(),
    )
    .unwrap();
    let required = [InputRequirement {
        components: ["P", "V"]
            .map(|role| InputComponent {
                role: role.into(),
                input: 0,
                path: vec![],
            })
            .to_vec(),
        ty: ty.clone(),
        observation,
    }];
    let facet = match observation {
        Observation::Value => json!("value"),
        Observation::Tag => json!("tag"),
        Observation::Extent { axis } => json!(["extent", axis.to_string()]),
    };
    // Local fixture pins identify bytes only; external authority is an application obligation.
    let bytes = zkc_format::logical::encode_tree(&json!([
        "zkc.input-bindings/0",
        hex(&Sha256::digest(program.bytes())),
        "main",
        [[
            [["P", "0", []], ["V", "0", []]],
            ty.spelling(),
            facet,
            ["active", hex(expected)]
        ]]
    ]))
    .unwrap();
    InputBindings::admit_pinned(
        &program,
        "main",
        &required,
        &bytes,
        &Sha256::digest(&bytes).into(),
    )
    .unwrap()
}

#[test]
fn cpu_extent_observation_binds_metadata_without_contents_or_wire_support() {
    let backend = backend();
    let ty = PhysicalType::default_for(
        LogicalType::sequence(LogicalType::parse("index").unwrap()).unwrap(),
    )
    .unwrap();
    let sequences: Vec<_> = [
        vec![Value::Index(3), Value::Index(4)],
        vec![Value::Index(9), Value::Index(8)],
    ]
    .into_iter()
    .map(|values| Value::Sequence(Sequence::new(ty.clone(), values, &Policy::default()).unwrap()))
    .collect();
    let context = pinned(ty, Observation::Extent { axis: 0 }, b"2");
    for (role, value) in ["P", "V"].into_iter().zip(sequences) {
        context
            .check_role(role, &backend, &[value], &ledger())
            .unwrap();
    }
    for (left, right, expected) in [
        (vec![], vec![], b"0".as_slice()),
        (
            vec![Scalar::from(1u64)],
            vec![Scalar::from(2u64)],
            b"1".as_slice(),
        ),
    ] {
        let left = Value::Vector(left.into());
        let right = Value::Vector(right.into());
        let context = pinned(
            left.physical_type(),
            Observation::Extent { axis: 0 },
            expected,
        );
        context
            .check_role("P", &backend, &[left], &ledger())
            .unwrap();
        context
            .check_role("V", &backend, &[right], &ledger())
            .unwrap();
    }
    let fixed_ty =
        PhysicalType::default_for(LogicalType::parse("fixed_vector<field:koala-bear,0>").unwrap())
            .unwrap();
    let fixed =
        Value::FixedVector(zkc_cpu::FixedVector::new(fixed_ty.clone(), vec![].into()).unwrap());
    assert!(!backend.supports_wire(&fixed_ty));
    pinned(fixed_ty, Observation::Extent { axis: 0 }, b"0")
        .check_role("P", &backend, &[fixed], &ledger())
        .unwrap();
}

#[test]
fn cpu_matrix_extent_keeps_rows_columns_and_contents_distinct() {
    let backend = backend();
    let policy = Policy::default();
    let left = Value::matrix(2, 3, &[(0, 1, Scalar::from(1u64))], &policy).unwrap();
    let right = Value::matrix(2, 3, &[(1, 2, Scalar::from(9u64))], &policy).unwrap();
    for (axis, expected) in [(0, b"2"), (1, b"3")] {
        let context = pinned(left.physical_type(), Observation::Extent { axis }, expected);
        context
            .check_role("P", &backend, std::slice::from_ref(&left), &ledger())
            .unwrap();
        context
            .check_role("V", &backend, std::slice::from_ref(&right), &ledger())
            .unwrap();
        let transposed_shape = Value::matrix(3, 2, &[], &policy).unwrap();
        assert_eq!(
            context.check_role("V", &backend, &[transposed_shape], &ledger()),
            Err(BindingError::Value)
        );
    }
    assert!(left.control_extent(2).is_err());
    assert!(Value::Index(0).control_extent(0).is_err());
}

#[test]
fn empty_variant_value_is_active_canonical_data_and_not_an_inactive_path() {
    let spelling =
        zkc_format::types::variant_spelling(&json!([["input_bindings", "Unit"], [["unit", []]]]))
            .unwrap();
    let ty = PhysicalType::default_for(LogicalType::parse(&spelling).unwrap()).unwrap();
    let value = Value::pack_variant(ty.clone(), 0, vec![]).unwrap();
    let backend = backend();
    let encoded = backend.encode_wire(&value).unwrap();
    let context = pinned(ty, Observation::Value, &encoded);
    context
        .check_role("P", &backend, &[value], &ledger())
        .unwrap();
}
