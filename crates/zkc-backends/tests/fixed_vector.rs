#[path = "domains/support.rs"]
mod support;

use p3_field::PrimeField32;
use serde_json::json;
use support::{Controlled, backend, one, program, run_program};
use zkc_backends::{FixedVector, KoalaBear, Policy, Value};
use zkc_runtime::interactive::{
    AttributeRule, Backend, ErrorCode, LogicalType, OperationBinding, PhysicalType, Representation,
    Value as RuntimeValue, admit_supplied,
};

fn binding(operation: &str, n: u64) -> OperationBinding {
    OperationBinding {
        contract: format!("fixed_vector.{operation}"),
        arguments: vec!["koala-bear".into(), n.to_string()],
        implementation: format!("plonky3/fixed_vector.{operation}"),
    }
}
fn vector(values: &[u32]) -> Value {
    Value::KoalaBearVector(values.iter().copied().map(KoalaBear::new).collect())
}
fn fixed(values: &[u32]) -> Value {
    let logical =
        LogicalType::parse(&format!("fixed_vector<field:koala-bear,{}>", values.len())).unwrap();
    Value::FixedVector(
        FixedVector::new(
            logical,
            values.iter().copied().map(KoalaBear::new).collect(),
        )
        .unwrap(),
    )
}
fn call(operation: &str, n: u64, args: Vec<Value>) -> Vec<Value> {
    one(backend(Policy::default()), binding(operation, n), &[], args)
        .0
        .unwrap()
}

#[test]
fn native_advertisement_is_exact_and_independent() {
    let native = backend(Policy::default());
    for operation in ["from_vector", "to_vector", "dot"] {
        for length in [0, 4, 1_048_576] {
            let b = binding(operation, length);
            let sig = native.binding_signature(&b).unwrap();
            assert_eq!(sig, b.signature().unwrap());
            assert_eq!(sig.attributes, AttributeRule::None);
            for physical in sig.inputs.iter().chain(&sig.outputs) {
                assert_eq!(
                    PhysicalType::parse(&physical.spelling()).unwrap(),
                    *physical
                );
            }
            let mut unsupported = b.clone();
            unsupported.arguments[0] = "bls12-381.fr".into();
            let mut open = unsupported.clone();
            open.implementation.clear();
            assert!(open.logical_signature().is_ok());
            assert!(unsupported.logical_signature().is_err());
            assert!(native.binding_signature(&unsupported).is_none());
            assert_eq!(
                unsupported.signature().unwrap_err().detail,
                "unrepresented logical type"
            );
            for implementation in [
                "arkworks/fixed_vector.dot",
                "plonky3/vector.dot",
                "plonky3/fixed_vector.unknown",
                "unknown/fixed_vector.dot",
            ] {
                let mut bad = b.clone();
                bad.implementation = implementation.into();
                assert!(bad.signature().is_err());
                assert!(native.binding_signature(&bad).is_none());
            }
        }
    }
    for n in ["01", " 1", "-1", "1048577", "18446744073709551616", "bool"] {
        let mut b = binding("dot", 1);
        b.arguments[1] = n.into();
        assert!(native.binding_signature(&b).is_none());
    }
    for contract in [
        "fixed_vector.unknown",
        "fixed_vector.encode",
        "fixed_vector.decode",
        "transcript.observe.fixed_vector",
    ] {
        let mut b = binding("dot", 1);
        b.contract = contract.into();
        b.implementation = format!("plonky3/{contract}");
        assert!(b.signature().is_err());
        assert!(native.binding_signature(&b).is_none());
    }
}

#[test]
fn conversions_retain_length_identity_and_never_expose_a_codec() {
    let input = vector(&[2, 3, 4]);
    let value = call("from_vector", 3, vec![input.clone()]).remove(0);
    assert_eq!(
        value.physical_type().spelling(),
        "fixed_vector<field:koala-bear,3>@plonky3.fixed-vector/0"
    );
    assert_ne!(value.physical_type(), input.physical_type());
    assert!(value.physical_type().is_duplicable());
    assert!(value.physical_type().is_discardable());
    assert!(!value.physical_type().is_serializable());
    let Value::FixedVector(storage) = &value else {
        panic!("a distinct bulk value is required");
    };
    assert_eq!(
        storage
            .elements()
            .iter()
            .map(PrimeField32::as_canonical_u32)
            .collect::<Vec<_>>(),
        [2, 3, 4]
    );
    let native = backend(Policy::default());
    assert_eq!(
        native.encode_native_value(&value).unwrap_err().to_string(),
        "native-wire-backend:native-wire-type"
    );
    let bytes = native.encode_native_value(&input).unwrap();
    assert_eq!(
        native
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err()
            .to_string(),
        "native-wire-backend:native-wire-type"
    );
    let output = call("to_vector", 3, vec![value]).remove(0);
    assert_eq!(output.physical_type(), input.physical_type());
    assert_eq!(native.encode_native_value(&output).unwrap(), bytes);
    assert_eq!(
        output.physical_type().representation(),
        Representation::KoalaBearVector
    );
}

#[test]
fn exact_length_is_checked_at_construction_and_conversion() {
    for n in [0, 2, 4] {
        assert_eq!(
            one(
                backend(Policy::default()),
                binding("from_vector", n),
                &[],
                vec![vector(&[1, 2, 3])]
            )
            .0
            .unwrap_err(),
            "refused:fixed-vector-length"
        );
    }
    let logical = LogicalType::parse("fixed_vector<field:koala-bear,4>").unwrap();
    assert_eq!(
        FixedVector::new(logical, vec![KoalaBear::new(1); 3].into())
            .unwrap_err()
            .code,
        "refused:fixed-vector-length"
    );
    let unsupported = LogicalType::parse("fixed_vector<field:bls12-381.fr,1>").unwrap();
    assert_eq!(
        FixedVector::new(unsupported, vec![KoalaBear::new(1)].into())
            .unwrap_err()
            .code,
        "refused:fixed-vector-representation"
    );
}

#[test]
fn dot_has_native_numerical_meaning_including_zero_and_modular_reduction() {
    for (a, b, expected) in [
        (vec![], vec![], 0),
        (vec![1, 2, 3], vec![4, 5, 6], 32),
        (vec![2_130_706_432, 2], vec![2, 3], 4),
    ] {
        let output = call("dot", a.len() as u64, vec![fixed(&a), fixed(&b)]).remove(0);
        let Value::KoalaBearField(result) = output else {
            panic!("field output");
        };
        assert_eq!(result.as_canonical_u32(), expected);
    }
    let empty = call("from_vector", 0, vec![vector(&[])]).remove(0);
    assert_eq!(
        empty.physical_type().logical().spelling(),
        "fixed_vector<field:koala-bear,0>"
    );
    assert!(
        matches!(call("to_vector", 0, vec![empty]).remove(0), Value::KoalaBearVector(v) if v.is_empty())
    );
}

#[test]
fn one_typed_local_program_executes_conversions_and_dot() {
    let from = binding("from_vector", 3);
    let to = binding("to_vector", 3);
    let dot = binding("dot", 3);
    let vector_type = from.signature().unwrap().inputs[0].clone();
    let field_type = dot.signature().unwrap().outputs[0].clone();
    let bytes = program(
        &[from, to, dot],
        &[vector_type.clone(), vector_type.clone()],
        vec![
            json!(["op", "left", "b0", [], ["a0"], ["x"]]),
            json!(["op", "right", "b0", [], ["a1"], ["y"]]),
            json!(["op", "dot", "b2", [], ["x", "y"], ["z"]]),
            json!(["op", "convert", "b1", [], ["x"], ["v"]]),
            json!(["release", ["x", "y"]]),
        ],
        &[field_type, vector_type],
        &["z".into(), "v".into()],
    );
    let (result, native) = run_program(
        backend(Policy::default()),
        &bytes,
        vec![vector(&[1, 2, 3]), vector(&[4, 5, 6])],
    );
    let values = result.unwrap();
    assert!(matches!(&values[0], Value::KoalaBearField(n) if n.as_canonical_u32() == 32));
    assert_eq!(
        native.encode_native_value(&values[1]).unwrap(),
        native.encode_native_value(&vector(&[1, 2, 3])).unwrap()
    );
}

#[test]
fn native_invocation_refuses_forged_types_attributes_and_dispatch_names() {
    for (replacement, attributes, kernel, expected) in [
        (Some(vector(&[1, 2])), None, None, "refused:kernel-operands"),
        (Some(fixed(&[1])), None, None, "refused:kernel-operands"),
        (
            None,
            Some(vec!["0".into()]),
            None,
            "refused:kernel-attributes",
        ),
        (
            None,
            None,
            Some("plonky3/fixed_vector.unknown".into()),
            "refused:kernel-operands",
        ),
    ] {
        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.substitute = replacement;
        controlled.attributes = attributes;
        controlled.implementation = kernel;
        assert_eq!(
            one(
                controlled,
                binding("dot", 2),
                &[],
                vec![fixed(&[1, 2]), fixed(&[3, 4])]
            )
            .0
            .unwrap_err(),
            expected
        );
    }
    let b = binding("from_vector", 2);
    let sig = b.signature().unwrap();
    let bytes = program(
        &[b],
        &sig.inputs,
        vec![json!(["op", "bad", "b0", ["2"], ["a0"], ["x"]])],
        &sig.outputs,
        &["x".into()],
    );
    assert_eq!(
        admit_supplied(&bytes, &backend(Policy::default()))
            .unwrap_err()
            .code,
        ErrorCode::Attributes
    );
}

#[test]
fn fixed_vector_output_storage_is_bounded_before_construction() {
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(1);
    assert_eq!(
        one(
            controlled,
            binding("from_vector", 2),
            &[],
            vec![vector(&[1, 2])]
        )
        .0
        .unwrap_err(),
        "exhausted:output-bytes"
    );
}

#[test]
fn canonical_generic_origin_arguments_retain_types_and_naturals_without_authority() {
    let b = binding("from_vector", 2);
    let sig = b.signature().unwrap();
    let bytes = program(
        &[b],
        &sig.inputs,
        vec![json!(["op", "make", "b0", [], ["a0"], ["x"]])],
        &sig.outputs,
        &["x".into()],
    );
    let mut carrier: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    carrier[2][0][5] = json!([
        "Generic",
        [
            ["F", "koala-bear"],
            ["N", "2"],
            ["T", "fixed_vector<field:koala-bear,2>"]
        ]
    ]);
    let bytes = serde_json::to_vec(&carrier).unwrap();
    let values = run_program(backend(Policy::default()), &bytes, vec![vector(&[3, 4])])
        .0
        .unwrap();
    assert_eq!(
        values[0].physical_type().logical().spelling(),
        "fixed_vector<field:koala-bear,2>"
    );
    for bad in [
        "02",
        "1048577",
        "unknown<bool,0>",
        "fixed_vector<bool,01>",
        "fixed_vector<bool,2>@plonky3.fixed-vector/0",
        "zkcv.fixed_vector.koala-bear/0",
    ] {
        carrier[2][0][5][1][1][1] = json!(bad);
        let error = admit_supplied(
            &serde_json::to_vec(&carrier).unwrap(),
            &backend(Policy::default()),
        )
        .unwrap_err();
        assert_eq!(error.code, ErrorCode::Type);
        assert_eq!(error.detail, "logical origin static identity");
    }
    // Even a canonical origin cannot change the independently resolved length.
    carrier[2][0][5][1][1][1] = json!("3");
    assert_eq!(
        run_program(
            backend(Policy::default()),
            &serde_json::to_vec(&carrier).unwrap(),
            vec![vector(&[3, 4, 5])]
        )
        .0
        .unwrap_err(),
        "refused:fixed-vector-length"
    );
}

#[test]
fn variants_contain_real_fixed_vectors_and_refuse_unrepresented_payloads() {
    let spelling = zkc_test_support::variants::logical(
        "Bulk",
        json!([
            ["value", ["fixed_vector<field:koala-bear,2>"]],
            ["empty", []]
        ]),
    );
    let logical = LogicalType::parse(&spelling).unwrap();
    let descriptor = logical.variant_descriptor().unwrap().clone();
    let value = Value::pack_variant(descriptor, 0, vec![fixed(&[1, 2])]).unwrap();
    backend(Policy::default()).validate_value(&value).unwrap();
    assert_eq!(value.physical_type().logical(), logical);
    assert!(matches!(
        value.unpack_variant().unwrap().2[0],
        Value::FixedVector(_)
    ));
    let unsupported = zkc_test_support::variants::logical(
        "Bulk",
        json!([
            ["value", ["fixed_vector<field:bls12-381.fr,2>"]],
            ["empty", []]
        ]),
    );
    let logical = LogicalType::parse(&unsupported).unwrap();
    let descriptor = logical.variant_descriptor().unwrap().clone();
    assert_eq!(
        Value::pack_variant(descriptor, 1, vec![]).unwrap_err().code,
        "refused:variant-payload-representation"
    );
}
