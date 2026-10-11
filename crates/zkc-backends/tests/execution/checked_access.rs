//! Checked access through independent binding advertisement and admitted execution.
use crate::support;
use support::{Controlled, assert_value, backend, one, program};
use zkc_backends::{
    Bn254Scalar, FieldArray, KoalaBear, KoalaBearExt8, Policy, RistrettoScalar, Scalar, Value,
};
use zkc_runtime::interactive::{
    Backend, ErrorCode, Identity, LogicalType, OperationBinding, Value as _, admit_supplied,
};

const FIELDS: [(&str, &str); 5] = [
    ("bls12-381.fr", "arkworks"),
    ("bn254.fr", "arkworks"),
    ("ristretto255.scalar", "dalek"),
    ("koala-bear", "plonky3"),
    ("koala-bear.ext8-binomial3", "plonky3"),
];

fn binding(contract: &str, field: usize, length: Option<usize>) -> OperationBinding {
    let mut arguments = vec![FIELDS[field].0.into()];
    if let Some(length) = length {
        arguments.push(length.to_string());
    }
    OperationBinding {
        contract: contract.into(),
        arguments,
        implementation: format!("{}/{contract}", FIELDS[field].1),
    }
}

fn scalar(field: usize, n: u64) -> Value {
    match field {
        0 => Value::Field(Scalar::from(n)),
        1 => Value::Bn254Field(Bn254Scalar::from(n)),
        2 => Value::RistrettoField(RistrettoScalar::from(n)),
        3 => Value::KoalaBearField(KoalaBear::new(n as u32)),
        4 => Value::KoalaBearExt8Field(KoalaBear::new(n as u32).into()),
        _ => unreachable!(),
    }
}

fn matrix(field: usize, rows: usize, columns: usize, entries: &[(u32, u32, u64)]) -> Value {
    macro_rules! make {
        ($constructor:ident, $convert:expr) => {
            Value::$constructor(
                rows,
                columns,
                &entries
                    .iter()
                    .map(|&(r, c, n)| (r, c, ($convert)(n)))
                    .collect::<Vec<_>>(),
                &Policy::default(),
            )
            .unwrap()
        };
    }
    match field {
        0 => make!(matrix, Scalar::from),
        1 => make!(bn254_matrix, Bn254Scalar::from),
        2 => make!(ristretto_matrix, RistrettoScalar::from),
        3 => make!(koala_bear_matrix, |n| KoalaBear::new(n as u32)),
        4 => make!(koala_bear_ext8_matrix, |n| KoalaBearExt8::from(
            KoalaBear::new(n as u32)
        )),
        _ => unreachable!(),
    }
}

#[test]
fn sparse_lookup_matches_independent_dense_oracle_in_every_field() {
    let entries = [(0, 1, 7), (0, 4, 11), (2, 0, 13), (2, 3, 17), (3, 4, 19)];
    let dense = [
        [0, 7, 0, 0, 11],
        [0; 5],
        [13, 0, 0, 17, 0],
        [0, 0, 0, 0, 19],
    ];
    for field in 0..FIELDS.len() {
        let m = matrix(field, 4, 5, &entries);
        let b = binding("matrix.get", field, None);
        let native = backend(Policy::default());
        let signature = native.binding_signature(&b).unwrap();
        assert_eq!(signature, b.signature().unwrap());
        assert_eq!(signature.outputs, vec![scalar(field, 0).physical_type()]);
        let empty = one(
            backend(Policy::default()),
            b.clone(),
            &[],
            vec![matrix(field, 4, 5, &[]), Value::Index(3), Value::Index(4)],
        )
        .0
        .unwrap();
        assert_value(&empty[0], &scalar(field, 0));
        for (r, row) in dense.iter().enumerate() {
            for (c, &expected) in row.iter().enumerate() {
                let result = one(
                    backend(Policy::default()),
                    b.clone(),
                    &[],
                    vec![m.clone(), Value::Index(r as u64), Value::Index(c as u64)],
                )
                .0
                .unwrap();
                assert_value(&result[0], &scalar(field, expected));
            }
        }
        // Maximum shape stays sparse; access neither materializes nor multiplies dimensions.
        let m = matrix(field, 65536, 65536, &[(65535, 65535, 23)]);
        for (r, c, expected) in [(65535, 65535, 23), (65535, 65534, 0)] {
            let result = one(
                backend(Policy::default()),
                b.clone(),
                &[],
                vec![m.clone(), Value::Index(r), Value::Index(c)],
            )
            .0
            .unwrap();
            assert_value(&result[0], &scalar(field, expected));
        }
    }
}

#[test]
fn extension_lookup_preserves_nonbase_coordinates() {
    use p3_field::BasedVectorSpace;
    let value = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new((i + 1) as u32));
    let m = Value::koala_bear_ext8_matrix(2, 3, &[(1, 2, value)], &Policy::default()).unwrap();
    let result = one(
        backend(Policy::default()),
        binding("matrix.get", 4, None),
        &[],
        vec![m, Value::Index(1), Value::Index(2)],
    )
    .0
    .unwrap();
    assert_value(&result[0], &Value::KoalaBearExt8Field(value));
}

#[test]
fn matrix_lookup_refuses_empty_shapes_and_untruncated_large_coordinates() {
    for field in 0..FIELDS.len() {
        for (rows, columns) in [(0, 0), (0, 3), (2, 0), (2, 3)] {
            for (r, c) in [
                (rows as u64, 0),
                (0, columns as u64),
                (u32::MAX as u64 + 1, 0),
                (0, u32::MAX as u64 + 1),
                (u64::MAX, 0),
                (0, u64::MAX),
            ] {
                let result = one(
                    backend(Policy::default()),
                    binding("matrix.get", field, None),
                    &[],
                    vec![
                        matrix(field, rows, columns, &[]),
                        Value::Index(r),
                        Value::Index(c),
                    ],
                )
                .0;
                assert_eq!(result.unwrap_err(), "refused:matrix-index");
            }
        }
    }
}

fn array(length: usize) -> Value {
    Value::FieldArray(
        FieldArray::new(
            LogicalType::field_array(Identity::Bls12381Fr, length as u64).unwrap(),
            (0..length)
                .map(|i| Scalar::from((3 * i + 7) as u64))
                .collect::<Vec<_>>()
                .into(),
        )
        .unwrap(),
    )
}

#[test]
fn dynamic_array_access_agrees_with_static_access_and_checks_bounds() {
    for length in [0, 1, 4] {
        let b = binding("field_array.get", 0, Some(length));
        assert_eq!(
            backend(Policy::default()).binding_signature(&b).unwrap(),
            b.signature().unwrap()
        );
        for index in 0..length {
            let dynamic = one(
                backend(Policy::default()),
                b.clone(),
                &[],
                vec![array(length), Value::Index(index as u64)],
            )
            .0
            .unwrap();
            let static_value = one(
                backend(Policy::default()),
                binding("field_array.at", 0, Some(length)),
                &[&index.to_string()],
                vec![array(length)],
            )
            .0
            .unwrap();
            assert_value(&dynamic[0], &scalar(0, (3 * index + 7) as u64));
            assert_value(&dynamic[0], &static_value[0]);
        }
        for index in [length as u64, u32::MAX as u64 + 1, u64::MAX] {
            assert_eq!(
                one(
                    backend(Policy::default()),
                    b.clone(),
                    &[],
                    vec![array(length), Value::Index(index)]
                )
                .0
                .unwrap_err(),
                "refused:field-array-index"
            );
        }
        assert_eq!(
            one(
                backend(Policy::default()),
                binding("field_array.at", 0, Some(length)),
                &[&length.to_string()],
                vec![array(length)]
            )
            .0
            .unwrap_err(),
            "refused:field-array-index"
        );
    }
}

#[test]
fn checked_access_rejects_attributes_wrong_ports_and_output_exhaustion() {
    for (b, args) in [
        (
            binding("matrix.get", 0, None),
            vec![matrix(0, 2, 3, &[]), Value::Index(1), Value::Index(2)],
        ),
        (
            binding("field_array.get", 0, Some(2)),
            vec![array(2), Value::Index(1)],
        ),
    ] {
        let sig = b.signature().unwrap();
        let names: Vec<_> = (0..args.len()).map(|i| format!("a{i}")).collect();
        for attrs in [vec!["0"], vec!["0", "1"]] {
            let bytes = program(
                std::slice::from_ref(&b),
                &sig.inputs,
                vec![serde_json::json!([
                    "op",
                    "get",
                    "b0",
                    attrs,
                    names,
                    ["out"]
                ])],
                &sig.outputs,
                &["out".into()],
            );
            assert_eq!(
                admit_supplied(&bytes, &backend(Policy::default()))
                    .err()
                    .unwrap()
                    .code,
                ErrorCode::Attributes
            );
        }
        let mut inputs = sig.inputs.clone();
        inputs[1] = scalar(0, 0).physical_type();
        let bytes = program(
            std::slice::from_ref(&b),
            &inputs,
            vec![serde_json::json!(["op", "get", "b0", [], names, ["out"]])],
            &sig.outputs,
            &["out".into()],
        );
        assert_eq!(
            admit_supplied(&bytes, &backend(Policy::default()))
                .err()
                .unwrap()
                .code,
            ErrorCode::Signature
        );
        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.output_limit = Some(0);
        assert_eq!(
            one(controlled, b, &[], args).0.unwrap_err(),
            "exhausted:output-bytes"
        );
    }
    for field in 1..FIELDS.len() {
        let b = binding("field_array.get", field, Some(2));
        let mut logical = b.clone();
        logical.implementation.clear();
        assert!(logical.logical_signature().is_ok());
        assert!(b.signature().is_err());
        assert!(backend(Policy::default()).binding_signature(&b).is_none());
    }
}
