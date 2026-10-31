//! Selected contractions through independent admission and native providers.
#[path = "domains/support.rs"]
mod support;

use p3_field::BasedVectorSpace;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use serde_json::json;
use support::{Controlled, assert_value, backend, one, program};
use zkc_cpu::{Bn254Scalar, KoalaBear, KoalaBearExt8, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::vm::{Backend, ErrorCode, OperationBinding, Value as _};

const FIELDS: [(&str, &str); 5] = [
    ("bls12-381.fr", "arkworks"),
    ("bn254.fr", "arkworks"),
    ("ristretto255.scalar", "dalek"),
    ("koala-bear", "plonky3"),
    ("koala-bear.ext8-binomial3", "plonky3"),
];
const CONTRACTIONS: [&str; 2] = ["matrix.row_dot", "matrix.column_dot"];

fn binding(field: usize, contract: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: vec![FIELDS[field].0.into()],
        implementation: format!("{}/{contract}", FIELDS[field].1),
        physical_arguments: vec![],
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

fn vector(field: usize, numbers: &[u64]) -> Value {
    macro_rules! make {
        ($constructor:ident, $convert:expr) => {
            Value::$constructor(
                &numbers.iter().map(|&n| ($convert)(n)).collect::<Vec<_>>(),
                &Policy::default(),
            )
            .unwrap()
        };
    }
    match field {
        0 => make!(vector, Scalar::from),
        1 => make!(bn254_vector, Bn254Scalar::from),
        2 => make!(ristretto_vector, RistrettoScalar::from),
        3 => make!(koala_bear_vector, |n| KoalaBear::new(n as u32)),
        4 => make!(koala_bear_ext8_vector, |n| KoalaBearExt8::from(
            KoalaBear::new(n as u32)
        )),
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
fn sparse_contractions_match_coordinate_oracle_in_every_installed_field() {
    let mut rng = StdRng::seed_from_u64(90117);
    for field in 0..FIELDS.len() {
        for (rows, columns) in [(0, 7), (9, 0), (1, 1), (5, 7), (17, 11)] {
            let entries = (0..rows)
                .flat_map(|r| (0..columns).map(move |c| (r as u32, c as u32)))
                .filter_map(|(r, c)| {
                    if rng.random_ratio(1, 4) {
                        Some((r, c, rng.random_range(1..1000)))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let m = matrix(field, rows, columns, &entries);
            for (contract, inner, selected) in [
                ("matrix.row_dot", columns, rows),
                ("matrix.column_dot", rows, columns),
            ] {
                let numbers = (0..inner)
                    .map(|_| rng.random_range(0..1000))
                    .collect::<Vec<u64>>();
                let v = vector(field, &numbers);
                let operation = binding(field, contract);
                let signature = operation.signature().unwrap();
                assert_eq!(
                    signature.inputs,
                    [
                        m.physical_type(),
                        v.physical_type(),
                        Value::Index(0).physical_type()
                    ]
                );
                assert_eq!(signature.outputs, [scalar(field, 0).physical_type()]);
                assert_eq!(
                    backend(Policy::default()).binding_signature(&operation),
                    Some(signature)
                );
                for index in 0..selected {
                    let expected = entries
                        .iter()
                        .filter_map(|&(r, c, a)| {
                            let (outer, inner) = if contract == "matrix.row_dot" {
                                (r, c)
                            } else {
                                (c, r)
                            };
                            (outer as usize == index).then(|| a * numbers[inner as usize])
                        })
                        .sum();
                    let result = one(
                        backend(Policy::default()),
                        operation.clone(),
                        &[],
                        vec![m.clone(), v.clone(), Value::Index(index as u64)],
                    )
                    .0
                    .unwrap();
                    assert_eq!(result.len(), 1);
                    assert_value(&result[0], &scalar(field, expected));
                    assert_eq!(result[0].retained_bytes(), zkc_cpu::VALUE_SLOT_BYTES);
                }
            }
        }
        // Include empty rows/columns between occupied ranges and after the last range.
        let m = matrix(field, 4, 4, &[(0, 0, 3), (2, 2, 5)]);
        for contract in CONTRACTIONS {
            for index in [1, 3] {
                let result = one(
                    backend(Policy::default()),
                    binding(field, contract),
                    &[],
                    vec![m.clone(), vector(field, &[2; 4]), Value::Index(index)],
                )
                .0
                .unwrap();
                assert_value(&result[0], &scalar(field, 0));
            }
        }
    }
}

#[test]
fn extension_contractions_multiply_non_base_coordinates() {
    // X * X^7 = 3 in the installed X^8 - 3 basis, independently of kernel arithmetic.
    let x = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(u32::from(i == 1)));
    let x7 = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(u32::from(i == 7)));
    let p = Policy::default();
    let m = Value::koala_bear_ext8_matrix(2, 2, &[(0, 1, x), (1, 0, x7)], &p).unwrap();
    let v = Value::koala_bear_ext8_vector(&[x, x7], &p).unwrap();
    let x2 = Value::KoalaBearExt8Field(KoalaBearExt8::from_basis_coefficients_fn(|i| {
        KoalaBear::new(u32::from(i == 2))
    }));
    for (contract, index, expected) in [
        ("matrix.row_dot", 0, scalar(4, 3)),
        ("matrix.column_dot", 1, x2),
    ] {
        let result = one(
            backend(p),
            binding(4, contract),
            &[],
            vec![m.clone(), v.clone(), Value::Index(index)],
        )
        .0
        .unwrap();
        assert_value(&result[0], &expected);
    }
}

#[test]
fn contractions_refuse_shape_before_index_including_empty_and_wide_indices() {
    for field in 0..FIELDS.len() {
        for contract in CONTRACTIONS {
            let row = contract == "matrix.row_dot";
            let m = matrix(field, 2, 3, &[]);
            let (inner, selected) = if row { (3, 2) } else { (2, 3) };
            for index in [selected, 1 << 32, u64::MAX] {
                for length in [inner - 1, inner, inner + 1] {
                    assert_eq!(
                        one(
                            backend(Policy::default()),
                            binding(field, contract),
                            &[],
                            vec![
                                m.clone(),
                                vector(field, &vec![1; length]),
                                Value::Index(index)
                            ]
                        )
                        .0
                        .unwrap_err(),
                        if length == inner {
                            "refused:matrix-index"
                        } else {
                            "refused:matrix-shape"
                        }
                    );
                }
            }
            for (rows, columns, length) in if row {
                [(0, 0, 0), (0, 3, 3)]
            } else {
                [(0, 0, 0), (2, 0, 2)]
            } {
                assert_eq!(
                    one(
                        backend(Policy::default()),
                        binding(field, contract),
                        &[],
                        vec![
                            matrix(field, rows, columns, &[]),
                            vector(field, &vec![1; length]),
                            Value::Index(0)
                        ]
                    )
                    .0
                    .unwrap_err(),
                    "refused:matrix-index"
                );
            }
        }
    }
}

#[test]
fn contractions_reserve_only_one_scalar_even_for_empty_or_large_selected_dimensions() {
    for field in 0..FIELDS.len() {
        for contract in CONTRACTIONS {
            let row = contract == "matrix.row_dot";
            for empty_inner in [false, true] {
                let (inner, entries, expected) = if empty_inner {
                    (0, vec![], 0)
                } else {
                    (1, vec![(0, 0, 7)], 21)
                };
                let (rows, columns) = if row { (65536, inner) } else { (inner, 65536) };
                let args = vec![
                    matrix(field, rows, columns, &entries),
                    vector(field, &vec![3; inner]),
                    Value::Index(0),
                ];
                for limit in [
                    0,
                    zkc_cpu::VALUE_SLOT_BYTES - 1,
                    zkc_cpu::VALUE_SLOT_BYTES,
                ] {
                    let mut controlled = Controlled::new(backend(Policy::default()));
                    controlled.output_limit = Some(limit);
                    let (result, observed) =
                        one(controlled, binding(field, contract), &[], args.clone());
                    if limit < zkc_cpu::VALUE_SLOT_BYTES {
                        assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
                        assert!(observed.outputs.is_empty());
                    } else {
                        let result = result.unwrap();
                        assert_eq!(result.len(), 1);
                        assert_eq!(result[0].retained_bytes(), zkc_cpu::VALUE_SLOT_BYTES);
                        assert_value(&result[0], &scalar(field, expected));
                    }
                }
                // A full product would require 65536 outputs and fail this policy.
                let p = Policy {
                    max_table_elements: 1,
                    max_value_bytes: 1024,
                    ..Policy::default()
                };
                assert_value(
                    &one(backend(p), binding(field, contract), &[], args)
                        .0
                        .unwrap()[0],
                    &scalar(field, expected),
                );
            }
            let (rows, columns) = if row { (65536, 0) } else { (0, 65536) };
            let p = Policy {
                max_table_elements: 1,
                max_value_bytes: zkc_cpu::VALUE_SLOT_BYTES,
                ..Policy::default()
            };
            assert_value(
                &one(
                    backend(p),
                    binding(field, contract),
                    &[],
                    vec![
                        matrix(field, rows, columns, &[]),
                        vector(field, &[]),
                        Value::Index(65535),
                    ],
                )
                .0
                .unwrap()[0],
                &scalar(field, 0),
            );
        }
    }
}

#[test]
fn maximum_valid_shape_contracts_the_last_row_or_column_without_dense_output() {
    for field in 0..FIELDS.len() {
        let m = matrix(
            field,
            65536,
            65536,
            &[(0, 65535, 3), (65535, 0, 5), (65535, 65535, 7)],
        );
        let mut numbers = vec![0; 65536];
        numbers[0] = 11;
        numbers[65535] = 13;
        let v = vector(field, &numbers);
        for (contract, expected) in [("matrix.row_dot", 146), ("matrix.column_dot", 124)] {
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.output_limit = Some(zkc_cpu::VALUE_SLOT_BYTES);
            let result = one(
                controlled,
                binding(field, contract),
                &[],
                vec![m.clone(), v.clone(), Value::Index(65535)],
            )
            .0
            .unwrap();
            assert_value(&result[0], &scalar(field, expected));
        }
    }
}

#[test]
fn native_reader_refuses_contraction_port_attribute_and_provider_mutations() {
    for (field, &(_, expected_provider)) in FIELDS.iter().enumerate() {
        for contract in CONTRACTIONS {
            let operation = binding(field, contract);
            let signature = operation.signature().unwrap();
            let mut wrong_field = signature.inputs.clone();
            wrong_field[1] = vector((field + 1) % FIELDS.len(), &[]).physical_type();
            for (inputs, args, outputs, attrs, code) in [
                (
                    signature.inputs.clone(),
                    vec!["a0", "a1"],
                    signature.outputs.clone(),
                    vec![],
                    ErrorCode::Signature,
                ),
                (
                    signature.inputs.clone(),
                    vec!["a0", "a2", "a1"],
                    signature.outputs.clone(),
                    vec![],
                    ErrorCode::Signature,
                ),
                (
                    wrong_field,
                    vec!["a0", "a1", "a2"],
                    signature.outputs.clone(),
                    vec![],
                    ErrorCode::Signature,
                ),
                (
                    signature.inputs.clone(),
                    vec!["a0", "a1", "a2"],
                    vec![signature.inputs[1].clone()],
                    vec![],
                    ErrorCode::Signature,
                ),
                (
                    signature.inputs.clone(),
                    vec!["a0", "a1", "a2"],
                    signature.outputs.clone(),
                    vec!["0"],
                    ErrorCode::Attributes,
                ),
            ] {
                let bytes = program(
                    std::slice::from_ref(&operation),
                    &inputs,
                    vec![json!(["op", "contraction", "b0", attrs, args, ["out"]])],
                    &outputs,
                    &["out".into()],
                );
                assert_eq!(
                    zkc_runtime::vm::Program::decode(&bytes, zkc_cpu::cpu_contracts())
                        .and_then(|program| {
                            program.check_installation(&backend(Policy::default()))?;
                            Ok(program)
                        })
                        .unwrap_err()
                        .code,
                    code
                );
            }
            for provider in ["arkworks", "dalek", "plonky3", "missing"] {
                let changed = OperationBinding {
                    implementation: format!("{provider}/{contract}"),
                    ..operation.clone()
                };
                assert_eq!(
                    backend(Policy::default())
                        .binding_signature(&changed)
                        .is_some(),
                    provider == expected_provider
                );
            }
            let args = vec![
                matrix(field, 1, 1, &[(0, 0, 7)]),
                vector(field, &[3]),
                Value::Index(0),
            ];
            for wrong in [
                scalar(field, 7),
                matrix((field + 1) % FIELDS.len(), 1, 1, &[]),
            ] {
                let mut controlled = Controlled::new(backend(Policy::default()));
                controlled.substitute = Some(wrong);
                assert_eq!(
                    one(controlled, operation.clone(), &[], args.clone())
                        .0
                        .unwrap_err(),
                    "refused:kernel-operands"
                );
            }
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.attributes = Some(vec!["0".into()]);
            assert_eq!(
                one(controlled, operation.clone(), &[], args.clone())
                    .0
                    .unwrap_err(),
                "refused:kernel-attributes"
            );
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.binding = Some(OperationBinding {
                contract: "matrix.bilinear".into(),
                implementation: format!("{expected_provider}/matrix.bilinear"),
                arguments: operation.arguments.clone(),
                physical_arguments: vec![],
            });
            assert_eq!(
                one(controlled, operation, &[], args).0.unwrap_err(),
                "refused:kernel-binding"
            );
        }
    }
}
