//! Canonical framing and aggregate limits, independent of compiler producers.
#[cfg(feature = "test-utils")]
use zkc_runtime::interpreter::Runner;
mod common;
use serde_json::json;
use zkc_native::{G1, NativeBackend, NativeWireError as Error, Policy, Scalar, Value, Variant};
use zkc_runtime::vm::{DecodeReason, LogicalType, Value as RuntimeValue};
use zkc_test_support::variants::logical;
fn variant(ty: &str, tag: usize, values: Vec<Value>) -> Value {
    let ty = LogicalType::parse(ty).unwrap();
    Value::Variant(
        Variant::new(
            zkc_runtime::vm::PhysicalType::default_for(ty.clone()).unwrap(),
            tag,
            values,
        )
        .unwrap(),
    )
}
fn bounded(policy: Policy) -> NativeBackend {
    NativeBackend::new(policy, common::entry(None), Default::default()).unwrap()
}
fn roundtrip(value: &Value) -> Vec<u8> {
    let backend = common::ark_backend(None);
    let ty = value.physical_type();
    backend.validate_native_input(value).unwrap();
    let bytes = backend.encode_native_value(value).unwrap();
    let loaded = backend.decode_native_value(&ty, &bytes).unwrap();
    assert_eq!(backend.encode_native_value(&loaded).unwrap(), bytes);
    for i in 0..bytes.len() {
        assert!(
            matches!(
                backend.decode_native_value(&ty, &bytes[..i]),
                Err(Error::Invalid(_))
            ),
            "prefix {i}"
        );
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert_eq!(
        backend.decode_native_value(&ty, &extra).unwrap_err(),
        Error::Invalid(DecodeReason::Length)
    );
    for i in 0..6 {
        let mut wrong = bytes.clone();
        wrong[i] ^= 1;
        assert_eq!(
            backend.decode_native_value(&ty, &wrong).unwrap_err(),
            Error::Invalid(DecodeReason::Header)
        );
    }
    bytes
}
#[test]
fn complete_expected_types_frame_records_alternatives_and_dynamic_data() {
    let optional = logical(
        "Optional",
        json!([["none", []], ["some", ["field:bls12-381.fr"]]]),
    );
    let record = logical(
        "Packet",
        json!([[
            "record",
            [
                optional,
                "vector:bls12-381.fr",
                "groups:bls12-381.g1",
                "indices"
            ]
        ]]),
    );
    for n in [0usize, 1, 4] {
        for tag in 0..2 {
            let option = variant(
                &optional,
                tag,
                if tag == 0 {
                    vec![]
                } else {
                    vec![Value::Field(Scalar::from(9))]
                },
            );
            let value = variant(
                &record,
                0,
                vec![
                    option,
                    Value::Vector(
                        (0..n)
                            .map(|i| Scalar::from(i as u64))
                            .collect::<Vec<_>>()
                            .into(),
                    ),
                    Value::Groups(vec![G1::generator(); n].into()),
                    Value::Indices(vec![u64::MAX; n].into()),
                ],
            );
            let bytes = roundtrip(&value);
            assert_eq!(&bytes[..10], b"ZKCV\x00\x41\0\0\0\0");
        }
    }
    for value in [
        Value::Vector(vec![Scalar::from(3)].into()),
        Value::Groups(vec![G1::identity()].into()),
        Value::Indices(vec![7].into()),
    ] {
        roundtrip(&value);
    }
    // Same flattened scalar leaves, different structural meaning.
    let pair = logical(
        "Pair",
        json!([["record", [optional, "vector:bls12-381.fr"]]]),
    );
    let a = variant(
        &pair,
        0,
        vec![
            variant(&optional, 0, vec![]),
            Value::Vector(vec![Scalar::from(9)].into()),
        ],
    );
    let b = variant(
        &pair,
        0,
        vec![
            variant(&optional, 1, vec![Value::Field(Scalar::from(9))]),
            Value::Vector(vec![].into()),
        ],
    );
    assert_ne!(roundtrip(&a), roundtrip(&b));
}
#[test]
fn malformed_tags_lengths_and_scalars_keep_typed_errors() {
    let backend = common::ark_backend(None);
    let ty = logical(
        "Sum",
        json!([["none", []], ["data", ["bool", "vector:bls12-381.fr"]]]),
    );
    let value = variant(
        &ty,
        1,
        vec![
            Value::Bool(true),
            Value::Vector(vec![Scalar::from(1)].into()),
        ],
    );
    let bytes = roundtrip(&value);
    for (offset, fill, reason) in [
        (6, 2, DecodeReason::Header),
        (10, 255, DecodeReason::Length),
        (20, 2, DecodeReason::Boolean),
    ] {
        let mut bad = bytes.clone();
        bad[offset] = fill;
        assert_eq!(
            backend
                .decode_native_value(&value.physical_type(), &bad)
                .unwrap_err(),
            Error::Invalid(reason)
        );
    }
    let mut bad = bytes.clone();
    bad[35..67].fill(255);
    assert_eq!(
        backend
            .decode_native_value(&value.physical_type(), &bad)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Scalar)
    );
    for value in [
        Value::Vector(vec![Scalar::from(1)].into()),
        Value::Groups(vec![G1::generator()].into()),
        Value::Indices(vec![1].into()),
    ] {
        let mut bad = backend.encode_native_value(&value).unwrap();
        bad[6..10].fill(255);
        assert_eq!(
            backend
                .decode_native_value(&value.physical_type(), &bad)
                .unwrap_err(),
            Error::Limit
        );
    }
}
#[test]
fn inactive_unsupported_payloads_do_not_inherit_wire_authority() {
    let backend = common::ark_backend(None);
    for leaf in [
        "rng:bls12-381.fr",
        "prover_key:multilinear.kzg.bls12-381/0",
        "verifier_key:multilinear.kzg.bls12-381/0",
        "table:bls12-381.fr",
        "polynomial:bn254.fr",
        "opening_state:rows.merkle-keccak256.koala-bear/0",
    ] {
        let ty = logical("Optional", json!([["none", []], ["some", [leaf]]]));
        let value = variant(&ty, 0, vec![]);
        assert!(!zkc_native::has_native_wire(&value.physical_type()));
        assert!(matches!(
            backend.encode_native_value(&value),
            Err(Error::Backend(_))
        ));
        assert!(matches!(
            backend.decode_native_value(&value.physical_type(), b"ZKCV\x00\x41\0\0\0\0"),
            Err(Error::Backend(_))
        ));
    }
}
#[test]
fn aggregate_preflight_refuses_before_payload_construction_and_production_agrees() {
    let ty = logical(
        "Pair",
        json!([["record", ["vector:bls12-381.fr", "vector:bls12-381.fr"]]]),
    );
    let values = vec![Value::Vector(vec![Scalar::from(1); 32].into()); 2];
    let value = variant(&ty, 0, values.clone());
    let bytes = common::ark_backend(None)
        .encode_native_value(&value)
        .unwrap();
    // Both children fit individually; their descriptor-bearing record does not.
    let limited = bounded(Policy {
        max_value_bytes: 5120,
        ..Policy::default()
    });
    for v in values {
        limited.encode_native_value(&v).unwrap();
    }
    assert_eq!(
        limited.encode_native_value(&value).unwrap_err(),
        Error::Limit
    );
    assert_eq!(
        limited
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        Error::Limit
    );
    for ceiling in [0, 1024, 4096, 8192, 16384, 65536] {
        let limited = bounded(Policy {
            max_value_bytes: ceiling,
            ..Policy::default()
        });
        if let Ok(encoded) = limited.encode_native_value(&value) {
            limited
                .decode_native_value(&value.physical_type(), &encoded)
                .unwrap();
        }
        if let Ok(decoded) = limited.decode_native_value(&value.physical_type(), &bytes) {
            assert_eq!(limited.encode_native_value(&decoded).unwrap(), bytes);
        }
    }
    let limited = bounded(Policy {
        max_table_elements: 0,
        ..Policy::default()
    });
    assert_eq!(
        limited
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        Error::Limit
    );
}
#[cfg(feature = "test-utils")]
#[test]
fn nested_pcs_frames_require_the_authorized_setup_and_exact_metadata() {
    use std::sync::Arc;
    let bounds = Policy::default().ark_bounds();
    let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        1,
        &mut ark_std::rand::thread_rng(),
        &bounds,
    )
    .unwrap();
    let state = keys
        .prover_key()
        .commit(
            &zkc_kernels::arkworks::bls12_381::Table::from_logical_vec(
                vec![Scalar::from(2), Scalar::from(5)],
                &bounds,
            )
            .unwrap(),
        )
        .unwrap();
    let (x, proof) = state.open(&[Scalar::from(7)]).unwrap();
    let ty = logical(
        "Opening",
        json!([
            ["none", []],
            [
                "some",
                ["field:bls12-381.fr", "proof:multilinear.kzg.bls12-381/0"]
            ]
        ]),
    );
    assert!(zkc_native::requires_setup(LogicalType::parse(&ty).unwrap()));
    let value = variant(&ty, 1, vec![Value::Field(x), Value::Proof(Arc::new(proof))]);
    let backend = common::backend()
        .verifier(keys.verifier_key().clone())
        .build();
    let bytes = backend.encode_native_value(&value).unwrap();
    assert_eq!(
        backend
            .encode_native_value(
                &backend
                    .decode_native_value(&value.physical_type(), &bytes)
                    .unwrap()
            )
            .unwrap(),
        bytes
    );
    assert!(matches!(
        common::ark_backend(None).decode_native_value(&value.physical_type(), &bytes),
        Err(Error::Backend(_))
    ));
    let other = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        1,
        &mut ark_std::rand::thread_rng(),
        &bounds,
    )
    .unwrap();
    let wrong = common::backend()
        .verifier(other.verifier_key().clone())
        .build();
    assert_eq!(
        wrong
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Header)
    );
    assert!(matches!(
        wrong.encode_native_value(&value),
        Err(Error::Backend(_))
    ));
}

#[test]
fn collection_limits_accumulate_across_record_children() {
    for (leaf, values, policy) in [
        (
            "vector:bls12-381.fr",
            Value::Vector(vec![Scalar::from(1); 2].into()),
            Policy {
                max_table_elements: 3,
                ..Policy::default()
            },
        ),
        (
            "groups:bls12-381.g1",
            Value::Groups(vec![G1::generator(); 2].into()),
            Policy {
                max_groups: 3,
                ..Policy::default()
            },
        ),
        (
            "indices",
            Value::Indices(vec![1; 2].into()),
            Policy {
                max_table_elements: 3,
                ..Policy::default()
            },
        ),
    ] {
        let ty = logical("Pair", json!([["record", [leaf, leaf]]]));
        let value = variant(&ty, 0, vec![values.clone(), values.clone()]);
        let bytes = common::ark_backend(None)
            .encode_native_value(&value)
            .unwrap();
        let limited = bounded(policy);
        limited.encode_native_value(&values).unwrap();
        assert_eq!(
            limited.encode_native_value(&value).unwrap_err(),
            Error::Limit
        );
        assert_eq!(
            limited
                .decode_native_value(&value.physical_type(), &bytes)
                .unwrap_err(),
            Error::Limit
        );
    }
}
#[test]
fn immutable_variant_bounds_count_shared_payload_occurrences() {
    let mut ty = String::from("bool");
    let mut value = Value::Bool(true);
    for _ in 0..3 {
        ty = logical("Layer", json!([["record", [ty]]]));
        value = variant(&ty, 0, vec![value]);
    }
    let pair_type = LogicalType::parse(&logical(
        "SharedLayers",
        json!([["pair", [ty.clone(), ty]]]),
    ))
    .unwrap();
    let physical_type = zkc_runtime::vm::PhysicalType::default_for(pair_type).unwrap();
    // Expanded charges count both occurrences, even though cloned immutable
    // variants share their backing. Decoding retains that same profile.
    let expected = physical_type.descriptor_bytes() + 256 + 2 * 512 + 2 * value.retained_bytes();
    let pair = Value::Variant(Variant::new(physical_type, 0, vec![value.clone(), value]).unwrap());
    assert_eq!(pair.retained_bytes(), expected);
    let backend = common::ark_backend(None);
    let bytes = backend.encode_native_value(&pair).unwrap();
    let decoded = backend
        .decode_native_value(&pair.physical_type(), &bytes)
        .unwrap();
    assert_eq!(decoded.retained_bytes(), expected);
    assert_eq!(pair.clone().retained_bytes(), expected);
}
#[test]
fn formed_type_depth_and_leaf_preflight_define_the_boundary() {
    let mut ty = String::from("bool");
    let mut value = Value::Bool(true);
    for _ in 0..8 {
        ty = logical("Layer", json!([["record", [ty]]]));
        value = variant(&ty, 0, vec![value]);
    }
    roundtrip(&value);
    let ty = logical("Boolean", json!([["record", ["bool"]]]));
    let value = variant(&ty, 0, vec![Value::Bool(true)]);
    let mut bytes = roundtrip(&value);
    bytes[10..14].copy_from_slice(&1000u32.to_le_bytes());
    bytes.resize(1014, 0);
    // Fixed-width inconsistency wins over the conservative retained estimate.
    let limited = bounded(Policy {
        max_value_bytes: 2048,
        ..Policy::default()
    });
    assert_eq!(
        limited
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Length)
    );
    let groups = Value::Groups(vec![G1::generator()].into());
    let mut bytes = roundtrip(&groups);
    bytes[10..].fill(255);
    assert_eq!(
        common::ark_backend(None)
            .decode_native_value(&groups.physical_type(), &bytes)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Group)
    );
    assert!(std::mem::size_of::<G1>() <= 128);
}

#[test]
fn nested_fixed_arrays_keep_empty_shape_and_full_retained_charge() {
    for n in [0, 1, 4] {
        let leaf = format!("field_array<bls12-381.fr,{n}>");
        let ty = logical("Arrays", json!([["record", [leaf, leaf]]]));
        let array = Value::FieldArray(
            zkc_native::FieldArray::new(
                zkc_runtime::vm::PhysicalType::default_for(LogicalType::parse(&leaf).unwrap())
                    .unwrap(),
                vec![Scalar::from(3); n].into(),
            )
            .unwrap(),
        );
        let value = variant(&ty, 0, vec![array.clone(), array]);
        let bytes = roundtrip(&value);
        // The recursive decoder reserves two retained backings before payload
        // decoding. Small arrays include the complete field-array wrapper.
        let below_peak = bounded(Policy {
            max_value_bytes: value.retained_bytes() * 2 - 1,
            ..Policy::default()
        });
        assert_eq!(
            below_peak
                .decode_native_value(&value.physical_type(), &bytes)
                .unwrap_err(),
            Error::Limit,
            "array {n} must reserve its complete aggregate backing"
        );
        let at_peak = bounded(Policy {
            max_value_bytes: value.retained_bytes() * 2,
            ..Policy::default()
        });
        let decoded = at_peak
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap();
        assert_eq!(decoded.retained_bytes(), value.retained_bytes());
        assert_eq!(at_peak.encode_native_value(&decoded).unwrap(), bytes);
        if n > 0 {
            let mut malformed = bytes.clone();
            malformed[20..52].fill(255);
            assert_eq!(
                below_peak
                    .decode_native_value(&value.physical_type(), &malformed)
                    .unwrap_err(),
                Error::Limit,
                "allocation preflight must precede scalar decoding"
            );
        }
        for limit in [1024, 2048, 4096, 8192, 16384] {
            let backend = bounded(Policy {
                max_value_bytes: limit,
                ..Policy::default()
            });
            let encoded = backend.encode_native_value(&value);
            let decoded = backend.decode_native_value(&value.physical_type(), &bytes);
            assert_eq!(encoded.is_ok(), decoded.is_ok(), "array {n}, limit {limit}");
            if let Ok(decoded) = decoded {
                assert_eq!(backend.encode_native_value(&decoded).unwrap(), bytes);
            }
        }
        if n > 0 {
            let mut bad = bytes.clone();
            bad[20..52].fill(255);
            assert_eq!(
                common::ark_backend(None)
                    .decode_native_value(&value.physical_type(), &bad)
                    .unwrap_err(),
                Error::Invalid(DecodeReason::Scalar)
            );
        }
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn pcs_observation_uses_the_same_setup_check_before_advancing_history() {
    use std::sync::Arc;
    use zkc_runtime::{logical as encoding, vm::Identity};
    let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        1,
        &mut ark_std::rand::thread_rng(),
        &Policy::default().ark_bounds(),
    )
    .unwrap();
    let table = zkc_kernels::arkworks::bls12_381::Table::from_logical_vec(
        vec![Scalar::from(2), Scalar::from(5)],
        &Policy::default().ark_bounds(),
    )
    .unwrap();
    let state = keys.prover_key().commit(&table).unwrap();
    let ty = logical(
        "Record",
        json!([["record", ["commitment:multilinear.kzg.bls12-381/0"]]]),
    );
    let value = variant(
        &ty,
        0,
        vec![Value::Commitment(Arc::new(state.commitment().clone()))],
    );
    for configured in [false, true] {
        let mut backend = if configured {
            common::backend()
                .verifier(keys.verifier_key().clone())
                .build()
        } else {
            common::ark_backend(None)
        };
        let root = encoding::encode_tree(&json!(["test-root"])).unwrap();
        let state = backend
            .issue_transcript_for(Identity::Merlin3Fr64Be, common::domain(), 1, &root)
            .unwrap();
        let Value::Transcript(token) = &state else {
            panic!()
        };
        let token = token.clone();
        let t = state.physical_type().spelling();
        let inputs = json!([
            ["t", t],
            ["v", value.physical_type().spelling()],
            ["ix", "indices@native.indices/0"]
        ]);
        let origin = zkc_test_support::hex(
            &encoding::encode_tree(&json!([
                "zkc.native-origin-template/0",
                "main",
                [],
                [],
                ["message", "main", "message", "message", "P", "V"]
            ]))
            .unwrap(),
        );
        let program = json!([
            "zkc.program/0",
            [[
                "observe",
                "transcript.native.indexed.observe.data",
                ["merlin3.bls12-381.fr64be/0", ty],
                "arkworks/transcript.native.indexed.observe.data",
                []
            ]],
            [[
                "function",
                "observer",
                inputs,
                [t],
                [
                    [
                        "op",
                        "observe",
                        "observe",
                        [origin],
                        ["t", "v", "ix"],
                        ["next"]
                    ],
                    ["return", ["next"]]
                ],
                ["observer", []]
            ]],
            [[
                "participant",
                "participant",
                "main",
                "P",
                inputs,
                [t],
                [
                    ["local", "call", "observer", ["t", "v", "ix"], ["next"]],
                    ["return", ["next"]]
                ],
                []
            ]],
            [["entry", "main", [["P", "participant"]]]]
        ]);
        let admitted = zkc_runtime::vm::Program::decode(
            &serde_json::to_vec(&program).unwrap(),
            zkc_native::native_contracts(),
        )
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
        let runner = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![state, value.clone(), Value::Indices(vec![].into())],
        );
        let backend = match runner {
            Ok(runner) => {
                assert!(configured);
                let (outcome, backend) = common::finish(runner);
                outcome.unwrap();
                backend
            }
            Err(error) => {
                assert!(!configured);
                assert!(error.error.to_string().contains("unauthorized-setup"));
                error.backend
            }
        };
        assert_eq!(
            backend.observe(&token).unwrap().generation,
            u64::from(configured)
        );
        assert_eq!(backend.active_frames(), 0);
    }
}

#[test]
fn typed_variant_payloads_preserve_aggregate_group_limits() {
    let ty = logical(
        "Groups",
        json!([["pair", ["groups:bls12-381.g1", "groups:bls12-381.g1"]]]),
    );
    let value = variant(
        &ty,
        0,
        vec![Value::Groups(vec![G1::generator(); 3].into()); 2],
    );
    let bytes = bounded(Policy::default())
        .encode_native_value(&value)
        .unwrap();
    let low = bounded(Policy {
        max_groups: 4,
        ..Policy::default()
    });
    assert_eq!(low.validate_native_input(&value).unwrap_err(), Error::Limit);
    assert_eq!(
        low.decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        Error::Limit
    );
    let exact = bounded(Policy {
        max_groups: 6,
        max_wire_bytes: 0,
        ..Policy::default()
    });
    exact.validate_native_input(&value).unwrap();
}

#[test]
fn native_and_wire_collection_admission_agree_across_nested_shapes() {
    fn sequence(values: Vec<Value>) -> Value {
        Value::Sequence(
            zkc_native::Sequence::new(
                zkc_runtime::vm::PhysicalType::default_for(
                    zkc_runtime::vm::LogicalType::sequence(values[0].physical_type().logical())
                        .unwrap(),
                )
                .unwrap(),
                values,
                &Policy::default(),
            )
            .unwrap(),
        )
    }
    let vector = Value::Vector(vec![Scalar::from(3); 3].into());
    let groups = Value::Groups(vec![G1::generator(); 2].into());
    let mixed = logical(
        "Mixed",
        json!([["payload", ["indices", "vector:bls12-381.fr"]]]),
    );
    let corpus = [
        sequence(vec![sequence(vec![vector.clone(), vector.clone()]); 2]),
        sequence(vec![groups.clone(), groups]),
        variant(&mixed, 0, vec![Value::Indices(vec![1, 2].into()), vector]),
    ];
    let encoder = bounded(Policy::default());
    for value in corpus {
        let ty = value.physical_type();
        let bytes = encoder.encode_native_value(&value).unwrap();
        for elements in 0..=14 {
            for groups in 0..=6 {
                let backend = bounded(Policy {
                    max_table_elements: elements,
                    max_groups: groups,
                    ..Policy::default()
                });
                assert_eq!(
                    backend.validate_native_input(&value).is_ok(),
                    backend.native_input_retained_bytes(&ty, &bytes).is_ok(),
                    "{}: elements={elements}, groups={groups}",
                    ty.spelling(),
                );
            }
        }
    }
}

#[test]
fn host_assembly_measures_complete_type_counts_and_construction_peak() {
    let backend = common::ark_backend(None);
    let ty = LogicalType::parse(&logical("HostPair", json!([["pair", ["bool", "bool"]]]))).unwrap();
    let physical = zkc_runtime::vm::PhysicalType::default_for(ty.clone()).unwrap();
    let a = Value::Bool(false);
    let b = Value::Bool(true);
    let sizes = [
        backend.measure_native_input(&a).unwrap(),
        backend.measure_native_input(&b).unwrap(),
    ];
    let measured = backend
        .measure_native_variant(&physical, 0, &sizes)
        .unwrap();
    let value = Value::Variant(
        Variant::new(
            zkc_runtime::vm::PhysicalType::default_for(ty.clone()).unwrap(),
            0,
            vec![a, b],
        )
        .unwrap(),
    );
    assert_eq!(measured.retained_bytes(), value.retained_bytes());
    let limited = bounded(Policy {
        max_value_bytes: measured.retained_bytes() * 2 - 1,
        ..Policy::default()
    });
    assert_eq!(
        limited
            .measure_native_variant(&physical, 0, &sizes)
            .unwrap_err(),
        Error::Limit
    );
    let changed = [
        backend.measure_native_input(&Value::Index(0)).unwrap(),
        backend.measure_native_input(&Value::Bool(false)).unwrap(),
    ];
    assert!(
        backend
            .measure_native_variant(&physical, 0, &changed)
            .is_err()
    );
    assert!(
        backend
            .measure_native_variant(&physical, 1, &sizes)
            .is_err()
    );
    assert!(
        backend
            .measure_native_variant(&physical, 0, &sizes[..1])
            .is_err()
    );
}

#[test]
fn mixed_host_payloads_charge_wire_peak_with_retained_siblings() {
    let backend = common::ark_backend(None);
    let logical = LogicalType::parse(&logical(
        "Mixed",
        json!([["pair", ["vector:bls12-381.fr", "vector:bls12-381.fr"]]]),
    ))
    .unwrap();
    let ty = zkc_runtime::vm::PhysicalType::default_for(logical).unwrap();
    let vector = Value::Vector(vec![Scalar::from(1); 512].into());
    let wire = backend.encode_native_value(&vector).unwrap();
    let sizes = [
        backend.measure_native_input(&vector).unwrap(),
        backend
            .measure_native_wire(&vector.physical_type(), &wire)
            .unwrap(),
    ];
    let total = backend
        .measure_native_variant(&ty, 0, &sizes)
        .unwrap()
        .retained_bytes();
    let limit = total * 2;
    assert!(total + 3 * wire.len() > limit);
    let bounded = bounded(Policy {
        max_value_bytes: limit,
        ..Policy::default()
    });
    // Both individual children fit. Their combined live buffers do not.
    assert!(bounded.measure_native_input(&vector).is_ok());
    assert!(
        bounded
            .measure_native_wire(&vector.physical_type(), &wire)
            .is_ok()
    );
    assert_eq!(
        bounded.measure_native_variant(&ty, 0, &sizes).unwrap_err(),
        Error::Limit
    );
    let native = [
        bounded.measure_native_input(&vector).unwrap(),
        bounded.measure_native_input(&vector).unwrap(),
    ];
    assert!(bounded.measure_native_variant(&ty, 0, &native).is_ok());
}

#[test]
fn runtime_owned_measurements_preserve_nonwire_data_and_complete_counts() {
    use zkc_runtime::vm::PhysicalType;
    let polynomial = Value::Polynomial(vec![Scalar::from(7); 3].into());
    let sequence = Value::Sequence(
        zkc_native::Sequence::new(
            zkc_runtime::vm::PhysicalType::default_for(
                zkc_runtime::vm::LogicalType::sequence(polynomial.physical_type().logical())
                    .unwrap(),
            )
            .unwrap(),
            vec![polynomial.clone(), polynomial.clone()],
            &Policy::default(),
        )
        .unwrap(),
    );
    let ty = PhysicalType::default_for(
        LogicalType::parse(&logical(
            "Internal",
            json!([
                ["empty", []],
                [
                    "polynomials",
                    [sequence.physical_type().logical().spelling()]
                ]
            ]),
        ))
        .unwrap(),
    )
    .unwrap();
    let backend = bounded(Policy::default());
    assert!(backend.measure_native_input(&polynomial).is_err());
    assert!(backend.measure_native_input(&sequence).is_err());
    let sizes = [backend.measure_native_value(&sequence).unwrap()];
    let measured = backend.measure_native_variant(&ty, 1, &sizes).unwrap();
    let value = Value::Variant(Variant::new(ty.clone(), 1, vec![sequence]).unwrap());
    assert_eq!(measured.retained_bytes(), value.retained_bytes());
    assert_eq!(
        backend
            .measure_native_value(&value)
            .unwrap()
            .retained_bytes(),
        value.retained_bytes()
    );
    assert!(
        backend.encode_native_value(&value).is_err(),
        "measurement grants no codec"
    );
    for elements in [5, 6] {
        let backend = bounded(Policy {
            max_table_elements: elements,
            ..Policy::default()
        });
        let sizes = [
            backend.measure_native_value(&polynomial).unwrap(),
            backend.measure_native_value(&polynomial).unwrap(),
        ];
        let pair = PhysicalType::default_for(
            LogicalType::parse(&logical(
                "Pair",
                json!([[
                    "pair",
                    ["polynomial:bls12-381.fr", "polynomial:bls12-381.fr"]
                ]]),
            ))
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            backend.measure_native_variant(&pair, 0, &sizes).is_ok(),
            elements == 6
        );
        assert_eq!(backend.measure_native_value(&value).is_ok(), elements == 6);
        // Inactive payloads do not count, but their descriptor is retained.
        assert!(backend.measure_native_variant(&ty, 0, &[]).is_ok());
    }
    let affine = PhysicalType::default_for(
        LogicalType::parse(&logical(
            "Affine",
            json!([["empty", []], ["rng", ["rng:bls12-381.fr"]]]),
        ))
        .unwrap(),
    )
    .unwrap();
    assert!(
        backend.measure_native_variant(&affine, 0, &[]).is_err(),
        "inactive resource types remain affine"
    );
}

#[test]
fn runtime_owned_handle_collections_count_handles_and_keep_backing_limits() {
    use std::sync::Arc;
    use zkc_kernels::plonky3::oracle as tree;
    use zkc_native::{KoalaBear, merkle, oracle};
    use zkc_runtime::vm::{Backend, PhysicalType};
    let policy = Policy {
        max_table_elements: 8,
        ..Policy::default()
    };
    // Each table fits its constructor's policy. Sharing two handles does not
    // turn the collection into a table with sixteen numeric elements.
    let shape = tree::Shape::new(8, 1, policy.max_table_elements).unwrap();
    let (_, state) =
        tree::commit(vec![KoalaBear::default(); 8], shape, policy.max_value_bytes).unwrap();
    let state = oracle::State::Base(Arc::new(state));
    let (_, merkle) = zkc_kernels::plonky3::merkle::commit::<
        zkc_kernels::plonky3::merkle::poseidon2::Base,
    >(vec![KoalaBear::default(); 8], shape, policy.max_value_bytes)
    .unwrap();
    let merkle = merkle::State::Poseidon2KoalaBear(Arc::new(merkle));
    let collections = [
        (
            Value::OracleState(state.clone()),
            Value::OracleStates(oracle::Domain::Base, vec![state.clone(); 2].into()),
            Value::OracleStates(oracle::Domain::Base, vec![state.clone(); 5].into()),
            Value::OracleStates(oracle::Domain::Base, vec![state; 9].into()),
        ),
        (
            Value::MerkleTree(merkle.clone()),
            Value::MerkleTrees(
                merkle::Scheme::Poseidon2KoalaBear,
                vec![merkle.clone(); 2].into(),
            ),
            Value::MerkleTrees(
                merkle::Scheme::Poseidon2KoalaBear,
                vec![merkle.clone(); 5].into(),
            ),
            Value::MerkleTrees(merkle::Scheme::Poseidon2KoalaBear, vec![merkle; 9].into()),
        ),
    ];
    let backend = bounded(policy);
    for (state, collection, five, excessive) in collections {
        for (value, legal) in [(&state, true), (&collection, true), (&five, false)] {
            backend.validate_value(value).unwrap();
            assert!(
                backend.measure_native_input(value).is_err(),
                "public input stays closed"
            );
            assert!(
                backend.encode_native_value(value).is_err(),
                "measurement grants no codec"
            );
            let spelling = value.physical_type().logical().spelling();
            let ty = PhysicalType::default_for(
                LogicalType::parse(&logical("Handles", json!([["pair", [spelling, spelling]]])))
                    .unwrap(),
            )
            .unwrap();
            let sizes = [
                backend.measure_native_value(value).unwrap(),
                backend.measure_native_value(value).unwrap(),
            ];
            let pair = Value::Variant(
                Variant::new(ty.clone(), 0, vec![value.clone(), value.clone()]).unwrap(),
            );
            assert_eq!(
                backend.measure_native_variant(&ty, 0, &sizes).is_ok(),
                legal
            );
            assert_eq!(backend.measure_native_value(&pair).is_ok(), legal);
            let short = bounded(Policy {
                max_value_bytes: value.retained_bytes() - 1,
                ..policy
            });
            assert!(short.validate_value(value).is_err());
            assert_eq!(short.measure_native_value(value).unwrap_err(), Error::Limit);
        }
        assert!(
            backend.validate_value(&excessive).is_err(),
            "owner handle limit still applies"
        );
        assert_eq!(
            backend.measure_native_value(&excessive).unwrap_err(),
            Error::Limit
        );
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn singular_pcs_handles_do_not_invent_backing_element_collection_counts() {
    use std::sync::Arc;
    use zkc_runtime::vm::{Backend, PhysicalType};
    let policy = Policy {
        max_table_elements: 8,
        ..Policy::default()
    };
    let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        3,
        &mut ark_std::rand::thread_rng(),
        &policy.ark_bounds(),
    )
    .unwrap();
    let table = zkc_kernels::arkworks::bls12_381::Table::from_logical_vec(
        vec![Scalar::from(7); 8],
        &policy.ark_bounds(),
    )
    .unwrap();
    let state = keys.prover_key().commit(&table).unwrap();
    let backend = common::backend()
        .policy(policy)
        .verifier(keys.verifier_key().clone())
        .build();
    for value in [
        Value::ProverKey(Arc::new(keys.prover_key().clone())),
        Value::VerifierKey(Arc::new(keys.verifier_key().clone())),
        Value::OpeningState(Arc::new(state)),
    ] {
        backend.validate_value(&value).unwrap();
        let spelling = value.physical_type().logical().spelling();
        let ty = PhysicalType::default_for(
            LogicalType::parse(&logical("Handles", json!([["pair", [spelling, spelling]]])))
                .unwrap(),
        )
        .unwrap();
        let sizes = [
            backend.measure_native_value(&value).unwrap(),
            backend.measure_native_value(&value).unwrap(),
        ];
        assert!(backend.measure_native_variant(&ty, 0, &sizes).is_ok());
        let pair = Value::Variant(Variant::new(ty.clone(), 0, vec![value.clone(), value]).unwrap());
        assert!(backend.measure_native_value(&pair).is_ok());
        assert!(backend.measure_native_input(&pair).is_err());
        assert!(backend.encode_native_value(&pair).is_err());
    }
}
