//! Canonical framing and aggregate limits, independent of compiler producers.
mod common;
use serde_json::json;
use zkc_backends::{
    GroupPoint, NativeBackend, NativeWireError as Error, Policy, Scalar, Value, Variant,
};
use zkc_runtime::interactive::{DecodeReason, LogicalType, Value as RuntimeValue};
use zkc_test_support::variants::logical;
fn variant(ty: &str, tag: usize, values: Vec<Value>) -> Value {
    let ty = LogicalType::parse(ty).unwrap();
    Value::Variant(Variant::new(ty.variant_descriptor().unwrap().clone(), tag, values).unwrap())
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
                    Value::Groups(vec![GroupPoint::generator(); n].into()),
                    Value::Indices(vec![u64::MAX; n].into()),
                ],
            );
            let bytes = roundtrip(&value);
            assert_eq!(&bytes[..10], b"ZKCV\x01\x41\0\0\0\0");
        }
    }
    for value in [
        Value::Vector(vec![Scalar::from(3)].into()),
        Value::Groups(vec![GroupPoint::identity()].into()),
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
        Value::Groups(vec![GroupPoint::generator()].into()),
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
        "prover_key:multilinear.kzg.bls12-381/1",
        "verifier_key:multilinear.kzg.bls12-381/1",
        "table:bls12-381.fr",
        "polynomial:bn254.fr",
        "opening_state:rows.merkle-keccak256.koala-bear/1",
    ] {
        let ty = logical("Optional", json!([["none", []], ["some", [leaf]]]));
        let value = variant(&ty, 0, vec![]);
        assert!(!zkc_backends::has_native_wire(&value.physical_type()));
        assert!(matches!(
            backend.encode_native_value(&value),
            Err(Error::Backend(_))
        ));
        assert!(matches!(
            backend.decode_native_value(&value.physical_type(), b"ZKCV\x01\x41\0\0\0\0"),
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
    let keys = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
    let state = keys
        .prover_key()
        .commit(
            &zkc_arkworks::Table::from_logical_vec(vec![Scalar::from(2), Scalar::from(5)], &bounds)
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
                ["field:bls12-381.fr", "proof:multilinear.kzg.bls12-381/1"]
            ]
        ]),
    );
    assert!(zkc_backends::requires_setup(
        LogicalType::parse(&ty).unwrap()
    ));
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
    let other = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
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
            Value::Groups(vec![GroupPoint::generator(); 2].into()),
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
    let groups = Value::Groups(vec![GroupPoint::generator()].into());
    let mut bytes = roundtrip(&groups);
    bytes[10..].fill(255);
    assert_eq!(
        common::ark_backend(None)
            .decode_native_value(&groups.physical_type(), &bytes)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Group)
    );
    assert!(std::mem::size_of::<GroupPoint>() <= 128);
}

#[test]
fn nested_fixed_arrays_keep_empty_shape_and_full_retained_charge() {
    for n in [0, 1, 4] {
        let leaf = format!("field_array<bls12-381.fr,{n}>");
        let ty = logical("Arrays", json!([["record", [leaf, leaf]]]));
        let array = Value::FieldArray(
            zkc_backends::FieldArray::new(
                LogicalType::parse(&leaf).unwrap(),
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
    use zkc_runtime::{
        interactive::{Identity, Runner, admit_supplied},
        logical as encoding,
    };
    let keys =
        zkc_arkworks::Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    let table = zkc_arkworks::Table::from_logical_vec(
        vec![Scalar::from(2), Scalar::from(5)],
        &Policy::default().ark_bounds(),
    )
    .unwrap();
    let state = keys.prover_key().commit(&table).unwrap();
    let ty = logical(
        "Record",
        json!([["record", ["commitment:multilinear.kzg.bls12-381/1"]]]),
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
            ["ix", "indices@native.indices/1"]
        ]);
        let origin = zkc_test_support::hex(
            &encoding::encode_tree(&json!([
                "zkc.native-origin-template/1",
                "main",
                [],
                [],
                ["message", "main", "message", "message", "P", "V"]
            ]))
            .unwrap(),
        );
        let program = json!([
            "zkc.program/2",
            [[
                "observe",
                "transcript.native.indexed.observe.data",
                ["merlin3.bls12-381.fr64be/1", ty],
                "arkworks/transcript.native.indexed.observe.data"
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
        let admitted = admit_supplied(&serde_json::to_vec(&program).unwrap(), &backend).unwrap();
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
        vec![Value::Groups(vec![GroupPoint::generator(); 3].into()); 2],
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
            zkc_backends::Sequence::new(
                values[0].physical_type().logical(),
                values,
                &Policy::default(),
            )
            .unwrap(),
        )
    }
    let vector = Value::Vector(vec![Scalar::from(3); 3].into());
    let groups = Value::Groups(vec![GroupPoint::generator(); 2].into());
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
    let physical = zkc_runtime::interactive::PhysicalType::default_for(ty.clone()).unwrap();
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
        Variant::new(ty.variant_descriptor().unwrap().clone(), 0, vec![a, b]).unwrap(),
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
    let ty = zkc_runtime::interactive::PhysicalType::default_for(logical).unwrap();
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
