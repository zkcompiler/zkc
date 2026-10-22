//! Exact public bytes and typed refusal controls for the native joint profile.
mod common;
use common::ark_backend;
use zkc_native::{
    GroupPoint, NativeBackend, NativeWireError, Policy, Scalar, Value, native_wire_size,
};
use zkc_runtime::host::wire::{WireBackend, WireError};
use zkc_runtime::vm::{DecodeReason, PhysicalType, Value as RuntimeValue};

#[test]
fn fixed_group_measurement_preserves_standalone_and_nested_collection_limits() {
    let backend = NativeBackend::new(
        Policy {
            max_groups: 0,
            ..Policy::default()
        },
        common::entry(None),
        Default::default(),
    )
    .unwrap();
    let ordinary = ark_backend(None);
    let point = Value::Curve(GroupPoint::generator());
    let ty = point.physical_type();
    let bytes = ordinary.encode_native_value(&point).unwrap();
    assert!(backend.decode_native_value(&ty, &bytes).is_ok());
    let measured = backend.measure_native_wire(&ty, &bytes).unwrap();
    assert!(backend.decoding_bound(&ty, &bytes).is_ok());
    // A root leaf is allowed, but its count must survive when it becomes a
    // child of a complete nested message.
    let sequence = Value::Sequence(
        zkc_native::Sequence::new(ty.logical(), vec![point], &Policy::default()).unwrap(),
    );
    let nested = ordinary.encode_native_value(&sequence).unwrap();
    assert_eq!(
        backend
            .measure_native_wire(&sequence.physical_type(), &nested)
            .unwrap_err(),
        NativeWireError::Limit
    );
    assert!(measured.retained_bytes() > 0);
    let logical = zkc_test_support::variants::logical(
        "PointMessage",
        serde_json::json!([["point", [ty.logical().spelling()]]]),
    );
    let variant =
        PhysicalType::default_for(zkc_runtime::vm::LogicalType::parse(&logical).unwrap()).unwrap();
    assert_eq!(
        backend
            .measure_native_variant(&variant, 0, &[measured])
            .unwrap_err(),
        NativeWireError::Limit
    );
}

#[test]
fn standalone_table_measurement_uses_table_decoder_limits() {
    let value = Value::table(&[Scalar::from(7)], &Policy::default()).unwrap();
    let ty = value.physical_type();
    let bytes = ark_backend(None).encode_native_value(&value).unwrap();
    assert_eq!(bytes.len(), 42);
    assert_eq!(value.retained_bytes(), 288);
    let policy = Policy {
        max_arity: 0,
        max_table_elements: 1,
        max_groups: 0,
        max_wire_bytes: bytes.len(),
        max_value_bytes: 600,
        ..Policy::default()
    };
    for max_value_bytes in [554, 600] {
        let backend = NativeBackend::new(
            Policy {
                max_value_bytes,
                ..policy
            },
            common::entry(None),
            Default::default(),
        )
        .unwrap();
        assert_eq!(backend.encode_native_value(&value).unwrap(), bytes);
        let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
        backend.validate_native_input(&decoded).unwrap();
        assert_eq!(
            backend
                .measure_native_wire(&ty, &bytes)
                .unwrap()
                .retained_bytes(),
            value.retained_bytes()
        );
        assert!(backend.decoding_bound(&ty, &bytes).is_ok());
        // Measurement grants no scalar validity: decoding remains independent.
        let mut noncanonical = bytes.clone();
        noncanonical[10..].fill(255);
        assert!(backend.measure_native_wire(&ty, &noncanonical).is_ok());
        assert_eq!(
            backend.decode_native_value(&ty, &noncanonical).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Scalar)
        );
    }
    for policy in [
        Policy {
            max_value_bytes: 553,
            ..policy
        },
        Policy {
            max_table_elements: 0,
            ..policy
        },
        Policy {
            max_wire_bytes: bytes.len() - 1,
            ..policy
        },
    ] {
        let backend = NativeBackend::new(policy, common::entry(None), Default::default()).unwrap();
        assert_eq!(
            backend.measure_native_wire(&ty, &bytes).unwrap_err(),
            NativeWireError::Limit
        );
        assert_eq!(
            backend.decode_native_value(&ty, &bytes).unwrap_err(),
            NativeWireError::Limit
        );
    }
}

#[test]
fn standalone_group_collection_measurement_ignores_numeric_element_ceiling() {
    let value = Value::Groups(vec![GroupPoint::generator()].into());
    let ty = value.physical_type();
    let bytes = ark_backend(None).encode_native_value(&value).unwrap();
    let policy = Policy {
        max_table_elements: 0,
        max_groups: 1,
        max_wire_bytes: bytes.len(),
        max_value_bytes: 768,
        ..Policy::default()
    };
    let backend = NativeBackend::new(policy, common::entry(None), Default::default()).unwrap();
    assert_eq!(backend.encode_native_value(&value).unwrap(), bytes);
    let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
    backend.validate_native_input(&decoded).unwrap();
    assert_eq!(
        backend
            .measure_native_wire(&ty, &bytes)
            .unwrap()
            .retained_bytes(),
        384
    );
    assert!(backend.decoding_bound(&ty, &bytes).is_ok());
    let mut noncanonical = bytes.clone();
    noncanonical[10..].fill(255);
    assert!(backend.measure_native_wire(&ty, &noncanonical).is_ok());
    assert_eq!(
        backend.decode_native_value(&ty, &noncanonical).unwrap_err(),
        NativeWireError::Invalid(DecodeReason::Group)
    );
    for policy in [
        Policy {
            max_groups: 0,
            ..policy
        },
        Policy {
            max_value_bytes: 767,
            ..policy
        },
        Policy {
            max_wire_bytes: bytes.len() - 1,
            ..policy
        },
    ] {
        let backend = NativeBackend::new(policy, common::entry(None), Default::default()).unwrap();
        assert_eq!(
            backend.measure_native_wire(&ty, &bytes).unwrap_err(),
            NativeWireError::Limit
        );
        assert_eq!(
            backend.decode_native_value(&ty, &bytes).unwrap_err(),
            NativeWireError::Limit
        );
    }
}

#[test]
fn standalone_collection_counts_survive_later_variant_assembly() {
    for value in [
        Value::table(&[Scalar::from(1), Scalar::from(2)], &Policy::default()).unwrap(),
        Value::Groups(vec![GroupPoint::generator(); 2].into()),
    ] {
        let ty = value.physical_type();
        let bytes = ark_backend(None).encode_native_value(&value).unwrap();
        let logical = zkc_test_support::variants::logical(
            "CollectionPair",
            serde_json::json!([["pair", [ty.logical().spelling(), ty.logical().spelling()]]]),
        );
        let variant =
            PhysicalType::default_for(zkc_runtime::vm::LogicalType::parse(&logical).unwrap())
                .unwrap();
        for ceiling in [3, 4] {
            let backend = NativeBackend::new(
                Policy {
                    max_table_elements: ceiling,
                    max_groups: ceiling,
                    ..Policy::default()
                },
                common::entry(None),
                Default::default(),
            )
            .unwrap();
            let children = [
                backend.measure_native_wire(&ty, &bytes).unwrap(),
                backend.measure_native_wire(&ty, &bytes).unwrap(),
            ];
            let measured = backend.measure_native_variant(&variant, 0, &children);
            if ceiling == 3 {
                // Three nodes fit; the four retained collection elements do not.
                assert_eq!(measured.unwrap_err(), NativeWireError::Limit);
            } else {
                assert!(measured.is_ok());
            }
        }
    }
}

#[test]
fn native_frames_decode_exact_values_and_refuse_malformed_bytes() {
    let backend = ark_backend(None);
    for (value, width) in [
        (Value::Index(0), 14),
        (Value::Index(u64::MAX), 14),
        (Value::Bool(false), 7),
        (Value::Bool(true), 7),
        (Value::Field(Scalar::from(19)), 38),
        (Value::Curve(GroupPoint::identity()), 54),
        (
            Value::Curve(GroupPoint::generator().scale(Scalar::from(17))),
            54,
        ),
    ] {
        let ty = value.physical_type();
        assert_eq!(native_wire_size(&ty), Some(width));
        let bytes = backend.encode_native_value(&value).unwrap();
        assert_eq!(bytes.len(), width);
        let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
        assert_eq!(backend.encode_native_value(&decoded).unwrap(), bytes);
        for end in 0..width {
            assert_eq!(
                backend.decode_native_value(&ty, &bytes[..end]).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Length)
            );
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert_eq!(
            backend.decode_native_value(&ty, &extra).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Length)
        );
        for i in 0..6 {
            let mut wrong = bytes.clone();
            wrong[i] ^= 1;
            assert_eq!(
                backend.decode_native_value(&ty, &wrong).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Header)
            );
        }
    }
}
#[test]
fn invalid_boolean_scalar_and_group_encodings_have_closed_reasons() {
    let backend = ark_backend(None);
    let boolean = Value::Bool(false).physical_type();
    for b in 2..=255 {
        let mut bytes = b"ZKCV\x00\x05".to_vec();
        bytes.push(b);
        assert_eq!(
            backend.decode_native_value(&boolean, &bytes).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Boolean)
        );
    }
    let field = Value::Field(Scalar::from(0)).physical_type();
    // Fr modulus in canonical little-endian integer bytes: it must not reduce.
    let modulus =
        zkc_test_support::unhex("01000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73");
    for payload in [modulus, vec![255; 32]] {
        let mut bytes = b"ZKCV\x00\x01".to_vec();
        bytes.extend(payload);
        assert_eq!(
            backend.decode_native_value(&field, &bytes).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Scalar)
        );
    }
    let group = Value::Curve(GroupPoint::identity()).physical_type();
    let mut nonsubgroup = vec![0; 48];
    nonsubgroup[0] = 0x80;
    let mut infinity = vec![0; 48];
    infinity[0] = 0xc0;
    infinity[47] = 1;
    for payload in [nonsubgroup, infinity, vec![255; 48], vec![0; 48]] {
        let mut bytes = b"ZKCV\x00\x09".to_vec();
        bytes.extend(payload);
        assert_eq!(
            backend.decode_native_value(&group, &bytes).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Group)
        );
    }
}
#[test]
fn policy_failure_and_other_providers_never_become_decode_stops() {
    let limited = NativeBackend::new(
        Policy {
            max_wire_bytes: 6,
            ..Policy::default()
        },
        common::entry(None),
        Default::default(),
    )
    .unwrap();
    let value = Value::Bool(true);
    let bytes = ark_backend(None).encode_native_value(&value).unwrap();
    assert_eq!(
        limited
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        NativeWireError::Limit
    );
    assert_eq!(
        limited.encode_native_value(&value).unwrap_err(),
        NativeWireError::Limit
    );
    let mut wrong = bytes;
    wrong.push(0);
    assert_eq!(
        limited
            .decode_native_value(&value.physical_type(), &wrong)
            .unwrap_err(),
        NativeWireError::Invalid(DecodeReason::Length)
    );
    let ty = PhysicalType::parse("polynomial:bn254.fr@arkworks.bn254-fr-polynomial/0").unwrap();
    assert_eq!(native_wire_size(&ty), None);
    assert!(matches!(
        limited.decode_native_value(&ty, &[]),
        Err(NativeWireError::Backend(_))
    ));
    let tiny = NativeBackend::new(
        Policy {
            max_value_bytes: 0,
            ..Policy::default()
        },
        common::entry(None),
        Default::default(),
    )
    .unwrap();
    assert_eq!(
        tiny.encode_native_value(&value).unwrap_err(),
        NativeWireError::Limit
    );
    let bytes = ark_backend(None).encode_native_value(&value).unwrap();
    assert_eq!(
        tiny.decode_native_value(&value.physical_type(), &bytes)
            .unwrap_err(),
        NativeWireError::Limit
    );
}

#[test]
fn host_measurement_preserves_decoder_framing_and_setup_precedence() {
    let limited = NativeBackend::new(
        Policy {
            max_wire_bytes: 0,
            max_value_bytes: 0,
            ..Policy::default()
        },
        common::entry(None),
        Default::default(),
    )
    .unwrap();
    for spelling in [
        "bool",
        "index",
        "field:bls12-381.fr",
        "field_array<bls12-381.fr,2>",
        "table:bls12-381.fr",
        "proof:multilinear.kzg.bls12-381/0",
        "bytes",
        "vector:bls12-381.fr",
    ] {
        let ty = PhysicalType::default_for(zkc_runtime::vm::LogicalType::parse(spelling).unwrap())
            .unwrap();
        let width = native_wire_size(&ty).unwrap_or(10);
        for bytes in [
            vec![],
            vec![0; width - 1],
            vec![0; width],
            vec![0; width + 1],
        ] {
            let expected = limited.decode_native_value(&ty, &bytes).unwrap_err();
            assert_eq!(
                limited.decoding_bound(&ty, &bytes).unwrap_err(),
                WireError::from(expected),
                "{spelling}, {} bytes",
                bytes.len()
            );
        }
    }
}

#[test]
fn native_public_tables_are_canonical_and_bounded_before_allocation() {
    let codec = ark_backend(None);
    for n in [0, 1, 3] {
        let values: Vec<_> = (0..1usize << n)
            .map(|i| Scalar::from(i as u64 + 1))
            .collect();
        let value = Value::table(&values, &Policy::default()).unwrap();
        let ty = value.physical_type();
        assert!(zkc_native::has_native_wire(&ty));
        assert_eq!(native_wire_size(&ty), None);
        let bytes = codec.encode_native_value(&value).unwrap();
        let expected = [
            b"ZKCV\x00\x02".to_vec(),
            (n as u32).to_le_bytes().to_vec(),
            (1..=1u64 << n)
                .flat_map(|x| [x.to_le_bytes().to_vec(), vec![0; 24]].concat())
                .collect(),
        ]
        .concat();
        assert_eq!(bytes, expected);
        assert_eq!(
            codec
                .encode_native_value(&codec.decode_native_value(&ty, &bytes).unwrap())
                .unwrap(),
            bytes
        );
        for end in [0, 5, 9, bytes.len() - 1] {
            assert_eq!(
                codec.decode_native_value(&ty, &bytes[..end]).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Length)
            );
        }
        let mut bad = bytes.clone();
        bad.push(0);
        assert_eq!(
            codec.decode_native_value(&ty, &bad).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Length)
        );
        let mut bad = bytes.clone();
        bad[10..42].fill(255);
        assert_eq!(
            codec.decode_native_value(&ty, &bad).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Scalar)
        );
        let mut bad = bytes.clone();
        bad[6..10].fill(255);
        assert_eq!(
            codec.decode_native_value(&ty, &bad).unwrap_err(),
            NativeWireError::Limit
        );
        for policy in [
            Policy {
                max_arity: 0,
                max_table_elements: 0,
                ..Policy::default()
            },
            Policy {
                max_wire_bytes: bytes.len() - 1,
                ..Policy::default()
            },
            Policy {
                max_value_bytes: 0,
                ..Policy::default()
            },
        ] {
            let limited =
                NativeBackend::new(policy, common::entry(None), Default::default()).unwrap();
            assert_eq!(
                limited.decode_native_value(&ty, &bytes).unwrap_err(),
                NativeWireError::Limit
            );
            assert_eq!(
                limited.encode_native_value(&value).unwrap_err(),
                NativeWireError::Limit
            );
        }
    }
    let other = PhysicalType::parse("table:bls12-381.fr@arkworks.mle-msb/0").unwrap();
    assert!(!zkc_native::has_native_wire(&other));
    assert!(matches!(
        codec.decode_native_value(&other, b"ZKCV\x00\x02"),
        Err(NativeWireError::Backend(_))
    ));
}

#[cfg(feature = "test-utils")]
#[test]
fn pcs_frames_require_the_selected_setup_and_canonical_payloads() {
    use std::sync::Arc;
    use zkc_kernels::{Keys, Table};
    let policy = Policy::default();
    let bounds = policy.ark_bounds();
    let keys = Keys::setup_for_development(2, &bounds).unwrap();
    let backend = common::backend()
        .verifier(keys.verifier_key().clone())
        .build();
    let other = Keys::setup_for_development(2, &bounds).unwrap();
    let wrong = common::backend()
        .verifier(other.verifier_key().clone())
        .build();
    for values in [
        vec![Scalar::from(0); 4],
        (1..=4).map(Scalar::from).collect(),
    ] {
        let state = keys
            .prover_key()
            .commit(&Table::from_logical_vec(values, &bounds).unwrap())
            .unwrap();
        let (_, proof) = state.open(&[Scalar::from(7), Scalar::from(11)]).unwrap();
        for (value, width) in [
            (Value::Commitment(Arc::new(state.commitment().clone())), 135),
            (Value::Proof(Arc::new(proof)), 279),
        ] {
            let ty = value.physical_type();
            let bytes = backend.encode_native_value(&value).unwrap();
            assert_eq!(bytes.len(), width);
            // Includes canonical infinity for the zero polynomial.
            let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
            assert_eq!(backend.encode_native_value(&decoded).unwrap(), bytes);
            assert_eq!(
                wrong.decode_native_value(&ty, &bytes).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Header)
            );
            assert!(matches!(
                ark_backend(None).decode_native_value(&ty, &bytes),
                Err(NativeWireError::Backend(_))
            ));
            for end in 0..width {
                assert_eq!(
                    backend.decode_native_value(&ty, &bytes[..end]).unwrap_err(),
                    NativeWireError::Invalid(DecodeReason::Length)
                );
            }
            let mut extra = bytes.clone();
            extra.push(0);
            assert_eq!(
                backend.decode_native_value(&ty, &extra).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Length)
            );
            for position in [0, 5, 6, 15, 23, 55] {
                let mut bad = bytes.clone();
                bad[position] ^= 1;
                assert_eq!(
                    backend.decode_native_value(&ty, &bad).unwrap_err(),
                    NativeWireError::Invalid(DecodeReason::Header)
                );
            }
            for fill in [0, 255] {
                let mut bad = bytes.clone();
                bad[87..].fill(fill);
                assert_eq!(
                    backend.decode_native_value(&ty, &bad).unwrap_err(),
                    NativeWireError::Invalid(DecodeReason::Group)
                );
            }
            let mut nonsubgroup = bytes.clone();
            nonsubgroup[87..].fill(0);
            nonsubgroup[87] = 0x80;
            assert_eq!(
                backend.decode_native_value(&ty, &nonsubgroup).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Group)
            );
            for limited in [
                Policy {
                    max_wire_bytes: width - 1,
                    ..policy
                },
                Policy {
                    max_value_bytes: Value::VerifierKey(Arc::new(keys.verifier_key().clone()))
                        .retained_bytes(),
                    ..policy
                },
            ] {
                let bounded = common::backend()
                    .policy(limited)
                    .verifier(keys.verifier_key().clone())
                    .build();
                assert_eq!(
                    bounded.decode_native_value(&ty, &bytes).unwrap_err(),
                    NativeWireError::Limit
                );
                if limited.max_wire_bytes < width {
                    assert_eq!(
                        bounded.encode_native_value(&value).unwrap_err(),
                        NativeWireError::Limit
                    );
                }
            }
        }
    }
}

#[test]
fn additional_domains_keep_exact_canonical_frames_and_typed_errors() {
    use zkc_native::{Bn254G1, Bn254G2, Bn254Scalar, KoalaBear, KoalaBearExt8, RistrettoScalar};
    let backend = ark_backend(None);
    let values = [
        Value::Bn254Field(Bn254Scalar::from(19)),
        Value::Bn254G1(Bn254G1::generator()),
        Value::Bn254G2(Bn254G2::generator()),
        Value::KoalaBearField(KoalaBear::new(19)),
        Value::KoalaBearExt8Field(KoalaBearExt8::from([
            KoalaBear::new(1),
            KoalaBear::new(2),
            KoalaBear::new(3),
            KoalaBear::new(4),
            KoalaBear::new(5),
            KoalaBear::new(6),
            KoalaBear::new(7),
            KoalaBear::new(8),
        ])),
        Value::RistrettoField(RistrettoScalar::from(19u64)),
        Value::RistrettoGroup(curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT),
    ];
    for value in &values {
        let ty = value.physical_type();
        let bytes = backend.encode_native_value(value).unwrap();
        assert_eq!(bytes, backend.encode_native_value(value).unwrap());
        assert_eq!(native_wire_size(&ty), Some(bytes.len()));
        assert_eq!(
            backend
                .encode_native_value(&backend.decode_native_value(&ty, &bytes).unwrap())
                .unwrap(),
            bytes
        );
        for end in 0..bytes.len() {
            assert_eq!(
                backend.decode_native_value(&ty, &bytes[..end]).unwrap_err(),
                NativeWireError::Invalid(DecodeReason::Length)
            );
        }
        for other in &values {
            if other.physical_type() != ty {
                assert!(
                    backend
                        .decode_native_value(&other.physical_type(), &bytes)
                        .is_err()
                );
            }
        }
        let mut bad = bytes.clone();
        bad[5] ^= 1;
        assert_eq!(
            backend.decode_native_value(&ty, &bad).unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Header)
        );
        let mut bad = bytes.clone();
        bad[6..].fill(255);
        assert_eq!(
            backend.decode_native_value(&ty, &bad).unwrap_err(),
            NativeWireError::Invalid(if ty.kind() == zkc_runtime::vm::Type::Field {
                DecodeReason::Scalar
            } else {
                DecodeReason::Group
            })
        );
        let sequence = Value::Sequence(
            zkc_native::Sequence::new(ty.logical(), vec![value.clone(); 3], &Policy::default())
                .unwrap(),
        );
        let nested = backend.encode_native_value(&sequence).unwrap();
        assert_eq!(
            backend
                .encode_native_value(
                    &backend
                        .decode_native_value(&sequence.physical_type(), &nested)
                        .unwrap()
                )
                .unwrap(),
            nested
        );
    }
}
