//! General nested data, canonical framing and preallocation limits.
use serde_json::json;
use zkc_backends::{NativeBackend, NativeWireError, Policy, Scalar, Sequence, Value, Variant};
use zkc_runtime::interactive::{DecodeReason, LogicalType, PhysicalType, Value as RuntimeValue};

fn sequence(element: &str, values: Vec<Value>) -> Value {
    Value::Sequence(
        Sequence::new(
            LogicalType::parse(element).unwrap(),
            values,
            &Policy::default(),
        )
        .unwrap(),
    )
}
fn roundtrip(value: &Value) -> Vec<u8> {
    let backend = support::backend(Policy::default());
    let bytes = backend.encode_native_value(value).unwrap();
    let ty = value.physical_type();
    let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
    assert_eq!(decoded.physical_type(), ty);
    assert_eq!(backend.encode_native_value(&decoded).unwrap(), bytes);
    for end in 0..bytes.len() {
        assert!(
            backend.decode_native_value(&ty, &bytes[..end]).is_err(),
            "prefix {end}"
        );
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(backend.decode_native_value(&ty, &extra).is_err());
    bytes
}

#[test]
fn formation_distinguishes_copying_storage_and_wire_permission() {
    let mut nested = "index".to_string();
    for _ in 0..8 {
        nested = format!("sequence<{nested}>");
    }
    assert!(PhysicalType::default_for(LogicalType::parse(&nested).unwrap()).is_ok());
    assert!(LogicalType::parse(&format!("sequence<{nested}>")).is_err());
    for element in [
        "index",
        "matrix:bls12-381.fr",
        "field:koala-bear",
        "sequence<index>",
        "prover_key:multilinear.kzg.bls12-381/1",
    ] {
        let ty = LogicalType::sequence(LogicalType::parse(element).unwrap()).unwrap();
        assert!(ty.is_duplicable() && ty.is_discardable());
        assert_eq!(LogicalType::parse(&ty.spelling()).unwrap(), ty);
        assert!(PhysicalType::default_for(ty).is_ok());
    }
    let affine =
        zkc_test_support::variants::logical("Affine", json!([["a", ["rng:bls12-381.fr"]]]));
    for element in [
        "rng:bls12-381.fr",
        "resource_unit:Guard",
        affine.as_str(),
        "sequence<rng:bls12-381.fr>",
    ] {
        assert!(LogicalType::parse(&format!("sequence<{element}>")).is_err());
    }
    let empty = sequence("polynomial:bn254.fr", vec![]);
    assert!(!empty.physical_type().has_native_data_frame());
    assert!(
        support::backend(Policy::default())
            .encode_native_value(&empty)
            .is_err()
    );
    let setup = LogicalType::parse("sequence<proof:multilinear.kzg.bls12-381/1>").unwrap();
    assert!(zkc_backends::requires_setup(setup));
}

#[test]
fn empty_records_sums_and_nested_sequences_have_canonical_boundaries() {
    assert_eq!(
        roundtrip(&sequence("index", vec![])),
        b"ZKCV\x01\x45\0\0\0\0"
    );
    let inner = sequence("index", vec![Value::Index(7)]);
    roundtrip(&sequence(
        "sequence<index>",
        vec![sequence("index", vec![]), inner],
    ));
    let record = zkc_test_support::variants::logical(
        "Query",
        json!([["q", ["index", "vector:bls12-381.fr"]]]),
    );
    let descriptor = LogicalType::parse(&record)
        .unwrap()
        .variant_descriptor()
        .unwrap()
        .clone();
    let items = (0..3)
        .map(|n| {
            Value::Variant(
                Variant::new(
                    descriptor.clone(),
                    0,
                    vec![
                        Value::Index(n),
                        Value::Vector(vec![Scalar::from(n); n as usize].into()),
                    ],
                )
                .unwrap(),
            )
        })
        .collect();
    roundtrip(&sequence(&record, items));
    let outer = zkc_test_support::variants::logical(
        "Nested",
        json!([["values", [format!("sequence<{record}>")]]]),
    );
    let outer = LogicalType::parse(&outer).unwrap();
    roundtrip(&Value::Variant(
        Variant::new(
            outer.variant_descriptor().unwrap().clone(),
            0,
            vec![sequence(&record, vec![])],
        )
        .unwrap(),
    ));
}

#[test]
fn ragged_matrices_preserve_shape_including_zero_dimensions() {
    let matrices = [(0, 5), (3, 0), (1, 2), (4, 3)]
        .into_iter()
        .map(|(r, c)| Value::matrix(r, c, &[], &Policy::default()).unwrap())
        .collect();
    let value = sequence("matrix:bls12-381.fr", matrices);
    let bytes = roundtrip(&value);
    let backend = support::backend(Policy::default());
    let Value::Sequence(loaded) = backend
        .decode_native_value(&value.physical_type(), &bytes)
        .unwrap()
    else {
        panic!()
    };
    let dims: Vec<_> = loaded
        .elements()
        .iter()
        .map(|v| {
            let Value::Matrix(m) = v else { panic!() };
            (m.rows(), m.columns())
        })
        .collect();
    assert_eq!(dims, [(0, 5), (3, 0), (1, 2), (4, 3)]);
    let matrix = Value::matrix(
        2,
        3,
        &[(0, 1, Scalar::from(9)), (1, 2, Scalar::from(4))],
        &Policy::default(),
    )
    .unwrap();
    let bytes = roundtrip(&matrix);
    assert_eq!(
        bytes,
        backend.encode_value(&matrix).unwrap(),
        "existing COO codec is reused"
    );
    for (offset, value) in [(6, u32::MAX), (10, u32::MAX), (14, u32::MAX)] {
        let mut bad = bytes.clone();
        bad[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        assert_eq!(
            backend
                .decode_native_value(&matrix.physical_type(), &bad)
                .unwrap_err(),
            NativeWireError::Limit,
        );
    }
    let mut zero = bytes.clone();
    zero[26..58].fill(0);
    assert!(matches!(
        backend.decode_native_value(&matrix.physical_type(), &zero),
        Err(NativeWireError::Invalid(_))
    ));
}

#[test]
fn corrupt_lengths_and_leaf_encodings_refuse_before_use() {
    let value = sequence("field:bls12-381.fr", vec![Value::Field(Scalar::from(7))]);
    let backend = support::backend(Policy::default());
    let bytes = roundtrip(&value);
    for offset in [6, 10] {
        let mut bad = bytes.clone();
        bad[offset..offset + 4].fill(255);
        assert_eq!(
            backend
                .decode_native_value(&value.physical_type(), &bad)
                .unwrap_err(),
            if offset == 6 {
                NativeWireError::Limit
            } else {
                NativeWireError::Invalid(DecodeReason::Length)
            },
        );
    }
    let mut noncanonical = bytes.clone();
    noncanonical[20..52].fill(255);
    assert!(matches!(
        backend.decode_native_value(&value.physical_type(), &noncanonical),
        Err(NativeWireError::Invalid(DecodeReason::Scalar))
    ));
    let mut wrong_length = bytes.clone();
    wrong_length[10..14].copy_from_slice(&37u32.to_le_bytes());
    assert_eq!(
        backend
            .decode_native_value(&value.physical_type(), &wrong_length)
            .unwrap_err(),
        NativeWireError::Invalid(DecodeReason::Length),
    );
}

#[test]
fn nested_limits_count_expanded_values_before_allocation() {
    let inner = sequence("index", vec![Value::Index(1); 8]);
    let value = sequence("sequence<index>", vec![inner; 8]);
    let bytes = roundtrip(&value);
    let policy = Policy {
        max_table_elements: 40,
        ..Policy::default()
    };
    let backend = NativeBackend::new(policy, support::entry(None), None).unwrap();
    assert!(matches!(
        backend.decode_native_value(&value.physical_type(), &bytes),
        Err(NativeWireError::Limit)
    ));
    assert!(backend.encode_native_value(&value).is_err());
    let mut value = Value::Index(1);
    let mut refused = false;
    for _ in 0..6 {
        match Sequence::new(
            value.physical_type().logical(),
            vec![value.clone(); 32],
            &Policy::default(),
        ) {
            Ok(v) => value = Value::Sequence(v),
            Err(_) => {
                refused = true;
                break;
            }
        }
    }
    assert!(refused, "sharing must not evade expanded-size charges");
}

#[test]
fn codec_preflight_matches_cached_retained_storage_at_the_exact_peak_limit() {
    let value = sequence(
        "sequence<index>",
        vec![
            sequence("index", vec![]),
            sequence("index", vec![Value::Index(7)]),
        ],
    );
    let bytes = roundtrip(&value);
    // The shared leaf scan reserves an extra four wire widths for the index.
    let retained = value.retained_bytes() + 4 * 14;
    let peak = (2 * retained).max(retained + 3 * bytes.len());
    for (limit, accepted) in [(peak, true), (peak - 1, false)] {
        let policy = Policy {
            max_value_bytes: limit,
            ..Policy::default()
        };
        let codec = NativeBackend::new(policy, support::entry(None), None).unwrap();
        assert_eq!(codec.encode_native_value(&value).is_ok(), accepted);
        assert_eq!(
            codec
                .decode_native_value(&value.physical_type(), &bytes)
                .is_ok(),
            accepted
        );
    }
}

#[test]
fn collection_framing_distinguishes_partitions_and_matrix_shapes() {
    let a = sequence(
        "sequence<index>",
        vec![
            sequence("index", vec![Value::Index(1), Value::Index(2)]),
            sequence("index", vec![Value::Index(3)]),
        ],
    );
    let b = sequence(
        "sequence<index>",
        vec![
            sequence("index", vec![Value::Index(1)]),
            sequence("index", vec![Value::Index(2), Value::Index(3)]),
        ],
    );
    assert_ne!(roundtrip(&a), roundtrip(&b));
    let matrix = |r, c| Value::matrix(r, c, &[], &Policy::default()).unwrap();
    assert_ne!(roundtrip(&matrix(2, 3)), roundtrip(&matrix(3, 2)));
}

#[path = "domains/support.rs"]
mod support;
use zkc_runtime::interactive::{Backend, OperationBinding};
fn binding(name: &str, element: &str) -> OperationBinding {
    OperationBinding {
        contract: format!("sequence.{name}"),
        arguments: vec![element.into()],
        implementation: format!("native/sequence.{name}"),
    }
}
fn one(
    backend: NativeBackend,
    b: OperationBinding,
    args: Vec<Value>,
) -> (Result<Vec<Value>, String>, NativeBackend) {
    let sig = b.signature().unwrap();
    assert_eq!(backend.binding_signature(&b).unwrap(), sig);
    let input_names: Vec<_> = (0..args.len()).map(|i| format!("a{i}")).collect();
    let output_names: Vec<_> = (0..sig.outputs.len()).map(|i| format!("o{i}")).collect();
    let bytes = support::program(
        &[b],
        &sig.inputs,
        vec![json!([
            "op",
            "sequence",
            "b0",
            [],
            input_names,
            output_names
        ])],
        &sig.outputs,
        &output_names,
    );
    let mut tree: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    tree[0] = json!("zkc.program/1");
    tree[4][0].as_array_mut().unwrap().push(json!([]));
    support::run_program(backend, &serde_json::to_vec(&tree).unwrap(), args)
}
#[test]
fn kernels_are_immutable_checked_and_charge_work_across_frames() {
    let (out, backend) = one(
        support::backend(Policy::default()),
        binding("empty", "index"),
        vec![],
    );
    let empty = out.unwrap().remove(0);
    let (out, backend) = one(
        backend,
        binding("append", "index"),
        vec![empty.clone(), Value::Index(7)],
    );
    let single = out.unwrap().remove(0);
    let (out, backend) = one(backend, binding("length", "index"), vec![empty]);
    assert!(matches!(out.unwrap().as_slice(), [Value::Index(0)]));
    let (out, backend) = one(
        backend,
        binding("at", "index"),
        vec![single.clone(), Value::Index(0)],
    );
    assert!(matches!(out.unwrap().as_slice(), [Value::Index(7)]));
    let before = backend.sequence_work_spent();
    let (out, backend) = one(
        backend,
        binding("at", "index"),
        vec![single.clone(), Value::Index(u64::MAX)],
    );
    assert_eq!(out.unwrap_err(), "refused:sequence-index");
    assert!(backend.sequence_work_spent() > before);
    assert_eq!(backend.active_frames(), 0);
    let spent = backend.sequence_work_spent();
    let (out, backend) = one(
        backend.with_sequence_work_limit(spent),
        binding("length", "index"),
        vec![single],
    );
    assert_eq!(out.unwrap_err(), "exhausted:sequence-work");
    assert_eq!(backend.sequence_work_spent(), spent);
    assert_eq!(backend.active_frames(), 0);
}
#[test]
fn empty_private_sequences_are_local_and_setup_checks_reach_active_elements() {
    let keys =
        zkc_arkworks::Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    let other =
        zkc_arkworks::Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    let empty = sequence("prover_key:multilinear.kzg.bls12-381/1", vec![]);
    assert!(
        support::backend(Policy::default())
            .encode_native_value(&empty)
            .is_err()
    );
    let table = zkc_arkworks::Table::from_logical_vec(
        vec![Scalar::from(1), Scalar::from(2)],
        &Policy::default().ark_bounds(),
    )
    .unwrap();
    let state = keys.prover_key().commit(&table).unwrap();
    let (_, proof) = state.open(&[Scalar::from(7)]).unwrap();
    let codec = NativeBackend::new(
        Policy::default(),
        support::entry(None),
        Some(keys.verifier_key().clone()),
    )
    .unwrap();
    let wrong = NativeBackend::new(
        Policy::default(),
        support::entry(None),
        Some(other.verifier_key().clone()),
    )
    .unwrap();
    let different_arity =
        zkc_arkworks::Keys::setup_for_development(2, &Policy::default().ark_bounds()).unwrap();
    let wrong_arity = NativeBackend::new(
        Policy::default(),
        support::entry(None),
        Some(different_arity.verifier_key().clone()),
    )
    .unwrap();
    for leaf in [
        Value::Commitment(std::sync::Arc::new(state.commitment().clone())),
        Value::Proof(std::sync::Arc::new(proof)),
    ] {
        let value = sequence(&leaf.physical_type().logical().spelling(), vec![leaf]);
        let bytes = codec.encode_native_value(&value).unwrap();
        for backend in [&wrong, &wrong_arity] {
            assert_eq!(
                backend.encode_native_value(&value).unwrap_err().to_string(),
                "native-wire-backend:native-wire-setup-mismatch",
            );
        }
        assert_eq!(
            wrong
                .decode_native_value(&value.physical_type(), &bytes)
                .unwrap_err(),
            NativeWireError::Invalid(DecodeReason::Header),
        );
        assert_eq!(
            support::backend(Policy::default())
                .encode_native_value(&value)
                .unwrap_err()
                .to_string(),
            "native-wire-backend:native-wire-setup-required",
        );
    }
}

#[test]
fn standalone_matrix_decoders_agree_on_canonicality_and_shape() {
    let codec = support::backend(Policy::default());
    let m = Value::matrix(
        2,
        3,
        &[(0, 1, Scalar::from(7)), (1, 2, Scalar::from(9))],
        &Policy::default(),
    )
    .unwrap();
    let wire = codec.encode_value(&m).unwrap();
    // This newly admitted native frame uses the shared structured peak policy;
    // the older typed leaf codec intentionally retains its narrower accounting.
    // The shared typed bulk reader retains 336 bytes and bounds max(2R,R+3W).
    let required = 672;
    for (limit, accepted) in [(required, true), (required - 1, false)] {
        let tight = support::backend(Policy {
            max_value_bytes: limit,
            ..Policy::default()
        });
        assert!(tight.decode_typed_value(m.physical_type(), &wire).is_ok());
        assert_eq!(
            tight.decode_native_value(&m.physical_type(), &wire).is_ok(),
            accepted
        );
    }
    for bytes in [&wire[..], &wire[..wire.len() - 1]] {
        let a = codec.decode_typed_value(m.physical_type(), bytes);
        let b = codec.decode_native_value(&m.physical_type(), bytes);
        assert_eq!(a.is_ok(), b.is_ok());
        if let (Ok(a), Ok(b)) = (a, b) {
            assert_eq!(
                codec.encode_value(&a).unwrap(),
                codec.encode_value(&b).unwrap()
            );
        }
    }
    for (start, end, fill) in [(6, 10, 255), (18, 22, 255), (26, 58, 0), (26, 58, 255)] {
        let mut bad = wire.clone();
        bad[start..end].fill(fill);
        assert!(codec.decode_typed_value(m.physical_type(), &bad).is_err());
        assert!(codec.decode_native_value(&m.physical_type(), &bad).is_err());
    }
    let mut duplicate = wire.clone();
    duplicate[58..98].copy_from_slice(&wire[18..58]);
    assert!(
        codec
            .decode_typed_value(m.physical_type(), &duplicate)
            .is_err()
    );
    assert!(
        codec
            .decode_native_value(&m.physical_type(), &duplicate)
            .is_err()
    );
    let mut reversed = wire.clone();
    reversed[18..58].copy_from_slice(&wire[58..98]);
    reversed[58..98].copy_from_slice(&wire[18..58]);
    assert!(
        codec
            .decode_typed_value(m.physical_type(), &reversed)
            .is_err()
    );
    assert!(
        codec
            .decode_native_value(&m.physical_type(), &reversed)
            .is_err()
    );
    // The installed matrix ceiling applies even under a more permissive host
    // policy, and an excessive declaration is refused before payload allocation.
    let generous = support::backend(Policy {
        max_table_elements: 1 << 21,
        ..Policy::default()
    });
    let mut excessive = b"ZKCV\x01\x17".to_vec();
    for n in [65536u32, 65536, (1 << 20) + 1] {
        excessive.extend_from_slice(&n.to_le_bytes());
    }
    assert_eq!(
        generous
            .decode_native_value(&m.physical_type(), &excessive)
            .unwrap_err(),
        NativeWireError::Limit
    );
}

#[test]
fn default_storage_and_wire_limits_cover_thousands_of_scalar_elements() {
    let codec = support::backend(Policy::default());
    for n in [1024, 4096, 8192] {
        let value = sequence("index", (0..n).map(|i| Value::Index(i as u64)).collect());
        let bytes = codec.encode_native_value(&value).unwrap();
        let decoded = codec
            .decode_native_value(&value.physical_type(), &bytes)
            .unwrap();
        assert_eq!(codec.encode_native_value(&decoded).unwrap(), bytes);
    }
    let nested = LogicalType::parse("fixed_vector<sequence<index>,2>").unwrap();
    assert!(
        PhysicalType::default_for(nested).is_err(),
        "fixed vectors do not store arbitrary Value trees"
    );
    let record =
        zkc_test_support::variants::logical("Matrix", json!([["m", ["matrix:bls12-381.fr"]]]));
    let descriptor = LogicalType::parse(&record)
        .unwrap()
        .variant_descriptor()
        .unwrap()
        .clone();
    roundtrip(&Value::Variant(
        Variant::new(
            descriptor,
            0,
            vec![Value::matrix(0, 7, &[], &Policy::default()).unwrap()],
        )
        .unwrap(),
    ));
}

#[test]
fn nested_data_and_external_calls_retain_independent_work_across_failed_frames() {
    let hash = || OperationBinding {
        contract: "external.monero.hash".into(),
        arguments: vec![],
        implementation: "native/external.monero.hash".into(),
    };
    let words = || Value::Indices(vec![0; 64].into());
    let backend = support::backend(Policy::default())
        .with_sequence_work_limit(21)
        .with_external_work_limit(65);
    let value = sequence("index", vec![]);
    let (out, backend) = one(backend, binding("length", "index"), vec![value.clone()]);
    assert!(matches!(out.unwrap().as_slice(), [Value::Index(0)]));
    assert_eq!(
        (backend.sequence_work_spent(), backend.external_work_spent()),
        (6, 0)
    );

    let (out, backend) = one(backend, hash(), vec![words()]);
    assert!(out.is_ok());
    assert_eq!(
        (backend.sequence_work_spent(), backend.external_work_spent()),
        (6, 65)
    );
    // This call spends its traversal allowance, then fails in the kernel.
    // A backend that commits work only on success must fail this assertion.
    let (out, backend) = one(
        backend,
        binding("at", "index"),
        vec![value.clone(), Value::Index(0)],
    );
    assert_eq!(out.unwrap_err(), "refused:sequence-index");
    assert_eq!(
        (backend.sequence_work_spent(), backend.external_work_spent()),
        (15, 65),
    );
    assert_eq!(backend.active_frames(), 0);
    let (out, backend) = one(backend, hash(), vec![words()]);
    assert_eq!(out.unwrap_err(), "exhausted:external-work-limit");
    assert_eq!(backend.active_frames(), 0);

    // An exhausted primitive does not refund data work or consume its remaining
    // allowance. A new frame continues against the same two spent prefixes.
    let (out, backend) = one(backend, binding("length", "index"), vec![value.clone()]);
    assert!(matches!(out.unwrap().as_slice(), [Value::Index(0)]));
    assert_eq!(
        (backend.sequence_work_spent(), backend.external_work_spent()),
        (21, 65)
    );
    let (out, backend) = one(backend, binding("length", "index"), vec![value]);
    assert_eq!(out.unwrap_err(), "exhausted:sequence-work");
    assert_eq!(backend.active_frames(), 0);

    // Raising one allowance preserves its consumed prefix and does not reset
    // the exhausted allowance in the other subsystem.
    let (out, backend) = one(backend.with_external_work_limit(130), hash(), vec![words()]);
    assert!(out.is_ok());
    assert_eq!(
        (backend.sequence_work_spent(), backend.external_work_spent()),
        (21, 130)
    );
    assert_eq!(backend.active_frames(), 0);
    let (out, backend) = one(
        backend,
        binding("length", "index"),
        vec![sequence("index", vec![])],
    );
    assert_eq!(out.unwrap_err(), "exhausted:sequence-work");
    assert_eq!(
        (backend.sequence_work_spent(), backend.external_work_spent()),
        (21, 130)
    );
    assert_eq!(backend.active_frames(), 0);
}
