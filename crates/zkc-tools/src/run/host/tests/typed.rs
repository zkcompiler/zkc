use super::*;
use crate::execution::ProverMaterial;
use zkc_runtime::interactive::Identity;

fn request(value: impl Fn() -> InputValue) -> RunInputs {
    RunInputs {
        session: "session".into(),
        roles: ["Alice", "Bob"]
            .into_iter()
            .map(|role| RoleInputs {
                role: role.into(),
                inputs: vec![value()],
                services: vec![],
            })
            .collect(),
        setups: BTreeMap::new(),
    }
}
fn refusal(host: &RunHost, request: &RunInputs) -> String {
    match host.prepare_typed(request) {
        Err(code) => code,
        Ok(_) => panic!("unexpected preparation success"),
    }
}

#[test]
fn native_values_match_wire_execution_without_decoding_or_request_borrow() {
    let (raw, input) = fixture("bool");
    let host = host(&raw, HostLimits::default());
    let expected = host
        .prepare(input.to_string().as_bytes())
        .unwrap()
        .execute()
        .json();
    crate::host::admission::DECODE_COUNT.set(0);
    let plan = {
        let mut inputs = request(|| InputValue::from(Value::Bool(false)));
        let plan = host.prepare_typed(&inputs).unwrap();
        // Mutation/drop of the request cannot affect already prepared data.
        inputs.roles[0].inputs[0] = InputValue::from(Value::Bool(true));
        plan
    };
    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
    assert_eq!(plan.execute().json(), expected);
    let wire = request(|| InputValue::Wire(vec![0x5a, 0x4b, 0x43, 0x56, 0, 5, 0]));
    assert_eq!(
        host.prepare_typed(&wire).unwrap().execute().json(),
        expected
    );
}

#[test]
fn typed_requests_preserve_structure_capacity_and_resource_refusals() {
    let (raw, _) = fixture("bool");
    let host = host(&raw, HostLimits::default());
    let mut inputs = request(|| InputValue::from(Value::Bool(false)));
    inputs.roles[1].inputs[0] = InputValue::from(Value::Index(0));
    assert_eq!(refusal(&host, &inputs), "native-input-type");
    inputs.roles[1].inputs[0] = InputValue::Resource { budget: 1 };
    assert_eq!(refusal(&host, &inputs), "bundle-input-kind");
    inputs.roles[1].inputs[0] = InputValue::from(Value::Bool(false));
    inputs.roles[1].services.push(0);
    assert_eq!(refusal(&host, &inputs), "bundle-input-count");
    inputs.roles[1].services.clear();
    inputs.roles.swap(0, 1);
    assert_eq!(refusal(&host, &inputs), "bundle-input-roles");
    inputs.roles.swap(0, 1);
    inputs.session = "bad session".into();
    assert_eq!(refusal(&host, &inputs), "bundle-input-name");
    inputs.session = "session".into();
    inputs.setups.insert("untrusted".into(), vec![]);
    assert_eq!(refusal(&host, &inputs), "bundle-setup-authority");
    inputs.setups.clear();

    let mut limits = HostLimits::default();
    limits.capacity.values.live_bytes = 512;
    let bounded = self::host(&raw, limits);
    assert_eq!(refusal(&bounded, &inputs), "artifact-input-bytes-limit");
    let mut limits = HostLimits::default();
    limits.capacity.value_bytes = 0;
    let bounded = self::host(&raw, limits);
    assert_eq!(
        refusal(&bounded, &inputs),
        "native-wire-backend:exhausted:output-bytes"
    );
    let mut limits = HostLimits::default();
    limits.capacity.wire_bytes = 6;
    let bounded = self::host(&raw, limits);
    let wire = request(|| InputValue::Wire(vec![0x5a, 0x4b, 0x43, 0x56, 0, 5, 0]));
    assert_eq!(refusal(&bounded, &wire), "native-capacity-wire");
    // Wire limits govern transport, not already constructed immutable data.
    assert!(bounded.prepare_typed(&inputs).is_ok());

    let (raw, _) = fixture("rng:bls12-381.fr");
    let rng_host = self::host(&raw, HostLimits::default());
    let mut rng = request(|| InputValue::Resource { budget: 1_000_001 });
    assert_eq!(refusal(&rng_host, &rng), "bundle-resource-budget");
    let domain = Domain::new("Alice", "session", "main", Some("root"));
    let mut foreign = NativeBackend::new(
        zkc_backends::Policy::default(),
        EntryPolicy::new(domain.clone(), None),
        Default::default(),
    )
    .unwrap();
    rng.roles[0].inputs[0] = InputValue::from(
        foreign
            .issue_rng_for(Identity::Bls12381Fr, domain, 1)
            .unwrap(),
    );
    assert_eq!(refusal(&rng_host, &rng), "native-input-private");
    let token = match &rng.roles[0].inputs[0] {
        InputValue::Native(value) => match value.as_ref() {
            Value::Rng(token) => token,
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };
    // Refusal must not consume, retire, or adopt a foreign root.
    assert_eq!(foreign.observe(token).unwrap().draw_count, 0);
    foreign.retire(token).unwrap();
}

#[test]
fn nested_native_and_wire_data_obey_the_same_selected_setup() {
    let policy = zkc_backends::Policy::default();
    let first = zkc_arkworks::Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let other = zkc_arkworks::Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let logical = LogicalType::parse("commitment:multilinear.kzg.bls12-381/0").unwrap();
    let seq = LogicalType::sequence(logical.clone()).unwrap();
    let (raw, _) = fixture(&seq.spelling());
    let authority = SetupAuthority {
        keys: BTreeMap::from([
            ("first".into(), first.verifier_key().metadata().key_id()),
            ("other".into(), other.verifier_key().metadata().key_id()),
        ]),
        inputs: BTreeMap::from([
            (("Alice".into(), 0), "first".into()),
            (("Bob".into(), 0), "first".into()),
        ]),
    };
    let host = RunHost::admit(
        &raw,
        &Sha256::digest(&raw).into(),
        HostLimits::default(),
        authority.clone(),
    )
    .unwrap();
    let table = zkc_arkworks::Table::from_logical(
        &[zkc_backends::Scalar::from(1), zkc_backends::Scalar::from(2)],
        &policy.ark_bounds(),
    )
    .unwrap();
    let backend = NativeBackend::new(
        policy,
        EntryPolicy::new(Domain::new("Alice", "session", "main", Some("root")), None),
        SetupRegistry::new(
            vec![first.verifier_key().clone(), other.verifier_key().clone()],
            &policy,
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        crate::host::setups::check_input(
            &Value::VerifierKey(Arc::new(other.verifier_key().clone())),
            first.verifier_key()
        )
        .unwrap_err(),
        "native-proof-input-setup"
    );
    for (key, allowed) in [(&first, true), (&other, false)] {
        let committed = key.prover_key().commit(&table).unwrap();
        let value = Value::Sequence(
            zkc_backends::Sequence::new(
                logical.clone(),
                vec![Value::Commitment(Arc::new(committed.commitment().clone()))],
                &policy,
            )
            .unwrap(),
        );
        let wire = backend.encode_native_value(&value).unwrap();
        let wrapped_type =
            zkc_test_support::variants::logical("Committed", json!([["data", [seq.spelling()]]]));
        let (wrapped_raw, _) = fixture(&wrapped_type);
        let wrapped_host = RunHost::admit(
            &wrapped_raw,
            &Sha256::digest(&wrapped_raw).into(),
            HostLimits::default(),
            authority.clone(),
        )
        .unwrap();
        for native in [false, true] {
            let mut wrapped = request(|| InputValue::Variant {
                alternative: 0,
                payload: vec![if native {
                    value.clone().into()
                } else {
                    InputValue::Wire(wire.clone())
                }],
            });
            wrapped.setups = BTreeMap::from([
                (
                    "first".into(),
                    first.verifier_key().to_bytes(&policy.ark_bounds()).unwrap(),
                ),
                (
                    "other".into(),
                    other.verifier_key().to_bytes(&policy.ark_bounds()).unwrap(),
                ),
            ]);
            if allowed {
                assert_eq!(
                    wrapped_host
                        .prepare_typed(&wrapped)
                        .unwrap()
                        .execute()
                        .execution
                        .unwrap()
                        .outcome,
                    Outcome::Completed
                );
            } else {
                crate::host::admission::DECODE_COUNT.set(0);
                assert_eq!(refusal(&wrapped_host, &wrapped), "native-proof-input-setup");
                if native {
                    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
                }
            }

            let mut inputs = request(|| {
                if native {
                    InputValue::from(value.clone())
                } else {
                    InputValue::Wire(wire.clone())
                }
            });
            inputs.setups = BTreeMap::from([
                (
                    "first".into(),
                    first.verifier_key().to_bytes(&policy.ark_bounds()).unwrap(),
                ),
                (
                    "other".into(),
                    other.verifier_key().to_bytes(&policy.ark_bounds()).unwrap(),
                ),
            ]);
            if allowed {
                let report = host.prepare_typed(&inputs).unwrap().execute();
                assert_eq!(
                    report.execution.as_ref().unwrap().outcome,
                    Outcome::Completed
                );
                assert!(report.cleanup_errors.is_empty());
                // Setup imports are bounded before expensive parsing.
                let mut limits = HostLimits::default();
                limits.capacity.values.total_bytes =
                    inputs.setups.values().map(Vec::len).sum::<usize>() - 1;
                let bounded = RunHost::admit(
                    &raw,
                    &Sha256::digest(&raw).into(),
                    limits,
                    authority.clone(),
                )
                .unwrap();
                assert_eq!(refusal(&bounded, &inputs), "artifact-input-work-limit");
                inputs.setups.remove("other");
                assert_eq!(refusal(&host, &inputs), "bundle-setup-material");
            } else {
                assert_eq!(refusal(&host, &inputs), "native-proof-input-setup");
                if native {
                    let good = first.prover_key().commit(&table).unwrap();
                    let good = Value::Sequence(
                        zkc_backends::Sequence::new(
                            logical.clone(),
                            vec![Value::Commitment(Arc::new(good.commitment().clone()))],
                            &policy,
                        )
                        .unwrap(),
                    );
                    inputs.roles[0].inputs[0] =
                        InputValue::Wire(backend.encode_native_value(&good).unwrap());
                    crate::host::admission::DECODE_COUNT.set(0);
                    assert_eq!(refusal(&host, &inputs), "native-proof-input-setup");
                    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
                }
            }
        }
    }
}

#[test]
fn native_aggregates_keep_whole_value_collection_limits_without_encoding() {
    let policy = zkc_backends::Policy::default();
    let leaf = Value::vector(&[zkc_backends::Scalar::from(1); 3], &policy).unwrap();
    let value = Value::Sequence(
        zkc_backends::Sequence::new(
            leaf.physical_type().logical(),
            vec![leaf.clone(), leaf],
            &policy,
        )
        .unwrap(),
    );
    let (raw, _) = fixture(&value.physical_type().logical().spelling());
    let encoder = NativeBackend::new(
        policy,
        EntryPolicy::new(Domain::new("Alice", "session", "main", Some("root")), None),
        Default::default(),
    )
    .unwrap();
    let bytes = encoder.encode_native_value(&value).unwrap();
    let mut limits = HostLimits::default();
    limits.capacity.elements = 4; // each vector and the node count fit; their sum does not.
    let host = host(&raw, limits);
    let wire = request(|| InputValue::Wire(bytes.clone()));
    assert_eq!(refusal(&host, &wire), "native-wire-limit");
    let native = request(|| InputValue::from(value.clone()));
    assert_eq!(refusal(&host, &native), "native-wire-limit");
}

#[test]
fn request_structure_and_all_setup_lengths_precede_material_import() {
    let (raw, _) = fixture("bool");
    let authority = SetupAuthority {
        keys: BTreeMap::from([("first".into(), [0; 32]), ("other".into(), [1; 32])]),
        inputs: BTreeMap::new(),
    };
    let mut limits = HostLimits::default();
    limits.capacity.wire_bytes = 4;
    let host = RunHost::admit(&raw, &Sha256::digest(&raw).into(), limits, authority).unwrap();
    let mut inputs = request(|| Value::Bool(false).into());
    inputs.setups.insert("first".into(), vec![0]);
    assert_eq!(refusal(&host, &inputs), "bundle-setup-material");
    inputs.setups.insert("other".into(), vec![0; 5]);
    assert_eq!(refusal(&host, &inputs), "native-capacity-wire");
    inputs.setups.insert("other".into(), vec![0]);
    inputs.roles.swap(0, 1);
    assert_eq!(refusal(&host, &inputs), "bundle-input-roles");
    inputs.roles.swap(0, 1);
    inputs.roles[0].inputs.clear();
    assert_eq!(refusal(&host, &inputs), "bundle-input-count");
    inputs.roles[0].inputs.push(Value::Index(0).into());
    assert_eq!(refusal(&host, &inputs), "native-input-type");
    inputs.roles[0].inputs[0] = InputValue::Resource { budget: 1 };
    assert_eq!(refusal(&host, &inputs), "bundle-input-kind");
    inputs.roles[0].inputs[0] = InputValue::Wire(vec![0; 5]);
    assert_eq!(refusal(&host, &inputs), "native-capacity-wire");

    let (raw, _) = fixture("rng:bls12-381.fr");
    let rng = RunHost::admit(
        &raw,
        &Sha256::digest(&raw).into(),
        limits,
        host.authority.clone(),
    )
    .unwrap();
    inputs.roles[0].inputs[0] = InputValue::Resource { budget: 1_000_001 };
    assert_eq!(refusal(&rng, &inputs), "bundle-resource-budget");
}

#[test]
fn typed_wire_work_is_reserved_before_scanning() {
    let (raw, _) = fixture("indices");
    let mut limits = HostLimits::default();
    limits.capacity.values.total_bytes = 1;
    let host = host(&raw, limits);
    let inputs = request(|| InputValue::Wire(vec![0; 10]));
    // The work refusal precedes even framing of this malformed input.
    assert_eq!(refusal(&host, &inputs), "artifact-input-work-limit");
}

#[test]
fn typed_key_imports_use_explicit_authorized_constructors() {
    let policy = zkc_backends::Policy::default();
    let keys = zkc_arkworks::Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let authority = SetupAuthority {
        keys: BTreeMap::from([("setup".into(), keys.verifier_key().metadata().key_id())]),
        inputs: BTreeMap::from([
            (("Alice".into(), 0), "setup".into()),
            (("Bob".into(), 0), "setup".into()),
        ]),
    };
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("key.pk");
    std::fs::write(
        &path,
        keys.prover_key().to_bytes(&policy.ark_bounds()).unwrap(),
    )
    .unwrap();
    for prover in [false, true] {
        let logical = if prover {
            "prover_key:multilinear.kzg.bls12-381/0"
        } else {
            "verifier_key:multilinear.kzg.bls12-381/0"
        };
        let (raw, _) = fixture(logical);
        let host = RunHost::admit(
            &raw,
            &Sha256::digest(&raw).into(),
            HostLimits::default(),
            authority.clone(),
        )
        .unwrap();
        let mut inputs = request(|| {
            if prover {
                InputValue::ProverKeyFile {
                    path: path.to_str().unwrap().into(),
                    fingerprint: keys.prover_key().material_fingerprint(),
                }
            } else {
                InputValue::VerifierKey
            }
        });
        inputs.setups.insert(
            "setup".into(),
            keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap(),
        );
        let report = host.prepare_typed(&inputs).unwrap().execute();
        assert_eq!(
            report.execution.as_ref().unwrap().outcome,
            Outcome::Completed
        );
        assert!(report.cleanup_errors.is_empty());
        inputs.roles[0].inputs[0] = if prover {
            Value::ProverKey(Arc::new(keys.prover_key().clone())).into()
        } else {
            Value::VerifierKey(Arc::new(keys.verifier_key().clone())).into()
        };
        assert_eq!(refusal(&host, &inputs), "native-input-private");
        inputs.roles[0].inputs[0] = InputValue::Wire(vec![]);
        assert_eq!(refusal(&host, &inputs), "bundle-input-kind");
    }
}

#[test]
fn compound_inputs_share_native_wire_layout_and_preserve_nested_data() {
    let inner =
        zkc_test_support::variants::logical("Maybe", json!([["none", []], ["some", ["bool"]]]));
    let outer =
        zkc_test_support::variants::logical("Envelope", json!([["packet", [inner, "index"]]]));
    let (raw, _) = fixture(&outer);
    let host = self::host(&raw, HostLimits::default());
    let request = request(|| InputValue::Variant {
        alternative: 0,
        payload: vec![
            InputValue::Variant {
                alternative: 1,
                payload: vec![InputValue::Wire(b"ZKCV\x00\x05\x01".to_vec())],
            },
            Value::Index(9).into(),
        ],
    });
    crate::host::admission::DECODE_COUNT.set(0);
    let plan = host.prepare_typed(&request).unwrap();
    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 2);
    let report = plan.execute();
    assert_eq!(
        report.execution.as_ref().unwrap().outcome,
        Outcome::Completed
    );
    let execution = report.execution.as_ref().unwrap();
    let backend = &execution.backends[0].1;
    let expected = backend
        .encode_native_value(&execution.roles[0].outputs[0])
        .unwrap();
    let wire = self::request(|| InputValue::Wire(expected.clone()));
    assert_eq!(
        host.prepare_typed(&wire).unwrap().execute().json(),
        report.json()
    );
    let data = execution.roles[0].outputs[0].clone();
    let native = self::request(|| InputValue::from(data.clone()));
    assert_eq!(
        host.prepare_typed(&native).unwrap().execute().json(),
        report.json()
    );
}

#[test]
fn compound_shape_and_aggregate_limits_refuse_before_payload_decoding() {
    let ty = zkc_test_support::variants::logical(
        "Pair",
        json!([["pair", ["vector:bls12-381.fr", "vector:bls12-381.fr"]]]),
    );
    let (raw, _) = fixture(&ty);
    let mut limits = HostLimits::default();
    limits.capacity.elements = 4;
    let host = self::host(&raw, limits);
    let vector = || InputValue::from(Value::Vector(vec![zkc_backends::Scalar::from(1); 3].into()));
    let mut wire = b"ZKCV\x00\x42\x03\0\0\0".to_vec();
    // Valid shape, deliberately invalid field encodings. Whole-value count
    // refusal must occur before expensive canonical element decoding.
    wire.extend_from_slice(&[255; 96]);
    let inputs = request(|| InputValue::Variant {
        alternative: 0,
        payload: vec![InputValue::Wire(wire.clone()), vector()],
    });
    crate::host::admission::DECODE_COUNT.set(0);
    assert_eq!(refusal(&host, &inputs), "native-wire-limit");
    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
    for (value, expected) in [
        (
            InputValue::Variant {
                alternative: 1,
                payload: vec![],
            },
            "native-input-alternative",
        ),
        (
            InputValue::Variant {
                alternative: 0,
                payload: vec![],
            },
            "native-input-payload",
        ),
        (
            InputValue::Variant {
                alternative: 0,
                payload: vec![vector(), Value::Bool(false).into()],
            },
            "native-input-type",
        ),
        (
            InputValue::Variant {
                alternative: 0,
                payload: vec![vector(), InputValue::Resource { budget: 1 }],
            },
            "native-input-private",
        ),
    ] {
        let mut inputs = request(|| InputValue::Variant {
            alternative: 0,
            payload: vec![vector(), vector()],
        });
        inputs.roles[0].inputs[0] = value;
        assert_eq!(refusal(&host, &inputs), expected);
        assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
    }
}

#[test]
fn reusable_material_retains_setup_checks_and_per_invocation_charges() {
    let capacity = Capacity::default();
    let bounds = capacity.backend().ark_bounds();
    let keys = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
    let other = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("material.pk");
    std::fs::write(&path, keys.prover_key().to_bytes(&bounds).unwrap()).unwrap();
    let material = ProverMaterial::from_file(
        &path,
        keys.prover_key().material_fingerprint(),
        keys.verifier_key(),
        capacity,
    )
    .unwrap();
    std::fs::remove_file(&path).unwrap();
    let authority = SetupAuthority {
        keys: BTreeMap::from([("setup".into(), keys.verifier_key().metadata().key_id())]),
        inputs: BTreeMap::from([
            (("Alice".into(), 0), "setup".into()),
            (("Bob".into(), 0), "setup".into()),
        ]),
    };
    let (raw, _) = fixture("prover_key:multilinear.kzg.bls12-381/0");
    let admit = |limits| {
        RunHost::admit(
            &raw,
            &Sha256::digest(&raw).into(),
            limits,
            authority.clone(),
        )
        .unwrap()
    };
    let host = admit(HostLimits::default());
    let mut inputs = request(|| InputValue::ProverKey(material.clone()));
    inputs.setups.insert(
        "setup".into(),
        keys.verifier_key().to_bytes(&bounds).unwrap(),
    );
    crate::host::admission::IMPORT_COUNT.set(0);
    let first = host.prepare_typed(&inputs).unwrap().execute();
    assert_eq!(
        first.execution.as_ref().unwrap().outcome,
        Outcome::Completed
    );
    assert!(first.cleanup_errors.is_empty());
    assert_eq!(crate::host::admission::IMPORT_COUNT.get(), 0);
    std::thread::scope(|scope| {
        let calls: Vec<_> = (0..2)
            .map(|_| scope.spawn(|| host.prepare_typed(&inputs).unwrap().execute().json()))
            .collect();
        for call in calls {
            assert_eq!(call.join().unwrap(), first.json());
        }
    });
    let mut limits = HostLimits::default();
    limits.capacity.values.live_bytes = 2 * material.value().retained_bytes()
        + Value::VerifierKey(Arc::new(keys.verifier_key().clone())).retained_bytes()
        - 1;
    assert_eq!(
        refusal(&admit(limits), &inputs),
        "artifact-input-bytes-limit"
    );
    limits = HostLimits::default();
    limits.capacity.value_bytes = material.value().retained_bytes() - 1;
    assert!(refusal(&admit(limits), &inputs).contains("output-bytes"));
    let wrong = ProverMaterial::from_bytes(
        &other.prover_key().to_bytes(&bounds).unwrap(),
        other.prover_key().material_fingerprint(),
        other.verifier_key(),
        capacity,
    )
    .unwrap();
    inputs.roles[0].inputs[0] = InputValue::ProverKeyFile {
        path: path.to_str().unwrap().into(),
        fingerprint: material.fingerprint(),
    };
    inputs.roles[1].inputs[0] = InputValue::ProverKey(wrong);
    assert_eq!(refusal(&host, &inputs), "native-proof-input-setup");
}
