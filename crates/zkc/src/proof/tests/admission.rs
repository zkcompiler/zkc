//! Independently authored Program and deployment: the verifier returns the
//! second received Boolean. Public input binding is a separate Host property.
use super::*;
mod reconstructed;

fn deployment() -> Json {
    let boolean = "bool@native.bool/0";
    let candidate = json!([
        "zkc.program/0",
        [],
        [],
        [
            [
                "participant",
                "p",
                "root",
                "P",
                [["a", boolean], ["b", boolean], ["public", boolean]],
                [],
                [
                    ["send", "first", "first", "V", "a"],
                    ["send", "second", "second", "V", "b"],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "v",
                "root",
                "V",
                [["public", boolean]],
                [boolean],
                [
                    ["receive", "first", "first", "P", "a", boolean],
                    ["receive", "second", "second", "P", "b", boolean],
                    ["return", ["b"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ]);
    let origin = |site| {
        hex(&logical::encode_tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            ["message", "protocol", site, site, "P", "V"]
        ]))
        .unwrap())
    };
    let first = origin("first");
    let second = origin("second");
    let descriptor = json!([
        "zkc.native-proof-descriptor/0",
        [
            "zkc.native-proof-policy/0",
            "main",
            "P",
            "V",
            "3",
            "",
            [],
            ["2"],
            [],
            "zkc.framed/0",
            "",
            []
        ],
        "zkc.native-origin/0",
        [["message", first], ["message", second]],
        [["V", "2", "bool", "zkcv.bool/0"]],
        [
            [first, "bool", "zkcv.bool/0"],
            [second, "bool", "zkcv.bool/0"]
        ],
        [],
        [],
        r#"{"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"entries":[],"kind":"exact"}}"#
    ]);
    let mut result = json!([
        "zkc.native-proof/0",
        "0".repeat(64),
        descriptor,
        "",
        candidate.to_string(),
        "",
        [
            [
                "P",
                "p",
                [["0", "bool"], ["1", "bool"], ["2", "bool"]],
                [],
                [],
                ""
            ],
            ["V", "v", [["2", "bool"]], [["3", "bool"]], [], "0"]
        ],
        [
            "true",
            "false",
            "false",
            "true",
            "false",
            "true",
            crate::entry::OracleSelection::default()
                .canonical_json()
                .unwrap()
        ],
        [[first, "first"], [second, "second"]]
    ]);
    seal(&mut result);
    result
}

fn seal(value: &mut Json) {
    value[3] = json!(hash(&logical::encode_tree(&value[2]).unwrap()));
    value[5] = json!(hash(value[4].as_str().unwrap().as_bytes()));
}

fn admit(value: &Json) -> Result<NativeDeployment> {
    let bytes = serde_json::to_vec(value).unwrap();
    NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
}

fn normalized_selection(entries: Json) -> String {
    json!({"authentication":"per-query", "format":"zkc.oracle-selection/0",
        "order":"unrestricted", "roots":{"entries":entries,"kind":"exact"}})
    .to_string()
}

fn selection_root(path: u32) -> Json {
    json!({"entry":"main", "path":[path], "scheme":"",
        "grouping":"individual", "order":"natural"})
}

#[test]
fn descriptor_requires_exactly_nine_fields() {
    let mut old = deployment();
    old[2].as_array_mut().unwrap().pop();
    seal(&mut old);
    assert!(admit(&old).is_err());
    let mut extra = deployment();
    extra[2].as_array_mut().unwrap().push(json!([]));
    seal(&mut extra);
    assert!(admit(&extra).is_err());
    assert_eq!(deployment()[2].as_array().unwrap().len(), 9);
    admit(&deployment()).unwrap();
}

#[test]
fn normalized_selection_requires_strict_exact_canonical_inventory() {
    let valid = normalized_selection(json!([selection_root(0)]));
    let parsed: Json = serde_json::from_str(&valid).unwrap();
    for bad in [
        String::new(),
        "{}".into(),
        "[]".into(),
        "null".into(),
        crate::entry::OracleSelection::default()
            .canonical_json()
            .unwrap(),
        format!(" {valid}"),
        serde_json::to_string_pretty(&parsed).unwrap(),
        valid.replace("per-query", "per\\u002dquery"),
        valid.replace("zkc.oracle-selection/0", "zkc.oracle-selection/1"),
        valid.replacen('{', "{\"unknown\":[],", 1),
        valid.replacen('{', "{\"authentication\":\"per-query\",", 1),
        valid.replace("\"scheme\":\"\"", "\"scheme\":\"\",\"sch\\u0065me\":\"\""),
        valid.replace("[0]", "[-0]"),
        valid.replace("[0]", "[]"),
        valid.replace("[0]", "[4294967296]"),
        normalized_selection(json!([selection_root(0), selection_root(0)])),
        normalized_selection(json!([selection_root(1), selection_root(0)])),
    ] {
        let mut value = deployment();
        value[2][8] = json!(bad);
        seal(&mut value);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-oracle-selection");
    }
    for field in ["format", "roots", "order", "authentication"] {
        let mut partial = parsed.clone();
        partial.as_object_mut().unwrap().remove(field);
        let mut value = deployment();
        value[2][8] = json!(partial.to_string());
        seal(&mut value);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-oracle-selection");
    }
}

#[test]
fn uniform_request_checks_every_table_and_global_selection_rule() {
    let roots = json!([selection_root(0), selection_root(1)]);
    let baseline: Json = serde_json::from_str(&normalized_selection(roots)).unwrap();
    let mut value = deployment();
    value[2][8] = json!(baseline.to_string());
    seal(&mut value);
    admit(&value).unwrap(); // Completeness requires source, which is absent here.
    for (field, changed) in [
        ("scheme", "selected/0"),
        ("grouping", "antipodal-pairs"),
        ("order", "bit-reversed"),
    ] {
        let mut normalized = baseline.clone();
        normalized["roots"]["entries"][1][field] = json!(changed);
        // Non-default layout is legal with an explicit scheme, but still must
        // agree with the requested uniform table for every root.
        normalized["roots"]["entries"][1]["scheme"] = json!("selected/0");
        value[2][8] = json!(normalized.to_string());
        seal(&mut value);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-oracle-selection");
    }
    for (field, changed) in [
        ("order", "after-final-draw"),
        ("authentication", "atomic-blocks"),
    ] {
        let mut normalized = baseline.clone();
        normalized[field] = json!(changed);
        value[2][8] = json!(normalized.to_string());
        seal(&mut value);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-oracle-selection");
    }
}

#[test]
fn exact_request_rejects_partial_extraneous_and_changed_root_inventory() {
    let canonical = normalized_selection(json!([selection_root(0), selection_root(1)]));
    let mut value = deployment();
    value[7][6] = json!(canonical);
    value[2][8] = json!(canonical);
    seal(&mut value);
    admit(&value).unwrap();
    for roots in [
        json!([]),
        json!([selection_root(0)]),
        json!([selection_root(0), selection_root(1), selection_root(2)]),
        json!([selection_root(0), selection_root(2)]),
    ] {
        value[2][8] = json!(normalized_selection(roots));
        seal(&mut value);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-oracle-selection");
    }
}

#[test]
fn oversized_event_inventories_refuse_before_decoding_their_rows() {
    for field in [3, 5] {
        let mut value = deployment();
        value[2][field] = json!(vec![json!([]); 2049]);
        seal(&mut value);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-event-map");
    }
}

#[test]
fn raw_transport_requires_one_byte_message_and_executes_through_the_sdk() {
    let mut value = deployment();
    value[2][1][9] = json!("raw.bytes/0");
    seal(&mut value);
    assert_eq!(admit(&value).unwrap_err(), "native-proof-format");
    let mut program: Json = serde_json::from_str(value[4].as_str().unwrap()).unwrap();
    for i in [0, 1] {
        program[3][0][4][i][1] = json!("bytes@native.bytes/0");
        value[6][0][2][i][1] = json!("bytes");
    }
    program[3][0][6].as_array_mut().unwrap().remove(1);
    program[3][1][6].as_array_mut().unwrap().remove(1);
    program[3][1][6][0][5] = json!("bytes@native.bytes/0");
    program[3][1][6][1][1] = json!(["public"]);
    value[4] = json!(program.to_string());
    value[2][3].as_array_mut().unwrap().truncate(1);
    value[2][5].as_array_mut().unwrap().truncate(1);
    value[2][5][0][1] = json!("bytes");
    value[2][5][0][2] = json!("zkc.native-data/0");
    value[8].as_array_mut().unwrap().truncate(1);
    seal(&mut value);
    let host = admit(&value).unwrap();
    let input = || InputValue::Native(Box::new(Value::Bytes((&b"raw payload"[..]).into())));
    let mut producer = request(true, true, true);
    producer.inputs[0] = input();
    producer.inputs[1] = input();
    let proof = host
        .execute(&producer, Invocation::Prove)
        .unwrap()
        .outcome
        .unwrap();
    assert_eq!(proof, b"raw payload");
    let verified = host
        .execute(&request(false, true, true), Invocation::Verify(&proof))
        .unwrap();
    assert!(verified.outcome.is_ok());
    assert!(verified.cleanup_errors.is_empty());
    assert_eq!(verified.bytes, proof.len());
    assert_eq!(verified.messages, 1);

    // Raw transport preserves the authored algorithm. Host context identifies
    // a report; it is not silently prepended to an external proof transcript.
    let mut other_context = request(false, true, true);
    other_context.context = b"another host invocation".to_vec();
    let other = host
        .execute(&other_context, Invocation::Verify(&proof))
        .unwrap();
    assert!(other.outcome.is_ok());
    assert_ne!(other.binding, verified.binding);

    producer.inputs[0] = InputValue::Native(Box::new(Value::Bytes(Default::default())));
    let empty = host.execute(&producer, Invocation::Prove).unwrap();
    assert!(empty.outcome.unwrap().is_empty());
    let empty = host
        .execute(&request(false, true, true), Invocation::Verify(&[]))
        .unwrap();
    assert!(empty.outcome.is_ok());
    assert_eq!(empty.messages, 1);
    assert_eq!(empty.bytes, 0);

    // Application calls attach one cumulative ledger; it must retain the same
    // raw format, including the single empty message, without native framing.
    for payload in [b"raw payload".as_slice(), b"".as_slice()] {
        let ledger =
            zkc_runtime::vm::ExecutionLedger::new(host.capacity.values, host.capacity.work);
        let mut capacity = host.capacity;
        capacity.values.live_bytes /= 2;
        let shared = host
            .clone()
            .with_invocation_limits(
                capacity,
                host.external_work_limit,
                host.ring_work_limit,
                host.sequence_work_limit,
                host.proof_bytes_limit,
            )
            .with_shared_ledger(ledger.clone());
        let report = shared
            .execute(&request(false, true, true), Invocation::Verify(payload))
            .unwrap();
        assert!(report.outcome.is_ok(), "{:?}", report.outcome);
        assert!(report.cleanup_errors.is_empty());
        assert_eq!(report.messages, 1);
        assert_eq!(report.bytes, payload.len());
        assert_eq!(ledger.snapshot().pending_value_bytes, 0);
    }
}

fn request(producer: bool, decision: bool, public: bool) -> ProofInputs {
    let value = |v| InputValue::Native(Box::new(Value::Bool(v)));
    ProofInputs {
        public: vec![value(public)],
        inputs: if producer {
            vec![value(!decision), value(decision), value(public)]
        } else {
            vec![value(public)]
        },
        context: b"independent host case".to_vec(),
        services: vec![],
        transcript_budget: 0,
    }
}

#[test]
fn cpu_context_reaches_both_proof_roles_without_changing_default_deployment() {
    let original = admit(&deployment()).unwrap();
    let worker = |cpu: &CpuExecution| cpu.execute(|| std::thread::current().id());
    let original_worker = worker(original.cpu());
    let cpu = CpuExecution::new(1).unwrap();
    let id = worker(&cpu);
    if cfg!(feature = "parallel") {
        assert_ne!(id, original_worker);
    } else {
        assert_eq!(id, original_worker);
    }
    assert_eq!(worker(original.clone().cpu()), original_worker);
    if cfg!(feature = "parallel") {
        assert_ne!(worker(admit(&deployment()).unwrap().cpu()), original_worker);
    } else {
        assert_eq!(worker(admit(&deployment()).unwrap().cpu()), original_worker);
    }
    assert_eq!(worker(original.clone().with_cpu(cpu.clone()).cpu()), id);
    let bytes = serde_json::to_vec(&deployment()).unwrap();
    let host = NativeDeployment::admit_with_cpu(
        &bytes,
        &Sha256::digest(&bytes).into(),
        Default::default(),
        cpu.clone(),
    )
    .unwrap();
    assert_eq!(worker(host.clone().cpu()), id);
    #[allow(clippy::drop_non_drop)] // Serial builds have no owned pool to release.
    drop(cpu);
    let ledger = zkc_runtime::vm::ExecutionLedger::new(host.capacity.values, host.capacity.work);
    let mut child_capacity = host.capacity;
    child_capacity.values.live_bytes /= 2;
    let host = host
        .clone()
        .with_invocation_limits(
            child_capacity,
            host.external_work_limit,
            host.ring_work_limit,
            host.sequence_work_limit,
            host.proof_bytes_limit,
        )
        .with_shared_ledger(ledger);
    for producer in [true, false] {
        let mut imports = crate::host::setups::VerifierKeys::new(
            host.capacity.backend().ark_bounds(),
            host.installation().clone(),
        );
        let prepared = host
            .prepare_inputs(&request(producer, true, true), producer, &mut imports)
            .unwrap();
        assert_eq!(worker(prepared.backend.cpu()), id);
    }
    let produced = host
        .execute(&request(true, true, true), Invocation::Prove)
        .unwrap();
    assert!(produced.cleanup_errors.is_empty());
    let proof = produced.outcome.unwrap();
    let verified = host
        .execute(&request(false, true, true), Invocation::Verify(&proof))
        .unwrap();
    assert_eq!(verified.verification_result(), Some(true));
    assert!(verified.cleanup_errors.is_empty());
    assert_eq!(worker(original.cpu()), original_worker);
}

fn deployment_with_preparation(private: bool) -> Json {
    let mut value = deployment();
    let mut program: Json = serde_json::from_str(value[4].as_str().unwrap()).unwrap();
    let boolean = "bool@native.bool/0";
    for (role, function) in [(0, "prepare_p"), (1, "prepare_v")] {
        program[2].as_array_mut().unwrap().push(json!([
            "function",
            function,
            [["x", boolean]],
            [boolean],
            [["return", ["x"]]],
            [function, []]
        ]));
        let input = if role == 0 && private { "b" } else { "public" };
        program[3][role][6].as_array_mut().unwrap().insert(
            0,
            json!(["local", "prepare", function, [input], ["prepared"]]),
        );
    }
    value[4] = json!(program.to_string());
    seal(&mut value);
    value
}

#[test]
fn host_authorizes_only_statement_ports_for_computation_reuse() {
    use crate::execution::{Capacity, PreparedData};
    let host = admit(&deployment_with_preparation(false)).unwrap();
    let mut inputs = request(true, true, true);
    // Equal canonical data retains authority even when public and role inputs
    // use different representations. Equality alone cannot authorize a witness.
    inputs.public[0] = PreparedData::from_value(Value::Bool(true), Capacity::default())
        .unwrap()
        .into();
    let cold = host.execute(&inputs, Invocation::Prove).unwrap();
    assert!(cold.outcome.is_ok());
    assert_eq!(host.preparation_stats().entries, 1);
    let hits = host.preparation_stats().hits;
    let warm = host.execute(&inputs, Invocation::Prove).unwrap();
    assert_eq!(host.preparation_stats().hits, hits + 1);
    assert_eq!(cold.outcome, warm.outcome);
    assert_eq!(cold.binding, warm.binding);
    assert_eq!(cold.usage, warm.usage);
    assert_eq!(cold.external_work, warm.external_work);
    assert!(cold.cleanup_errors.is_empty() && warm.cleanup_errors.is_empty());

    let proof = warm.outcome.unwrap();
    let verifier = request(false, true, true);
    let cold = host.execute(&verifier, Invocation::Verify(&proof)).unwrap();
    assert!(cold.outcome.is_ok());
    assert_eq!(host.preparation_stats().entries, 2);
    let hits = host.preparation_stats().hits;
    let warm = host.execute(&verifier, Invocation::Verify(&proof)).unwrap();
    assert_eq!(host.preparation_stats().hits, hits + 1);
    assert_eq!(cold.outcome, warm.outcome);
    assert_eq!(cold.binding, warm.binding);
    assert_eq!(cold.usage, warm.usage);
    for report in [&cold, &warm] {
        assert!(matches!(
            report.outputs.as_ref().unwrap()[&3],
            Value::Bool(true)
        ));
        assert!(report.cleanup_errors.is_empty());
    }
    inputs.inputs[2] = InputValue::Native(Box::new(Value::Bool(false)));
    assert_eq!(
        host.execute(&inputs, Invocation::Prove).err().unwrap(),
        "native-proof-shared-public-input"
    );

    let private = admit(&deployment_with_preparation(true)).unwrap();
    for _ in 0..2 {
        assert!(
            private
                .execute(&request(true, true, true), Invocation::Prove)
                .unwrap()
                .outcome
                .is_ok()
        );
    }
    assert_eq!(private.preparation_stats().entries, 0);
    assert_eq!(private.preparation_stats().hits, 0);
}

#[test]
fn prepared_public_data_preserves_binding_and_statement_authority() {
    use crate::execution::{Capacity, PreparedData};
    let host = admit(&deployment()).unwrap();
    let data = PreparedData::from_value(Value::Bool(true), Capacity::default()).unwrap();
    let expected = host
        .execute(&request(true, true, true), Invocation::Prove)
        .unwrap();
    let mut inputs = request(true, true, true);
    inputs.public[0] = data.clone().into();
    inputs.inputs[2] = PreparedData::from_wire(
        data.physical_type().clone(),
        data.canonical_bytes().to_vec(),
        Capacity::default(),
    )
    .unwrap()
    .into();
    crate::host::admission::DECODE_COUNT.set(0);
    let actual = host.execute(&inputs, Invocation::Prove).unwrap();
    assert_eq!(actual.binding, expected.binding);
    assert_eq!(actual.outcome, expected.outcome);
    assert_eq!(crate::host::admission::DECODE_COUNT.get(), 0);
    let proof = actual.outcome.unwrap();
    let mut verifier = request(false, true, true);
    verifier.public[0] = data.clone().into();
    verifier.inputs[0] = data.into();
    for _ in 0..3 {
        assert!(
            host.execute(&verifier, Invocation::Verify(&proof))
                .unwrap()
                .outcome
                .is_ok()
        );
    }
    inputs.inputs[2] = PreparedData::from_value(Value::Bool(false), Capacity::default())
        .unwrap()
        .into();
    assert_eq!(
        host.execute(&inputs, Invocation::Prove).err().unwrap(),
        "native-proof-shared-public-input"
    );
}

#[test]
fn shared_wire_public_data_uses_contents_and_canonical_admission() {
    use crate::execution::{Capacity, PreparedData};
    use std::sync::Arc;

    let host = admit(&deployment()).unwrap();
    let data = PreparedData::from_value(Value::Bool(true), Capacity::default()).unwrap();
    let expected = host
        .execute(&request(true, true, true), Invocation::Prove)
        .unwrap();
    for same_owner in [false, true] {
        let public: Arc<Vec<u8>> = data.canonical_bytes().to_vec().into();
        let role = if same_owner {
            public.clone()
        } else {
            data.canonical_bytes().to_vec().into()
        };
        assert_eq!(Arc::ptr_eq(&public, &role), same_owner);
        assert_eq!(public.as_slice(), role.as_slice());
        let mut inputs = request(true, true, true);
        inputs.public[0] = InputValue::Wire(public.clone());
        inputs.inputs[2] = InputValue::Wire(role);
        crate::host::admission::DECODE_COUNT.set(0);
        let actual = host.execute(&inputs, Invocation::Prove).unwrap();
        assert_eq!(actual.binding, expected.binding);
        assert_eq!(actual.outcome, expected.outcome);
        assert_eq!(crate::host::admission::DECODE_COUNT.get(), 1);
        let proof = actual.outcome.unwrap();
        let mut verifier = request(false, true, true);
        verifier.public[0] = InputValue::Wire(public);
        verifier.inputs[0] = InputValue::Wire(data.canonical_bytes().to_vec().into());
        assert!(
            host.execute(&verifier, Invocation::Verify(&proof))
                .unwrap()
                .outcome
                .is_ok()
        );
        for change_public in [false, true] {
            let public: Arc<Vec<u8>> = data.canonical_bytes().to_vec().into();
            let mut changed = public.clone();
            Arc::make_mut(&mut changed)[6] = 0;
            assert_eq!(public.as_slice(), data.canonical_bytes());
            inputs.public[0] = InputValue::Wire(if change_public {
                changed.clone()
            } else {
                public.clone()
            });
            inputs.inputs[2] = InputValue::Wire(if change_public { public } else { changed });
            assert_eq!(
                host.execute(&inputs, Invocation::Prove).err().unwrap(),
                "native-proof-shared-public-input"
            );
        }
    }
    // Sharing one invalid frame cannot replace canonical decoding with identity.
    let invalid: Arc<Vec<u8>> = b"ZKCV\x00\x05\x02".to_vec().into();
    let mut inputs = request(true, true, true);
    inputs.public[0] = InputValue::Wire(invalid.clone());
    inputs.inputs[2] = InputValue::Wire(invalid);
    let invalid_wire = host.execute(&inputs, Invocation::Prove).err().unwrap();
    assert_eq!(invalid_wire, "native-wire-invalid:boolean");
    let canonical_control = PreparedData::from_wire(
        data.physical_type().clone(),
        b"ZKCV\x00\x05\x02".to_vec(),
        Capacity::default(),
    )
    .unwrap_err();
    assert_eq!(invalid_wire, canonical_control);
    inputs.public[0] = InputValue::Wire(data.canonical_bytes().to_vec().into());
    inputs.inputs[2] = Value::Index(0).into();
    assert_eq!(
        host.execute(&inputs, Invocation::Prove).err().unwrap(),
        "native-input-type"
    );
}

#[test]
fn actual_received_decision_and_public_context_govern_verification() {
    let deployment = admit(&deployment()).unwrap();
    for decision in [false, true] {
        let produced = deployment
            .execute(
                &request(true, decision, true),
                crate::proof::Invocation::one_shot(None),
            )
            .unwrap();
        assert!(produced.cleanup_errors.is_empty());
        assert_eq!(produced.messages, 2);
        let proof = produced.outcome.unwrap();
        // Two canonical Boolean frames, in the actual send order.
        assert_eq!(proof.len(), 70);
        let mut expected = Vec::new();
        for value in [!decision, decision] {
            expected.extend([7, 0, 0, 0, 0, 0, 0, 0]);
            expected.extend(b"ZKCV\x00\x05");
            expected.push(u8::from(value));
        }
        assert_eq!(&proof[40..], expected);
        let verified = deployment
            .execute(
                &request(false, true, true),
                crate::proof::Invocation::one_shot(Some(&proof)),
            )
            .unwrap();
        assert_eq!(verified.messages, 2);
        assert!(verified.cleanup_errors.is_empty());
        if decision {
            assert!(verified.outcome.is_ok());
            assert!(matches!(verified.outputs.unwrap()[&3], Value::Bool(true)));
            let changed = deployment
                .execute(
                    &request(false, true, false),
                    crate::proof::Invocation::one_shot(Some(&proof)),
                )
                .unwrap();
            assert_eq!(changed.outcome.unwrap_err(), "proof-header");
            assert!(changed.outputs.is_none());
        } else {
            assert_eq!(verified.outcome.unwrap_err(), "artifact-rejected");
            assert!(verified.outputs.is_none());
        }
    }
}

#[test]
fn wire_role_public_and_authority_checks_keep_their_refusal_order() {
    let valid = deployment();
    let mut bad = valid.clone();
    bad[8][0][1] = json!("second");
    bad[8][1][1] = json!("first");
    bad[6][0][1] = json!("wrong-participant");
    bad[2][4][0][1] = json!("1");
    seal(&mut bad);
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-wire-map");
    bad[8] = valid[8].clone();
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-role-map");
    bad[6] = valid[6].clone();
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-public-map");
    bad[2][4] = valid[2][4].clone();
    seal(&mut bad);
    let bytes = serde_json::to_vec(&bad).unwrap();
    let extra_authority = SetupAuthority {
        keys: [(2, [0; 32])].into(),
        inputs: BTreeMap::new(),
    };
    assert_eq!(
        NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), extra_authority)
            .unwrap_err(),
        "native-proof-key-authority"
    );
    assert!(admit(&bad).is_ok());
}

#[test]
fn typed_pin_admission_limits_then_authenticates_before_decoding() {
    let bytes = serde_json::to_vec(&deployment()).unwrap();
    let expected_sha256: [u8; 32] = Sha256::digest(&bytes).into();
    let admitted = NativeDeployment::admit(&bytes, &expected_sha256, Default::default()).unwrap();
    assert_eq!(admitted.publication, hex(&expected_sha256));

    assert_eq!(
        NativeDeployment::admit(
            &vec![b'['; INPUT_LIMIT + 1],
            &expected_sha256,
            Default::default(),
        )
        .unwrap_err(),
        "native-proof-deployment-limit"
    );
    assert_eq!(
        NativeDeployment::admit(b"[", &expected_sha256, Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    assert_eq!(
        NativeDeployment::admit(b"[", &Sha256::digest(b"[").into(), Default::default())
            .unwrap_err(),
        "artifact-json"
    );

    // Even a semantically identical JSON payload cannot reuse the original pin.
    let mut changed = bytes;
    changed.push(b'\n');
    assert_eq!(
        NativeDeployment::admit(&changed, &expected_sha256, Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    assert!(
        NativeDeployment::admit(
            &changed,
            &Sha256::digest(&changed).into(),
            Default::default(),
        )
        .is_ok()
    );
}

#[test]
fn authenticated_payload_still_requires_canonical_inner_source_digest() {
    let mut value = deployment();
    for source in [
        String::new(),
        "0".repeat(63),
        "0".repeat(65),
        "AB".repeat(32),
        "g".repeat(64),
        format!("0x{}", "0".repeat(62)),
        "é".repeat(32),
    ] {
        value[1] = json!(source);
        assert_eq!(admit(&value).unwrap_err(), "native-proof-digest");
    }
    value[1] = json!("ab".repeat(32));
    assert!(admit(&value).is_ok());
}

#[test]
fn authentication_and_inner_bindings_precede_candidate_and_interface_checks() {
    assert_eq!(
        NativeDeployment::admit(b"not json", &[0; 32], Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    let mut bad = deployment();
    bad[3] = json!("0".repeat(64));
    bad[4] = json!("invalid candidate");
    bad[6] = json!([]);
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-descriptor-binding");
    bad[3] = json!(hash(&logical::encode_tree(&bad[2]).unwrap()));
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-candidate-binding");
    seal(&mut bad);
    // Compare with independent ordinary Program admission of the same bad bytes.
    let backend = CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "native-proof", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let expected = zkc_runtime::vm::Program::decode(b"invalid candidate", zkc_cpu::cpu_contracts())
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap_err()
        .to_string();
    assert_eq!(admit(&bad).unwrap_err(), expected);
}

#[test]
fn message_origins_are_unique_complete_and_match_both_participants() {
    let valid = deployment();
    let mut duplicate = valid.clone();
    duplicate[2][3][1] = duplicate[2][3][0].clone();
    seal(&mut duplicate);
    assert_eq!(admit(&duplicate).unwrap_err(), "native-proof-origin-map");
    let mut missing = valid.clone();
    missing[2][5].as_array_mut().unwrap().pop();
    seal(&mut missing);
    assert_eq!(admit(&missing).unwrap_err(), "native-proof-message-map");
    let mut drift = valid;
    let mut candidate: Json = serde_json::from_str(drift[4].as_str().unwrap()).unwrap();
    candidate[3][1][6][0][2] = json!("other-schema");
    drift[4] = json!(candidate.to_string());
    seal(&mut drift);
    assert_eq!(admit(&drift).unwrap_err(), "native-proof-wire-map");
}

#[test]
fn ring_work_limit_cannot_raise_the_host_ceiling() {
    let limit = zkc_cpu::ring::DEFAULT_WORK_LIMIT;
    for allowed in [0, limit] {
        assert!(
            admit(&deployment())
                .unwrap()
                .with_ring_work_limit(allowed)
                .is_ok()
        );
    }
    assert_eq!(
        admit(&deployment())
            .unwrap()
            .with_ring_work_limit(limit + 1)
            .err()
            .unwrap(),
        "native-proof-ring-work-limit"
    );
}

#[test]
fn deployment_compilation_choices_have_exact_seven_string_shape() {
    let original = deployment();
    for choices in [
        json!([]),
        json!(["true", "false"]),
        json!(["true", "false", "false"]),
        json!(["true", "false", "false", "true"]),
        json!(["true", "false", "false", "true", "false"]),
        json!(["true", "false", "false", "true", "false", "true"]),
        json!(["true", "false", "false", "true", "false", "true", "false"]),
        json!([
            "true", "false", "false", "true", "false", "true", "false", "false"
        ]),
        json!(["true", "false", false, "true", "false", "true"]),
        json!(["true", "false", "false", "true", "false", "invalid"]),
        json!({"collectFoldFusion": false}),
    ] {
        let mut changed = original.clone();
        changed[7] = choices;
        assert!(admit(&changed).is_err());
    }
    for index in 0..7 {
        for value in [
            json!(false),
            json!(0),
            json!(null),
            json!([]),
            json!({}),
            json!("invalid"),
        ] {
            let mut changed = original.clone();
            // The outer tree admits strings and arrays only. Other JSON kinds
            // are rejected before compilation-choice decoding is reached.
            let expected = if value.is_string() || value.is_array() {
                "native-proof-choices"
            } else if value.is_object() {
                "artifact-json-kind"
            } else {
                "tree-kind"
            };
            changed[7][index] = value;
            assert_eq!(admit(&changed).err().unwrap(), expected, "choice {index}");
        }
    }
    for fuse in [false, true] {
        for finite in [false, true] {
            for collect_fold in [false, true] {
                for batching in [false, true] {
                    let mut changed = original.clone();
                    changed[7][2] = json!(if fuse { "true" } else { "false" });
                    changed[7][3] = json!(if finite { "true" } else { "false" });
                    changed[7][4] = json!(if collect_fold { "true" } else { "false" });
                    changed[7][5] = json!(if batching { "true" } else { "false" });
                    let mut expected: Vec<_> = [true, false, fuse, finite, collect_fold, batching]
                        .map(|value| value.to_string())
                        .into();
                    expected.push(
                        crate::entry::OracleSelection::default()
                            .canonical_json()
                            .unwrap(),
                    );
                    let admitted = admit(&changed).unwrap();
                    assert_eq!(admitted.choices.as_slice(), expected);
                    assert_eq!(admitted.source_interface().choices.as_slice(), expected);
                }
            }
        }
    }
}

#[test]
fn deployment_preserves_canonical_requested_selection_without_source_coverage_claims() {
    use crate::entry::{
        OracleAuthentication, OracleRoots, OracleSelection, OracleTableRealization,
    };
    let exact = OracleSelection::parse(
        r#"{"format":"zkc.oracle-selection/0","roots":{"kind":"exact","entries":[{"entry":"検証","path":[2,0],"scheme":"selected/0","grouping":"antipodal-pairs","order":"bit-reversed"},{"entry":"main","path":[0],"scheme":"","grouping":"individual","order":"natural"}]},"order":"after-final-draw","authentication":"atomic-blocks"}"#,
    )
    .unwrap();
    for selection in [
        OracleSelection::default(),
        OracleSelection {
            roots: OracleRoots::Exact(vec![]),
            ..Default::default()
        },
        OracleSelection {
            roots: OracleRoots::Uniform(OracleTableRealization {
                scheme: "selected/0".into(),
                ..Default::default()
            }),
            authentication: OracleAuthentication::AtomicBlocks,
            ..Default::default()
        },
        exact,
    ] {
        let mut changed = deployment();
        let canonical = selection.canonical_json().unwrap();
        changed[7][6] = json!(canonical);
        let mut normalized = selection;
        if matches!(normalized.roots, OracleRoots::Uniform(_)) {
            normalized.roots = OracleRoots::Exact(vec![]);
        }
        changed[2][8] = json!(normalized.canonical_json().unwrap());
        seal(&mut changed);
        // The Host checks requested/normalized consistency. It has no prepared
        // source inventory to establish completeness or scheme installation.
        let admitted = admit(&changed).unwrap();
        let expected = [
            "true", "false", "false", "true", "false", "true", &canonical,
        ]
        .map(str::to_owned);
        assert_eq!(admitted.choices, expected);
        assert_eq!(admitted.source_interface().choices, &expected);
    }
}

#[test]
fn deployment_selection_requires_strict_typed_canonical_json() {
    let canonical = crate::entry::OracleSelection::default()
        .canonical_json()
        .unwrap();
    let root =
        r#"{"entry":"main","path":[0],"scheme":"","grouping":"individual","order":"natural"}"#;
    let exact = format!(
        r#"{{"format":"zkc.oracle-selection/0","roots":{{"kind":"exact","entries":[{root}]}},"order":"unrestricted","authentication":"per-query"}}"#
    );
    for malformed in [
        String::new(),
        "{}".into(),
        "[]".into(),
        "null".into(),
        canonical.replace("zkc.oracle-selection/0", "zkc.oracle-selection/1"),
        canonical.replacen('{', "{\"unknown\":0,", 1),
        canonical.replacen('{', "{\"format\":\"zkc.oracle-selection/0\",", 1),
        canonical.replace("\"scheme\":\"\"", "\"scheme\":\"\",\"sch\\u0065me\":\"\""),
        canonical.replace("\"scheme\":\"\"", "\"scheme\":null"),
        canonical.replace("\"scheme\":\"\"", "\"scheme\":\"\\ud800\""),
        canonical.replace("\"uniform\"", "\"unknown\""),
        canonical.replace("\"individual\"", "\"unknown\""),
        canonical.replace("\"natural\"", "\"unknown\""),
        canonical.replace("\"unrestricted\"", "\"unknown\""),
        canonical.replace("\"per-query\"", "\"unknown\""),
        canonical.replace("\"individual\"", "\"antipodal-pairs\""),
        exact.replace(root, &format!("{root},{root}")),
        exact.replace("[0]", "[]"),
        exact.replace("[0]", "[-0]"),
        exact.replace("[0]", "[1.0]"),
        exact.replace("[0]", "[4294967296]"),
        format!("{canonical}{{}}"),
        "[".repeat(33) + &"]".repeat(33),
        " ".repeat(1024 * 1024 + 1),
        // Valid requests still refuse noncanonical artifact representation.
        format!(" {canonical}"),
        canonical.replace("per-query", "per\\u002dquery"),
        serde_json::to_string_pretty(&serde_json::from_str::<Json>(&canonical).unwrap()).unwrap(),
        exact,
    ] {
        let mut changed = deployment();
        changed[7][6] = json!(malformed);
        assert_eq!(admit(&changed).err().unwrap(), "native-proof-choices");
    }
}

#[test]
fn selected_installation_is_retained_by_low_level_proof_admission() {
    let selected = || {
        zkc_cpu::CpuInstallation::builder()
            .include(zkc_cpu::providers::Plonky3)
            .finish()
            .unwrap()
    };
    let raw = deployment().to_string().into_bytes();
    let host = NativeDeployment::admit_with_installation(
        &raw,
        &Sha256::digest(&raw).into(),
        Default::default(),
        CpuExecution::serial().unwrap(),
        selected(),
    )
    .unwrap();
    assert!(!host.installation().supports_setup());
    let report = host
        .execute(&request(true, true, true), Invocation::Prove)
        .unwrap();
    assert!(report.outcome.is_ok() && report.cleanup_errors.is_empty());
    let mut value = deployment();
    let mut program: Json = serde_json::from_str(value[4].as_str().unwrap()).unwrap();
    program[3][0][4]
        .as_array_mut()
        .unwrap()
        .push(json!(["omitted", "field:bls12-381.fr@arkworks.fr/0"]));
    value[6][0][2]
        .as_array_mut()
        .unwrap()
        .push(json!(["4", "field:bls12-381.fr"]));
    value[4] = json!(program.to_string());
    seal(&mut value);
    assert!(admit(&value).is_ok());
    let raw = value.to_string().into_bytes();
    assert!(
        NativeDeployment::admit_with_installation(
            &raw,
            &Sha256::digest(&raw).into(),
            Default::default(),
            CpuExecution::serial().unwrap(),
            selected()
        )
        .is_err()
    );
}
