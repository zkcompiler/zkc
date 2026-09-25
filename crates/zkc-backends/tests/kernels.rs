use zkc_runtime::interactive::Value as RuntimeValue;
mod common;
use common::*;
use serde_json::json;
use std::{collections::BTreeMap, sync::Arc};
use zkc_backends::*;
use zkc_runtime::interactive::{Runner, admit_supplied};

#[test]
fn every_field_polynomial_kernel_matches_hand_calculation() {
    let operations = vec![
        json!(["op", "c", "arkworks/field.constant", ["2"], [], ["two"]]),
        op("sum", "arkworks/poly.product_sum", &["a", "b"], &["sum"]),
        op("round", "arkworks/poly.product_round", &["a", "b"], &["q"]),
        op("boundary", "arkworks/poly.boundary", &["q"], &["boundary"]),
        op("rq", "arkworks/poly.round_evaluate", &["q", "r"], &["qr"]),
        op("fa", "arkworks/poly.fold", &["a", "r"], &["folded"]),
        op("eval", "arkworks/poly.evaluate", &["a", "p"], &["eval"]),
        op("empty", "arkworks/poly.empty_point", &[], &["empty"]),
        op(
            "append",
            "arkworks/poly.append_point",
            &["empty", "r"],
            &["onepoint"],
        ),
        op("add", "arkworks/field.add", &["r", "two"], &["plus"]),
        op("mul", "arkworks/field.mul", &["plus", "two"], &["times"]),
        op("eq", "arkworks/field.equal", &["sum", "boundary"], &["eq"]),
        op("and", "arkworks/bool.and", &["eq", "eq"], &["yes"]),
        op("require", "arkworks/control.require", &["yes"], &[]),
    ];
    let bytes = program(
        Some(2),
        &[
            ("a", "table"),
            ("b", "table"),
            ("r", "field"),
            ("p", "point"),
        ],
        operations,
        &[
            "field", "round", "field", "table", "field", "point", "field",
        ],
        &["sum", "q", "qr", "folded", "eval", "onepoint", "times"],
    );
    let (out, backend) = run(
        &bytes,
        ark_backend(Some(2)),
        vec![
            table(&[2, 3, 5, 7]),
            table(&[11, 13, 17, 19]),
            f(2),
            point(&[2, 3]),
        ],
    );
    let out = out.unwrap();
    assert_eq!(scalar(&out[0]), Scalar::from(279u64));
    let Value::Round(q) = &out[1] else { panic!() };
    // (2+3r)(11+6r) + (3+4r)(13+6r)
    assert_eq!(*q, [61u64, 115, 42].map(Scalar::from));
    assert_eq!(scalar(&out[2]), Scalar::from(459u64));
    let Value::Table(t) = &out[3] else { panic!() };
    assert_eq!(t.logical_values().unwrap(), [8u64, 11].map(Scalar::from));
    assert_eq!(scalar(&out[4]), Scalar::from(17u64));
    assert_eq!(scalar(&out[6]), Scalar::from(8u64));
    assert_eq!(backend.active_frames(), 0);
}

fn committed_fixture() -> (NativeBackend, Keys, Value, Vec<Value>) {
    let p = Policy::default();
    let keys = Keys::setup_for_development(2, &p.ark_bounds()).unwrap();
    let t = table(&[2, 3, 5, 7]);
    let bytes = program(
        Some(2),
        &[
            ("pk", "prover_key"),
            ("t", "table"),
            ("p", "point"),
            ("r", "field"),
        ],
        vec![
            op(
                "commit",
                "arkworks/pcs.commit",
                &["pk", "t"],
                &["c", "state"],
            ),
            op("scratch", "arkworks/poly.fold", &["t", "r"], &["scratch"]),
            op(
                "open",
                "arkworks/pcs.open",
                &["state", "p"],
                &["y", "proof"],
            ),
        ],
        &["commitment", "field", "proof", "opening_state"],
        &["c", "y", "proof", "state"],
    );
    let (out, backend) = run(
        &bytes,
        ark_backend(Some(2)),
        vec![
            Value::ProverKey(Arc::new(keys.prover_key().clone())),
            t.clone(),
            point(&[11, 13]),
            f(11),
        ],
    );
    (backend, keys, t, out.unwrap())
}
#[test]
fn original_custody_real_pcs_and_verifier_only_public_bytes() {
    let (prover, keys, original, out) = committed_fixture();
    assert!(matches!(out[3], Value::OpeningState(_)));
    let vkbytes = keys
        .verifier_key()
        .to_bytes(&Policy::default().ark_bounds())
        .unwrap();
    let key = zkc_arkworks::VerifierKey::from_bytes(
        &vkbytes,
        keys.verifier_key().metadata().key_id(),
        &Policy::default().ark_bounds(),
    )
    .unwrap();
    let verifier =
        NativeBackend::new(Policy::default(), entry(Some(2)), Some(key.clone())).unwrap();
    let c = verifier
        .decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse(
                    "commitment:multilinear.kzg.bls12-381/1",
                )
                .unwrap(),
            ),
            &prover.encode_value(&out[0]).unwrap(),
        )
        .unwrap();
    let y = verifier
        .decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("field:bls12-381.fr").unwrap(),
            ),
            &prover.encode_value(&out[1]).unwrap(),
        )
        .unwrap();
    let proof = verifier
        .decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("proof:multilinear.kzg.bls12-381/1")
                    .unwrap(),
            ),
            &prover.encode_value(&out[2]).unwrap(),
        )
        .unwrap();
    assert_eq!(verifier.active_frames(), 0);
    let bytes = program(
        Some(2),
        &[
            ("vk", "verifier_key"),
            ("c", "commitment"),
            ("p", "point"),
            ("y", "field"),
            ("proof", "proof"),
        ],
        vec![
            op(
                "check",
                "arkworks/pcs.check",
                &["vk", "c", "p", "y", "proof"],
                &["ok"],
            ),
            op("require", "arkworks/control.require", &["ok"], &[]),
        ],
        &["bool"],
        &["ok"],
    );
    let args = vec![
        Value::VerifierKey(Arc::new(key.clone())),
        c,
        point(&[11, 13]),
        y,
        proof,
    ];
    let (ok, v) = run(&bytes, verifier, args.clone());
    assert!(matches!(ok.unwrap()[0], Value::Bool(true)));
    assert_eq!(v.active_frames(), 0);
    let mut bad = args;
    bad[3] = f(0);
    let (failed, _) = run(
        &bytes,
        NativeBackend::new(Policy::default(), entry(Some(2)), Some(key)).unwrap(),
        bad,
    );
    assert_eq!(code(&failed.unwrap_err()), "rejected:require");
    let Value::Table(t) = original else { panic!() };
    assert_eq!(
        t.logical_values().unwrap(),
        [2u64, 3, 5, 7].map(Scalar::from)
    );
}
#[test]
fn opening_refuses_table_and_folded_scratch_at_admission() {
    // A mathematical table, whether original/equal/folded, is not private state.
    // No earlier commit in the same body supplies implicit access to an original.
    for replacement in ["t", "scratch"] {
        let bytes = program(
            Some(2),
            &[
                ("pk", "prover_key"),
                ("t", "table"),
                ("p", "point"),
                ("r", "field"),
            ],
            vec![
                op(
                    "commit",
                    "arkworks/pcs.commit",
                    &["pk", "t"],
                    &["c", "state"],
                ),
                op("fold", "arkworks/poly.fold", &["t", "r"], &["scratch"]),
                op(
                    "open",
                    "arkworks/pcs.open",
                    &[replacement, "p"],
                    &["y", "proof"],
                ),
            ],
            &["field", "proof"],
            &["y", "proof"],
        );
        assert_eq!(
            admit_supplied(&bytes, &ark_backend(Some(2)))
                .unwrap_err()
                .code,
            zkc_runtime::interactive::ErrorCode::Signature
        );
    }
}
#[test]
fn hostile_key_aware_codec_and_exact_length() {
    let (prover, keys, _, out) = committed_fixture();
    let recv = NativeBackend::new(
        Policy::default(),
        entry(Some(2)),
        Some(keys.verifier_key().clone()),
    )
    .unwrap();
    let other = Keys::setup_for_development(2, &Policy::default().ark_bounds()).unwrap();
    let wrong = NativeBackend::new(
        Policy::default(),
        entry(Some(2)),
        Some(other.verifier_key().clone()),
    )
    .unwrap();
    let different_arity = Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    let wrong_n = NativeBackend::new(
        Policy::default(),
        entry(Some(1)),
        Some(different_arity.verifier_key().clone()),
    )
    .unwrap();
    for index in [0, 2] {
        let v = &out[index];
        let ty = v.physical_type();
        let valid = prover.encode_value(v).unwrap();
        assert!(recv.decode_typed_value(ty.clone(), &valid).is_ok());
        assert!(wrong.decode_typed_value(ty.clone(), &valid).is_err());
        assert!(wrong_n.decode_typed_value(ty.clone(), &valid).is_err());
        assert!(
            ark_backend(Some(2))
                .decode_typed_value(ty.clone(), &valid)
                .is_err()
        );
        for end in 0..valid.len() {
            assert!(recv.decode_typed_value(ty.clone(), &valid[..end]).is_err());
        }
        let mut trailing = valid.clone();
        trailing.push(0);
        assert!(recv.decode_typed_value(ty.clone(), &trailing).is_err());
        for position in [0, 5, 6, 14, 23, 55] {
            let mut damaged = valid.clone();
            damaged[position] ^= 0xff;
            assert!(
                recv.decode_typed_value(ty.clone(), &damaged).is_err(),
                "accepted offset {position}"
            );
        }
        let mut arity = valid.clone();
        arity[15..23].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(recv.decode_typed_value(ty.clone(), &arity).is_err());
        let mut point = valid.clone();
        point[87..].fill(0xff);
        assert!(recv.decode_typed_value(ty.clone(), &point).is_err());
    }
    let mut noncanonical = recv.encode_value(&f(1)).unwrap();
    noncanonical[6..].fill(0xff);
    assert!(
        recv.decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("field:bls12-381.fr").unwrap()
            ),
            &noncanonical
        )
        .is_err()
    );
    assert!(zkc_runtime::interactive::LogicalType::parse("scalar:bls12-381.fr").is_err());
    // The removed scalar carrier's wire tag cannot be decoded as a nominal field.
    let mut old_scalar = recv.encode_value(&f(1)).unwrap();
    old_scalar[5] = 8;
    assert!(
        recv.decode_typed_value(f(1).physical_type(), &old_scalar)
            .is_err()
    );
    assert!(
        prover
            .encode_value(&Value::ProverKey(Arc::new(keys.prover_key().clone())))
            .is_err()
    );
    let small = NativeBackend::new(
        Policy {
            max_wire_bytes: 10,
            ..Policy::default()
        },
        entry(None),
        None,
    )
    .unwrap();
    assert_eq!(
        small
            .decode_typed_value(
                zkc_runtime::interactive::PhysicalType::default_for(
                    zkc_runtime::interactive::LogicalType::parse("field:bls12-381.fr").unwrap()
                ),
                &recv.encode_value(&f(1)).unwrap()
            )
            .unwrap_err()
            .code,
        "exhausted:wire-bytes"
    );
}
#[test]
fn entry_shape_setup_and_public_correspondence_policy() {
    let keys = Keys::setup_for_development(2, &Policy::default().ark_bounds()).unwrap();
    let other = Keys::setup_for_development(2, &Policy::default().ark_bounds()).unwrap();
    let bytes = program(
        Some(2),
        &[
            ("pk", "prover_key"),
            ("vk", "verifier_key"),
            ("t", "table"),
            ("claim", "field"),
        ],
        vec![],
        &["field"],
        &["claim"],
    );
    for (vk, t) in [
        (keys.verifier_key().clone(), table(&[1, 2])),
        (other.verifier_key().clone(), table(&[1, 2, 3, 4])),
    ] {
        let b = ark_backend(Some(2));
        let admitted = admit_supplied(&bytes, &b).unwrap();
        assert!(
            Runner::new(
                &admitted,
                "main",
                "P",
                "session",
                b,
                vec![
                    Value::ProverKey(Arc::new(keys.prover_key().clone())),
                    Value::VerifierKey(Arc::new(vk)),
                    t,
                    f(1)
                ]
            )
            .is_err()
        );
    }
    let policy = EntryPolicy::new(
        domain(),
        Some(2),
        PublicInputs::Exact(BTreeMap::from([("claim".into(), f(7))])),
    );
    let b = NativeBackend::new(Policy::default(), policy, None).unwrap();
    let admitted = admit_supplied(&bytes, &b).unwrap();
    let result = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        b,
        vec![
            Value::ProverKey(Arc::new(keys.prover_key().clone())),
            Value::VerifierKey(Arc::new(keys.verifier_key().clone())),
            table(&[1, 2, 3, 4]),
            f(8),
        ],
    );
    match result {
        Err(e) => {
            assert!(e.error.to_string().contains("public-input-mismatch"));
            assert_eq!(e.backend.active_frames(), 0);
        }
        Ok(_) => panic!(),
    }
}
#[test]
fn zero_arity_polynomial_and_policy_failures() {
    let b = ark_backend(Some(0));
    let bytes = program(
        Some(0),
        &[("t", "table"), ("p", "point")],
        vec![op(
            "evaluate",
            "arkworks/poly.evaluate",
            &["t", "p"],
            &["y"],
        )],
        &["field"],
        &["y"],
    );
    let (out, _) = run(&bytes, b, vec![table(&[9]), point(&[])]);
    assert_eq!(scalar(&out.unwrap()[0]), Scalar::from(9u64));
    let policy = Policy {
        max_arity: 1,
        ..Policy::default()
    };
    assert!(Value::table(&[Scalar::from(1u64); 4], &policy).is_err());
    assert!(Value::table(&[], &policy).is_err());
}
#[test]
fn json_input_api_uses_only_admitted_role_ports_and_host_bindings() {
    let mut b = ark_backend(Some(1));
    let rng = b.issue_rng(domain(), 2).unwrap();
    let bytes = program(
        Some(1),
        &[("t", "table"), ("claim", "field"), ("rng", "rng")],
        vec![],
        &["field"],
        &["claim"],
    );
    let admitted = admit_supplied(&bytes, &b).unwrap();
    let role = admitted.entry("main").unwrap().remove(0);
    let mut host = InputBindings::new();
    host.insert("challenge", rng).unwrap();
    let input=br#"["zkc.inputs/1",[["t",["table",["2","3"]]],["claim",["field","5"]],["rng",["host","challenge"]]]]"#;
    let values = b.inputs_from_json(&role, input, &host).unwrap();
    assert_eq!(values.len(), 3);
    let (out, _) = run(&bytes, b, values);
    assert_eq!(scalar(&out.unwrap()[0]), Scalar::from(5u64));
    let b = ark_backend(Some(1));
    for bad in [br#"["zkc.inputs/1",[["t",["table",["02","3"]]],["claim",["field","5"]],["rng",["host","challenge"]]]]"#.as_slice(),
        br#"["zkc.inputs/1",[["t",["table",["2","3"]]],["claim",["field","5"]],["rng",["rng","0"]]]]"#,
        br#"["zkc.inputs/1",[["t",["table",["2","3"]]],["t",["field","5"]],["rng",["host","challenge"]]]]"#] {
        assert!(b.inputs_from_json(&role,bad,&host).is_err());
    }
}

#[test]
fn all_public_codecs_roundtrip_and_type_length_and_count_fail_closed() {
    let backend = ark_backend(None);
    for v in [
        f(9),
        Value::Bool(true),
        table(&[1, 2, 3, 4]),
        point(&[5, 6]),
        Value::Round([1u64, 2, 3].map(Scalar::from)),
    ] {
        let bytes = backend.encode_value(&v).unwrap();
        assert_eq!(
            backend
                .encode_value(
                    &backend
                        .decode_typed_value(v.physical_type(), &bytes)
                        .unwrap()
                )
                .unwrap(),
            bytes
        );
        for end in 0..bytes.len() {
            assert!(
                backend
                    .decode_typed_value(v.physical_type(), &bytes[..end])
                    .is_err()
            );
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(
            backend
                .decode_typed_value(v.physical_type(), &extra)
                .is_err()
        );
        if matches!(v, Value::Table(_) | Value::Point(_)) {
            let mut count = bytes.clone();
            count[6..10].fill(0xff);
            assert!(
                backend
                    .decode_typed_value(v.physical_type(), &count)
                    .is_err()
            );
        }
    }
    let mut boolean = backend.encode_value(&Value::Bool(true)).unwrap();
    boolean[6] = 2;
    assert!(
        backend
            .decode_typed_value(
                zkc_runtime::interactive::PhysicalType::default_for(
                    zkc_runtime::interactive::LogicalType::parse("bool").unwrap()
                ),
                &boolean
            )
            .is_err()
    );
}

#[test]
fn keys_must_match_entry_arity_and_opening_must_match_point() {
    let keys = Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    for ty in ["prover_key", "verifier_key"] {
        let bytes = program(Some(2), &[("key", ty)], vec![], &[], &[]);
        let b = ark_backend(Some(2));
        let admitted = admit_supplied(&bytes, &b).unwrap();
        let key = if ty == "prover_key" {
            Value::ProverKey(Arc::new(keys.prover_key().clone()))
        } else {
            Value::VerifierKey(Arc::new(keys.verifier_key().clone()))
        };
        assert!(Runner::new(&admitted, "main", "P", "session", b, vec![key]).is_err());
    }
    let (backend, _, _, out) = committed_fixture();
    let bytes = program(
        Some(2),
        &[("state", "opening_state"), ("p", "point")],
        vec![op(
            "open",
            "arkworks/pcs.open",
            &["state", "p"],
            &["y", "proof"],
        )],
        &["field", "proof"],
        &["y", "proof"],
    );
    let (failed, backend) = run(&bytes, backend, vec![out[3].clone(), point(&[1])]);
    assert_eq!(code(&failed.unwrap_err()), "refused:arity-mismatch");
    // A failed query leaves the immutable state usable, without recommitting.
    let (retried, backend) = run(&bytes, backend, vec![out[3].clone(), point(&[11, 13])]);
    assert_eq!(scalar(&retried.unwrap()[0]), scalar(&out[1]));
    assert_eq!(backend.active_frames(), 0);
}
