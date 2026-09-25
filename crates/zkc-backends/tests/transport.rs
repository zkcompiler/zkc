mod common;
use common::*;
use serde_json::json;
use std::{collections::BTreeMap, sync::Arc};
use zkc_backends::*;
use zkc_runtime::interactive::{Action, Packet, Runner, admit_supplied};

#[test]
fn independent_runners_exchange_only_bound_public_bytes_and_reject_bad_packets() {
    let policy = Policy::default();
    let keys = Keys::setup_for_development(2, &policy.ark_bounds()).unwrap();
    let bytes = participants(json!([
        [
            [
                "function",
                "commit_open",
                [["pk", "prover_key"], ["t", "table"], ["p", "point"]],
                ["commitment", "field", "proof"],
                [
                    op(
                        "commit",
                        "arkworks/pcs.commit",
                        &["pk", "t"],
                        &["c", "state"]
                    ),
                    op(
                        "open",
                        "arkworks/pcs.open",
                        &["state", "p"],
                        &["y", "proof"]
                    ),
                    ["return", ["c", "y", "proof"]]
                ]
            ],
            [
                "function",
                "verify",
                [
                    ["vk", "verifier_key"],
                    ["c", "commitment"],
                    ["p", "point"],
                    ["y", "field"],
                    ["proof", "proof"]
                ],
                ["bool"],
                [
                    op(
                        "check",
                        "arkworks/pcs.check",
                        &["vk", "c", "p", "y", "proof"],
                        &["ok"]
                    ),
                    op("require", "arkworks/control.require", &["ok"], &[]),
                    ["return", ["ok"]]
                ]
            ]
        ],
        [
            [
                "participant",
                "prover",
                "instance",
                "P",
                [["n", "2"]],
                [["pk", "prover_key"], ["t", "table"], ["p", "point"]],
                [],
                [
                    [
                        "local",
                        "prepare",
                        "commit_open",
                        ["pk", "t", "p"],
                        ["c", "y", "proof"]
                    ],
                    ["send", "commitment_site", "commitment_schema", "V", "c"],
                    ["send", "value_site", "value_schema", "V", "y"],
                    ["send", "proof_site", "proof_schema", "V", "proof"],
                    ["return", []]
                ]
            ],
            [
                "participant",
                "verifier",
                "instance",
                "V",
                [["n", "2"]],
                [["vk", "verifier_key"], ["p", "point"]],
                ["bool"],
                [
                    [
                        "receive",
                        "commitment_site",
                        "commitment_schema",
                        "P",
                        "c",
                        "commitment"
                    ],
                    ["receive", "value_site", "value_schema", "P", "y", "field"],
                    [
                        "receive",
                        "proof_site",
                        "proof_schema",
                        "P",
                        "proof",
                        "proof"
                    ],
                    [
                        "local",
                        "verify_site",
                        "verify",
                        ["vk", "c", "p", "y", "proof"],
                        ["ok"]
                    ],
                    ["return", ["ok"]]
                ]
            ]
        ],
        [["entry", "main", [["P", "prover"], ["V", "verifier"]]]]
    ]))
    .unwrap();
    let public_point = point(&[11, 13]);
    let pins = PublicInputs::Exact(BTreeMap::from([("p".into(), public_point.clone())]));
    let prover = NativeBackend::new(
        policy,
        EntryPolicy::new(domain(), Some(2), pins.clone()),
        None,
    )
    .unwrap();
    let verifier = NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("V", "session", "main", Some("instance")),
            Some(2),
            pins,
        ),
        Some(keys.verifier_key().clone()),
    )
    .unwrap();
    let admitted = admit_supplied(&bytes, &prover).unwrap();
    let mut p = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        prover,
        vec![
            Value::ProverKey(Arc::new(keys.prover_key().clone())),
            table(&[2, 3, 5, 7]),
            public_point.clone(),
        ],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let mut v = Runner::new(
        &admitted,
        "main",
        "V",
        "session",
        verifier,
        vec![
            Value::VerifierKey(Arc::new(keys.verifier_key().clone())),
            public_point,
        ],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Local(local) = p.poll() else {
        panic!()
    };
    p.execute_local(&local.cut).unwrap();
    for _ in 0..3 {
        let Action::Receive(expected) = v.poll() else {
            panic!()
        };
        let send = p.poll();
        assert!(matches!(send, Action::Send(_)));
        let packet = p.take_send(&send.cut().unwrap()).unwrap();
        let wire = p.backend().encode_value(&packet.payload).unwrap();
        assert!(
            v.backend()
                .decode_typed_value(expected.ty.clone(), &wire[..wire.len() - 1])
                .is_err()
        );
        assert!(matches!(v.poll(),Action::Receive(ref still) if still == &expected));
        let payload = v
            .backend()
            .decode_typed_value(expected.ty.clone(), &wire)
            .unwrap();
        let mut wrong = Packet {
            envelope: packet.envelope.clone(),
            ty: packet.ty.clone(),
            payload: payload.clone(),
        };
        wrong.envelope.origin.session = "wrong-session".into();
        assert!(v.deliver(wrong).is_err());
        assert!(matches!(v.poll(),Action::Receive(ref still) if still == &expected));
        v.deliver(Packet {
            envelope: packet.envelope,
            ty: packet.ty.clone(),
            payload,
        })
        .unwrap();
    }
    // Prover terminates without observing verifier state. Verifier has no original custody.
    assert!(matches!(p.poll(), Action::Returned(_)));
    assert_eq!(v.backend().active_frames(), 1);
    let Action::Local(check) = v.poll() else {
        panic!()
    };
    v.execute_local(&check.cut).unwrap();
    assert!(
        matches!(v.poll(),Action::Returned(ref result) if matches!(result[0],Value::Bool(true)))
    );
    assert_eq!(p.into_backend().active_frames(), 0);
    assert_eq!(v.into_backend().active_frames(), 0);
}
