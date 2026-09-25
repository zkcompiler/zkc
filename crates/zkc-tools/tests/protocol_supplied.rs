//! An authored supplied participant has executable admission, not correspondence.
//! This intentionally separate test never weakens source-relative admission.
#![cfg(feature = "test-utils")]

use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{
    Action, Packet, Runner, RuntimeError, Value as RuntimeValue, admit_supplied,
};

#[test]
fn actual_supplied_participant_waits_and_retains_nonce_after_wrong_session() {
    let bytes = include_bytes!("../../../examples/protocols/supplied-participant.json");
    let domain = Domain::new("P", "supplied_test", "main", None);
    let mut backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(domain.clone(), None, PublicInputs::LocalOnly),
        None,
    )
    .unwrap();
    let nonce = backend
        .issue_test_nonce(domain, 2, Scalar::from(17u64))
        .unwrap();
    let token = match &nonce {
        Value::Nonce(token) => token.clone(),
        _ => unreachable!(),
    };
    let admitted = admit_supplied(bytes, &backend).unwrap();
    assert!(admitted.checked_source().is_none());
    assert_eq!(admitted.entry("main").unwrap().len(), 1);
    let mut runner = Runner::new(
        &admitted,
        "main",
        "P",
        "supplied_test",
        backend,
        vec![Value::Field(Scalar::from(13u64)), nonce],
    )
    .map_err(|e| e.error)
    .unwrap();
    // This public codec endpoint has no participant, peer state or protocol code.
    let peer_codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("V", "supplied_test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let mut sent = Vec::new();
    let pending = loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Send(packet) => {
                let cut = Action::Send(packet).cut().unwrap();
                let packet = runner.take_send(&cut).unwrap();
                let bytes = runner.backend().encode_value(&packet.payload).unwrap();
                sent.push(peer_codec.decode_typed_value(packet.ty, &bytes).unwrap());
            }
            Action::Receive(receive) => break receive,
            _ => panic!("supplied participant terminated before challenge"),
        }
    };
    assert_eq!(sent.len(), 2);
    assert!(
        matches!(&sent[0], Value::Curve(x) if *x == GroupPoint::generator().scale(Scalar::from(13u64)))
    );
    assert!(
        matches!(&sent[1], Value::Curve(x) if *x == GroupPoint::generator().scale(Scalar::from(17u64)))
    );
    let before = runner.backend().observe(&token).unwrap();
    assert_eq!(
        (before.generation, before.draw_count, before.stage),
        (1, 1, "committed")
    );
    let usage = runner.usage();
    assert!(matches!(runner.poll(), Action::Receive(r) if r == pending));
    assert_eq!(runner.usage(), usage);
    let bytes = peer_codec
        .encode_value(&Value::Field(Scalar::from(19u64)))
        .unwrap();
    let payload = runner
        .backend()
        .decode_typed_value(
            zkc_runtime::interactive::PhysicalType::default_for(
                zkc_runtime::interactive::LogicalType::parse("field:bls12-381.fr").unwrap(),
            ),
            &bytes,
        )
        .unwrap();
    let valid = Packet {
        envelope: pending.envelope.clone(),
        ty: payload.physical_type(),
        payload,
    };
    let mut wrong = valid.clone();
    wrong.envelope.origin.session = "other_session".into();
    assert_eq!(runner.deliver(wrong), Err(RuntimeError::Envelope));
    assert_eq!(runner.backend().observe(&token).unwrap(), before);
    assert_eq!(runner.usage(), usage);
    assert!(matches!(runner.poll(), Action::Receive(r) if r == pending));
    runner.deliver(valid).unwrap();
    loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            Action::Send(packet) => {
                let cut = Action::Send(packet).cut().unwrap();
                let packet = runner.take_send(&cut).unwrap();
                let bytes = runner.backend().encode_value(&packet.payload).unwrap();
                sent.push(peer_codec.decode_typed_value(packet.ty, &bytes).unwrap());
            }
            Action::Returned(values) => {
                assert!(values.is_empty());
                break;
            }
            _ => panic!("unexpected supplied participant suffix"),
        }
    }
    assert_eq!(sent.len(), 3);
    assert!(matches!(&sent[2], Value::Field(s) if *s == Scalar::from(264u64)));
    let after = runner.backend().observe(&token).unwrap();
    assert_eq!(
        (
            after.generation,
            after.draw_count,
            after.budget,
            after.stage
        ),
        (2, 2, 0, "spent")
    );
    assert_eq!(runner.backend().active_frames(), 0);
}
