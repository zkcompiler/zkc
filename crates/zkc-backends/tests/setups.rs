mod common;
use common::*;
use std::{collections::BTreeMap, sync::Arc};
use zkc_backends::*;
use zkc_runtime::interactive::{Backend, PhysicalType, Value as RuntimeValue};

#[test]
fn authorized_setups_are_per_port_and_peer_bytes_cannot_select_authority() {
    let policy = Policy::default();
    let a = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let b = Keys::setup_for_development(2, &policy.ark_bounds()).unwrap();
    let foreign = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let registry = || {
        SetupRegistry::new(
            vec![a.verifier_key().clone(), b.verifier_key().clone()],
            &policy,
        )
        .unwrap()
    };
    let port_policy = || {
        entry(None).with_ports(BTreeMap::from([
            (
                "a".into(),
                PortConstraint {
                    arity: Some(1),
                    setup: Some(a.verifier_key().metadata()),
                },
            ),
            (
                "b".into(),
                PortConstraint {
                    arity: Some(2),
                    setup: Some(b.verifier_key().metadata()),
                },
            ),
        ]))
    };
    let backend = || NativeBackend::with_setups(policy, port_policy(), registry()).unwrap();
    let bytes = program(
        None,
        &[("a", "verifier_key"), ("b", "verifier_key")],
        vec![],
        &[],
        &[],
    );
    let (out, _) = run(
        &bytes,
        backend(),
        vec![
            Value::VerifierKey(Arc::new(a.verifier_key().clone())),
            Value::VerifierKey(Arc::new(b.verifier_key().clone())),
        ],
    );
    assert!(out.unwrap().is_empty());
    let admitted = zkc_runtime::interactive::admit_supplied(&bytes, &backend()).unwrap();
    let wrong = zkc_runtime::interactive::Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        backend(),
        vec![
            Value::VerifierKey(Arc::new(b.verifier_key().clone())),
            Value::VerifierKey(Arc::new(a.verifier_key().clone())),
        ],
    );
    assert!(
        wrong
            .err()
            .unwrap()
            .error
            .to_string()
            .contains("entry-port-shape")
    );
    let host = backend();
    assert!(
        host.validate_value(&Value::VerifierKey(Arc::new(
            foreign.verifier_key().clone()
        )))
        .unwrap_err()
        .code
        .contains("unauthorized-setup")
    );
    assert!(
        SetupRegistry::new(
            vec![a.verifier_key().clone(), a.verifier_key().clone()],
            &policy
        )
        .is_err()
    );
    assert!(SetupRegistry::new(vec![a.verifier_key().clone(); 65], &policy).is_err());

    let table = zkc_arkworks::Table::from_logical(
        &[Scalar::from(2), Scalar::from(5)],
        &policy.ark_bounds(),
    )
    .unwrap();
    let state = a.prover_key().commit(&table).unwrap();
    let value = Value::Commitment(Arc::new(state.commitment().clone()));
    let wire = host.encode_value(&value).unwrap();
    // Ambiguous implicit selection fails; the host must name the authorized context.
    assert!(
        host.decode_typed_value(value.physical_type(), &wire)
            .is_err()
    );
    assert!(
        host.decode_for_setup(value.physical_type(), a.verifier_key().metadata(), &wire)
            .is_ok()
    );
    assert!(
        host.decode_for_setup(value.physical_type(), b.verifier_key().metadata(), &wire)
            .is_err()
    );
    assert!(
        host.decode_for_setup(
            value.physical_type(),
            foreign.verifier_key().metadata(),
            &wire
        )
        .is_err()
    );
    assert!(
        host.decode_for_setup(
            PhysicalType::parse("field:bls12-381.fr@arkworks.fr/1").unwrap(),
            a.verifier_key().metadata(),
            &wire
        )
        .is_err()
    );

    // Public entry bytes use a host-selected port context too. Even a sole
    // registered setup does not implicitly become the input's expected setup.
    let port = zkc_runtime::interactive::EntryRole {
        role: "P".into(),
        participant: "p".into(),
        instance: "root".into(),
        parameters: BTreeMap::new(),
        inputs: vec![("c".into(), value.physical_type())],
        outputs: vec![],
    };
    let input = serde_json::to_vec(&serde_json::json!([
        "zkc.inputs/1",
        [["c", ["wire", zkc_test_support::hex(&wire)]]]
    ]))
    .unwrap();
    let constrained = |metadata| {
        NativeBackend::with_setups(
            policy,
            entry(None).with_ports(BTreeMap::from([(
                "c".into(),
                PortConstraint {
                    arity: None,
                    setup: metadata,
                },
            )])),
            registry(),
        )
        .unwrap()
    };
    let bindings = InputBindings::new();
    assert!(
        constrained(Some(a.verifier_key().metadata()))
            .inputs_from_json(&port, &input, &bindings)
            .is_ok()
    );
    assert!(
        constrained(Some(b.verifier_key().metadata()))
            .inputs_from_json(&port, &input, &bindings)
            .is_err()
    );
    assert!(
        constrained(None)
            .inputs_from_json(&port, &input, &bindings)
            .unwrap_err()
            .code
            .contains("input-setup-required")
    );
    let sole = NativeBackend::with_setups(
        policy,
        entry(None),
        SetupRegistry::new(vec![a.verifier_key().clone()], &policy).unwrap(),
    )
    .unwrap();
    assert!(
        sole.inputs_from_json(&port, &input, &bindings)
            .unwrap_err()
            .code
            .contains("input-setup-required")
    );
}

#[test]
fn both_table_layouts_use_the_same_logical_wire_codec() {
    let policy = Policy::default();
    let backend = ark_backend(None);
    let lsb = table(&[0, 1, 4, 9]);
    let msb = Value::TableMsb(Arc::new(
        zkc_arkworks::MsbTable::from_logical(
            &[0u64, 1, 4, 9].map(Scalar::from),
            &policy.ark_bounds(),
        )
        .unwrap(),
    ));
    let wire = backend.encode_value(&lsb).unwrap();
    assert_eq!(wire, backend.encode_value(&msb).unwrap());
    for value in [&lsb, &msb] {
        let decoded = backend
            .decode_typed_value(value.physical_type(), &wire)
            .unwrap();
        assert_eq!(decoded.physical_type(), value.physical_type());
        assert_eq!(backend.encode_value(&decoded).unwrap(), wire);
    }
    let mut bad = wire.clone();
    bad[6..10].copy_from_slice(&31u32.to_le_bytes());
    assert!(
        backend
            .decode_typed_value(msb.physical_type(), &bad)
            .is_err()
    );
    assert!(
        backend
            .decode_typed_value(msb.physical_type(), &wire[..wire.len() - 1])
            .is_err()
    );
}
