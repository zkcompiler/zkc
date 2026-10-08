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
    let backend = || NativeBackend::new(policy, port_policy(), registry()).unwrap();
    let bytes = program(
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
    let wire = host.encode_native_value(&value).unwrap();
    // Native headers select metadata only within the independently authorized registry.
    assert!(
        host.decode_native_value(&value.physical_type(), &wire)
            .is_ok()
    );
    let foreign_state = foreign.prover_key().commit(&table).unwrap();
    let foreign_value = Value::Commitment(Arc::new(foreign_state.commitment().clone()));
    let foreign_host = NativeBackend::new(
        policy,
        entry(None),
        zkc_backends::SetupRegistry::new(
            vec![foreign.verifier_key().clone()],
            &zkc_backends::Policy::default(),
        )
        .unwrap(),
    )
    .unwrap();
    let foreign_wire = foreign_host.encode_native_value(&foreign_value).unwrap();
    assert!(
        host.decode_native_value(&value.physical_type(), &foreign_wire)
            .is_err()
    );
    assert!(
        host.decode_native_value(
            &PhysicalType::parse("field:bls12-381.fr@arkworks.fr/1").unwrap(),
            &wire
        )
        .is_err()
    );
    // Public entry bytes use a host-selected port context too. Even a sole
    // registered setup does not implicitly become the input's expected setup.
    let port = zkc_runtime::interactive::EntryRole {
        services: vec![],
        role: "P".into(),
        participant: "p".into(),
        instance: "root".into(),
        inputs: vec![("c".into(), value.physical_type())],
        outputs: vec![],
    };
    let constrained = |metadata| {
        NativeBackend::new(
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
    assert!(
        constrained(Some(a.verifier_key().metadata()))
            .check_entry_values(&port, &[Some(&value)])
            .is_ok()
    );
    assert!(
        constrained(Some(b.verifier_key().metadata()))
            .check_entry_values(&port, &[Some(&value)])
            .is_err()
    );
    // Registry membership alone is sufficient unless the Host selected an input constraint.
    assert!(
        constrained(None)
            .check_entry_values(&port, &[Some(&value)])
            .is_ok()
    );
}

#[test]
fn only_default_table_layout_crosses_native_wire() {
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
    let wire = backend.encode_native_value(&lsb).unwrap();
    assert!(backend.encode_native_value(&msb).is_err());
    assert!(
        backend
            .decode_native_value(&msb.physical_type(), &wire)
            .is_err()
    );
    let Value::TableMsb(ref alternate) = msb else {
        unreachable!()
    };
    let canonical = Value::Table(Arc::new(alternate.to_lsb(&policy.ark_bounds()).unwrap()));
    assert_eq!(backend.encode_native_value(&canonical).unwrap(), wire);
    for value in [&lsb, &canonical] {
        let decoded = backend
            .decode_native_value(&value.physical_type(), &wire)
            .unwrap();
        assert_eq!(decoded.physical_type(), value.physical_type());
        assert_eq!(backend.encode_native_value(&decoded).unwrap(), wire);
    }
    let mut bad = wire.clone();
    bad[6..10].copy_from_slice(&31u32.to_le_bytes());
    assert!(
        backend
            .decode_native_value(&msb.physical_type(), &bad)
            .is_err()
    );
    assert!(
        backend
            .decode_native_value(&msb.physical_type(), &wire[..wire.len() - 1])
            .is_err()
    );
}

#[test]
fn native_nested_messages_resolve_only_registered_setups() {
    let policy = Policy::default();
    let bounds = policy.ark_bounds();
    let keys: Vec<_> = [1, 2, 1]
        .into_iter()
        .map(|n| Keys::setup_for_development(n, &bounds).unwrap())
        .collect();
    let host = NativeBackend::new(
        policy,
        entry(None),
        SetupRegistry::new(
            keys[..2].iter().map(|k| k.verifier_key().clone()).collect(),
            &policy,
        )
        .unwrap(),
    )
    .unwrap();
    let values: Vec<_> = keys
        .iter()
        .map(|k| {
            let n = 1 << k.verifier_key().metadata().arity();
            let state = k
                .prover_key()
                .commit(
                    &zkc_arkworks::Table::from_logical_vec(vec![Scalar::from(7); n], &bounds)
                        .unwrap(),
                )
                .unwrap();
            Value::Commitment(Arc::new(state.commitment().clone()))
        })
        .collect();
    let logical = values[0].physical_type().logical();
    let value =
        Value::Sequence(Sequence::new(logical.clone(), values[..2].to_vec(), &policy).unwrap());
    let bytes = host.encode_native_value(&value).unwrap();
    let decoded = host
        .decode_native_value(&value.physical_type(), &bytes)
        .unwrap();
    assert_eq!(host.encode_native_value(&decoded).unwrap(), bytes);
    let empty = NativeBackend::new(
        policy,
        entry(None),
        SetupRegistry::new(vec![], &policy).unwrap(),
    )
    .unwrap();
    for error in [
        empty.encode_native_value(&values[0]).unwrap_err(),
        empty
            .decode_native_value(
                &values[0].physical_type(),
                &host.encode_native_value(&values[0]).unwrap(),
            )
            .unwrap_err(),
    ] {
        assert_eq!(
            error.to_string(),
            "native-wire-backend:native-wire-setup-required"
        );
    }
    assert!(host.encode_native_value(&values[2]).is_err());
    let foreign = NativeBackend::new(
        policy,
        entry(None),
        zkc_backends::SetupRegistry::new(
            vec![keys[2].verifier_key().clone()],
            &zkc_backends::Policy::default(),
        )
        .unwrap(),
    )
    .unwrap();
    let bytes = foreign.encode_native_value(&values[2]).unwrap();
    assert!(
        host.decode_native_value(&values[2].physical_type(), &bytes)
            .is_err()
    );
    let bad = Value::Sequence(
        Sequence::new(logical, vec![values[0].clone(), values[2].clone()], &policy).unwrap(),
    );
    assert!(host.encode_native_value(&bad).is_err());
}
