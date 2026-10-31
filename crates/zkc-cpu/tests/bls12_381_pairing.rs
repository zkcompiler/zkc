//! BLS12-381 G2, pairing target, pairing kernels and native frames through
//! the backend registry; the G1 group and scalar field were installed before.
#[path = "domains/support.rs"]
mod support;
use std::sync::Arc;
use zkc_cpu::{Bls12381G2 as G2, Bls12381Gt as Gt, G1, Policy, Scalar as F, Value};
use zkc_runtime::vm::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, Type, Value as RuntimeValue,
};

fn binding(name: &str, domain: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![domain.into()],
        implementation: format!("arkworks/{name}"),
        physical_arguments: vec![],
    }
}
fn call(name: &str, domain: &str, args: Vec<Value>) -> Vec<Value> {
    support::one(
        support::backend(Policy::default()),
        binding(name, domain),
        &[],
        args,
    )
    .0
    .unwrap()
}
fn f(n: u64) -> Value {
    Value::Field(F::from(n))
}
fn vecf(n: &[u64]) -> Value {
    Value::Vector(n.iter().copied().map(F::from).collect::<Vec<_>>().into())
}

#[test]
fn pairing_signatures_preserve_each_fields_ordered_groups() {
    let backend = support::backend(Policy::default());
    for (field, left, right, target) in [
        (
            "bn254.fr",
            Identity::Bn254G1,
            Identity::Bn254G2,
            Identity::Bn254Gt,
        ),
        (
            "bls12-381.fr",
            Identity::Bls12381G1,
            Identity::Bls12381G2,
            Identity::Bls12381Gt,
        ),
    ] {
        for (name, kind, output, identity) in [
            ("pairing.apply", Type::Group, Type::Group, target),
            ("pairing.check", Type::Groups, Type::Bool, Identity::None),
        ] {
            let operation = binding(name, field);
            let physical = |kind, identity| {
                PhysicalType::default_for(LogicalType::new(kind, identity).unwrap()).unwrap()
            };
            let signature = operation.signature().unwrap();
            assert_eq!(
                signature.inputs,
                [physical(kind, left), physical(kind, right)],
                "{name} {field}"
            );
            assert_eq!(
                signature.outputs,
                [physical(output, identity)],
                "{name} {field}"
            );
            assert_eq!(backend.binding_signature(&operation), Some(signature));
        }
    }
}

#[test]
fn bindings_follow_the_pairing_field_association() {
    let b = support::backend(Policy::default());
    for (name, domain) in [
        ("pairing.check", "bls12-381.fr"),
        ("pairing.apply", "bls12-381.fr"),
        ("curve.generator", "bls12-381.g2"),
        ("curve.identity", "bls12-381.g2"),
        ("curve.add", "bls12-381.g2"),
        ("curve.scale", "bls12-381.g2"),
        ("curve.neg", "bls12-381.g2"),
        ("curve.equal", "bls12-381.g2"),
        ("curve.msm", "bls12-381.g2"),
        ("curve.empty", "bls12-381.g2"),
        ("curve.append", "bls12-381.g2"),
        ("curve.generator", "bls12-381.gt"),
        ("curve.add", "bls12-381.gt"),
        ("curve.scale", "bls12-381.gt"),
        ("curve.equal", "bls12-381.gt"),
        ("encoding.group_compressed", "bls12-381.g2"),
        ("encoding.group_from_compressed", "bls12-381.g2"),
    ] {
        let op = binding(name, domain);
        assert_eq!(
            Some(op.signature().unwrap()),
            b.binding_signature(&op),
            "{name} {domain}"
        );
    }
    // The target has no vectors, and pairings select a field, not a group.
    for (name, domain) in [
        ("curve.msm", "bls12-381.gt"),
        ("curve.empty", "bls12-381.gt"),
        ("pairing.check", "bls12-381.g1"),
        ("pairing.check", "bls12-381.g2"),
        ("encoding.group_compressed", "bls12-381.gt"),
        ("encoding.groups_compressed", "bls12-381.g2"),
    ] {
        let op = binding(name, domain);
        assert!(b.binding_signature(&op).is_none(), "{name} {domain}");
    }
}

#[test]
fn groups_pairings_and_target_arithmetic() {
    let a = G1::generator().scale(F::from(3));
    let b = G2::generator().scale(F::from(7));
    let a2 = Value::Groups(vec![a, a.neg()].into());
    let b2 = Value::Bls12381G2Vector(vec![b, b].into());
    assert!(matches!(
        call(
            "pairing.check",
            "bls12-381.fr",
            vec![a2.clone(), b2.clone()]
        )[0],
        Value::Bool(true)
    ));
    assert!(matches!(
        call(
            "pairing.check",
            "bls12-381.fr",
            vec![
                Value::Groups(vec![a].into()),
                Value::Bls12381G2Vector(vec![b].into())
            ]
        )[0],
        Value::Bool(false)
    ));
    let out = call("curve.msm", "bls12-381.g2", vec![vecf(&[2, 5]), b2.clone()]);
    assert!(matches!(&out[0], Value::Bls12381G2(x) if **x == b.scale(F::from(7))));
    let sum = call(
        "curve.add",
        "bls12-381.g2",
        vec![
            Value::Bls12381G2(b.into()),
            Value::Bls12381G2(b.neg().into()),
        ],
    );
    assert!(matches!(&sum[0], Value::Bls12381G2(x) if **x == G2::identity()));
    let paired = call(
        "pairing.apply",
        "bls12-381.fr",
        vec![Value::Curve(a.into()), Value::Bls12381G2(b.into())],
    );
    let Value::Bls12381Gt(target) = &paired[0] else {
        panic!("target")
    };
    assert_eq!(**target, Gt::generator().scale(F::from(21)));
    let scaled = call(
        "curve.scale",
        "bls12-381.gt",
        vec![Value::Bls12381Gt(Arc::new(Gt::generator())), f(21)],
    );
    assert!(matches!(
        &call(
            "curve.equal",
            "bls12-381.gt",
            vec![scaled[0].clone(), paired[0].clone()]
        )[0],
        Value::Bool(true)
    ));
    assert_eq!(
        support::one(
            support::backend(Policy::default()),
            binding("pairing.check", "bls12-381.fr"),
            &[],
            vec![
                Value::Groups(vec![a].into()),
                Value::Bls12381G2Vector(vec![].into())
            ]
        )
        .0
        .unwrap_err(),
        "refused:length-mismatch"
    );
}

#[test]
fn native_frames_round_trip_and_reject_damage() {
    let backend = support::backend(Policy::default());
    let b = G2::generator().scale(F::from(11));
    for (v, tag, width) in [
        (Value::Bls12381G2((b).into()), 51, 102),
        (
            Value::Bls12381G2Vector(vec![b, G2::identity()].into()),
            52,
            202,
        ),
        (Value::Bls12381Gt(Arc::new(Gt::generator())), 53, 582),
    ] {
        assert!(zkc_cpu::has_native_wire(&v.physical_type()));
        let bytes = backend.encode_native_value(&v).unwrap();
        assert_eq!(&bytes[..6], [b"ZKCV\x00".as_slice(), &[tag]].concat());
        assert_eq!(bytes.len(), width);
        let ty = v.physical_type();
        let decoded = backend.decode_native_value(&ty, &bytes).unwrap();
        assert_eq!(backend.encode_native_value(&decoded).unwrap(), bytes);
        assert!(
            Value::typed_wire_retained_bytes_bound(ty.clone(), bytes.len(), &Policy::default())
                .unwrap()
                >= decoded.retained_bytes()
        );
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(backend.decode_native_value(&ty, &bad).is_err());
        let mut bad = bytes.clone();
        bad[5] ^= 1;
        assert!(backend.decode_native_value(&ty, &bad).is_err());
        // Clearing the compression flag of the first element is not canonical.
        let mut bad = bytes;
        bad[if tag == 52 { 10 } else { 6 }] ^= 0x80;
        assert!(backend.decode_native_value(&ty, &bad).is_err());
    }
    // A G1 frame is not a G2 frame, even for the shared scalar field.
    let g1 = backend
        .encode_native_value(&Value::Curve((G1::generator()).into()))
        .unwrap();
    assert!(
        backend
            .decode_native_value(&Value::Bls12381G2(b.into()).physical_type(), &g1)
            .is_err()
    );
}
