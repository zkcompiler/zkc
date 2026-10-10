//! Nullary identities use each installed group's actual representation.
#[path = "domains/support.rs"]
mod support;
use curve25519_dalek::traits::Identity as _;
use zkc_backends::{Bn254G1, Bn254G2, Bn254Gt, GroupPoint, Policy, Value};
use zkc_runtime::interactive::{Backend, OperationBinding, Value as RuntimeValue};

fn binding(group: &str, contract: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: vec![group.into()],
        implementation: format!(
            "{}/{contract}",
            if group == "ristretto255.group" {
                "dalek"
            } else {
                "arkworks"
            }
        ),
    }
}
fn call(group: &str, contract: &str, args: Vec<Value>) -> Value {
    support::one(
        support::backend(Policy::default()),
        binding(group, contract),
        &[],
        args,
    )
    .0
    .unwrap()
    .remove(0)
}
fn equal(group: &str, a: Value, b: Value) {
    assert!(matches!(
        call(group, "curve.equal", vec![a, b]),
        Value::Bool(true)
    ));
}
fn check(group: &str, expected: Value, zero: Value, scalar: Value, empty: Option<(Value, Value)>) {
    let backend = support::backend(Policy::default());
    let operation = binding(group, "curve.identity");
    assert_eq!(
        Some(operation.signature().unwrap()),
        backend.binding_signature(&operation)
    );
    assert!(operation.signature().unwrap().inputs.is_empty());
    let identity = call(group, "curve.identity", vec![]);
    let generator = call(group, "curve.generator", vec![]);
    equal(group, identity.clone(), expected.clone());
    equal(
        group,
        call(
            group,
            "curve.add",
            vec![identity.clone(), generator.clone()],
        ),
        generator.clone(),
    );
    equal(
        group,
        call(
            group,
            "curve.add",
            vec![generator.clone(), identity.clone()],
        ),
        generator.clone(),
    );
    equal(
        group,
        call(group, "curve.scale", vec![generator.clone(), zero]),
        identity.clone(),
    );
    equal(
        group,
        call(group, "curve.scale", vec![identity.clone(), scalar]),
        identity.clone(),
    );
    assert!(matches!(
        call(group, "curve.nonidentity", vec![identity.clone()]),
        Value::Bool(false)
    ));
    assert!(matches!(
        call(group, "curve.nonidentity", vec![generator]),
        Value::Bool(true)
    ));
    if let Some((scalars, points)) = empty {
        equal(
            group,
            call(group, "curve.msm", vec![scalars, points]),
            identity.clone(),
        );
    }
    backend.validate_native_input(&identity).unwrap();
    let bytes = backend.encode_native_value(&identity).unwrap();
    assert_eq!(bytes, backend.encode_native_value(&expected).unwrap());
    let decoded = backend
        .decode_native_value(&identity.physical_type(), &bytes)
        .unwrap();
    equal(group, decoded, identity);
    let limited = support::backend(Policy {
        max_value_bytes: 0,
        ..Policy::default()
    });
    let error = support::one(limited, operation, &[], vec![]).0.unwrap_err();
    assert!(error.starts_with("exhausted:"), "{error}");
}
#[test]
fn ristretto_identity() {
    check(
        "ristretto255.group",
        Value::RistrettoGroup(zkc_backends::RistrettoPoint::identity()),
        support::field(true, 0),
        support::field(true, 7),
        Some((support::vector(true, &[]), support::groups(true, &[]))),
    );
}
#[test]
fn bls_g1_identity() {
    check(
        "bls12-381.g1",
        Value::Curve(GroupPoint::identity()),
        support::field(false, 0),
        support::field(false, 7),
        Some((support::vector(false, &[]), support::groups(false, &[]))),
    );
}
#[test]
fn bn254_g1_identity() {
    check(
        "bn254.g1",
        Value::Bn254G1(Bn254G1::identity()),
        Value::Bn254Field(0.into()),
        Value::Bn254Field(7.into()),
        Some((
            Value::Bn254Vector(vec![].into()),
            Value::Bn254G1Vector(vec![].into()),
        )),
    );
}
#[test]
fn bn254_g2_identity() {
    check(
        "bn254.g2",
        Value::Bn254G2(Bn254G2::identity()),
        Value::Bn254Field(0.into()),
        Value::Bn254Field(7.into()),
        Some((
            Value::Bn254Vector(vec![].into()),
            Value::Bn254G2Vector(vec![].into()),
        )),
    );
}
#[test]
fn bn254_target_identity_is_multiplicative_one() {
    let identity = Value::Bn254Gt(Bn254Gt::identity());
    check(
        "bn254.gt",
        identity.clone(),
        Value::Bn254Field(0.into()),
        Value::Bn254Field(7.into()),
        None,
    );
    let backend = support::backend(Policy::default());
    let mut bytes = backend.encode_native_value(&identity).unwrap();
    // Canonical Fq12 one starts with the base-field one, not all-zero bytes.
    assert_eq!(bytes[6], 1);
    assert!(bytes[7..].iter().all(|b| *b == 0));
    bytes[6] = 0;
    assert!(
        backend
            .decode_native_value(&identity.physical_type(), &bytes)
            .is_err()
    );
    assert!(binding("bn254.gt", "curve.msm").signature().is_err());
}
#[test]
fn exact_provider_group_codec_and_nullary_signature() {
    let backend = support::backend(Policy::default());
    for group in [
        "ristretto255.group",
        "bls12-381.g1",
        "bn254.g1",
        "bn254.g2",
        "bn254.gt",
    ] {
        let mut wrong = binding(group, "curve.identity");
        wrong.implementation = if group == "ristretto255.group" {
            "arkworks/curve.identity"
        } else {
            "dalek/curve.identity"
        }
        .into();
        assert!(wrong.signature().is_err());
        assert!(backend.binding_signature(&wrong).is_none());
        let identity = call(group, "curve.identity", vec![]);
        let bytes = backend.encode_native_value(&identity).unwrap();
        for other in [
            "ristretto255.group",
            "bls12-381.g1",
            "bn254.g1",
            "bn254.g2",
            "bn254.gt",
        ] {
            if other != group {
                let expected = binding(other, "curve.identity")
                    .signature()
                    .unwrap()
                    .outputs[0]
                    .clone();
                assert!(backend.decode_native_value(&expected, &bytes).is_err());
            }
        }
        let sig = binding(group, "curve.identity").signature().unwrap();
        for (attrs, args) in [(vec!["0"], vec![]), (vec![], vec!["a0"])] {
            let wire = support::program(
                &[binding(group, "curve.identity")],
                &sig.outputs,
                vec![serde_json::json!(["op", "zero", "b0", attrs, args, ["z"]])],
                &sig.outputs,
                &["z".into()],
            );
            assert!(zkc_runtime::interactive::admit_supplied(&wire, &backend).is_err());
        }
    }
    for group in ["bn254.fr", "bls12-381.g2", "bls12-381.gt", "unknown"] {
        let wrong = binding(group, "curve.identity");
        assert!(wrong.signature().is_err());
        assert!(backend.binding_signature(&wrong).is_none());
    }
}
