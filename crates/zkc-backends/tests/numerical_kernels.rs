#[path = "domains/support.rs"]
mod support;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use support::{assert_value, backend, one};
use zkc_backends::{KoalaBear, KoalaBearExt8, Policy, Value, domains};
use zkc_runtime::interactive::{Backend, OperationBinding, Type};

fn binding(name: &str, domain: domains::NativeDomain) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![domain.field.name().into()],
        implementation: format!("{}/{name}", domain.provider),
    }
}
fn call(name: &str, args: Vec<Value>) -> Value {
    one(
        backend(Policy::default()),
        binding(name, domains::KOALA_BEAR),
        &[],
        args,
    )
    .0
    .unwrap()
    .remove(0)
}
fn vector(ns: &[u32]) -> Value {
    Value::KoalaBearVector(
        ns.iter()
            .map(|n| KoalaBear::new(*n))
            .collect::<Vec<_>>()
            .into(),
    )
}
#[test]
fn dynamic_sequences_preserve_order_and_prefix_conventions() {
    let xs = vector(&[2, 3, 4]);
    assert_value(
        &call("vector.rotate", vec![xs.clone(), Value::Index(1)]),
        &vector(&[3, 4, 2]),
    );
    assert_value(
        &call("vector.interleave", vec![xs.clone(), vector(&[5, 6, 7])]),
        &vector(&[2, 5, 3, 6, 4, 7]),
    );
    assert_value(
        &call("vector.prefix_product", vec![xs.clone()]),
        &vector(&[2, 6, 24]),
    );
    assert_value(
        &call("vector.prefix_sum", vec![xs.clone()]),
        &vector(&[2, 5, 9]),
    );
    let inverse = call("vector.inverse", vec![xs.clone()]);
    assert_value(&call("vector.mul", vec![xs, inverse]), &vector(&[1, 1, 1]));
    assert_value(
        &call(
            "vector.fill",
            vec![Value::KoalaBearField(KoalaBear::new(9)), Value::Index(3)],
        ),
        &vector(&[9, 9, 9]),
    );
    assert_value(
        &call(
            "vector.geometric",
            vec![Value::KoalaBearField(KoalaBear::new(3)), Value::Index(4)],
        ),
        &vector(&[1, 3, 9, 27]),
    );
    assert_value(
        &call("field.from_index", vec![Value::Index(u64::MAX)]),
        &Value::KoalaBearField(KoalaBear::from_u64(u64::MAX)),
    );
    for (name, args, diagnostic) in [
        (
            "vector.rotate",
            vec![vector(&[]), Value::Index(0)],
            "vector-rotation",
        ),
        (
            "vector.rotate",
            vec![vector(&[1]), Value::Index(1)],
            "vector-rotation",
        ),
        (
            "vector.interleave",
            vec![vector(&[1]), vector(&[])],
            "length-mismatch",
        ),
        ("vector.inverse", vec![vector(&[1, 0, 2])], "zero-inverse"),
        (
            "vector.get",
            vec![vector(&[1]), Value::Index(u64::MAX)],
            "vector-index",
        ),
        (
            "vector.fill",
            vec![Value::KoalaBearField(KoalaBear::ONE), Value::Index(1 << 21)],
            "element-limit",
        ),
    ] {
        assert!(
            one(
                backend(Policy::default()),
                binding(name, domains::KOALA_BEAR),
                &[],
                args
            )
            .0
            .unwrap_err()
            .contains(diagnostic)
        );
    }
}
#[test]
fn opening_division_has_exact_remainder_and_normalization() {
    let p = call("poly.from_coefficients", vec![vector(&[5, 3, 2])]);
    let z = Value::KoalaBearField(KoalaBear::new(7));
    let y = call("poly.univariate_evaluate", vec![p.clone(), z.clone()]);
    let q = call("poly.divide_opening", vec![p.clone(), z.clone(), y]);
    assert_value(&call("poly.coefficients", vec![q]), &vector(&[17, 2]));
    let bad = one(
        backend(Policy::default()),
        binding("poly.divide_opening", domains::KOALA_BEAR),
        &[],
        vec![p, z, Value::KoalaBearField(KoalaBear::ZERO)],
    )
    .0;
    assert!(bad.unwrap_err().contains("polynomial-opening-value"));
}
#[test]
fn capabilities_are_nominal_and_embedding_preserves_all_coordinates() {
    let b = backend(Policy::default());
    for d in domains::INSTALLED {
        let signature = binding("poly.domain_root", *d);
        assert_eq!(
            signature.signature().is_ok(),
            matches!(
                d.field,
                zkc_runtime::interactive::Identity::Bn254Fr
                    | zkc_runtime::interactive::Identity::KoalaBear
                    | zkc_runtime::interactive::Identity::KoalaBearExt8
            )
        );
        assert_eq!(
            b.binding_signature(&signature).is_some(),
            signature.signature().is_ok()
        );
        assert!(b.binding_signature(&binding("vector.get", *d)).is_some());
        assert!(
            b.binding_signature(&binding("poly.divide_opening", *d))
                .is_some()
        );
    }
    let result = one(
        backend(Policy::default()),
        binding("vector.embed", domains::KOALA_BEAR_EXT8),
        &[],
        vec![vector(&[1, 2])],
    )
    .0
    .unwrap();
    let Value::KoalaBearExt8Vector(v) = &result[0] else {
        panic!("wrong carrier")
    };
    for (i, x) in v.iter().enumerate() {
        let coefficients: &[KoalaBear] = x.as_basis_coefficients_slice();
        assert_eq!(coefficients[0], KoalaBear::new(i as u32 + 1));
        assert!(coefficients[1..].iter().all(|x| *x == KoalaBear::ZERO));
    }
    let e = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(i as u32 + 1));
    let literal = Value::KoalaBearExt8Field(e);
    assert!(domains::KOALA_BEAR_EXT8.physical(Type::Field).is_some());
    assert!(b.encode_value(&literal).is_ok());
}
