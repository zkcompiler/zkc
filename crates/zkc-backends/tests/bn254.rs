#[path = "domains/support.rs"]
mod support;
use ark_ff::{Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use zkc_backends::{Bn254G1 as G1, Bn254G2 as G2, Bn254Scalar as F, Policy, Value};
use zkc_runtime::interactive::{Backend, Identity, OperationBinding, Value as RuntimeValue};
fn binding(name: &str, domain: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![domain.into()],
        implementation: format!("arkworks/{name}"),
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
    Value::Bn254Field(F::from(n))
}
fn vecf(n: &[u64]) -> Value {
    Value::Bn254Vector(n.iter().copied().map(F::from).collect::<Vec<_>>().into())
}
fn scalar(v: &Value) -> F {
    let Value::Bn254Field(x) = v else { panic!() };
    *x
}
fn vector(v: &Value) -> &[F] {
    let Value::Bn254Vector(x) = v else { panic!() };
    x
}
#[test]
fn field_vector_matrix_operations_and_exact_admission() {
    let out = call("field.mul", "bn254.fr", vec![f(7), f(9)]);
    assert_eq!(scalar(&out[0]), F::from(63));
    assert_eq!(
        scalar(&call("field.inverse", "bn254.fr", vec![f(7)])[0]) * F::from(7),
        F::one()
    );
    assert_eq!(
        scalar(
            &call(
                "vector.dot",
                "bn254.fr",
                vec![vecf(&[1, 2, 3]), vecf(&[3, 4, 5])]
            )[0]
        ),
        F::from(26)
    );
    let m = Value::bn254_matrix(
        2,
        3,
        &[(0, 0, F::from(2)), (0, 2, F::from(3)), (1, 1, F::from(7))],
        &Policy::default(),
    )
    .unwrap();
    assert_eq!(
        vector(
            &call(
                "matrix.mul_vector",
                "bn254.fr",
                vec![m.clone(), vecf(&[3, 5, 7])]
            )[0]
        ),
        [F::from(27), F::from(35)]
    );
    assert_eq!(
        vector(
            &call(
                "matrix.transpose_mul_vector",
                "bn254.fr",
                vec![m, vecf(&[3, 5])]
            )[0]
        ),
        [F::from(6), F::from(35), F::from(9)]
    );
    for (name, args, code) in [
        ("field.inverse", vec![f(0)], "refused:zero-inverse"),
        (
            "vector.dot",
            vec![vecf(&[1]), vecf(&[])],
            "refused:length-mismatch",
        ),
    ] {
        assert_eq!(
            support::one(
                support::backend(Policy::default()),
                binding(name, "bn254.fr"),
                &[],
                args
            )
            .0
            .unwrap_err(),
            code
        );
    }
    let b = support::backend(Policy::default());
    for name in [
        "field.constant",
        "vector.constant",
        "poly.coset_evaluate",
        "matrix.mul_vector",
        "random.draw",
        "random.vector",
        "pairing.check",
    ] {
        let op = binding(name, "bn254.fr");
        assert_eq!(Some(op.signature().unwrap()), b.binding_signature(&op));
    }
    for domain in ["bn254.g1", "bn254.g2"] {
        for name in [
            "curve.generator",
            "curve.add",
            "curve.msm",
            "curve.scale",
            "curve.neg",
        ] {
            let op = binding(name, domain);
            assert_eq!(Some(op.signature().unwrap()), b.binding_signature(&op));
        }
    }
    for (name, domain) in [
        ("curve.msm", "bn254.fr"),
        ("pcs.commit", "bn254.fr"),
        ("poly.product_sum", "bn254.fr"),
        ("curve.commit", "bn254.g1"),
        ("pairing.check", "bn254.g1"),
    ] {
        let op = binding(name, domain);
        assert!(op.signature().is_err());
        assert!(b.binding_signature(&op).is_none());
    }
}
#[test]
fn fft_coset_natural_order_interpolation_fold_and_quotient() {
    for n in [1usize, 2, 4, 16, 64] {
        let coeff = (1..=n).map(|j| F::from(j as u64)).collect::<Vec<_>>();
        let shift = F::from(9);
        let domain = Radix2EvaluationDomain::new(n * 2)
            .unwrap()
            .get_coset(shift)
            .unwrap();
        let poly = Value::Bn254Polynomial(coeff.clone().into());
        let ev = call(
            "poly.coset_evaluate",
            "bn254.fr",
            vec![poly, Value::Bn254Field(shift), Value::Index((2 * n) as u64)],
        )
        .remove(0);
        let expected = domain
            .elements()
            .map(|x| coeff.iter().rev().fold(F::zero(), |a, c| a * x + c))
            .collect::<Vec<_>>();
        assert_eq!(vector(&ev), expected);
        let got = call(
            "poly.coset_interpolate",
            "bn254.fr",
            vec![ev.clone(), Value::Bn254Field(shift)],
        );
        let Value::Bn254Polynomial(got) = &got[0] else {
            panic!()
        };
        assert_eq!(got.as_ref(), coeff);
        let points = call(
            "poly.domain_points",
            "bn254.fr",
            vec![Value::Bn254Field(shift), Value::Index((2 * n) as u64)],
        );
        assert_eq!(vector(&points[0]), domain.elements().collect::<Vec<_>>());
        let folded = call(
            "poly.even_odd_fold",
            "bn254.fr",
            vec![ev.clone(), Value::Bn254Field(shift), f(7)],
        );
        let folded_coeff = coeff
            .chunks(2)
            .map(|p| p[0] + p.get(1).copied().unwrap_or_default() * F::from(7))
            .collect::<Vec<_>>();
        let folded_domain = Radix2EvaluationDomain::new(n)
            .unwrap()
            .get_coset(shift.square())
            .unwrap();
        assert_eq!(vector(&folded[0]), folded_domain.fft(&folded_coeff));
        let point = F::from(3);
        let value = coeff.iter().rev().fold(F::zero(), |a, c| a * point + c);
        let q = call(
            "poly.opening_quotient",
            "bn254.fr",
            vec![
                ev,
                Value::Bn254Field(shift),
                Value::Bn254Field(point),
                Value::Bn254Field(value),
            ],
        );
        for ((q, y), x) in vector(&q[0]).iter().zip(expected).zip(domain.elements()) {
            assert_eq!(*q * (x - point), y - value);
        }
    }
    for (name, args, code) in [
        (
            "poly.domain_root",
            vec![Value::Index(3)],
            "refused:coset-size",
        ),
        (
            "poly.domain_points",
            vec![f(0), Value::Index(4)],
            "refused:coset-zero-shift",
        ),
        (
            "poly.domain_point",
            vec![f(1), Value::Index(4), Value::Index(4)],
            "refused:coset-coordinate",
        ),
        (
            "poly.even_odd_fold",
            vec![vecf(&[1]), f(1), f(7)],
            "refused:coset-fold-size",
        ),
        (
            "poly.opening_quotient",
            vec![vecf(&[1, 2]), f(1), f(1), f(0)],
            "refused:coset-opening-point",
        ),
        (
            "poly.coset_evaluate",
            vec![
                Value::Bn254Polynomial(vec![F::one(); 3].into()),
                f(1),
                Value::Index(2),
            ],
            "refused:coset-coefficient-count",
        ),
    ] {
        assert_eq!(
            support::one(
                support::backend(Policy::default()),
                binding(name, "bn254.fr"),
                &[],
                args
            )
            .0
            .unwrap_err(),
            code
        );
    }
}
#[test]
fn groups_pairing_codecs_nominal_separation_and_memory_limits() {
    let a = G1::generator().scale(F::from(3));
    let b = G2::generator().scale(F::from(7));
    let a2 = Value::Bn254G1Vector(vec![a, a.neg()].into());
    let b2 = Value::Bn254G2Vector(vec![b, b].into());
    assert!(matches!(
        call("pairing.check", "bn254.fr", vec![a2.clone(), b2.clone()])[0],
        Value::Bool(true)
    ));
    assert!(matches!(
        call(
            "pairing.check",
            "bn254.fr",
            vec![
                Value::Bn254G1Vector(vec![a].into()),
                Value::Bn254G2Vector(vec![b].into())
            ]
        )[0],
        Value::Bool(false)
    ));
    for (domain, v) in [("bn254.g1", a2.clone()), ("bn254.g2", b2.clone())] {
        let out = call("curve.msm", domain, vec![vecf(&[2, 5]), v]);
        match &out[0] {
            Value::Bn254G1(x) => {
                assert_eq!(*x, a.scale(F::from(2)).add(&a.neg().scale(F::from(5))))
            }
            Value::Bn254G2(x) => assert_eq!(*x, b.scale(F::from(7))),
            _ => panic!(),
        }
    }
    let backend = support::backend(Policy::default());
    for v in [
        f(123),
        vecf(&[1, 2]),
        Value::Bn254Polynomial(vec![F::one()].into()),
        Value::Bn254Round([F::one(); 3]),
        Value::Bn254G1(a),
        Value::Bn254G2(b),
        a2,
        b2,
        Value::bn254_matrix(1, 1, &[(0, 0, F::one())], &Policy::default()).unwrap(),
    ] {
        let bytes = backend.encode_value(&v).unwrap();
        let ty = v.physical_type();
        let decoded = backend.decode_typed_value(ty.clone(), &bytes).unwrap();
        assert_eq!(backend.encode_value(&decoded).unwrap(), bytes);
        assert!(
            Value::typed_wire_retained_bytes_bound(ty.clone(), bytes.len(), &Policy::default())
                .unwrap()
                >= decoded.retained_bytes()
        );
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(backend.decode_typed_value(ty.clone(), &bad).is_err());
        let mut bad = bytes;
        bad[5] ^= 1;
        assert!(backend.decode_typed_value(ty.clone(), &bad).is_err());
    }
    let v = Value::Bn254G2Vector(vec![b; 3].into());
    let bytes = backend.encode_value(&v).unwrap();
    let constrained = support::backend(Policy {
        max_value_bytes: v.retained_bytes() - 1,
        ..Policy::default()
    });
    assert!(
        constrained
            .decode_typed_value(v.physical_type(), &bytes)
            .is_err()
    );
    assert_eq!(
        support::one(
            backend,
            binding("pairing.check", "bn254.fr"),
            &[],
            vec![
                Value::Bn254G1Vector(vec![a].into()),
                Value::Bn254G2Vector(vec![].into())
            ]
        )
        .0
        .unwrap_err(),
        "refused:length-mismatch"
    );
}
#[cfg(feature = "test-utils")]
#[test]
fn explicit_tape_and_os_rng_resources() {
    let mut b = support::backend(Policy::default());
    let token = b
        .issue_test_bn254_tape(support::domain(), 2, vec![F::from(17), F::from(23)])
        .unwrap();
    let (out, _) = support::one(b, binding("random.vector", "bn254.fr"), &["2"], vec![token]);
    assert_eq!(vector(&out.unwrap()[0]), [F::from(17), F::from(23)]);
    let mut b = support::backend(Policy::default());
    let token = b
        .issue_rng_for(Identity::Bn254Fr, support::domain(), 1)
        .unwrap();
    let (out, _) = support::one(b, binding("random.draw", "bn254.fr"), &[], vec![token]);
    assert!(matches!(out.unwrap()[0], Value::Bn254Field(_)));
}

#[test]
fn literal_admission_uses_bn254_modulus_and_wire_is_fixed() {
    use serde_json::json;
    use zkc_runtime::interactive::admit_supplied;
    let backend = support::backend(Policy::default());
    for name in ["field.constant", "vector.constant"] {
        let b = binding(name, "bn254.fr");
        let sig = b.signature().unwrap();
        for literal in ["01", "-1", zkc_arkworks::bn254::MODULUS] {
            let program = support::program(
                std::slice::from_ref(&b),
                &[],
                vec![json!(["op", "constant", "b0", [literal], [], ["v"]])],
                &sig.outputs,
                &["v".into()],
            );
            assert!(admit_supplied(&program, &backend).is_err());
        }
        let out = support::one(support::backend(Policy::default()), b, &["17"], vec![])
            .0
            .unwrap();
        assert!(matches!(
            &out[0],
            Value::Bn254Field(_) | Value::Bn254Vector(_)
        ));
    }
    let bytes = backend.encode_value(&f(1)).unwrap();
    let mut expected = b"ZKCV\x01\x28".to_vec();
    expected.push(1);
    expected.extend([0; 31]);
    assert_eq!(bytes, expected);
    let g = Value::Bn254G1(G1::generator());
    let bytes = backend.encode_value(&g).unwrap();
    let mut expected = b"ZKCV\x01\x2e".to_vec();
    // Arkworks BN254's smaller y-coordinate sign is clear for (1,2).
    expected.push(1);
    expected.extend([0; 31]);
    assert_eq!(bytes, expected);
    assert!(
        backend
            .decode_typed_value(Value::Bn254G2(G2::generator()).physical_type(), &bytes)
            .is_err()
    );
    assert_eq!(
        <F as ark_ff::FftField>::TWO_ADIC_ROOT_OF_UNITY,
        zkc_arkworks::bn254::parse_decimal(
            "19103219067921713944291392827692070036145651957329286315305642004821462161904"
        )
        .unwrap()
    );
}
