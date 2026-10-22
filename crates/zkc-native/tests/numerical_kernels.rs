#[path = "domains/support.rs"]
mod support;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use support::{Controlled, assert_value, backend, one};
use zkc_native::{KoalaBear, KoalaBearExt8, Policy, Value, domains};
use zkc_runtime::vm::{Backend, OperationBinding, Type};

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
fn batch_inverse_preserves_zero_before_output_refusal() {
    for (values, allowance, expected) in [
        (&[0, 2, 3][..], 0, Some("refused:zero-inverse")),
        (&[2, 0, 3][..], 0, Some("refused:zero-inverse")),
        (&[2, 3, 0][..], 0, Some("refused:zero-inverse")),
        (&[2, 3, 4][..], 0, Some("exhausted:output-bytes")),
        (&[][..], 255, Some("exhausted:output-bytes")),
        (&[][..], 256, None),
    ] {
        let mut driver = Controlled::new(backend(Policy::default()));
        driver.output_limit = Some(allowance);
        let (result, driver) = one(
            driver,
            binding("vector.inverse", domains::KOALA_BEAR),
            &[],
            vec![vector(values)],
        );
        if let Some(code) = expected {
            assert_eq!(result.unwrap_err(), code);
            assert!(driver.outputs.is_empty());
        } else {
            assert_value(&result.unwrap()[0], &vector(&[]));
            assert_eq!(driver.outputs.len(), 1);
        }
        assert_eq!(driver.inner.active_frames(), 0);
    }
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
                zkc_runtime::vm::Identity::Bn254Fr
                    | zkc_runtime::vm::Identity::KoalaBear
                    | zkc_runtime::vm::Identity::KoalaBearExt8
                    | zkc_runtime::vm::Identity::KoalaBearExt4
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
    assert!(b.encode_native_value(&literal).is_ok());
}

/// Reverse the low `bits` bits of `i` one digit at a time, independently of
/// the kernel's word-level reversal.
fn reversed(i: usize, bits: u32) -> usize {
    (0..bits).fold(0, |r, b| (r << 1) | ((i >> b) & 1))
}
#[test]
fn bit_reversal_permutes_elements_and_whole_rows() {
    for bits in 0..=6 {
        let n = 1usize << bits;
        let input: Vec<u32> = (0..n as u32).map(|i| 1000 + i).collect();
        let expected: Vec<u32> = (0..n).map(|i| input[reversed(i, bits)]).collect();
        assert_value(
            &call("vector.bit_reverse", vec![vector(&input)]),
            &vector(&expected),
        );
        // An involution: applying it twice restores the input.
        let once = call("vector.bit_reverse", vec![vector(&input)]);
        assert_value(&call("vector.bit_reverse", vec![once]), &vector(&input));
        for width in [1usize, 2, 3] {
            let table: Vec<u32> = (0..(n * width) as u32).collect();
            let expected: Vec<u32> = (0..n)
                .flat_map(|row| {
                    let source = reversed(row, bits);
                    table[source * width..(source + 1) * width].to_vec()
                })
                .collect();
            assert_value(
                &call(
                    "vector.bit_reverse_rows",
                    vec![vector(&table), Value::Index(width as u64)],
                ),
                &vector(&expected),
            );
        }
    }
    for (name, args, diagnostic) in [
        (
            "vector.bit_reverse",
            vec![vector(&[])],
            "vector-bit-reversal",
        ),
        (
            "vector.bit_reverse",
            vec![vector(&[1, 2, 3])],
            "vector-bit-reversal",
        ),
        (
            "vector.bit_reverse_rows",
            vec![vector(&[1, 2, 3, 4, 5, 6]), Value::Index(2)],
            "vector-bit-reversal",
        ),
        (
            "vector.bit_reverse_rows",
            vec![vector(&[1, 2, 3]), Value::Index(2)],
            "vector-shape",
        ),
        (
            "vector.bit_reverse_rows",
            vec![vector(&[1, 2]), Value::Index(0)],
            "vector-shape",
        ),
        (
            "vector.bit_reverse_rows",
            vec![vector(&[]), Value::Index(1)],
            "vector-bit-reversal",
        ),
        (
            "vector.bit_reverse_rows",
            vec![vector(&[1, 2]), Value::Index(u64::MAX)],
            "vector-shape",
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
            .contains(diagnostic),
            "{name}"
        );
    }
    // Positional only: every installed field family binds it.
    let b = backend(Policy::default());
    for d in domains::INSTALLED {
        for name in ["vector.bit_reverse", "vector.bit_reverse_rows"] {
            assert!(b.binding_signature(&binding(name, *d)).is_some(), "{name}");
        }
    }
}
