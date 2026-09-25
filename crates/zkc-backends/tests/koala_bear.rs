#[path = "domains/support.rs"]
mod support;

use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use serde_json::json;
use support::{Controlled, assert_value, backend, one, program, run_program};
use zkc_backends::{InputBindings, KoalaBear, Policy, Value, domains::KOALA_BEAR, plonky3};
use zkc_runtime::interactive::{
    Backend, ErrorCode, Identity, LogicalType, OperationBinding, PhysicalType, Representation,
    Type, Value as RuntimeValue, admit_supplied,
};

fn binding(name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec!["koala-bear".into()],
        implementation: format!("plonky3/{name}"),
    }
}
fn field(n: u32) -> Value {
    Value::KoalaBearField(KoalaBear::new(n))
}
fn vector(values: &[u32]) -> Value {
    Value::koala_bear_vector(
        &values
            .iter()
            .copied()
            .map(KoalaBear::new)
            .collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}
fn call(name: &str, attrs: &[&str], args: Vec<Value>) -> Vec<Value> {
    one(backend(Policy::default()), binding(name), attrs, args)
        .0
        .unwrap()
}
fn failure(name: &str, attrs: &[&str], args: Vec<Value>, code: &str) {
    assert_eq!(
        one(backend(Policy::default()), binding(name), attrs, args)
            .0
            .unwrap_err(),
        code
    );
}

#[test]
fn numerical_identity_and_independent_installation_have_no_crypto_associations() {
    let b = backend(Policy::default());
    assert_eq!(Identity::parse("koala-bear").unwrap(), Identity::KoalaBear);
    assert_eq!(
        Identity::KoalaBear.scalar_field(),
        Some(Identity::KoalaBear)
    );
    assert_eq!(Identity::KoalaBear.provider(), Some("plonky3"));
    assert_eq!(Identity::KoalaBear.group(), None);
    assert_eq!(Identity::KoalaBear.transcript(), None);
    assert_eq!(KOALA_BEAR.group, None);
    assert!(
        !zkc_backends::domains::TRANSCRIPTS
            .iter()
            .any(|t| t.domain.field == KOALA_BEAR.field)
    );
    assert!(zkc_backends::domains::for_identity(Identity::None).is_none());
    for (kind, repr) in [
        (Type::Field, "plonky3.koala-bear/1"),
        (Type::Vector, "plonky3.koala-bear-vector/1"),
        (Type::Polynomial, "plonky3.koala-bear-polynomial/1"),
        (Type::Round, "plonky3.koala-bear-quadratic/1"),
    ] {
        let ty = KOALA_BEAR.physical(kind).unwrap();
        assert_eq!(ty.representation().name(), repr);
        assert_eq!(PhysicalType::parse(&ty.spelling()).unwrap(), ty);
        assert_eq!(KOALA_BEAR.codec(kind), ty.logical().codec());
        assert_eq!(
            ty.logical().codec().unwrap(),
            format!("zkcv.{}.koala-bear/1", kind.name())
        );
        assert!(PhysicalType::new(ty.logical(), Representation::Fr).is_err());
        assert!(PhysicalType::new(ty.logical(), Representation::DalekScalar).is_err());
    }
    for kind in [
        Type::Rng,
        Type::Nonce,
        Type::Transcript,
        Type::Group,
        Type::Groups,
        Type::Table,
        Type::Point,
        Type::Commitment,
        Type::Proof,
        Type::ProverKey,
        Type::VerifierKey,
        Type::OpeningState,
    ] {
        assert!(LogicalType::new(kind, Identity::KoalaBear).is_err());
        assert!(KOALA_BEAR.physical(kind).is_none());
        assert!(KOALA_BEAR.codec(kind).is_none());
    }
    for name in [
        "field.constant",
        "field.add",
        "field.sub",
        "field.mul",
        "field.neg",
        "field.inverse",
        "field.equal",
        "vector.empty",
        "vector.append",
        "vector.splat",
        "vector.powers",
        "vector.add",
        "vector.sub",
        "vector.mul",
        "vector.scale",
        "vector.sum",
        "vector.dot",
        "vector.split",
        "vector.concat",
        "vector.at",
        "vector.length_check",
        "vector.gather",
        "vector.kronecker",
        "vector.matvec",
        "poly.from_coefficients",
        "poly.coefficients",
        "poly.degree_check",
        "poly.univariate_evaluate",
        "poly.univariate_boundary",
        "poly.boundary",
        "poly.round_evaluate",
    ] {
        let bind = binding(name);
        assert_eq!(
            b.binding_signature(&bind),
            Some(bind.signature().unwrap()),
            "{name}"
        );
        for provider in ["invented", "arkworks", "dalek", "plonky3-diagonal"] {
            let wrong = OperationBinding {
                implementation: format!("{provider}/{name}"),
                ..bind.clone()
            };
            assert!(wrong.signature().is_err());
            assert!(b.binding_signature(&wrong).is_none());
        }
    }
    for name in [
        "random.draw",
        "random.vector",
        "transcript.challenge",
        "transcript.observe.field",
        "curve.generator",
        "curve.response",
        "curve.msm",
        "pcs.commit",
        "pcs.open",
        "pcs.check",
        "poly.fold",
        "poly.product_round",
        "poly.evaluate",
        "poly.equality_weights",
        "vector.from_table",
        "vector.to_point",
        "table.relayout",
    ] {
        assert!(binding(name).signature().is_err(), "{name}");
        assert!(b.binding_signature(&binding(name)).is_none(), "{name}");
    }
    let mut b = b;
    assert_eq!(
        b.issue_rng_for(Identity::KoalaBear, support::domain(), 1)
            .unwrap_err()
            .code,
        "refused:rng-field"
    );
    assert_eq!(
        b.issue_nonce_for(Identity::KoalaBear, support::domain(), 1)
            .unwrap_err()
            .code,
        "refused:nonce-field"
    );
    assert_eq!(
        b.issue_transcript_for(Identity::KoalaBear, support::domain(), 1, b"")
            .unwrap_err()
            .code,
        "refused:transcript-suite"
    );
}

#[test]
fn scalar_arithmetic_matches_integer_modular_reference_and_zero_inverse_refuses() {
    assert_eq!(KoalaBear::ORDER_U32, plonky3::MODULUS);
    let p = u64::from(plonky3::MODULUS);
    for a in [0, 1, 2, 17, plonky3::MODULUS - 1] {
        for b in [0, 1, 42, plonky3::MODULUS - 1] {
            for (name, expected) in [
                ("field.add", (u64::from(a) + u64::from(b)) % p),
                ("field.sub", (p + u64::from(a) - u64::from(b)) % p),
                ("field.mul", (u64::from(a) * u64::from(b)) % p),
            ] {
                assert_value(
                    &call(name, &[], vec![field(a), field(b)])[0],
                    &field(expected as u32),
                );
            }
            assert!(
                matches!(call("field.equal", &[], vec![field(a), field(b)])[0], Value::Bool(x) if x == (a == b))
            );
        }
        assert_value(
            &call("field.neg", &[], vec![field(a)])[0],
            &field(((p - u64::from(a)) % p) as u32),
        );
        if a != 0 {
            let Value::KoalaBearField(inverse) = call("field.inverse", &[], vec![field(a)])[0]
            else {
                panic!()
            };
            assert_eq!(
                (u64::from(inverse.as_canonical_u32()) * u64::from(a)) % p,
                1
            );
        }
    }
    failure("field.inverse", &[], vec![field(0)], "refused:zero-inverse");
    assert!(KoalaBear::ZERO.try_inverse().is_none());
    for bad in [
        "",
        "00",
        "01",
        "+1",
        "-1",
        " 1",
        "1 ",
        "1.0",
        "1e2",
        "2130706433",
        "4294967295",
    ] {
        assert_eq!(
            plonky3::parse_decimal(bad).unwrap_err().code,
            "refused:noncanonical-scalar"
        );
        let bind = binding("field.constant");
        let sig = bind.signature().unwrap();
        let bytes = program(
            &[bind],
            &[],
            vec![json!(["op", "constant", "b0", [bad], [], ["x"]])],
            &sig.outputs,
            &["x".into()],
        );
        assert_eq!(
            admit_supplied(&bytes, &backend(Policy::default()))
                .unwrap_err()
                .code,
            ErrorCode::Attributes
        );
    }
    assert_value(
        &call("field.constant", &["2130706432"], vec![])[0],
        &field(plonky3::MODULUS - 1),
    );
}

#[test]
fn packed_product_and_dot_match_integer_reference_including_suffixes() {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    assert!(plonky3::PACKING_WIDTH >= 8);
    let p = u64::from(plonky3::MODULUS);
    for n in [0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 65, 257] {
        let a = (0..n)
            .map(|j| ((p - 1 - (j as u64 * 97531) % p) % p) as u32)
            .collect::<Vec<_>>();
        let b = (0..n)
            .map(|j| ((j as u64 * 13579 + p - 7) % p) as u32)
            .collect::<Vec<_>>();
        let products = a
            .iter()
            .zip(&b)
            .map(|(a, b)| (u64::from(*a) * u64::from(*b) % p) as u32)
            .collect::<Vec<_>>();
        let dot = products.iter().fold(0u64, |s, x| (s + u64::from(*x)) % p) as u32;
        assert_value(
            &call("vector.mul", &[], vec![vector(&a), vector(&b)])[0],
            &vector(&products),
        );
        assert_value(
            &call("vector.dot", &[], vec![vector(&a), vector(&b)])[0],
            &field(dot),
        );
        let a = a.into_iter().map(KoalaBear::new).collect::<Vec<_>>();
        let b = b.into_iter().map(KoalaBear::new).collect::<Vec<_>>();
        assert_eq!(plonky3::dot(&a, &b).unwrap().as_canonical_u32(), dot);
        let mut output = vec![KoalaBear::ZERO; n];
        plonky3::mul_into(&a, &b, &mut output).unwrap();
        assert_eq!(
            output
                .iter()
                .map(PrimeField32::as_canonical_u32)
                .collect::<Vec<_>>(),
            products
        );
    }
    let mut out = [KoalaBear::new(7)];
    assert_eq!(
        plonky3::mul_into(&[], &[], &mut out).unwrap_err().code,
        "refused:length-mismatch"
    );
    assert_eq!(out[0].as_canonical_u32(), 7);
    assert_eq!(
        plonky3::dot(&[], &[KoalaBear::ONE]).unwrap_err().code,
        "refused:length-mismatch"
    );
}

#[test]
fn vector_shapes_and_polynomial_semantics_are_preserved() {
    for name in ["vector.add", "vector.sub", "vector.mul", "vector.dot"] {
        failure(
            name,
            &[],
            vec![vector(&[1, 2]), vector(&[3])],
            "refused:length-mismatch",
        );
    }
    for v in [vector(&[]), vector(&[1]), vector(&[1, 2, 3])] {
        failure("vector.split", &[], vec![v], "refused:split-length");
    }
    failure(
        "vector.at",
        &["0"],
        vec![vector(&[])],
        "refused:vector-index",
    );
    failure(
        "vector.gather",
        &["0", "2"],
        vec![vector(&[1, 2])],
        "refused:vector-index",
    );
    failure(
        "vector.matvec",
        &["2", "2", "0"],
        vec![vector(&[1, 2, 3]), vector(&[4, 5])],
        "refused:length-mismatch",
    );
    assert_value(&call("vector.sum", &[], vec![vector(&[])])[0], &field(0));
    assert_value(
        &call("vector.powers", &["4"], vec![field(3)])[0],
        &vector(&[1, 3, 9, 27]),
    );
    assert_value(
        &call(
            "vector.kronecker",
            &[],
            vec![vector(&[2, 3]), vector(&[5, 7])],
        )[0],
        &vector(&[10, 14, 15, 21]),
    );
    assert_value(
        &call(
            "vector.matvec",
            &["2", "3", "0"],
            vec![vector(&[1, 2, 3, 4, 5, 6]), vector(&[7, 8, 9])],
        )[0],
        &vector(&[50, 122]),
    );
    assert_value(
        &call(
            "vector.matvec",
            &["2", "3", "1"],
            vec![vector(&[1, 2, 3, 4, 5, 6]), vector(&[7, 8])],
        )[0],
        &vector(&[39, 54, 69]),
    );
    assert_value(
        &call(
            "vector.matvec",
            &["2", "0", "0"],
            vec![vector(&[]), vector(&[])],
        )[0],
        &vector(&[0, 0]),
    );
    let poly = call(
        "poly.from_coefficients",
        &[],
        vec![vector(&[2, 3, 4, 0, 0])],
    )
    .remove(0);
    assert_value(
        &call("poly.coefficients", &[], vec![poly.clone()])[0],
        &vector(&[2, 3, 4]),
    );
    assert_value(
        &call(
            "poly.univariate_evaluate",
            &[],
            vec![poly.clone(), field(5)],
        )[0],
        &field(117),
    );
    assert_value(
        &call("poly.univariate_boundary", &[], vec![poly.clone()])[0],
        &field(11),
    );
    assert!(matches!(
        call("poly.degree_check", &["1"], vec![poly])[0],
        Value::Bool(false)
    ));
    let zero = call("poly.from_coefficients", &[], vec![vector(&[0, 0])]).remove(0);
    assert_value(
        &call("poly.coefficients", &[], vec![zero.clone()])[0],
        &vector(&[]),
    );
    assert_value(
        &call(
            "poly.univariate_evaluate",
            &[],
            vec![zero.clone(), field(5)],
        )[0],
        &field(0),
    );
    assert!(matches!(
        call("poly.degree_check", &["0"], vec![zero])[0],
        Value::Bool(true)
    ));
    let round = Value::KoalaBearRound([2, 3, 4].map(KoalaBear::new));
    assert_value(
        &call("poly.round_evaluate", &[], vec![round.clone(), field(5)])[0],
        &field(117),
    );
    assert_value(&call("poly.boundary", &[], vec![round])[0], &field(11));
}

#[test]
fn composed_product_dot_and_affine_fold_execute_without_setup() {
    let bindings = [
        "vector.mul",
        "vector.dot",
        "vector.split",
        "vector.sub",
        "vector.scale",
        "vector.add",
    ]
    .map(binding);
    let v = KOALA_BEAR.physical(Type::Vector).unwrap();
    let f = KOALA_BEAR.physical(Type::Field).unwrap();
    let bytes = program(
        &bindings,
        &[v.clone(), v.clone(), f.clone()],
        vec![
            json!(["op", "product", "b0", [], ["a0", "a1"], ["product"]]),
            json!(["op", "dot", "b1", [], ["a0", "a1"], ["dot"]]),
            json!(["op", "split", "b2", [], ["product"], ["lo", "hi"]]),
            json!(["op", "difference", "b3", [], ["hi", "lo"], ["delta"]]),
            json!(["op", "scale", "b4", [], ["delta", "a2"], ["scaled"]]),
            json!(["op", "add", "b5", [], ["lo", "scaled"], ["folded"]]),
        ],
        &[f, v],
        &["dot".into(), "folded".into()],
    );
    let (result, b) = run_program(
        backend(Policy::default()),
        &bytes,
        vec![vector(&[1, 2, 3, 4]), vector(&[5, 6, 7, 8]), field(2)],
    );
    let result = result.unwrap();
    assert_value(&result[0], &field(70));
    assert_value(&result[1], &vector(&[37, 52]));
    assert_eq!(b.active_frames(), 0);
    assert!(b.verifier_key().is_none());
}

fn wire(tag: u8, count: Option<u32>, scalars: &[u32]) -> Vec<u8> {
    let mut bytes = vec![0x5a, 0x4b, 0x43, 0x56, 1, tag];
    if let Some(n) = count {
        bytes.extend(n.to_le_bytes());
    }
    for n in scalars {
        bytes.extend(n.to_le_bytes());
    }
    bytes
}

#[test]
fn independent_golden_bytes_roundtrip_and_canonical_rejections() {
    let b = backend(Policy::default());
    for (value, bytes) in [
        (
            field(plonky3::MODULUS - 1),
            wire(19, None, &[plonky3::MODULUS - 1]),
        ),
        (vector(&[2, 3]), wire(20, Some(2), &[2, 3])),
        (vector(&[]), wire(20, Some(0), &[])),
        (
            Value::KoalaBearPolynomial([KoalaBear::new(2), KoalaBear::new(3)].into()),
            wire(21, Some(2), &[2, 3]),
        ),
        (
            Value::KoalaBearPolynomial([].into()),
            wire(21, Some(0), &[]),
        ),
        (
            Value::KoalaBearRound([0, 1, 2].map(KoalaBear::new)),
            wire(22, None, &[0, 1, 2]),
        ),
    ] {
        assert_eq!(b.encode_value(&value).unwrap(), bytes);
        let decoded = b.decode_typed_value(value.physical_type(), &bytes).unwrap();
        assert_value(&decoded, &value);
        assert!(
            Value::typed_wire_retained_bytes_bound(value.physical_type(), bytes.len(), b.policy())
                .unwrap()
                >= value.retained_bytes()
        );
        for len in 0..bytes.len() {
            assert!(
                b.decode_typed_value(value.physical_type(), &bytes[..len])
                    .is_err()
            );
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(
            b.decode_typed_value(value.physical_type(), &trailing)
                .unwrap_err()
                .code,
            "refused:wire-length"
        );
        let mut wrong = bytes.clone();
        wrong[5] ^= 1;
        assert_eq!(
            b.decode_typed_value(value.physical_type(), &wrong)
                .unwrap_err()
                .code,
            "refused:wire-header"
        );
    }
    for n in [plonky3::MODULUS, plonky3::MODULUS + 1, u32::MAX] {
        for (kind, bytes) in [
            (Type::Field, wire(19, None, &[n])),
            (Type::Vector, wire(20, Some(1), &[n])),
            (Type::Polynomial, wire(21, Some(1), &[n])),
            (Type::Round, wire(22, None, &[1, 2, n])),
        ] {
            assert_eq!(
                b.decode_typed_value(KOALA_BEAR.physical(kind).unwrap(), &bytes)
                    .unwrap_err()
                    .code,
                "refused:noncanonical-scalar"
            );
        }
    }
    assert_eq!(
        b.decode_typed_value(
            KOALA_BEAR.physical(Type::Polynomial).unwrap(),
            &wire(21, Some(1), &[0])
        )
        .unwrap_err()
        .code,
        "refused:polynomial-normalization"
    );
    assert_eq!(
        b.encode_value(&Value::KoalaBearPolynomial([KoalaBear::ZERO].into()))
            .unwrap_err()
            .code,
        "refused:polynomial-normalization"
    );
    assert_eq!(
        b.decode_typed_value(
            KOALA_BEAR.physical(Type::Vector).unwrap(),
            &wire(20, Some(u32::MAX), &[])
        )
        .unwrap_err()
        .code,
        "refused:wire-length"
    );
    for d in [zkc_backends::domains::BLS, zkc_backends::domains::RISTRETTO] {
        assert_eq!(
            b.decode_typed_value(d.physical(Type::Field).unwrap(), &wire(19, None, &[1]))
                .unwrap_err()
                .code,
            "refused:wire-header"
        );
    }
}

#[test]
fn bounds_are_checked_before_result_allocation_at_actual_element_width() {
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(256 + 4 * 3 - 1);
    assert_eq!(
        one(
            controlled,
            binding("vector.mul"),
            &[],
            vec![vector(&[1, 2, 3]), vector(&[4, 5, 6])]
        )
        .0
        .unwrap_err(),
        "exhausted:output-bytes"
    );
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(256 + 4 * 3);
    assert!(
        one(
            controlled,
            binding("vector.mul"),
            &[],
            vec![vector(&[1, 2, 3]), vector(&[4, 5, 6])]
        )
        .0
        .is_ok()
    );
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(511);
    assert_eq!(
        one(
            controlled,
            binding("vector.dot"),
            &[],
            vec![vector(&[]), vector(&[])]
        )
        .0
        .unwrap_err(),
        "exhausted:output-bytes"
    );
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(2 * (256 + 4) - 1);
    assert_eq!(
        one(
            controlled,
            binding("vector.split"),
            &[],
            vec![vector(&[1, 2])]
        )
        .0
        .unwrap_err(),
        "exhausted:output-bytes"
    );
    let p = Policy {
        max_value_bytes: 268,
        ..Policy::default()
    };
    assert!(Value::koala_bear_vector(&[KoalaBear::ONE; 3], &p).is_ok());
    assert_eq!(
        Value::koala_bear_vector(&[KoalaBear::ONE; 4], &p)
            .unwrap_err()
            .code,
        "exhausted:output-bytes"
    );
    let b = backend(p);
    assert_eq!(
        b.decode_typed_value(
            KOALA_BEAR.physical(Type::Vector).unwrap(),
            &wire(20, Some(4), &[1; 4])
        )
        .unwrap_err()
        .code,
        "exhausted:output-bytes"
    );
    let b = backend(Policy {
        max_table_elements: 2,
        ..Policy::default()
    });
    assert_eq!(
        b.decode_typed_value(
            KOALA_BEAR.physical(Type::Vector).unwrap(),
            &wire(20, Some(3), &[1; 3])
        )
        .unwrap_err()
        .code,
        "exhausted:element-limit"
    );
    let b = backend(Policy {
        max_wire_bytes: 9,
        ..Policy::default()
    });
    assert_eq!(
        b.encode_value(&field(0)).unwrap_err().code,
        "exhausted:wire-bytes"
    );
    // The largest size admission accepts exceeds the default element limit.
    failure(
        "vector.splat",
        &["1048576"],
        vec![field(1)],
        "exhausted:element-limit",
    );
}

#[test]
fn wrong_domains_and_implementations_fail_before_arithmetic() {
    for replacement in [support::field(false, 1), support::field(true, 1)] {
        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.substitute = Some(replacement);
        assert_eq!(
            one(
                controlled,
                binding("field.add"),
                &[],
                vec![field(1), field(2)]
            )
            .0
            .unwrap_err(),
            "refused:kernel-operands"
        );
    }
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.implementation = Some("arkworks/field.add".into());
    assert_eq!(
        one(
            controlled,
            binding("field.add"),
            &[],
            vec![field(1), field(2)]
        )
        .0
        .unwrap_err(),
        "refused:kernel-operands"
    );
    assert_ne!(
        field(1).physical_type(),
        zkc_backends::domains::BLS.physical(Type::Field).unwrap()
    );
}

#[test]
fn host_decimal_wire_and_handle_inputs_use_exact_nominal_type() {
    let b = backend(Policy::default());
    let v = KOALA_BEAR.physical(Type::Vector).unwrap();
    let f = KOALA_BEAR.physical(Type::Field).unwrap();
    let bytes = program(
        &[binding("vector.scale")],
        &[v.clone(), f],
        vec![json!(["op", "scale", "b0", [], ["a0", "a1"], ["out"]])],
        &[v],
        &["out".into()],
    );
    let admitted = admit_supplied(&bytes, &b).unwrap();
    let role = admitted.entry("main").unwrap().remove(0);
    let mut host = InputBindings::new();
    host.insert("local", vector(&[2, 3])).unwrap();
    host.insert("wrong", support::vector(false, &[2, 3]))
        .unwrap();
    for input in [
        json!(["vector", ["2", "3"]]),
        json!(["host", "local"]),
        json!(["wire", "5a4b43560114020000000200000003000000"]),
    ] {
        let document = serde_json::to_vec(&json!([
            "zkc.inputs/1",
            [["a0", input], ["a1", ["field", "5"]]]
        ]))
        .unwrap();
        let values = b.inputs_from_json(&role, &document, &host).unwrap();
        assert_value(
            &run_program(backend(Policy::default()), &bytes, values)
                .0
                .unwrap()[0],
            &vector(&[10, 15]),
        );
    }
    for (input, code) in [
        (json!(["host", "wrong"]), "refused:input-type"),
        (
            json!(["vector", ["2130706433"]]),
            "refused:noncanonical-scalar",
        ),
        (json!(["vector", [1]]), "refused:input-string"),
    ] {
        let document = serde_json::to_vec(&json!([
            "zkc.inputs/1",
            [["a0", input], ["a1", ["field", "5"]]]
        ]))
        .unwrap();
        assert_eq!(
            b.inputs_from_json(&role, &document, &host)
                .unwrap_err()
                .code,
            code
        );
    }
}

#[test]
fn independent_participants_exchange_only_canonical_numeric_bytes() {
    use zkc_backends::{Domain, EntryPolicy, NativeBackend, PublicInputs};
    use zkc_runtime::interactive::{Action, Packet, Runner};
    let f = KOALA_BEAR.physical(Type::Field).unwrap();
    let v = KOALA_BEAR.physical(Type::Vector).unwrap();
    let b = binding("vector.dot");
    let bytes = serde_json::to_vec(&json!([
        "zkc.participants/1",
        [["dot", b.contract, b.arguments, b.implementation]],
        "physical",
        [[
            "function",
            "calculate",
            [["a", v.spelling()], ["b", v.spelling()]],
            [f.spelling()],
            [
                ["op", "dot", "dot", [], ["a", "b"], ["result"]],
                ["return", ["result"]]
            ],
            ["calculate", []]
        ]],
        [
            [
                "participant",
                "sender",
                "instance",
                "P",
                [],
                [["a", v.spelling()], ["b", v.spelling()]],
                [],
                [
                    ["local", "calculate", "calculate", ["a", "b"], ["result"]],
                    ["send", "result_site", "result_schema", "V", "result"],
                    ["return", []]
                ]
            ],
            [
                "participant",
                "receiver",
                "instance",
                "V",
                [],
                [],
                [f.spelling()],
                [
                    [
                        "receive",
                        "result_site",
                        "result_schema",
                        "P",
                        "result",
                        f.spelling()
                    ],
                    ["return", ["result"]]
                ]
            ]
        ],
        [["entry", "main", [["P", "sender"], ["V", "receiver"]]]]
    ]))
    .unwrap();
    let admitted = admit_supplied(&bytes, &backend(Policy::default())).unwrap();
    let make = |role| {
        NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(
                Domain::new(role, "session", "main", None),
                None,
                PublicInputs::LocalOnly,
            ),
            None,
        )
        .unwrap()
    };
    let mut p = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        make("P"),
        vec![vector(&[1, 2, 3]), vector(&[4, 5, 6])],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let mut v = Runner::new(&admitted, "main", "V", "session", make("V"), vec![])
        .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Local(local) = p.poll() else {
        panic!()
    };
    p.execute_local(&local.cut).unwrap();
    let Action::Receive(expected) = v.poll() else {
        panic!()
    };
    let send = p.poll().cut().unwrap();
    let packet = p.take_send(&send).unwrap();
    let bytes = p.backend().encode_value(&packet.payload).unwrap();
    assert_eq!(bytes, wire(19, None, &[32]));
    assert!(
        v.backend()
            .decode_typed_value(expected.ty.clone(), &wire(19, None, &[plonky3::MODULUS]))
            .is_err()
    );
    assert!(matches!(v.poll(), Action::Receive(ref still) if still == &expected));
    let decoded = v
        .backend()
        .decode_typed_value(expected.ty.clone(), &bytes)
        .unwrap();
    v.deliver(Packet {
        envelope: packet.envelope,
        ty: packet.ty.clone(),
        payload: decoded,
    })
    .unwrap();
    let Action::Returned(values) = v.poll() else {
        panic!()
    };
    assert_value(&values[0], &field(32));
    assert!(matches!(p.poll(), Action::Returned(_)));
    assert_eq!(p.backend().active_frames(), 0);
    assert_eq!(v.backend().active_frames(), 0);
}
