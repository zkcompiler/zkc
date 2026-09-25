#[path = "domains/support.rs"]
mod support;

use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use serde_json::json;
use support::{Controlled, assert_value, backend, one, program};
use zkc_backends::{KoalaBear, KoalaBearExt8, Policy, Value, domains::KOALA_BEAR_EXT8, plonky3};
use zkc_runtime::interactive::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, Type, Value as RuntimeValue,
    admit_supplied,
};

const EXT: &str = "koala-bear.ext8-binomial3";
fn binding(name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![EXT.into()],
        implementation: format!("plonky3/{name}"),
    }
}
fn scalar(a: [u32; 8]) -> KoalaBearExt8 {
    KoalaBearExt8::from(a.map(KoalaBear::new))
}
fn field(a: [u32; 8]) -> Value {
    Value::KoalaBearExt8Field(scalar(a))
}
fn vector(a: &[[u32; 8]]) -> Value {
    Value::koala_bear_ext8_vector(
        &a.iter().copied().map(scalar).collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}
fn call(name: &str, attrs: &[&str], args: Vec<Value>) -> Vec<Value> {
    one(backend(Policy::default()), binding(name), attrs, args)
        .0
        .unwrap()
}
const ONE: [u32; 8] = [1, 0, 0, 0, 0, 0, 0, 0];
const X: [u32; 8] = [0, 1, 0, 0, 0, 0, 0, 0];
const X7: [u32; 8] = [0, 0, 0, 0, 0, 0, 0, 1];
const ZERO: [u32; 8] = [0; 8];
// Integer convolution, independent of upstream multiplication and wire encoding.
fn product(a: [u32; 8], b: [u32; 8]) -> [u32; 8] {
    let p = u128::from(plonky3::MODULUS);
    let mut out = [0u128; 8];
    for i in 0..8 {
        for j in 0..8 {
            out[(i + j) % 8] = (out[(i + j) % 8]
                + u128::from(a[i]) * u128::from(b[j]) * if i + j >= 8 { 3 } else { 1 })
                % p;
        }
    }
    out.map(|x| x as u32)
}

#[test]
fn nominal_admission_and_native_signatures_are_independent() {
    let b = backend(Policy::default());
    let identity = Identity::parse(EXT).unwrap();
    assert_eq!(identity, Identity::KoalaBearExt8);
    assert_eq!(identity.base_field(), Some(Identity::KoalaBear));
    assert_eq!(identity.scalar_field(), Some(identity));
    assert_eq!(identity.group(), None);
    assert_eq!(identity.transcript(), None);
    assert!(
        zkc_backends::domains::TRANSCRIPTS
            .iter()
            .any(|t| t.domain.field == identity && t.suite == Identity::Merlin3KoalaBearExt8)
    );
    for kind in [
        Type::Field,
        Type::Vector,
        Type::Polynomial,
        Type::Round,
        Type::Matrix,
    ] {
        let ty = KOALA_BEAR_EXT8.physical(kind).unwrap();
        assert_eq!(PhysicalType::parse(&ty.spelling()).unwrap(), ty);
        assert_eq!(ty.logical().codec(), KOALA_BEAR_EXT8.codec(kind));
        assert!(ty.spelling().contains(EXT));
    }
    assert!(LogicalType::new(Type::Rng, identity).is_ok());
    assert!(KOALA_BEAR_EXT8.physical(Type::Rng).is_some());
    for kind in [
        Type::Nonce,
        Type::Transcript,
        Type::Table,
        Type::Point,
        Type::Group,
        Type::Groups,
        Type::Commitment,
        Type::Proof,
        Type::ProverKey,
        Type::VerifierKey,
        Type::OpeningState,
    ] {
        assert!(LogicalType::new(kind, identity).is_err());
        assert!(KOALA_BEAR_EXT8.physical(kind).is_none());
    }
    for name in [
        "field.embed",
        "field.constant",
        "field.add",
        "field.sub",
        "field.mul",
        "field.neg",
        "field.inverse",
        "field.equal",
        "vector.constant",
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
        "vector.scatter_sum",
        "vector.kronecker",
        "vector.matvec",
        "poly.from_coefficients",
        "poly.coefficients",
        "poly.degree_check",
        "poly.univariate_evaluate",
        "poly.univariate_boundary",
        "poly.boundary",
        "poly.round_evaluate",
        "matrix.mul_vector",
        "matrix.transpose_mul_vector",
        "matrix.bilinear",
        "matrix.shape_check",
    ] {
        let bind = binding(name);
        assert_eq!(
            Some(bind.signature().unwrap()),
            b.binding_signature(&bind),
            "{name}"
        );
        for provider in ["arkworks", "dalek", "plonky3-diagonal", "uninstalled"] {
            let mut wrong = bind.clone();
            wrong.implementation = format!("{provider}/{name}");
            assert!(wrong.signature().is_err(), "{name}");
            assert!(b.binding_signature(&wrong).is_none(), "{name}");
        }
    }
    let sig = binding("field.embed").signature().unwrap();
    assert_eq!(sig.inputs[0].logical().identity(), Identity::KoalaBear);
    assert_eq!(sig.outputs[0].logical().identity(), identity);
    for base in ["koala-bear", "bls12-381.fr", "ristretto255.scalar"] {
        let mut wrong = binding("field.embed");
        wrong.arguments = vec![base.into()];
        assert!(wrong.signature().is_err());
        assert!(b.binding_signature(&wrong).is_none());
    }
    let mut wrong_provider = binding("field.embed");
    wrong_provider.implementation = "arkworks/field.embed".into();
    assert!(wrong_provider.signature().is_err());
    assert!(b.binding_signature(&wrong_provider).is_none());
    for name in [
        "transcript.challenge",
        "poly.fold",
        "pcs.open",
        "curve.generator",
        "vector.to_point",
        "vector.from_table",
    ] {
        assert!(binding(name).signature().is_err());
        assert!(b.binding_signature(&binding(name)).is_none());
    }
}

#[test]
fn non_base_arithmetic_wraps_by_three_and_inverse_is_checked() {
    assert_value(
        &call("field.mul", &[], vec![field(X), field(X7)])[0],
        &field([3, 0, 0, 0, 0, 0, 0, 0]),
    );
    let mut state = 17u64;
    let mut next = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((state >> 32) % u64::from(plonky3::MODULUS)) as u32
    };
    for _ in 0..40 {
        let a = std::array::from_fn(|_| next());
        let b = std::array::from_fn(|_| next());
        assert_value(
            &call("field.mul", &[], vec![field(a), field(b)])[0],
            &field(product(a, b)),
        );
        let inverse = call("field.inverse", &[], vec![field(a)]).remove(0);
        assert_value(
            &call("field.mul", &[], vec![field(a), inverse])[0],
            &field(ONE),
        );
        let minus = call("field.neg", &[], vec![field(a)]).remove(0);
        assert_value(
            &call("field.add", &[], vec![field(a), minus])[0],
            &field(ZERO),
        );
        assert_value(
            &call("field.sub", &[], vec![field(a), field(a)])[0],
            &field(ZERO),
        );
    }
    assert_eq!(
        one(
            backend(Policy::default()),
            binding("field.inverse"),
            &[],
            vec![field(ZERO)]
        )
        .0
        .unwrap_err(),
        "refused:zero-inverse"
    );
    for n in [0, 1, 3, plonky3::MODULUS - 1] {
        let expected = field([n, 0, 0, 0, 0, 0, 0, 0]);
        assert_value(
            &call(
                "field.embed",
                &[],
                vec![Value::KoalaBearField(KoalaBear::new(n))],
            )[0],
            &expected,
        );
        assert_value(
            &call("field.constant", &[&n.to_string()], vec![])[0],
            &expected,
        );
    }
}

#[test]
fn shared_vector_polynomial_round_and_matrix_kernels() {
    let a = [ONE, X, X7];
    let b = [X7, X, ONE];
    let products = a
        .into_iter()
        .zip(b)
        .map(|(a, b)| product(a, b))
        .collect::<Vec<_>>();
    assert_value(
        &call("vector.mul", &[], vec![vector(&a), vector(&b)])[0],
        &vector(&products),
    );
    let dot = call("vector.dot", &[], vec![vector(&a), vector(&b)]).remove(0);
    assert_value(&dot, &call("vector.sum", &[], vec![vector(&products)])[0]);
    let poly = call(
        "poly.from_coefficients",
        &[],
        vec![vector(&[ONE, X7, ZERO])],
    )
    .remove(0);
    assert_value(
        &call("poly.coefficients", &[], vec![poly.clone()])[0],
        &vector(&[ONE, X7]),
    );
    assert_value(
        &call("poly.univariate_evaluate", &[], vec![poly, field(X)])[0],
        &field([4, 0, 0, 0, 0, 0, 0, 0]),
    );
    let round = Value::KoalaBearExt8Round([scalar(ONE), scalar(X7), KoalaBearExt8::ZERO]);
    assert_value(
        &call("poly.round_evaluate", &[], vec![round, field(X)])[0],
        &field([4, 0, 0, 0, 0, 0, 0, 0]),
    );
    let matrix = Value::koala_bear_ext8_matrix(
        2,
        2,
        &[(0, 1, scalar(X7)), (1, 0, scalar(X))],
        &Policy::default(),
    )
    .unwrap();
    assert_value(
        &call(
            "matrix.mul_vector",
            &[],
            vec![matrix.clone(), vector(&[X7, X])],
        )[0],
        &vector(&[[3, 0, 0, 0, 0, 0, 0, 0]; 2]),
    );
    assert_value(
        &call(
            "matrix.transpose_mul_vector",
            &[],
            vec![matrix.clone(), vector(&[X, X7])],
        )[0],
        &vector(&[[3, 0, 0, 0, 0, 0, 0, 0]; 2]),
    );
    assert_value(
        &call(
            "matrix.bilinear",
            &[],
            vec![matrix, vector(&[ONE, ONE]), vector(&[X7, X])],
        )[0],
        &field([6, 0, 0, 0, 0, 0, 0, 0]),
    );
}

#[test]
fn canonical_coordinate_wire_is_exact_and_domain_separated() {
    let b = backend(Policy::default());
    let a = [0, 1, 2, 3, 4, 5, 6, plonky3::MODULUS - 1];
    let bytes = plonky3::encode_extension(scalar(a));
    assert_eq!(
        bytes.to_vec(),
        a.into_iter().flat_map(u32::to_le_bytes).collect::<Vec<_>>()
    );
    assert_eq!(plonky3::decode_extension(&bytes).unwrap(), scalar(a));
    assert_eq!(
        <KoalaBearExt8 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(&scalar(a)),
        &a.map(KoalaBear::new)
    );
    for n in [0, 4, 28, 31, 33, 64] {
        assert!(plonky3::decode_extension(&vec![0; n]).is_err());
    }
    let values = vec![
        field(a),
        vector(&[a, X]),
        Value::KoalaBearExt8Polynomial([scalar(a), scalar(X)].into()),
        Value::KoalaBearExt8Round([scalar(a), scalar(X), scalar(X7)]),
        Value::koala_bear_ext8_matrix(2, 2, &[(0, 1, scalar(a))], &Policy::default()).unwrap(),
    ];
    for (value, tag) in values.into_iter().zip(26..=30) {
        let ty = value.physical_type();
        let bytes = b.encode_value(&value).unwrap();
        assert_eq!(&bytes[..6], &[b'Z', b'K', b'C', b'V', 1, tag]);
        let decoded = b.decode_typed_value(ty.clone(), &bytes).unwrap();
        assert_value(&value, &decoded);
        assert!(
            Value::typed_wire_retained_bytes_bound(ty.clone(), bytes.len(), &Policy::default())
                .unwrap()
                >= decoded.retained_bytes()
        );
        for len in 0..bytes.len() {
            assert!(b.decode_typed_value(ty.clone(), &bytes[..len]).is_err());
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(b.decode_typed_value(ty.clone(), &extra).is_err());
        for domain in [
            zkc_backends::domains::BLS,
            zkc_backends::domains::RISTRETTO,
            zkc_backends::domains::KOALA_BEAR,
        ] {
            assert!(
                b.decode_typed_value(domain.physical(ty.kind()).unwrap(), &bytes)
                    .is_err()
            );
        }
        let start = match ty.kind() {
            Type::Matrix => 26,
            Type::Vector | Type::Polynomial => 10,
            _ => 6,
        };
        for i in 0..8 {
            for invalid in [plonky3::MODULUS, plonky3::MODULUS + 1, u32::MAX] {
                let mut bad = bytes.clone();
                bad[start + 4 * i..start + 4 * i + 4].copy_from_slice(&invalid.to_le_bytes());
                assert_eq!(
                    b.decode_typed_value(ty.clone(), &bad).unwrap_err().code,
                    "refused:noncanonical-scalar"
                );
            }
        }
    }
    assert!(
        b.encode_value(&Value::KoalaBearExt8Polynomial(
            [KoalaBearExt8::ZERO].into()
        ))
        .is_err()
    );
    let mut bad = b.encode_value(&vector(&[X])).unwrap();
    bad[6..10].copy_from_slice(&u32::MAX.to_le_bytes());
    assert_eq!(
        b.decode_typed_value(KOALA_BEAR_EXT8.physical(Type::Vector).unwrap(), &bad)
            .unwrap_err()
            .code,
        "refused:wire-length"
    );
    assert!(
        Value::koala_bear_ext8_matrix(1, 1, &[(0, 0, KoalaBearExt8::ZERO)], &Policy::default())
            .is_err()
    );
    assert!(Value::koala_bear_ext8_matrix(1, 1, &[(1, 0, scalar(X))], &Policy::default()).is_err());
}

#[test]
fn resource_limits_and_hostile_operands_fail_closed() {
    assert_eq!(vector(&[X, X7]).retained_bytes(), 256 + 64);
    for (limit, success) in [(319, false), (320, true)] {
        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.output_limit = Some(limit);
        assert_eq!(
            one(
                controlled,
                binding("vector.mul"),
                &[],
                vec![vector(&[X, X7]), vector(&[X7, X])]
            )
            .0
            .is_ok(),
            success
        );
    }
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.output_limit = Some(511);
    assert_eq!(
        one(
            controlled,
            binding("field.embed"),
            &[],
            vec![Value::KoalaBearField(KoalaBear::ONE)]
        )
        .0
        .unwrap_err(),
        "exhausted:output-bytes"
    );
    let policy = Policy {
        max_value_bytes: 319,
        ..Policy::default()
    };
    assert!(Value::koala_bear_ext8_vector(&[scalar(X); 2], &policy).is_err());
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.substitute = Some(Value::KoalaBearField(KoalaBear::ONE));
    assert!(
        one(
            controlled,
            binding("field.mul"),
            &[],
            vec![field(X), field(X7)]
        )
        .0
        .is_err()
    );
    // Admission sees the complete mixed-base types before execution.
    let base = zkc_backends::domains::KOALA_BEAR
        .physical(Type::Field)
        .unwrap();
    let ext = KOALA_BEAR_EXT8.physical(Type::Field).unwrap();
    let bytes = program(
        &[binding("field.mul")],
        &[base, ext.clone()],
        vec![json!(["op", "mul", "b0", [], ["a0", "a1"], ["out"]])],
        std::slice::from_ref(&ext),
        &["out".into()],
    );
    assert!(admit_supplied(&bytes, &backend(Policy::default())).is_err());
    for literal in ["2130706433", "00", "-1", "1.0"] {
        let bytes = program(
            &[binding("field.constant")],
            &[],
            vec![json!(["op", "c", "b0", [literal], [], ["out"]])],
            std::slice::from_ref(&ext),
            &["out".into()],
        );
        assert!(admit_supplied(&bytes, &backend(Policy::default())).is_err());
    }
}
