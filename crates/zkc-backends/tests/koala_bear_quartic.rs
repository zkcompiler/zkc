#[path = "domains/support.rs"]
mod support;

use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use support::{Controlled, assert_value, backend, one};
use zkc_backends::{KoalaBear, KoalaBearExt4, Policy, Value, domains::KOALA_BEAR_EXT4};
use zkc_kernels::plonky3;
use zkc_runtime::vm::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, Type, Value as RuntimeValue,
};

const EXT: &str = "koala-bear.ext4-binomial3";
fn binding(name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![EXT.into()],
        implementation: format!("plonky3/{name}"),
    }
}
fn scalar(a: [u32; 4]) -> KoalaBearExt4 {
    KoalaBearExt4::from(a.map(KoalaBear::new))
}
fn field(a: [u32; 4]) -> Value {
    Value::KoalaBearExt4Field(scalar(a))
}
fn vector(a: &[[u32; 4]]) -> Value {
    Value::koala_bear_ext4_vector(
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
const ONE: [u32; 4] = [1, 0, 0, 0];
const X: [u32; 4] = [0, 1, 0, 0];
const X3: [u32; 4] = [0, 0, 0, 1];
const ZERO: [u32; 4] = [0; 4];
/// Integer convolution modulo X^4 - 3, independent of upstream multiplication.
fn product(a: [u32; 4], b: [u32; 4]) -> [u32; 4] {
    let p = u128::from(plonky3::MODULUS);
    let mut out = [0u128; 4];
    for i in 0..4 {
        for j in 0..4 {
            out[(i + j) % 4] = (out[(i + j) % 4]
                + u128::from(a[i]) * u128::from(b[j]) * if i + j >= 4 { 3 } else { 1 })
                % p;
        }
    }
    out.map(|x| x as u32)
}

#[test]
fn nominal_admission_and_native_signatures_are_independent() {
    let b = backend(Policy::default());
    let identity = Identity::parse(EXT).unwrap();
    assert_eq!(identity, Identity::KoalaBearExt4);
    assert_eq!(identity.base_field(), Some(Identity::KoalaBear));
    assert_eq!(identity.scalar_field(), Some(identity));
    assert_eq!(identity.group(), None);
    assert_eq!(identity.transcript(), None);
    // Sampling and transcript suites are not installed for this extension.
    assert!(
        !zkc_backends::domains::TRANSCRIPTS
            .iter()
            .any(|t| t.domain.field == identity)
    );
    for kind in [
        Type::Field,
        Type::Vector,
        Type::Polynomial,
        Type::Round,
        Type::Matrix,
    ] {
        let ty = KOALA_BEAR_EXT4.physical(kind).unwrap();
        assert_eq!(PhysicalType::parse(&ty.spelling()).unwrap(), ty);
        assert_eq!(ty.logical().codec(), KOALA_BEAR_EXT4.codec(kind));
        assert!(ty.spelling().contains(EXT));
    }
    for kind in [
        Type::Rng,
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
        assert!(KOALA_BEAR_EXT4.physical(kind).is_none());
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
        "vector.product",
        "vector.dot",
        "vector.split",
        "vector.concat",
        "vector.at",
        "vector.length_check",
        "vector.gather",
        "vector.scatter_sum",
        "vector.kronecker",
        "vector.matvec",
        "vector.bit_reverse",
        "vector.bit_reverse_rows",
        "poly.from_coefficients",
        "poly.coefficients",
        "poly.degree_check",
        "poly.univariate_evaluate",
        "poly.univariate_boundary",
        "poly.boundary",
        "poly.round_evaluate",
        "poly.coset_evaluate",
        "poly.coset_interpolate",
        "poly.even_odd_fold",
        "matrix.mul_vector",
        "matrix.transpose_mul_vector",
        "matrix.bilinear",
        "matrix.shape_check",
        "encoding.field_le",
        "encoding.fields_from_montgomery_le",
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
    for name in [
        "transcript.challenge",
        "random.draw",
        "random.index",
        "hash.poseidon2_16",
        "poly.fold",
        "pcs.open",
        "curve.generator",
        "vector.to_point",
    ] {
        assert!(binding(name).signature().is_err(), "{name}");
        assert!(b.binding_signature(&binding(name)).is_none(), "{name}");
    }
}

#[test]
fn quartic_arithmetic_wraps_by_three_and_inverse_is_checked() {
    assert_value(
        &call("field.mul", &[], vec![field(X), field(X3)])[0],
        &field([3, 0, 0, 0]),
    );
    let mut state = 23u64;
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
        let expected = field([n, 0, 0, 0]);
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
    let embedded = call(
        "vector.embed",
        &[],
        vec![Value::KoalaBearVector(
            vec![KoalaBear::new(5), KoalaBear::new(7)].into(),
        )],
    );
    assert_value(&embedded[0], &vector(&[[5, 0, 0, 0], [7, 0, 0, 0]]));
}

#[test]
fn shared_vector_polynomial_round_and_matrix_kernels() {
    let a = [ONE, X, X3];
    let b = [X3, X, ONE];
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
        vec![vector(&[ONE, X3, ZERO])],
    )
    .remove(0);
    assert_value(
        &call("poly.coefficients", &[], vec![poly.clone()])[0],
        &vector(&[ONE, X3]),
    );
    assert_value(
        &call("poly.univariate_evaluate", &[], vec![poly, field(X)])[0],
        &field([4, 0, 0, 0]),
    );
    let round = Value::KoalaBearExt4Round([scalar(ONE), scalar(X3), KoalaBearExt4::ZERO]);
    assert_value(
        &call("poly.round_evaluate", &[], vec![round, field(X)])[0],
        &field([4, 0, 0, 0]),
    );
    let matrix = Value::koala_bear_ext4_matrix(
        2,
        2,
        &[(0, 1, scalar(X3)), (1, 0, scalar(X))],
        &Policy::default(),
    )
    .unwrap();
    assert_value(
        &call(
            "matrix.mul_vector",
            &[],
            vec![matrix.clone(), vector(&[X3, X])],
        )[0],
        &vector(&[[3, 0, 0, 0]; 2]),
    );
    assert_value(
        &call(
            "matrix.bilinear",
            &[],
            vec![matrix, vector(&[ONE, ONE]), vector(&[X3, X])],
        )[0],
        &field([6, 0, 0, 0]),
    );
    // Coset evaluation and interpolation over base-field subgroups.
    let coefficients = vector(&[[1, 2, 3, 4], [5, 6, 7, 8], ZERO, ZERO]);
    let poly = call("poly.from_coefficients", &[], vec![coefficients]).remove(0);
    let values = call(
        "poly.coset_evaluate",
        &[],
        vec![poly.clone(), field([3, 0, 0, 0]), Value::Index(4)],
    )
    .remove(0);
    let back = call(
        "poly.coset_interpolate",
        &[],
        vec![values, field([3, 0, 0, 0])],
    )
    .remove(0);
    // Polynomials have no wire form; compare their coefficient vectors.
    assert_value(
        &call("poly.coefficients", &[], vec![back])[0],
        &call("poly.coefficients", &[], vec![poly])[0],
    );
}

#[test]
fn canonical_coordinate_wire_is_exact_and_domain_separated() {
    let b = backend(Policy::default());
    let a = [0, 1, 2, plonky3::MODULUS - 1];
    let bytes = plonky3::encode_quartic(scalar(a));
    assert_eq!(
        bytes.to_vec(),
        a.into_iter().flat_map(u32::to_le_bytes).collect::<Vec<_>>()
    );
    assert_eq!(plonky3::decode_quartic(&bytes).unwrap(), scalar(a));
    assert_eq!(
        <KoalaBearExt4 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(&scalar(a)),
        &a.map(KoalaBear::new)
    );
    for n in [0, 4, 12, 15, 17, 32] {
        assert!(plonky3::decode_quartic(&vec![0; n]).is_err());
    }
    let values = vec![
        (field(a), Some(21)),
        (vector(&[a, X]), Some(22)),
        (
            Value::KoalaBearExt4Polynomial([scalar(a), scalar(X)].into()),
            None,
        ),
        (
            Value::KoalaBearExt4Round([scalar(a), scalar(X), scalar(X3)]),
            None,
        ),
        (
            Value::koala_bear_ext4_matrix(2, 2, &[(0, 1, scalar(a))], &Policy::default()).unwrap(),
            Some(28),
        ),
    ];
    for (value, tag) in values {
        let ty = value.physical_type();
        let Some(tag) = tag else {
            assert!(!zkc_backends::has_native_wire(&ty));
            assert!(b.encode_native_value(&value).is_err());
            continue;
        };
        let bytes = b.encode_native_value(&value).unwrap();
        assert_eq!(&bytes[..6], &[b'Z', b'K', b'C', b'V', 0, tag]);
        let decoded = b.decode_native_value(&ty.clone(), &bytes).unwrap();
        assert_value(&value, &decoded);
        for len in 0..bytes.len() {
            assert!(b.decode_native_value(&ty.clone(), &bytes[..len]).is_err());
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(b.decode_native_value(&ty.clone(), &extra).is_err());
        // The octic carrier of the same kind never reads a quartic frame.
        assert!(
            b.decode_native_value(
                &zkc_backends::domains::KOALA_BEAR_EXT8
                    .physical(ty.kind())
                    .unwrap(),
                &bytes
            )
            .is_err()
        );
        let start = match ty.kind() {
            Type::Matrix => 26,
            Type::Vector => 10,
            _ => 6,
        };
        for i in 0..4 {
            for invalid in [plonky3::MODULUS, u32::MAX] {
                let mut bad = bytes.clone();
                bad[start + 4 * i..start + 4 * i + 4].copy_from_slice(&invalid.to_le_bytes());
                assert_eq!(
                    b.decode_native_value(&ty.clone(), &bad)
                        .unwrap_err()
                        .to_string(),
                    "native-wire-invalid:scalar"
                );
            }
        }
    }
    assert!(
        Value::koala_bear_ext4_matrix(1, 1, &[(0, 0, KoalaBearExt4::ZERO)], &Policy::default())
            .is_err()
    );
}

#[test]
fn resource_limits_and_hostile_operands_fail_closed() {
    assert_eq!(vector(&[X, X3]).retained_bytes(), 256 + 32);
    for (limit, success) in [(287, false), (288, true)] {
        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.output_limit = Some(limit);
        assert_eq!(
            one(
                controlled,
                binding("vector.mul"),
                &[],
                vec![vector(&[X, X3]), vector(&[X3, X])]
            )
            .0
            .is_ok(),
            success
        );
    }
    let policy = Policy {
        max_value_bytes: 287,
        ..Policy::default()
    };
    assert!(Value::koala_bear_ext4_vector(&[scalar(X); 2], &policy).is_err());
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.substitute = Some(Value::KoalaBearField(KoalaBear::ONE));
    assert!(
        one(
            controlled,
            binding("field.mul"),
            &[],
            vec![field(X), field(X3)]
        )
        .0
        .is_err()
    );
}
