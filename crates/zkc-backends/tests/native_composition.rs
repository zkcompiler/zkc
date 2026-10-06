//! Native bulk ingress, nested aggregate bounds and target-group execution.
#[path = "domains/support.rs"]
mod support;
use p3_field::PrimeCharacteristicRing;
use zkc_backends::{
    Bn254G1, Bn254G2, Bn254Gt, Bn254Scalar as F, NativeBackend, NativeWireError as Error, Policy,
    RistrettoScalar, Value,
};
use zkc_runtime::interactive::{
    DecodeReason, LogicalType, OperationBinding, Value as RuntimeValue,
};

fn backend(policy: Policy) -> NativeBackend {
    support::backend(policy)
}
fn roundtrip(v: Value) {
    let b = backend(Policy::default());
    assert!(v.physical_type().logical().is_native_message_data());
    let bytes = b.encode_native_value(&v).unwrap();
    let got = b.decode_native_value(&v.physical_type(), &bytes).unwrap();
    // Existing canonical leaf formats remain identical across codec owners.
    // Native BLS vector/group tags and recursive frames are intentionally distinct.
    if !matches!(bytes[5], 65..=69) {
        let old = b.decode_typed_value(v.physical_type(), &bytes).unwrap();
        assert_eq!(b.encode_native_value(&old).unwrap(), bytes);
    }
    assert_eq!(b.encode_native_value(&got).unwrap(), bytes);
    assert_eq!(got.physical_type(), v.physical_type());
    for n in [0, 5, bytes.len() - 1] {
        assert!(matches!(
            b.decode_native_value(&v.physical_type(), &bytes[..n]),
            Err(Error::Invalid(_))
        ));
    }
    let mut wrong = bytes.clone();
    wrong[5] ^= 128;
    assert_eq!(
        b.decode_native_value(&v.physical_type(), &wrong)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Header)
    );
    let mut extra = bytes;
    extra.push(0);
    assert_eq!(
        b.decode_native_value(&v.physical_type(), &extra)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Length)
    );
    // Every leaf also passes through expected-type recursive framing.
    let seq = zkc_backends::Sequence::new(v.physical_type().logical(), vec![v], &Policy::default())
        .unwrap();
    let value = Value::Sequence(seq);
    let bytes = b.encode_native_value(&value).unwrap();
    assert_eq!(
        b.encode_native_value(
            &b.decode_native_value(&value.physical_type(), &bytes)
                .unwrap()
        )
        .unwrap(),
        bytes
    );
}
#[test]
fn installed_bulk_domains_and_oracle_leaves_use_canonical_bytes() {
    let p = Policy::default();
    for n in [0, 1, 3, 64] {
        for v in [
            Value::Vector(vec![zkc_backends::Scalar::from(7); n].into()),
            Value::Groups(vec![zkc_backends::GroupPoint::generator(); n].into()),
            Value::Bn254Vector(vec![F::from(7); n].into()),
            Value::Bn254G1Vector(vec![Bn254G1::generator(); n].into()),
            Value::Bn254G2Vector(vec![Bn254G2::generator(); n].into()),
            Value::RistrettoVector(vec![RistrettoScalar::from(11u64); n].into()),
            Value::RistrettoGroups(
                vec![curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT; n].into(),
            ),
            Value::KoalaBearVector(vec![zkc_backends::KoalaBear::from_u64(5); n].into()),
            Value::KoalaBearExt8Vector(vec![zkc_backends::KoalaBearExt8::from_u64(9); n].into()),
        ] {
            roundtrip(v);
        }
    }
    for v in [
        Value::matrix(128, 128, &[(127, 127, zkc_backends::Scalar::from(5))], &p).unwrap(),
        Value::bn254_matrix(128, 128, &[(127, 127, F::from(5))], &p).unwrap(),
        Value::ristretto_matrix(128, 128, &[(127, 127, RistrettoScalar::from(5u64))], &p).unwrap(),
        Value::koala_bear_matrix(
            128,
            128,
            &[(127, 127, zkc_backends::KoalaBear::from_u64(5))],
            &p,
        )
        .unwrap(),
        Value::koala_bear_ext8_matrix(
            128,
            128,
            &[(127, 127, zkc_backends::KoalaBearExt8::from_u64(5))],
            &p,
        )
        .unwrap(),
        Value::Bn254Gt(Bn254Gt::generator()),
    ] {
        roundtrip(v);
    }
    for d in [
        zkc_backends::oracle::Domain::Base,
        zkc_backends::oracle::Domain::Extension,
    ] {
        roundtrip(Value::OracleRoot(d, [42; 32]));
        for n in [0, 1, 24] {
            roundtrip(Value::OraclePath(d, vec![[7; 32]; n].into()));
        }
    }
}
#[test]
fn typed_errors_and_aggregate_limits_precede_bulk_allocation() {
    let b = backend(Policy::default());
    let value = Value::Bn254Vector(vec![F::from(3); 4].into());
    let ty = value.physical_type();
    let bytes = b.encode_native_value(&value).unwrap();
    let small = backend(Policy {
        max_table_elements: 3,
        ..Policy::default()
    });
    assert_eq!(
        small.decode_native_value(&ty, &bytes).unwrap_err(),
        Error::Limit
    );
    assert_eq!(small.encode_native_value(&value).unwrap_err(), Error::Limit);
    let mut bad = bytes.clone();
    bad[6..10].fill(255);
    assert_eq!(b.decode_native_value(&ty, &bad).unwrap_err(), Error::Limit);
    let mut bad = bytes;
    bad[106..138].fill(255);
    assert_eq!(
        b.decode_native_value(&ty, &bad).unwrap_err(),
        Error::Invalid(DecodeReason::Scalar)
    );
    let p = Policy {
        max_table_elements: 6,
        ..Policy::default()
    };
    let nested = Value::Sequence(
        zkc_backends::Sequence::new(ty.logical(), vec![value.clone(), value], &Policy::default())
            .unwrap(),
    );
    let bytes = b.encode_native_value(&nested).unwrap();
    assert_eq!(
        backend(p)
            .decode_native_value(&nested.physical_type(), &bytes)
            .unwrap_err(),
        Error::Limit
    );
    assert_eq!(
        backend(p).encode_native_value(&nested).unwrap_err(),
        Error::Limit
    );
    let point = Value::Bn254Gt(Bn254Gt::identity());
    let mut bytes = b.encode_native_value(&point).unwrap();
    bytes[6..].fill(0);
    assert_eq!(
        b.decode_native_value(&point.physical_type(), &bytes)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Group)
    );
    let limited = backend(Policy {
        max_value_bytes: 511,
        ..Policy::default()
    });
    assert_eq!(
        limited
            .decode_native_value(&point.physical_type(), &bytes)
            .unwrap_err(),
        Error::Limit,
        "fixed-value policy must precede subgroup validation"
    );
    // Length and header still fail before the value policy.
    assert_eq!(
        limited
            .decode_native_value(&point.physical_type(), &bytes[..bytes.len() - 1])
            .unwrap_err(),
        Error::Invalid(DecodeReason::Length)
    );
    assert!(LogicalType::parse("groups:bn254.gt").is_err());
}
#[test]
fn pairing_result_uses_ordinary_group_contracts() {
    let call = |name: &str, domain: &str, args: Vec<Value>| {
        support::one(
            backend(Policy::default()),
            OperationBinding {
                contract: name.into(),
                arguments: vec![domain.into()],
                implementation: format!("arkworks/{name}"),
            },
            &[],
            args,
        )
        .0
        .unwrap()
        .remove(0)
    };
    let g1 = Bn254G1::generator().scale(F::from(3));
    let g2 = Bn254G2::generator().scale(F::from(5));
    let paired = call(
        "pairing.apply",
        "bn254.fr",
        vec![Value::Bn254G1(g1), Value::Bn254G2(g2)],
    );
    let scaled = call(
        "curve.scale",
        "bn254.gt",
        vec![
            Value::Bn254Gt(Bn254Gt::generator()),
            Value::Bn254Field(F::from(15)),
        ],
    );
    assert!(matches!(
        call("curve.equal", "bn254.gt", vec![paired.clone(), scaled]),
        Value::Bool(true)
    ));
    let inverse = call("curve.neg", "bn254.gt", vec![paired.clone()]);
    let identity = call("curve.add", "bn254.gt", vec![paired, inverse]);
    assert!(matches!(
        call("curve.nonidentity", "bn254.gt", vec![identity]),
        Value::Bool(false)
    ));
}

#[test]
fn pairing_preparation_obeys_value_capacity() {
    for (contract, domain, args) in [
        (
            "pairing.apply",
            "bn254.fr",
            vec![
                Value::Bn254G1(Bn254G1::generator()),
                Value::Bn254G2(Bn254G2::generator()),
            ],
        ),
        ("curve.generator", "bn254.gt", vec![]),
    ] {
        for (limit, succeeds) in [(32767, false), (32768, true)] {
            let result = support::one(
                backend(Policy {
                    max_value_bytes: limit,
                    ..Policy::default()
                }),
                OperationBinding {
                    contract: contract.into(),
                    arguments: vec![domain.into()],
                    implementation: format!("arkworks/{contract}"),
                },
                &[],
                args.clone(),
            )
            .0;
            if succeeds {
                assert!(result.is_ok(), "{contract}: {result:?}");
            } else {
                assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
            }
        }
    }
}

#[test]
fn nested_target_budget_precedes_subgroup_validation() {
    let p = Policy::default();
    let b = backend(p);
    let point = Value::Bn254Gt(Bn254Gt::generator());
    let nested = Value::Sequence(
        zkc_backends::Sequence::new(
            point.physical_type().logical(),
            vec![point.clone(), point],
            &p,
        )
        .unwrap(),
    );
    let mut bytes = b.encode_native_value(&nested).unwrap();
    // Invalid second target; with a one-group budget preflight must stop
    // before reaching the expensive subgroup parser for either target.
    let end = bytes.len();
    bytes[end - 384..].fill(0);
    assert_eq!(
        backend(Policy { max_groups: 1, ..p })
            .decode_native_value(&nested.physical_type(), &bytes)
            .unwrap_err(),
        Error::Limit
    );
    assert_eq!(
        b.decode_native_value(&nested.physical_type(), &bytes)
            .unwrap_err(),
        Error::Invalid(DecodeReason::Group)
    );
}
#[test]
fn equality_compares_every_element_and_length() {
    for domain in [
        "bn254.fr",
        "bls12-381.fr",
        "ristretto255.scalar",
        "koala-bear",
        "koala-bear.ext8-binomial3",
    ] {
        let vector = |xs: &[u64]| match domain {
            "bn254.fr" => {
                Value::Bn254Vector(xs.iter().map(|x| F::from(*x)).collect::<Vec<_>>().into())
            }
            "bls12-381.fr" => Value::Vector(
                xs.iter()
                    .map(|x| zkc_backends::Scalar::from(*x))
                    .collect::<Vec<_>>()
                    .into(),
            ),
            "ristretto255.scalar" => Value::RistrettoVector(
                xs.iter()
                    .map(|x| RistrettoScalar::from(*x))
                    .collect::<Vec<_>>()
                    .into(),
            ),
            "koala-bear" => Value::KoalaBearVector(
                xs.iter()
                    .map(|x| zkc_backends::KoalaBear::from_u64(*x))
                    .collect::<Vec<_>>()
                    .into(),
            ),
            _ => Value::KoalaBearExt8Vector(
                xs.iter()
                    .map(|x| zkc_backends::KoalaBearExt8::from_u64(*x))
                    .collect::<Vec<_>>()
                    .into(),
            ),
        };
        for (a, b, want) in [
            (&[][..], &[][..], true),
            (&[1, 2, 3][..], &[1, 2, 3][..], true),
            (&[1, 2, 3][..], &[1, 2, 4][..], false),
            (&[1, 2, 3][..], &[1, 2][..], false),
        ] {
            let result = support::one(
                backend(Policy::default()),
                OperationBinding {
                    contract: "vector.equal".into(),
                    arguments: vec![domain.into()],
                    implementation: format!(
                        "{}/vector.equal",
                        if domain.starts_with("koala") {
                            "plonky3"
                        } else if domain.starts_with("ristretto") {
                            "dalek"
                        } else {
                            "arkworks"
                        }
                    ),
                },
                &[],
                vec![vector(a), vector(b)],
            )
            .0
            .unwrap();
            assert!(matches!(&result[..], [Value::Bool(v)] if *v==want));
        }
    }
}
