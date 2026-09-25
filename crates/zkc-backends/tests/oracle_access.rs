#[path = "domains/support.rs"]
mod support;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use support::{backend, one};
use zkc_backends::{KoalaBear, KoalaBearExt8, Policy, Value, oracle::Domain};
use zkc_runtime::interactive::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, Type, Value as RuntimeValue,
};

fn binding(domain: Domain, name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![domain.identity().name().into()],
        implementation: format!("plonky3/{name}"),
    }
}
fn run(domain: Domain, name: &str, args: Vec<Value>) -> Vec<Value> {
    one(backend(Policy::default()), binding(domain, name), &[], args)
        .0
        .unwrap()
}
fn vector(domain: Domain, n: usize) -> Value {
    match domain {
        Domain::Base => Value::KoalaBearVector(
            (0..n)
                .map(|i| KoalaBear::from_usize(i + 1))
                .collect::<Vec<_>>()
                .into(),
        ),
        Domain::Extension => Value::KoalaBearExt8Vector(
            (0..n)
                .map(|i| {
                    KoalaBearExt8::from_basis_coefficients_fn(|j| {
                        KoalaBear::from_usize(3 * i + j + 1)
                    })
                })
                .collect::<Vec<_>>()
                .into(),
        ),
    }
}
#[test]
fn authenticated_rows_collections_and_shape_are_independent_of_polynomials() {
    for domain in [Domain::Base, Domain::Extension] {
        for (width, height) in [(1, 1), (2, 3), (3, 8)] {
            let committed = run(
                domain,
                "oracle.commit",
                vec![vector(domain, width * height), Value::Index(width as u64)],
            );
            let root = committed[0].clone();
            let state = committed[1].clone();
            let mut roots = run(domain, "commitments.empty", vec![]).remove(0);
            let mut states = run(domain, "opening_states.empty", vec![]).remove(0);
            for _ in 0..2 {
                roots = run(domain, "commitments.append", vec![roots, root.clone()]).remove(0);
                states =
                    run(domain, "opening_states.append", vec![states, state.clone()]).remove(0);
            }
            assert!(matches!(
                run(domain, "commitments.length", vec![roots.clone()])[0],
                Value::Index(2)
            ));
            assert!(matches!(
                run(domain, "opening_states.length", vec![states.clone()])[0],
                Value::Index(2)
            ));
            let selected = run(
                domain,
                "opening_states.at",
                vec![states.clone(), Value::Index(1)],
            )
            .remove(0);
            let root = run(domain, "commitments.at", vec![roots, Value::Index(1)]).remove(0);
            let opened = run(
                domain,
                "oracle.open",
                vec![selected, Value::Index((height - 1) as u64)],
            );
            let args = vec![
                root,
                Value::Index(width as u64),
                Value::Index(height as u64),
                Value::Index((height - 1) as u64),
                opened[0].clone(),
                opened[1].clone(),
            ];
            assert!(matches!(
                run(domain, "oracle.check", args.clone())[0],
                Value::Bool(true)
            ));
            let mut bad = args.clone();
            if let Value::OracleRoot(_, h) = &mut bad[0] {
                h[0] ^= 1;
            }
            assert!(matches!(
                run(domain, "oracle.check", bad)[0],
                Value::Bool(false)
            ));
            let mut bad = args.clone();
            bad[5] = Value::OraclePath(domain, vec![[0; 32]; 24].into());
            assert!(matches!(
                run(domain, "oracle.check", bad)[0],
                Value::Bool(false)
            ));
            if height == 3 {
                let mut bad = args;
                bad[2] = Value::Index(4);
                assert!(matches!(
                    run(domain, "oracle.check", bad)[0],
                    Value::Bool(false)
                ));
            }
            // Immutable opening custody is not an input/output codec.
            assert!(backend(Policy::default()).encode_value(&state).is_err());
            assert!(backend(Policy::default()).encode_value(&states).is_err());
        }
    }
}
#[test]
fn wire_nominality_canonicality_and_preimport_accounting() {
    for domain in [Domain::Base, Domain::Extension] {
        let committed = run(
            domain,
            "oracle.commit",
            vec![vector(domain, 14), Value::Index(2)],
        );
        let opened = run(
            domain,
            "oracle.open",
            vec![committed[1].clone(), Value::Index(6)],
        );
        let roots = run(
            domain,
            "commitments.append",
            vec![
                run(domain, "commitments.empty", vec![]).remove(0),
                committed[0].clone(),
            ],
        )
        .remove(0);
        let b = backend(Policy::default());
        for value in [committed[0].clone(), opened[1].clone(), roots] {
            let bytes = b.encode_value(&value).unwrap();
            let ty = value.physical_type();
            let recovered = b.decode_typed_value(ty.clone(), &bytes).unwrap();
            assert_eq!(b.encode_value(&recovered).unwrap(), bytes);
            assert!(
                Value::typed_wire_retained_bytes_bound(ty.clone(), bytes.len(), &Policy::default())
                    .unwrap()
                    >= recovered.retained_bytes()
            );
            for length in 0..bytes.len() {
                assert!(b.decode_typed_value(ty.clone(), &bytes[..length]).is_err());
            }
            let mut extra = bytes.clone();
            extra.push(0);
            assert!(b.decode_typed_value(ty.clone(), &extra).is_err());
            let other = if domain == Domain::Base {
                Domain::Extension
            } else {
                Domain::Base
            };
            let other_ty =
                PhysicalType::default_for(LogicalType::new(ty.kind(), other.identity()).unwrap());
            assert!(b.decode_typed_value(other_ty, &bytes).is_err());
        }
    }
}
#[test]
fn bad_coordinates_and_resource_ceiling_refuse_before_allocation() {
    let d = Domain::Base;
    for (name, args, code) in [
        (
            "oracle.commit",
            vec![vector(d, 4), Value::Index(0)],
            "oracle-shape",
        ),
        (
            "oracle.commit",
            vec![vector(d, 4), Value::Index(3)],
            "oracle-shape",
        ),
        (
            "oracle.commit",
            vec![vector(d, 0), Value::Index(1)],
            "oracle-shape",
        ),
        (
            "commitments.at",
            vec![
                run(d, "commitments.empty", vec![]).remove(0),
                Value::Index(0),
            ],
            "oracle-coordinate",
        ),
        (
            "opening_states.at",
            vec![
                run(d, "opening_states.empty", vec![]).remove(0),
                Value::Index(u64::MAX),
            ],
            "oracle-coordinate",
        ),
    ] {
        assert!(
            one(backend(Policy::default()), binding(d, name), &[], args)
                .0
                .unwrap_err()
                .contains(code)
        );
    }
    let committed = run(d, "oracle.commit", vec![vector(d, 4), Value::Index(1)]);
    let err = one(
        backend(Policy::default()),
        binding(d, "oracle.open"),
        &[],
        vec![committed[1].clone(), Value::Index(4)],
    )
    .0
    .unwrap_err();
    assert!(err.contains("oracle-coordinate"));
    let policy = Policy {
        max_value_bytes: 512,
        ..Policy::default()
    };
    assert!(
        one(
            backend(policy),
            binding(d, "oracle.commit"),
            &[],
            vec![vector(d, 4), Value::Index(1)]
        )
        .0
        .unwrap_err()
        .contains("output-bytes")
    );
}
#[test]
fn native_contracts_agree_with_admission_without_promoting_row_authentication_to_pcs() {
    let b = backend(Policy::default());
    for d in [Domain::Base, Domain::Extension] {
        for name in [
            "oracle.commit",
            "oracle.open",
            "oracle.check",
            "commitments.empty",
            "commitments.append",
            "commitments.at",
            "commitments.length",
            "opening_states.empty",
            "opening_states.append",
            "opening_states.at",
            "opening_states.length",
        ] {
            let binding = binding(d, name);
            assert_eq!(
                Some(binding.signature().unwrap()),
                b.binding_signature(&binding)
            );
        }
        assert!(binding(d, "pcs.open").signature().is_err());
        assert!(b.binding_signature(&binding(d, "pcs.open")).is_none());
        for kind in [Type::ProverKey, Type::VerifierKey] {
            assert!(LogicalType::new(kind, d.identity()).is_err());
        }
    }
    let mut wrong = binding(Domain::Base, "oracle.commit");
    wrong.arguments = vec![Identity::MultilinearKzgBls12381.name().into()];
    assert!(wrong.signature().is_err());
    assert!(b.binding_signature(&wrong).is_none());
}
