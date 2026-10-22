//! Resident provider integration: exact ports, matched wire language, arithmetic,
//! timing authorization and resource refusal through the existing Runner.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use std::sync::Arc;
use zkc_kernels::blst::bls12_381 as kernel;
use zkc_native::{
    Bls12381G2, Domain, EntryPolicy, G1, NativeBackend, NativeWireError, Policy, Scalar,
    SetupRegistry, Value, native_contracts, native_contracts_with_policy,
};
use zkc_runtime::{
    interpreter::Runner,
    vm::{
        Action, Backend, Contracts, ExecutionPolicy, Identity, InstalledOperation,
        OperationBinding, PhysicalType, Program, StopKind, Type, Value as _,
    },
};

fn backend(policy: Policy, contracts: &Contracts) -> NativeBackend {
    NativeBackend::new(
        policy,
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        SetupRegistry::default(),
    )
    .unwrap()
    .with_contracts(contracts.clone())
    .unwrap()
}
fn binding(name: &str, domain: &str, resident: bool) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![domain.into()],
        implementation: format!(
            "{}/{name}",
            if resident {
                "blst/resident"
            } else {
                "arkworks"
            }
        ),
        physical_arguments: vec![],
    }
}
fn physical(kind: Type, identity: Identity) -> PhysicalType {
    let repr = match identity {
        Identity::Bls12381Fr => "blst/fr",
        Identity::Bls12381G1 => "blst/g1",
        Identity::Bls12381G2 => "blst/g2",
        _ => panic!("resident identity"),
    };
    let logical = zkc_runtime::vm::LogicalType::new(kind, identity).unwrap();
    native_contracts()
        .physical_type(&format!("{}@{repr}", logical.spelling()))
        .unwrap()
}
fn resident(backend: &NativeBackend, value: &Value) -> Value {
    if matches!(value.ty(), Type::Index | Type::Indices | Type::Bool) {
        return value.clone();
    }
    let source = value.physical_type();
    let target = physical(source.kind(), source.logical().identity());
    let bytes = backend.encode_native_value(value).unwrap();
    backend.decode_native_value(&target, &bytes).unwrap()
}
fn program(
    backend: &NativeBackend,
    binding: &OperationBinding,
    attributes: &[&str],
    repeats: usize,
) -> Vec<u8> {
    // Actual independently owned ports construct this test carrier. Admission
    // still resolves expected facts and checks installation independently.
    let operation = backend
        .prepare_binding(binding)
        .expect("installed native operation");
    let signature = operation.signature();
    let names: Vec<_> = (0..signature.inputs.len())
        .map(|i| format!("a{i}"))
        .collect();
    let inputs: Vec<_> = names
        .iter()
        .zip(&signature.inputs)
        .map(|(name, ty)| json!([name, ty.spelling()]))
        .collect();
    let outputs: Vec<_> = signature
        .outputs
        .iter()
        .map(PhysicalType::spelling)
        .collect();
    let mut body = Vec::new();
    let mut returned = Vec::new();
    for n in 0..repeats {
        returned = (0..outputs.len()).map(|i| format!("r{n}_{i}")).collect();
        body.push(json!([
            "op",
            format!("call{n}"),
            "b",
            attributes,
            names,
            returned
        ]));
    }
    body.push(json!(["return", returned]));
    serde_json::to_vec(&json!([
        "zkc.program/0",
        [[
            "b",
            binding.contract,
            binding.arguments,
            binding.implementation,
            binding.physical_arguments
        ]],
        [["function", "f", inputs, outputs, body, ["f", []]]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            inputs,
            outputs,
            [
                ["local", "work", "f", names, returned],
                ["return", returned]
            ],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}
fn run(
    backend: NativeBackend,
    binding: &OperationBinding,
    attrs: &[&str],
    args: Vec<Value>,
    repeats: usize,
) -> (Result<Vec<Value>, String>, zkc_runtime::vm::Usage) {
    let admitted = Program::decode(
        &program(&backend, binding, attrs, repeats),
        backend.contracts(),
    )
    .unwrap();
    admitted.check_installation(&backend).unwrap();
    let mut runner = Runner::new(&admitted, "main", "P", "session", backend, args)
        .unwrap_or_else(|e| panic!("{:?}", e.error));
    loop {
        match runner.poll() {
            Action::Local(action) => {
                runner.execute_local(&action.cut).unwrap();
            }
            Action::Returned(values) => return (Ok(values), runner.usage()),
            Action::Stopped(stop) => {
                return (
                    Err(match stop.kind {
                        StopKind::Backend(error) => error.code,
                        other => panic!("{other:?}"),
                    }),
                    runner.usage(),
                );
            }
            other => panic!("unexpected action: {other:?}"),
        }
    }
}
fn compare(name: &str, domain: &str, attrs: &[&str], args: Vec<Value>) {
    let contracts = native_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    let ordinary = backend(Policy::default(), &contracts);
    let resident_args = args.iter().map(|v| resident(&ordinary, v)).collect();
    let left = run(ordinary, &binding(name, domain, false), attrs, args, 1).0;
    let right = run(
        backend(Policy::default(), &contracts),
        &binding(name, domain, true),
        attrs,
        resident_args,
        1,
    )
    .0;
    let encoder = backend(Policy::default(), &contracts);
    match (left, right) {
        (Ok(left), Ok(right)) => {
            assert_eq!(left.len(), right.len(), "{name}");
            for (a, b) in left.iter().zip(&right) {
                assert_eq!(
                    a.physical_type().logical(),
                    b.physical_type().logical(),
                    "{name}"
                );
                assert_eq!(
                    encoder.encode_native_value(a).unwrap(),
                    encoder.encode_native_value(b).unwrap(),
                    "{name}"
                );
            }
        }
        (Err(left), Err(right)) => assert_eq!(left, right, "{name}"),
        (left, right) => panic!("{name}: {left:?} != {right:?}"),
    }
}
fn vector(values: &[u64]) -> Value {
    Value::Vector(
        values
            .iter()
            .map(|v| Scalar::from(*v))
            .collect::<Vec<_>>()
            .into(),
    )
}

#[test]
fn resident_scalar_and_vector_closure_matches_arkworks() {
    for name in ["field.add", "field.sub", "field.mul", "field.equal"] {
        compare(
            name,
            "bls12-381.fr",
            &[],
            vec![
                Value::Field(Scalar::from(7)),
                Value::Field(Scalar::from(11)),
            ],
        );
    }
    for name in ["field.neg", "field.inverse"] {
        for value in [0, 1, 17] {
            compare(
                name,
                "bls12-381.fr",
                &[],
                vec![Value::Field(Scalar::from(value))],
            );
        }
    }
    compare("field.constant", "bls12-381.fr", &["123456789"], vec![]);
    compare(
        "field.from_index",
        "bls12-381.fr",
        &[],
        vec![Value::Index(u64::MAX)],
    );
    compare("vector.constant", "bls12-381.fr", &["0", "2", "7"], vec![]);
    for n in [0, 1, 8] {
        let a = vector(&(1..=n).collect::<Vec<_>>());
        let b = vector(&(10..10 + n).collect::<Vec<_>>());
        for name in [
            "vector.add",
            "vector.sub",
            "vector.mul",
            "vector.dot",
            "vector.equal",
            "vector.concat",
            "vector.interleave",
        ] {
            compare(name, "bls12-381.fr", &[], vec![a.clone(), b.clone()]);
        }
        for name in [
            "vector.sum",
            "vector.product",
            "vector.inverse",
            "vector.prefix_sum",
            "vector.prefix_product",
            "vector.length",
        ] {
            compare(name, "bls12-381.fr", &[], vec![a.clone()]);
        }
        compare(
            "vector.scale",
            "bls12-381.fr",
            &[],
            vec![a.clone(), Value::Field(Scalar::from(3))],
        );
        compare(
            "vector.append",
            "bls12-381.fr",
            &[],
            vec![a.clone(), Value::Field(Scalar::from(0))],
        );
    }
    compare("vector.empty", "bls12-381.fr", &[], vec![]);
    compare(
        "vector.split",
        "bls12-381.fr",
        &[],
        vec![vector(&[1, 2, 3, 4])],
    );
    compare(
        "vector.at",
        "bls12-381.fr",
        &["2"],
        vec![vector(&[1, 2, 3])],
    );
    compare(
        "vector.get",
        "bls12-381.fr",
        &[],
        vec![vector(&[1, 2]), Value::Index(2)],
    );
    compare(
        "vector.slice",
        "bls12-381.fr",
        &[],
        vec![vector(&[1, 2, 3, 4]), Value::Index(1), Value::Index(2)],
    );
    compare(
        "vector.length_check",
        "bls12-381.fr",
        &["4"],
        vec![vector(&[1, 2, 3, 4])],
    );
    for name in ["vector.splat", "vector.powers"] {
        compare(
            name,
            "bls12-381.fr",
            &["5"],
            vec![Value::Field(Scalar::from(3))],
        );
    }
}

#[test]
fn resident_g1_g2_and_pairing_closure_matches_arkworks() {
    for g2 in [false, true] {
        let domain = if g2 { "bls12-381.g2" } else { "bls12-381.g1" };
        let point = |n| {
            if g2 {
                Value::Bls12381G2(Bls12381G2::generator().scale(Scalar::from(n)))
            } else {
                Value::Curve(G1::generator().scale(Scalar::from(n)))
            }
        };
        let points = |n| {
            if g2 {
                Value::Bls12381G2Vector(
                    (0..n)
                        .map(|v| Bls12381G2::generator().scale(Scalar::from(v)))
                        .collect::<Vec<_>>()
                        .into(),
                )
            } else {
                Value::Groups(
                    (0..n)
                        .map(|v| G1::generator().scale(Scalar::from(v)))
                        .collect::<Vec<_>>()
                        .into(),
                )
            }
        };
        for name in ["curve.identity", "curve.generator", "curve.empty"] {
            compare(name, domain, &[], vec![]);
        }
        for n in [0, 1, 8] {
            compare(
                "curve.msm",
                domain,
                &[],
                vec![vector(&(0..n).collect::<Vec<_>>()), points(n)],
            );
            compare(
                "curve.scale_each",
                domain,
                &[],
                vec![vector(&(0..n).collect::<Vec<_>>()), points(n)],
            );
            compare(
                "curve.vector_scale",
                domain,
                &[],
                vec![points(n), Value::Field(Scalar::from(3))],
            );
            for name in ["curve.vector_add", "curve.concat"] {
                compare(name, domain, &[], vec![points(n), points(n)]);
            }
            compare("curve.append", domain, &[], vec![points(n), point(9)]);
            compare("curve.length", domain, &[], vec![points(n)]);
        }
        for name in ["curve.add", "curve.equal"] {
            compare(name, domain, &[], vec![point(3), point(7)]);
        }
        for name in ["curve.neg", "curve.nonidentity"] {
            compare(name, domain, &[], vec![point(0)]);
            compare(name, domain, &[], vec![point(7)]);
        }
        compare(
            "curve.scale",
            domain,
            &[],
            vec![point(7), Value::Field(Scalar::from(0))],
        );
        compare("curve.at", domain, &["1"], vec![points(3)]);
        compare("curve.get", domain, &[], vec![points(3), Value::Index(2)]);
        compare("curve.split", domain, &[], vec![points(4)]);
    }
    for n in [0, 1, 2] {
        compare(
            "pairing.check",
            "bls12-381.fr",
            &[],
            vec![
                Value::Groups(vec![G1::identity(); n].into()),
                Value::Bls12381G2Vector(vec![Bls12381G2::generator(); n].into()),
            ],
        );
    }
    compare(
        "pairing.check",
        "bls12-381.fr",
        &[],
        vec![
            Value::Groups(vec![G1::generator(), G1::generator().neg()].into()),
            Value::Bls12381G2Vector(vec![Bls12381G2::generator(); 2].into()),
        ],
    );
}

#[test]
fn selected_codecs_match_canonical_language_and_reject_invalid_encodings() {
    let backend = backend(Policy::default(), native_contracts());
    for value in [
        Value::Field(Scalar::from(0)),
        Value::Field(Scalar::from(9)),
        Value::Curve(G1::identity()),
        Value::Curve(G1::generator()),
        Value::Bls12381G2(Bls12381G2::identity()),
        Value::Bls12381G2(Bls12381G2::generator()),
        vector(&[]),
        vector(&[0, 1, 7]),
        Value::Groups(vec![G1::identity(), G1::generator()].into()),
        Value::Bls12381G2Vector(vec![Bls12381G2::generator()].into()),
    ] {
        let bytes = backend.encode_native_value(&value).unwrap();
        let selected = resident(&backend, &value);
        assert_eq!(backend.encode_native_value(&selected).unwrap(), bytes);
        let ty = selected.physical_type();
        assert!(zkc_native::has_native_wire(&ty));
        assert!(
            backend
                .measure_native_wire(&ty, &bytes)
                .unwrap()
                .retained_bytes()
                >= selected.retained_bytes()
        );
        for index in [0, 5, bytes.len() - 1] {
            let mut invalid = bytes.clone();
            invalid[index] ^= 0xff;
            assert_eq!(
                backend
                    .decode_native_value(&value.physical_type(), &invalid)
                    .is_ok(),
                backend.decode_native_value(&ty, &invalid).is_ok()
            );
        }
        assert!(matches!(
            backend.decode_native_value(&ty, &bytes[..bytes.len() - 1]),
            Err(NativeWireError::Invalid(_))
        ));
    }
    for (kind, identity, width) in [
        (Type::Field, Identity::Bls12381Fr, 32),
        (Type::Group, Identity::Bls12381G1, 48),
        (Type::Group, Identity::Bls12381G2, 96),
    ] {
        let ty = physical(kind, identity);
        let mut bytes = vec![0xff; width + 6];
        bytes[..5].copy_from_slice(b"ZKCV\0");
        bytes[5] = if width == 32 {
            1
        } else if width == 48 {
            9
        } else {
            51
        };
        assert!(matches!(
            backend.decode_native_value(&ty, &bytes),
            Err(NativeWireError::Invalid(_))
        ));
    }
}

#[test]
fn variable_time_permission_is_explicit_and_no_ark_fallback_is_installed() {
    let b = binding("curve.msm", "bls12-381.g1", true);
    assert!(native_contracts().resolve(b.clone()).is_err());
    assert!(
        backend(Policy::default(), native_contracts())
            .prepare_binding(&b)
            .is_none()
    );
    let allowed = native_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    assert!(allowed.resolve(b.clone()).is_ok());
    assert!(
        backend(Policy::default(), &allowed)
            .prepare_binding(&b)
            .is_some()
    );
    let backend = backend(Policy::default(), &allowed);
    for b in [
        binding("pairing.apply", "bls12-381.fr", true),
        binding("curve.scale", "bls12-381.gt", true),
        binding("poly.from_coefficients", "bls12-381.fr", true),
        OperationBinding {
            implementation: "blst/curve.scale".into(),
            ..binding("curve.scale", "bls12-381.g1", true)
        },
    ] {
        assert!(backend.prepare_binding(&b).is_none());
    }
    // A resident exact signature refuses Ark inputs at entry, before any call.
    let binding = binding("curve.scale", "bls12-381.g1", true);
    let program = Program::decode(&program(&backend, &binding, &[], 1), &allowed).unwrap();
    assert!(
        Runner::new(
            &program,
            "main",
            "P",
            "session",
            backend,
            vec![Value::Curve(G1::generator()), Value::Field(Scalar::from(1))]
        )
        .is_err()
    );
}

#[test]
fn retained_bulk_clones_are_shared_bounded_and_cold_warm_results_agree() {
    assert!(std::mem::size_of::<Value>() <= 512);
    let b = backend(Policy::default(), native_contracts());
    let values = resident(&b, &vector(&[1, 2, 3, 4]));
    let alias = values.clone();
    let (Value::BlstVector(a), Value::BlstVector(bulk)) = (&values, &alias) else {
        panic!()
    };
    assert!(Arc::ptr_eq(a, bulk));
    assert_eq!(values.retained_bytes(), 256 + a.storage_bytes());
    let op = binding("vector.scale", "bls12-381.fr", true);
    let args = vec![values, Value::BlstField(kernel::Scalar::from(7))];
    let cold = run(
        backend(Policy::default(), native_contracts()),
        &op,
        &[],
        args.clone(),
        1,
    )
    .0
    .unwrap();
    let warm = run(
        backend(Policy::default(), native_contracts()),
        &op,
        &[],
        args.clone(),
        3,
    )
    .0
    .unwrap();
    assert_eq!(
        b.encode_native_value(&cold[0]).unwrap(),
        b.encode_native_value(&warm[0]).unwrap()
    );
    assert_eq!(args[0].retained_bytes(), alias.retained_bytes());
    let limited = Policy {
        max_numerical_bytes: 0,
        ..Policy::default()
    };
    for repeats in [1, 3] {
        assert!(
            run(
                backend(limited, native_contracts()),
                &op,
                &[],
                args.clone(),
                repeats
            )
            .0
            .unwrap_err()
            .starts_with("exhausted:")
        );
    }
}

#[test]
fn explicit_conversions_are_bidirectional_and_preserve_wire() {
    let b = backend(Policy::default(), native_contracts());
    for value in [
        Value::Field(Scalar::from(19)),
        vector(&[0, 1, 19]),
        Value::Curve(G1::generator()),
        Value::Groups(vec![G1::identity(), G1::generator()].into()),
        Value::Bls12381G2(Bls12381G2::generator()),
        Value::Bls12381G2Vector(vec![Bls12381G2::generator()].into()),
    ] {
        let source = value.physical_type();
        let target = physical(source.kind(), source.logical().identity());
        let convert = |source: &PhysicalType, target: &PhysicalType| OperationBinding {
            contract: "representation.convert".into(),
            arguments: vec![source.logical().spelling()],
            physical_arguments: vec![source.spelling(), target.spelling()],
            implementation: "native/representation.convert".into(),
        };
        let output = run(
            backend(Policy::default(), native_contracts()),
            &convert(&source, &target),
            &[],
            vec![value.clone()],
            1,
        )
        .0
        .unwrap()
        .remove(0);
        assert_eq!(output.physical_type(), target);
        let recovered = run(
            backend(Policy::default(), native_contracts()),
            &convert(&target, &source),
            &[],
            vec![output],
            1,
        )
        .0
        .unwrap()
        .remove(0);
        assert_eq!(
            b.encode_native_value(&value).unwrap(),
            b.encode_native_value(&recovered).unwrap()
        );
    }
}

#[test]
fn remaining_flat_vector_operations_match_arkworks() {
    let a = vector(&[1, 2, 3, 4, 5, 6, 7, 8]);
    for (name, attrs, args) in [
        (
            "vector.transpose",
            vec![],
            vec![a.clone(), Value::Index(2), Value::Index(4)],
        ),
        ("vector.rotate", vec![], vec![a.clone(), Value::Index(3)]),
        ("vector.rotate", vec![], vec![vector(&[]), Value::Index(0)]),
        ("vector.bit_reverse", vec![], vec![a.clone()]),
        (
            "vector.bit_reverse_rows",
            vec![],
            vec![a.clone(), Value::Index(2)],
        ),
        (
            "vector.find_last",
            vec![],
            vec![a.clone(), Value::Field(Scalar::from(5))],
        ),
        (
            "vector.find_last",
            vec![],
            vec![a.clone(), Value::Field(Scalar::from(9))],
        ),
        ("vector.gather", vec!["7", "0", "7"], vec![a.clone()]),
        ("vector.gather", vec!["8"], vec![a.clone()]),
        (
            "vector.scatter_sum",
            vec!["3", "0", "1", "1", "2"],
            vec![vector(&[3, 5, 7, 9])],
        ),
        (
            "vector.kronecker",
            vec![],
            vec![vector(&[2, 3]), vector(&[5, 7])],
        ),
        (
            "vector.matvec",
            vec!["2", "4", "0"],
            vec![a.clone(), vector(&[2, 3, 5, 7])],
        ),
        (
            "vector.matvec",
            vec!["2", "4", "1"],
            vec![a, vector(&[2, 3])],
        ),
        ("vector.inverse", vec![], vec![vector(&[1, 0, 3])]),
        ("vector.add", vec![], vec![vector(&[1]), vector(&[2, 3])]),
    ] {
        compare(name, "bls12-381.fr", &attrs, args);
    }
    for name in ["vector.fill", "vector.geometric"] {
        compare(
            name,
            "bls12-381.fr",
            &[],
            vec![Value::Field(Scalar::from(7)), Value::Index(9)],
        );
    }
    // Full-width operands exercise the Montgomery representation boundary.
    let large = zkc_kernels::arkworks::bls12_381::parse_decimal(
        "52435875175126190479447740508185965837690552500527637822603658699938581184512",
    )
    .unwrap();
    for name in ["field.add", "field.sub", "field.mul"] {
        compare(
            name,
            "bls12-381.fr",
            &[],
            vec![Value::Field(large), Value::Field(large)],
        );
    }
    compare(
        "field.inverse",
        "bls12-381.fr",
        &[],
        vec![Value::Field(large)],
    );
    compare(
        "pairing.check",
        "bls12-381.fr",
        &[],
        vec![
            Value::Groups(vec![G1::generator()].into()),
            Value::Bls12381G2Vector(vec![Bls12381G2::generator()].into()),
        ],
    );
}

#[test]
fn selected_codecs_reject_noncanonical_scalars_and_wrong_subgroups_at_each_bulk_position() {
    use ark_ff::{BigInteger, PrimeField};
    let b = backend(Policy::default(), native_contracts());
    let mut wrong_g1 = vec![0; 48];
    wrong_g1[0] = 0x80; // (0,2), an on-curve point of order three.
    let modulus = Scalar::MODULUS.to_bytes_le();
    for (value, malformed) in [
        (Value::Field(Scalar::from(1)), modulus.clone()),
        (vector(&[1, 2, 3]), modulus),
        (Value::Curve(G1::generator()), wrong_g1.clone()),
        (Value::Groups(vec![G1::generator(); 3].into()), wrong_g1),
    ] {
        let ty = physical(value.ty(), value.physical_type().logical().identity());
        let original = b.encode_native_value(&value).unwrap();
        let bulk = matches!(value.ty(), Type::Vector | Type::Groups);
        for position in 0..if bulk { 3 } else { 1 } {
            let mut bytes = original.clone();
            let offset = if bulk { 10 } else { 6 } + position * malformed.len();
            bytes[offset..offset + malformed.len()].copy_from_slice(&malformed);
            assert!(matches!(
                b.decode_native_value(&ty, &bytes),
                Err(NativeWireError::Invalid(_))
            ));
            assert!(matches!(
                b.decode_native_value(&value.physical_type(), &bytes),
                Err(NativeWireError::Invalid(_))
            ));
        }
    }
    for value in [
        Value::Curve(G1::identity()),
        Value::Bls12381G2(Bls12381G2::identity()),
    ] {
        let ty = physical(value.ty(), value.physical_type().logical().identity());
        let mut bytes = b.encode_native_value(&value).unwrap();
        bytes[6] |= 0x20; // Infinity's sign bit must be zero.
        assert!(matches!(
            b.decode_native_value(&ty, &bytes),
            Err(NativeWireError::Invalid(_))
        ));
    }
}

#[test]
fn resident_output_work_and_memory_refusals_preserve_input_aliases() {
    let encoder = backend(Policy::default(), native_contracts());
    for (name, domain, ark_args, bytes, work) in [
        (
            "vector.scale",
            "bls12-381.fr",
            vec![vector(&[1, 2, 3]), Value::Field(Scalar::from(7))],
            96,
            Some(16),
        ),
        (
            "vector.append",
            "bls12-381.fr",
            vec![vector(&[1, 2]), Value::Field(Scalar::from(7))],
            96,
            None,
        ),
        (
            "curve.vector_scale",
            "bls12-381.g1",
            vec![
                Value::Groups(vec![G1::generator(); 3].into()),
                Value::Field(Scalar::from(7)),
            ],
            432,
            None,
        ),
        (
            "curve.vector_scale",
            "bls12-381.g2",
            vec![
                Value::Bls12381G2Vector(vec![Bls12381G2::generator(); 3].into()),
                Value::Field(Scalar::from(7)),
            ],
            864,
            None,
        ),
    ] {
        let args: Vec<_> = ark_args.iter().map(|v| resident(&encoder, v)).collect();
        let original: Vec<_> = args
            .iter()
            .map(|v| encoder.encode_native_value(v).unwrap())
            .collect();
        let op = binding(name, domain, true);
        // Destination families retain staging and final charges concurrently.
        let memory = if name == "vector.scale" {
            256 + bytes * 2
        } else {
            256 + bytes
        };
        let retained = 256 + bytes;
        for (policy, available, expected) in [
            (
                Policy {
                    max_numerical_bytes: memory,
                    ..Policy::default()
                },
                retained,
                None,
            ),
            (
                Policy {
                    max_numerical_bytes: memory - 1,
                    ..Policy::default()
                },
                retained,
                Some("exhausted:numerical-bytes"),
            ),
            (
                Policy::default(),
                retained - 1,
                Some("exhausted:output-bytes"),
            ),
        ] {
            let mut driver = support::Controlled::new(backend(policy, native_contracts()));
            driver.output_limit = Some(available);
            let bytes = program(&driver.inner, &op, &[], 1);
            let (result, driver) = support::run_program(driver, &bytes, args.clone());
            if let Some(error) = expected {
                assert_eq!(result.unwrap_err(), error, "{name}");
                assert!(driver.outputs.is_empty());
            } else {
                assert_eq!(result.unwrap().len(), 1);
            }
            assert_eq!(driver.inner.active_frames(), 0);
        }
        if let Some(work) = work {
            let limited = Policy {
                max_numerical_work: work - 1,
                ..Policy::default()
            };
            assert_eq!(
                run(
                    backend(limited, native_contracts()),
                    &op,
                    &[],
                    args.clone(),
                    1
                )
                .0
                .unwrap_err(),
                "exhausted:numerical-work"
            );
        }
        let guard = zkc_kernels::allocation::failure::after(0);
        let failed = run(
            backend(Policy::default(), native_contracts()),
            &op,
            &[],
            args.clone(),
            1,
        )
        .0;
        drop(guard);
        assert_eq!(failed.unwrap_err(), "exhausted:allocation");
        for (arg, saved) in args.iter().zip(original) {
            assert_eq!(encoder.encode_native_value(arg).unwrap(), saved);
        }
    }
}

#[test]
fn repeated_resident_msm_does_not_reconstruct_adapter_owned_bulk_buffers() {
    let contracts = native_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    let encoder = backend(Policy::default(), &contracts);
    for (domain, ark_points) in [
        (
            "bls12-381.g1",
            Value::Groups(vec![G1::generator(); 8].into()),
        ),
        (
            "bls12-381.g2",
            Value::Bls12381G2Vector(vec![Bls12381G2::generator(); 8].into()),
        ),
    ] {
        let args = vec![
            resident(&encoder, &vector(&[1, 2, 3, 4, 5, 6, 7, 8])),
            resident(&encoder, &ark_points),
        ];
        let op = binding("curve.msm", domain, true);
        let guard = zkc_kernels::allocation::failure::after(0);
        let result = run(
            backend(Policy::default(), &contracts),
            &op,
            &[],
            args.clone(),
            3,
        )
        .0;
        assert!(result.is_ok());
        // The pending adapter failure must remain unconsumed across all MSMs.
        assert!(kernel::ScalarVector::filled(1, kernel::Scalar::ONE).is_err());
        drop(guard);
        for policy in [
            Policy {
                max_numerical_work: 0,
                ..Policy::default()
            },
            Policy {
                max_numerical_bytes: 0,
                ..Policy::default()
            },
        ] {
            assert!(
                run(backend(policy, &contracts), &op, &[], args.clone(), 1)
                    .0
                    .unwrap_err()
                    .starts_with("exhausted:")
            );
        }
    }
    let op = binding("field.constant", "bls12-381.fr", true);
    for repeats in [1, 3] {
        let (result, _) = run(
            backend(Policy::default(), &contracts),
            &op,
            &["123456789"],
            vec![],
            repeats,
        );
        assert!(matches!(&result.unwrap()[0], Value::BlstField(_)));
    }
}

#[test]
fn granting_g1_msm_does_not_grant_g2_or_weaken_operand_premises() {
    use zkc_runtime::vm::{ImplementationRequirements, TimingRequirement};
    let g1 = binding("curve.msm", "bls12-381.g1", true);
    let g2 = binding("curve.msm", "bls12-381.g2", true);
    let requirements = ImplementationRequirements {
        timing: TimingRequirement::VariableTime,
        timing_operands: &[0, 1],
    };
    let contracts = native_contracts()
        .with_timing_grant(g1.clone(), requirements)
        .unwrap();
    assert_eq!(
        contracts.resolve(g1.clone()).unwrap().requirements(),
        requirements
    );
    assert!(contracts.resolve(g2.clone()).is_err());
    assert!(native_contracts().resolve(g1.clone()).is_err());
    let backend = backend(Policy::default(), &contracts);
    assert_eq!(
        backend.prepare_binding(&g1).unwrap().requirements(),
        requirements
    );
    assert!(backend.prepare_binding(&g2).is_none());
    for timing_operands in [&[0][..], &[1][..]] {
        assert!(
            contracts
                .with_timing_grant(
                    g1.clone(),
                    ImplementationRequirements {
                        timing: TimingRequirement::VariableTime,
                        timing_operands,
                    }
                )
                .is_err()
        );
    }
    let args = vec![
        Value::BlstVector(Arc::new(kernel::ScalarVector::from_elements(vec![]))),
        Value::BlstG1Vector(Arc::new(kernel::G1Vector::from_elements(vec![]))),
    ];
    let (result, _) = run(backend, &g1, &[], args, 1);
    assert!(
        matches!(result.unwrap().as_slice(), [Value::BlstG1(point)] if *point == kernel::G1::identity())
    );
}
