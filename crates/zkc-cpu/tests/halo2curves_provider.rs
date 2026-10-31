//! Resident provider integration: exact ports, matched wire language, arithmetic,
//! timing authorization and resource refusal through the existing Runner.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use std::sync::Arc;
use zkc_cpu::{
    Bn254G1 as G1, Bn254G2, Bn254Scalar as Scalar, CpuBackend, Domain, EntryPolicy,
    NativeWireError, Policy, SetupRegistry, Value, cpu_contracts, cpu_contracts_with_policy,
};
use zkc_kernels::halo2curves::bn254 as kernel;
use zkc_runtime::{
    interpreter::Runner,
    vm::{
        Action, Backend, Contracts, ExecutionPolicy, Identity, InstalledOperation,
        OperationBinding, PhysicalType, Program, StopKind, Type, Value as _,
    },
};

fn backend(policy: Policy, contracts: &Contracts) -> CpuBackend {
    CpuBackend::new(
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
                "halo2curves-axiom/resident"
            } else {
                "arkworks"
            }
        ),
        physical_arguments: vec![],
    }
}
fn physical(kind: Type, identity: Identity) -> PhysicalType {
    let repr = match identity {
        Identity::Bn254Fr => "halo2curves-axiom/bn254.fr",
        Identity::Bn254G1 => "halo2curves-axiom/bn254.g1",
        Identity::Bn254G2 => "halo2curves-axiom/bn254.g2",
        _ => panic!("resident identity"),
    };
    let logical = zkc_runtime::vm::LogicalType::new(kind, identity).unwrap();
    cpu_contracts()
        .physical_type(&format!("{}@{repr}", logical.spelling()))
        .unwrap()
}
fn resident(backend: &CpuBackend, value: &Value) -> Value {
    if matches!(value.ty(), Type::Index | Type::Indices | Type::Bool) {
        return value.clone();
    }
    let source = value.physical_type();
    let target = physical(source.kind(), source.logical().identity());
    let bytes = backend.encode_native_value(value).unwrap();
    backend.decode_native_value(&target, &bytes).unwrap()
}
fn program(
    backend: &CpuBackend,
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
    backend: CpuBackend,
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
    compare_expected(name, domain, attrs, args, None);
}
fn compare_expected(
    name: &str,
    domain: &str,
    attrs: &[&str],
    args: Vec<Value>,
    error: Option<&str>,
) {
    let contracts = cpu_contracts_with_policy(ExecutionPolicy {
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
    match (left, right, error) {
        (Ok(left), Ok(right), None) => {
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
        (Err(left), Err(right), Some(expected)) => {
            assert_eq!(left, expected, "{name}");
            assert_eq!(right, expected, "{name}");
        }
        (left, right, expected) => {
            panic!("{name}: {left:?}, {right:?}; expected error {expected:?}")
        }
    }
}
fn vector(values: &[u64]) -> Value {
    Value::Bn254Vector(
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
            "bn254.fr",
            &[],
            vec![
                Value::Bn254Field(Scalar::from(7)),
                Value::Bn254Field(Scalar::from(11)),
            ],
        );
    }
    for name in ["field.neg", "field.inverse"] {
        for value in [0, 1, 17] {
            compare_expected(
                name,
                "bn254.fr",
                &[],
                vec![Value::Bn254Field(Scalar::from(value))],
                (name == "field.inverse" && value == 0).then_some("refused:zero-inverse"),
            );
        }
    }
    compare("field.constant", "bn254.fr", &["123456789"], vec![]);
    compare(
        "field.from_index",
        "bn254.fr",
        &[],
        vec![Value::Index(u64::MAX)],
    );
    compare("vector.constant", "bn254.fr", &["0", "2", "7"], vec![]);
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
        ] {
            compare(name, "bn254.fr", &[], vec![a.clone(), b.clone()]);
        }
        for name in ["vector.sum", "vector.product", "vector.length"] {
            compare(name, "bn254.fr", &[], vec![a.clone()]);
        }
        compare(
            "vector.scale",
            "bn254.fr",
            &[],
            vec![a.clone(), Value::Bn254Field(Scalar::from(3))],
        );
        compare(
            "vector.append",
            "bn254.fr",
            &[],
            vec![a.clone(), Value::Bn254Field(Scalar::from(0))],
        );
    }
    compare("vector.empty", "bn254.fr", &[], vec![]);
    compare("vector.split", "bn254.fr", &[], vec![vector(&[1, 2, 3, 4])]);
    compare("vector.at", "bn254.fr", &["2"], vec![vector(&[1, 2, 3])]);
    compare_expected(
        "vector.get",
        "bn254.fr",
        &[],
        vec![vector(&[1, 2]), Value::Index(2)],
        Some("refused:vector-index"),
    );
    compare(
        "vector.slice",
        "bn254.fr",
        &[],
        vec![vector(&[1, 2, 3, 4]), Value::Index(1), Value::Index(2)],
    );
    compare(
        "vector.length_check",
        "bn254.fr",
        &["4"],
        vec![vector(&[1, 2, 3, 4])],
    );
    compare(
        "vector.splat",
        "bn254.fr",
        &["5"],
        vec![Value::Bn254Field(Scalar::from(3))],
    );
}

#[test]
fn resident_g1_g2_and_pairing_closure_matches_arkworks() {
    for g2 in [false, true] {
        let domain = if g2 { "bn254.g2" } else { "bn254.g1" };
        let point = |n| {
            if g2 {
                Value::Bn254G2(Bn254G2::generator().scale(Scalar::from(n)))
            } else {
                Value::Bn254G1(G1::generator().scale(Scalar::from(n)))
            }
        };
        let points = |n| {
            if g2 {
                Value::Bn254G2Vector(
                    (0..n)
                        .map(|v| Bn254G2::generator().scale(Scalar::from(v)))
                        .collect::<Vec<_>>()
                        .into(),
                )
            } else {
                Value::Bn254G1Vector(
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
                vec![points(n), Value::Bn254Field(Scalar::from(3))],
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
            vec![point(7), Value::Bn254Field(Scalar::from(0))],
        );
        compare("curve.at", domain, &["1"], vec![points(3)]);
        compare("curve.get", domain, &[], vec![points(3), Value::Index(2)]);
        compare("curve.split", domain, &[], vec![points(4)]);
    }
    for n in [0, 1, 2] {
        compare(
            "pairing.check",
            "bn254.fr",
            &[],
            vec![
                Value::Bn254G1Vector(vec![G1::identity(); n].into()),
                Value::Bn254G2Vector(vec![Bn254G2::generator(); n].into()),
            ],
        );
    }
    compare(
        "pairing.check",
        "bn254.fr",
        &[],
        vec![
            Value::Bn254G1Vector(vec![G1::generator(), G1::generator().neg()].into()),
            Value::Bn254G2Vector(vec![Bn254G2::generator(); 2].into()),
        ],
    );
}

#[test]
fn selected_codecs_match_canonical_language_and_reject_invalid_encodings() {
    let backend = backend(Policy::default(), cpu_contracts());
    for value in [
        Value::Bn254Field(Scalar::from(0)),
        Value::Bn254Field(Scalar::from(9)),
        Value::Bn254G1(G1::identity()),
        Value::Bn254G1(G1::generator()),
        Value::Bn254G2(Bn254G2::identity()),
        Value::Bn254G2(Bn254G2::generator()),
        vector(&[]),
        vector(&[0, 1, 7]),
        Value::Bn254G1Vector(vec![G1::identity(), G1::generator()].into()),
        Value::Bn254G2Vector(vec![Bn254G2::generator()].into()),
    ] {
        let bytes = backend.encode_native_value(&value).unwrap();
        let selected = resident(&backend, &value);
        assert_eq!(backend.encode_native_value(&selected).unwrap(), bytes);
        let ty = selected.physical_type();
        assert!(zkc_cpu::has_native_wire(&ty));
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
    for (kind, identity, width, tag) in [
        (Type::Field, Identity::Bn254Fr, 32, 40),
        (Type::Group, Identity::Bn254G1, 32, 46),
        (Type::Group, Identity::Bn254G2, 64, 48),
    ] {
        let ty = physical(kind, identity);
        let mut bytes = vec![0xff; width + 6];
        bytes[..5].copy_from_slice(b"ZKCV\0");
        bytes[5] = tag;
        assert!(matches!(
            backend.decode_native_value(&ty, &bytes),
            Err(NativeWireError::Invalid(_))
        ));
    }
}

#[test]
fn variable_time_permission_is_explicit_and_no_ark_fallback_is_installed() {
    let b = binding("curve.msm", "bn254.g1", true);
    assert!(cpu_contracts().resolve(b.clone()).is_err());
    assert!(
        backend(Policy::default(), cpu_contracts())
            .prepare_binding(&b)
            .is_none()
    );
    let allowed = cpu_contracts_with_policy(ExecutionPolicy {
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
        binding("pairing.apply", "bn254.fr", true),
        binding("curve.scale", "bn254.gt", true),
        binding("poly.from_coefficients", "bn254.fr", true),
        OperationBinding {
            implementation: "halo2curves-axiom/curve.scale".into(),
            ..binding("curve.scale", "bn254.g1", true)
        },
    ] {
        assert!(backend.prepare_binding(&b).is_none());
    }
    // A resident exact signature refuses Ark inputs at entry, before any call.
    let binding = binding("curve.scale", "bn254.g1", true);
    let program = Program::decode(&program(&backend, &binding, &[], 1), &allowed).unwrap();
    assert!(
        Runner::new(
            &program,
            "main",
            "P",
            "session",
            backend,
            vec![
                Value::Bn254G1(G1::generator()),
                Value::Bn254Field(Scalar::from(1))
            ]
        )
        .is_err()
    );
}

#[test]
fn retained_bulk_clones_are_shared_bounded_and_cold_warm_results_agree() {
    assert!(std::mem::size_of::<Value>() <= 512);
    let b = backend(Policy::default(), cpu_contracts());
    let values = resident(&b, &vector(&[1, 2, 3, 4]));
    let alias = values.clone();
    let (Value::HaloVector(a), Value::HaloVector(bulk)) = (&values, &alias) else {
        panic!()
    };
    assert!(Arc::ptr_eq(a, bulk));
    assert_eq!(values.retained_bytes(), 256 + a.storage_bytes());
    let op = binding("vector.scale", "bn254.fr", true);
    let args = vec![values, Value::HaloField(kernel::Scalar::from(7))];
    let cold = run(
        backend(Policy::default(), cpu_contracts()),
        &op,
        &[],
        args.clone(),
        1,
    )
    .0
    .unwrap();
    let warm = run(
        backend(Policy::default(), cpu_contracts()),
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
                backend(limited, cpu_contracts()),
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
    let b = backend(Policy::default(), cpu_contracts());
    for value in [
        Value::Bn254Field(Scalar::from(19)),
        vector(&[0, 1, 19]),
        Value::Bn254G1(G1::generator()),
        Value::Bn254G1Vector(vec![G1::identity(), G1::generator()].into()),
        Value::Bn254G2(Bn254G2::generator()),
        Value::Bn254G2Vector(vec![Bn254G2::generator()].into()),
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
            backend(Policy::default(), cpu_contracts()),
            &convert(&source, &target),
            &[],
            vec![value.clone()],
            1,
        )
        .0
        .unwrap()
        .remove(0);
        assert_eq!(output.physical_type(), target);
        for (declaration, input, importing) in [
            (convert(&source, &target), value.clone(), true),
            (convert(&target, &source), output.clone(), false),
        ] {
            let payload = match &input {
                Value::Bn254Vector(v) => Some(v.len() * 32),
                Value::HaloVector(v) => Some(v.len() * 32),
                Value::Bn254G1Vector(v) => Some(v.len() * std::mem::size_of::<kernel::G1>()),
                Value::HaloG1Vector(v) => Some(v.len() * std::mem::size_of::<G1>()),
                Value::Bn254G2Vector(v) => Some(v.len() * std::mem::size_of::<kernel::G2>()),
                Value::HaloG2Vector(v) => Some(v.len() * std::mem::size_of::<Bn254G2>()),
                _ => None,
            };
            let scalar_bytes = match (&input, importing) {
                (Value::Bls12381G2(_) | Value::Bn254G2(_), true) => 512,
                (Value::BlstG2(_) | Value::HaloG2(_), true) => unreachable!(),
                _ => zkc_cpu::VALUE_SLOT_BYTES,
            };
            let retained = payload.map_or(scalar_bytes, |bytes| bytes + 256);
            let memory = if !importing && payload.is_some() {
                2 * retained
            } else {
                retained
            };
            for (limit, available, error) in [
                (memory, retained, None),
                (memory - 1, retained, Some("exhausted:numerical-bytes")),
                (0, retained - 1, Some("exhausted:output-bytes")),
            ] {
                let native = backend(
                    Policy {
                        max_numerical_bytes: limit,
                        ..Policy::default()
                    },
                    cpu_contracts(),
                );
                let carrier = program(&native, &declaration, &[], 1);
                let mut driver = support::Controlled::new(native);
                driver.output_limit = Some(available);
                let (result, driver) = support::run_program(driver, &carrier, vec![input.clone()]);
                if let Some(error) = error {
                    assert_eq!(result.unwrap_err(), error);
                    assert!(driver.outputs.is_empty());
                } else {
                    let result = result.unwrap();
                    assert_eq!(
                        b.encode_native_value(&result[0]).unwrap(),
                        b.encode_native_value(&value).unwrap()
                    );
                }
                assert_eq!(driver.inner.active_frames(), 0);
            }
        }
        let recovered = run(
            backend(Policy::default(), cpu_contracts()),
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
fn repeated_resident_msm_does_not_reconstruct_adapter_owned_bulk_buffers() {
    let contracts = cpu_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    let encoder = backend(Policy::default(), &contracts);
    for (domain, ark_points) in [
        (
            "bn254.g1",
            Value::Bn254G1Vector(vec![G1::generator(); 8].into()),
        ),
        (
            "bn254.g2",
            Value::Bn254G2Vector(vec![Bn254G2::generator(); 8].into()),
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
    let op = binding("field.constant", "bn254.fr", true);
    for repeats in [1, 3] {
        let (result, _) = run(
            backend(Policy::default(), &contracts),
            &op,
            &["123456789"],
            vec![],
            repeats,
        );
        assert!(matches!(&result.unwrap()[0], Value::HaloField(_)));
    }
}

#[test]
fn granting_g1_msm_does_not_grant_g2_or_weaken_operand_premises() {
    use zkc_runtime::vm::{ImplementationRequirements, TimingRequirement};
    let g1 = binding("curve.msm", "bn254.g1", true);
    let g2 = binding("curve.msm", "bn254.g2", true);
    let requirements = ImplementationRequirements {
        timing: TimingRequirement::VariableTime,
        timing_operands: &[0, 1],
    };
    let contracts = cpu_contracts()
        .with_timing_grant(g1.clone(), requirements)
        .unwrap();
    assert_eq!(
        contracts.resolve(g1.clone()).unwrap().requirements(),
        requirements
    );
    assert!(contracts.resolve(g2.clone()).is_err());
    assert!(cpu_contracts().resolve(g1.clone()).is_err());
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
        Value::HaloVector(Arc::new(
            kernel::ScalarVector::from_elements(vec![]).unwrap(),
        )),
        Value::HaloG1Vector(Arc::new(kernel::G1Vector::from_elements(vec![]).unwrap())),
    ];
    let (result, _) = run(backend, &g1, &[], args, 1);
    assert!(
        matches!(result.unwrap().as_slice(), [Value::HaloG1(point)] if *point == kernel::G1::identity())
    );
}

#[test]
fn retained_handles_recheck_revoked_policy_and_exact_grants_before_work() {
    use zkc_cpu::{CpuCall, CpuOperation};
    use zkc_runtime::vm::{
        BackendError, Frame, FrameExit, ImplementationRequirements, Invocation, TimingRequirement,
    };
    struct Revoked {
        inner: Option<CpuBackend>,
        revoke: bool,
        prepared: bool,
    }
    impl Backend for Revoked {
        type Value = Value;
        type Operation = CpuOperation;
        type Call = CpuCall;
        type Checkpoint = zkc_cpu::ComputationCheckpoint;
        fn computation_checkpoint(&self) -> Option<Self::Checkpoint> {
            self.inner.as_ref().unwrap().computation_checkpoint()
        }
        fn replay_computation(
            &mut self,
            before: Self::Checkpoint,
            after: Self::Checkpoint,
        ) -> bool {
            self.inner
                .as_mut()
                .unwrap()
                .replay_computation(before, after)
        }
        fn prepare_binding(&self, binding: &OperationBinding) -> Option<CpuOperation> {
            self.inner.as_ref().unwrap().prepare_binding(binding)
        }
        fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
            self.inner.as_ref().unwrap().validate_value(value)
        }
        fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
            if self.revoke {
                self.inner = Some(
                    self.inner
                        .take()
                        .unwrap()
                        .with_contracts(cpu_contracts().clone())?,
                );
                self.revoke = false;
            }
            self.inner.as_mut().unwrap().enter_frame(frame, args)
        }
        fn leave_frame(
            &mut self,
            frame: &Frame,
            exit: FrameExit,
            outputs: &[Value],
        ) -> Result<(), BackendError> {
            self.inner
                .as_mut()
                .unwrap()
                .leave_frame(frame, exit, outputs)
        }
        fn apply(
            &mut self,
            operation: &CpuOperation,
            i: &Invocation<'_>,
            args: &[Value],
        ) -> Result<Vec<Value>, BackendError> {
            let inner = self.inner.as_mut().unwrap();
            inner.apply(operation, i, args)
        }
        fn apply_prepared(
            &mut self,
            operation: &CpuOperation,
            call: &mut Option<CpuCall>,
            i: &Invocation<'_>,
            args: &[Value],
        ) -> Result<Vec<Value>, BackendError> {
            if !self.prepared {
                return self.apply(operation, i, args);
            }
            let inner = self.inner.as_mut().unwrap();
            inner.apply_prepared(operation, call, i, args)
        }
    }
    let binding = binding("curve.msm", "bn254.g1", true);
    let grant = cpu_contracts()
        .with_timing_grant(
            binding.clone(),
            ImplementationRequirements {
                timing: TimingRequirement::VariableTime,
                timing_operands: &[0, 1],
            },
        )
        .unwrap();
    for contracts in [
        cpu_contracts_with_policy(ExecutionPolicy::general_purpose()),
        grant,
    ] {
        let native = backend(Policy::default(), &contracts);
        let group = physical(Type::Group, Identity::Bn254G1).spelling();
        let carrier = serde_json::to_vec(&json!([
            "zkc.program/0",
            [
                [
                    "scalars",
                    "vector.constant",
                    ["bn254.fr"],
                    "halo2curves-axiom/resident/vector.constant",
                    []
                ],
                [
                    "points",
                    "curve.empty",
                    ["bn254.g1"],
                    "halo2curves-axiom/resident/curve.empty",
                    []
                ],
                [
                    "msm",
                    "curve.msm",
                    ["bn254.g1"],
                    "halo2curves-axiom/resident/curve.msm",
                    []
                ]
            ],
            [[
                "function",
                "f",
                [],
                [group],
                [
                    ["op", "scalars", "scalars", [], [], ["xs"]],
                    ["op", "points", "points", [], [], ["points"]],
                    ["op", "msm", "msm", [], ["xs", "points"], ["out"]],
                    ["return", ["out"]]
                ],
                ["f", []]
            ]],
            [[
                "participant",
                "actor",
                "instance",
                "P",
                [],
                [group],
                [
                    ["local", "work", "f", [], ["result"]],
                    ["return", ["result"]]
                ],
                []
            ]],
            [["entry", "main", [["P", "actor"]]]]
        ]))
        .unwrap();
        let admitted = Program::decode(&carrier, &contracts).unwrap();
        admitted.check_installation(&native).unwrap();
        let cache = zkc_runtime::vm::PreparedComputations::new(
            &admitted,
            zkc_runtime::vm::PreparationLimits::default(),
        );
        for revoke in [false, false, true] {
            let caller = Revoked {
                inner: Some(backend(Policy::default(), &contracts)),
                revoke,
                prepared: true,
            };
            let mut runner = Runner::new(&admitted, "main", "P", "session", caller, vec![])
                .unwrap_or_else(|e| panic!("{}", e.error));
            runner.prepare_computations(cache.clone(), &[]).unwrap();
            loop {
                match runner.poll() {
                    Action::Local(action) => {
                        runner.execute_local(&action.cut).unwrap();
                    }
                    Action::Returned(_) => {
                        assert!(!revoke);
                        break;
                    }
                    Action::Stopped(stop) => {
                        assert!(revoke);
                        assert!(matches!(stop.kind, StopKind::Backend(ref error)
                            if error.code == "refused:implementation-permission"));
                        break;
                    }
                    other => panic!("unexpected action: {other:?}"),
                }
            }
            assert_eq!(runner.backend().inner.as_ref().unwrap().active_frames(), 0);
        }
        assert_eq!(cache.stats().entries, 1);
        assert_eq!(cache.stats().hits, 1);
        for prepared in [false, true] {
            let native = backend(
                Policy {
                    max_numerical_work: 0,
                    ..Policy::default()
                },
                &contracts,
            );
            let carrier = program(&native, &binding, &[], 1);
            let admitted = Program::decode(&carrier, &contracts).unwrap();
            let caller = Revoked {
                inner: Some(native),
                revoke: true,
                prepared,
            };
            let args = vec![
                Value::HaloVector(Arc::new(
                    kernel::ScalarVector::from_elements(vec![]).unwrap(),
                )),
                Value::HaloG1Vector(Arc::new(kernel::G1Vector::from_elements(vec![]).unwrap())),
            ];
            let mut runner = Runner::new(&admitted, "main", "P", "session", caller, args)
                .unwrap_or_else(|e| panic!("{}", e.error));
            loop {
                match runner.poll() {
                    Action::Local(action) => {
                        runner.execute_local(&action.cut).unwrap();
                    }
                    Action::Stopped(stop) => {
                        assert!(
                            matches!(stop.kind, StopKind::Backend(ref error) if error.code == "refused:implementation-permission")
                        );
                        break;
                    }
                    other => panic!("unexpected action: {other:?}"),
                }
            }
            assert_eq!(runner.backend().inner.as_ref().unwrap().active_frames(), 0);
        }
    }
}

#[test]
fn empty_zero_and_mismatched_bulk_shapes_remain_exact() {
    for domain in ["bn254.g1", "bn254.g2"] {
        let points = if domain.ends_with("g1") {
            Value::Bn254G1Vector(vec![G1::generator(); 3].into())
        } else {
            Value::Bn254G2Vector(vec![Bn254G2::generator(); 3].into())
        };
        compare(
            "curve.msm",
            domain,
            &[],
            vec![vector(&[0, 0, 0]), points.clone()],
        );
        for name in ["curve.msm", "curve.scale_each"] {
            compare_expected(
                name,
                domain,
                &[],
                vec![vector(&[1, 2]), points.clone()],
                Some("refused:length-mismatch"),
            );
        }
    }
    compare_expected(
        "pairing.check",
        "bn254.fr",
        &[],
        vec![
            Value::Bn254G1Vector(vec![G1::generator()].into()),
            Value::Bn254G2Vector(vec![].into()),
        ],
        Some("refused:length-mismatch"),
    );
    compare(
        "pairing.check",
        "bn254.fr",
        &[],
        vec![
            Value::Bn254G1Vector(vec![G1::generator()].into()),
            Value::Bn254G2Vector(vec![Bn254G2::generator()].into()),
        ],
    );
}

#[test]
fn canonical_readable_ingress_and_capacity_preflight_choose_selected_carriers() {
    let b = backend(Policy::default(), cpu_contracts());
    for (kind, json, ordinary) in [
        (
            Type::Field,
            json!("19"),
            Value::Bn254Field(Scalar::from(19)),
        ),
        (Type::Vector, json!(["0", "1", "19"]), vector(&[0, 1, 19])),
    ] {
        let ty = physical(kind, Identity::Bn254Fr);
        let wire = zkc_cpu::readable_wire(&ty, &json, 1024).unwrap();
        assert_eq!(wire, b.encode_native_value(&ordinary).unwrap());
        let value = b.decode_native_value(&ty, &wire).unwrap();
        assert_eq!(value.physical_type(), ty);
        assert!(value.preparation_output());
    }
    for ordinary in [
        Value::Bn254Field(Scalar::from(19)),
        vector(&[0, 1, 19]),
        Value::Bn254G1(G1::generator()),
        Value::Bn254G2(Bn254G2::generator()),
        Value::Bn254G1Vector(vec![G1::identity(), G1::generator()].into()),
        Value::Bn254G2Vector(vec![Bn254G2::identity(), Bn254G2::generator()].into()),
    ] {
        let selected = resident(&b, &ordinary);
        let canonical = serde_json::to_value(b.encode_readable_value(&ordinary).unwrap()).unwrap();
        let readable = serde_json::to_value(b.encode_readable_value(&selected).unwrap()).unwrap();
        assert_eq!(canonical, readable);
        let bytes = b.encode_native_value(&ordinary).unwrap();
        assert_eq!(
            zkc_cpu::readable_wire(&selected.physical_type(), &readable, bytes.len()).unwrap(),
            bytes
        );
        assert!(
            zkc_cpu::readable_wire(&selected.physical_type(), &readable, bytes.len() - 1).is_err()
        );
    }
    let mut elements = Vec::with_capacity(32);
    elements.push(kernel::Scalar::ONE.into_element());
    let bulk = kernel::ScalarVector::from_elements(elements).unwrap();
    let capacity = bulk.storage_bytes();
    let value = Value::HaloVector(Arc::new(bulk));
    assert_eq!(value.retained_bytes(), 256 + capacity);
    assert!(b.validate_value(&value).is_ok());
    let limited = backend(
        Policy {
            max_value_bytes: 256 + capacity - 1,
            ..Policy::default()
        },
        cpu_contracts(),
    );
    assert!(limited.validate_value(&value).is_err());
}

#[test]
fn noncanonical_scalar_payloads_refuse_at_every_bulk_position() {
    use ark_ff::{BigInteger, PrimeField};
    let b = backend(Policy::default(), cpu_contracts());
    let modulus = Scalar::MODULUS.to_bytes_le();
    for value in [Value::Bn254Field(Scalar::from(1)), vector(&[1, 2, 3])] {
        let ty = physical(value.ty(), Identity::Bn254Fr);
        let original = b.encode_native_value(&value).unwrap();
        for index in 0..if value.ty() == Type::Vector { 3 } else { 1 } {
            let mut bytes = original.clone();
            let start = if value.ty() == Type::Vector { 10 } else { 6 } + 32 * index;
            bytes[start..start + 32].copy_from_slice(&modulus);
            assert!(matches!(
                b.decode_native_value(&ty, &bytes),
                Err(NativeWireError::Invalid(_))
            ));
        }
    }
}

#[test]
fn expected_and_actual_inventories_agree_on_exact_operations_and_ports() {
    use zkc_runtime::vm::{ImplementationRequirements, TimingRequirement};
    // This expected list is independent of both production inventories.
    let expected = [
        "field.constant",
        "field.from_index",
        "field.add",
        "field.sub",
        "field.neg",
        "field.mul",
        "field.inverse",
        "field.equal",
        "vector.empty",
        "vector.constant",
        "vector.splat",
        "vector.append",
        "vector.at",
        "vector.get",
        "vector.length",
        "vector.length_check",
        "vector.add",
        "vector.sub",
        "vector.mul",
        "vector.dot",
        "vector.scale",
        "vector.sum",
        "vector.product",
        "vector.split",
        "vector.concat",
        "vector.slice",
        "vector.equal",
        "curve.generator",
        "curve.identity",
        "curve.add",
        "curve.neg",
        "curve.equal",
        "curve.nonidentity",
        "curve.scale",
        "curve.empty",
        "curve.append",
        "curve.at",
        "curve.get",
        "curve.length",
        "curve.vector_add",
        "curve.scale_each",
        "curve.vector_scale",
        "curve.split",
        "curve.concat",
        "curve.msm",
        "pairing.check",
    ];
    let contracts = cpu_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    let native = backend(Policy::default(), &contracts);
    let mut names: Vec<_> = expected
        .iter()
        .map(|name| (format!("halo2curves-axiom/resident/{name}"), *name))
        .collect();
    names.sort();
    for inventory in [
        contracts.installed_implementations(),
        native.installed_implementations(),
    ] {
        let mut halo: Vec<_> = inventory
            .into_iter()
            .filter(|(implementation, _)| implementation.starts_with("halo2curves-axiom/"))
            .collect();
        halo.sort();
        assert_eq!(halo, names);
    }
    for name in expected {
        let domains: &[&str] = if name.starts_with("curve.") {
            &["bn254.g1", "bn254.g2"]
        } else {
            &["bn254.fr"]
        };
        for domain in domains {
            let declaration = binding(name, domain, true);
            let expected = contracts.resolve(declaration.clone()).unwrap();
            let actual = native.prepare_binding(&declaration).unwrap();
            assert_eq!(expected.signature(), actual.signature());
            assert_eq!(expected.requirements(), actual.requirements());
            if name == "curve.msm" {
                assert_eq!(
                    actual.requirements(),
                    ImplementationRequirements {
                        timing: TimingRequirement::VariableTime,
                        timing_operands: &[0, 1],
                    }
                );
            }
            for port in actual
                .signature()
                .inputs
                .iter()
                .chain(&actual.signature().outputs)
            {
                if !matches!(port.kind(), Type::Index | Type::Indices | Type::Bool) {
                    assert_eq!(*port, physical(port.kind(), port.logical().identity()));
                }
            }
            let wrong = match *domain {
                "bn254.g1" => "bls12-381.g1",
                "bn254.g2" => "bls12-381.g2",
                _ => "bls12-381.fr",
            };
            assert!(contracts.resolve(binding(name, wrong, true)).is_err());
            assert!(
                native
                    .prepare_binding(&binding(name, wrong, true))
                    .is_none()
            );
            let mut extra = declaration;
            extra
                .physical_arguments
                .push("halo2curves-axiom/bn254.fr".into());
            assert!(contracts.resolve(extra.clone()).is_err());
            assert!(native.prepare_binding(&extra).is_none());
        }
    }
    for name in [
        "pairing.apply",
        "pcs.commit",
        "poly.fft",
        "matrix.mul_vector",
        "field_array.from_vector",
        "fixed_vector.from_vector",
        "vector.powers",
    ] {
        let declaration = binding(name, "bn254.fr", true);
        assert!(contracts.resolve(declaration.clone()).is_err());
        assert!(native.prepare_binding(&declaration).is_none());
    }
}

#[test]
fn kernel_work_workspace_and_output_boundaries_refuse_before_execution() {
    let contracts = cpu_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    let encoder = backend(Policy::default(), &contracts);
    for (name, domain, ordinary) in [
        (
            "curve.msm",
            "bn254.g1",
            vec![
                vector(&[1, 2]),
                Value::Bn254G1Vector(vec![G1::generator(); 2].into()),
            ],
        ),
        (
            "curve.msm",
            "bn254.g2",
            vec![
                vector(&[1, 2]),
                Value::Bn254G2Vector(vec![Bn254G2::generator(); 2].into()),
            ],
        ),
        (
            "pairing.check",
            "bn254.fr",
            vec![
                Value::Bn254G1Vector(vec![G1::generator(), G1::generator().neg()].into()),
                Value::Bn254G2Vector(vec![Bn254G2::generator(); 2].into()),
            ],
        ),
    ] {
        let args: Vec<_> = ordinary.iter().map(|v| resident(&encoder, v)).collect();
        let original: Vec<_> = args
            .iter()
            .map(|v| encoder.encode_native_value(v).unwrap())
            .collect();
        let (work, scratch) = if name == "curve.msm" {
            (
                kernel::msm_work(2).unwrap(),
                kernel::msm_workspace_bytes(2).unwrap(),
            )
        } else {
            (
                kernel::pairing_work(2).unwrap(),
                kernel::pairing_workspace_bytes(2).unwrap(),
            )
        };
        let output = if domain == "bn254.g2" {
            512
        } else {
            zkc_cpu::VALUE_SLOT_BYTES
        };
        let memory = output + scratch;
        let declaration = binding(name, domain, true);
        for (work_limit, memory_limit, output_limit, error) in [
            (work, memory, output, None),
            (work - 1, memory, output, Some("exhausted:numerical-work")),
            (work, memory - 1, output, Some("exhausted:numerical-bytes")),
            (work, memory, output - 1, Some("exhausted:output-bytes")),
        ] {
            let native = backend(
                Policy {
                    max_numerical_work: work_limit,
                    max_numerical_bytes: memory_limit,
                    ..Policy::default()
                },
                &contracts,
            );
            let carrier = program(&native, &declaration, &[], 1);
            let mut driver = support::Controlled::new(native);
            driver.output_limit = Some(output_limit);
            // Refusal must not reach any fallible kernel staging allocation.
            let guard = error.map(|_| zkc_kernels::allocation::failure::after(0));
            let (result, driver) =
                support::run_program_with_contracts(driver, &carrier, args.clone(), &contracts);
            if let Some(error) = error {
                assert_eq!(result.unwrap_err(), error, "{name}/{domain}");
                assert!(driver.outputs.is_empty());
                assert!(kernel::ScalarVector::filled(1, kernel::Scalar::ONE).is_err());
            } else {
                let expected = run(
                    backend(Policy::default(), &contracts),
                    &binding(name, domain, false),
                    &[],
                    ordinary.clone(),
                    1,
                )
                .0
                .unwrap();
                let actual = result.unwrap();
                assert_eq!(
                    encoder.encode_native_value(&actual[0]).unwrap(),
                    encoder.encode_native_value(&expected[0]).unwrap()
                );
            }
            drop(guard);
            assert_eq!(driver.inner.active_frames(), 0);
            for (value, bytes) in args.iter().zip(&original) {
                assert_eq!(encoder.encode_native_value(value).unwrap(), *bytes);
            }
        }
    }
}

#[test]
fn noncanonical_infinity_aliases_refuse_for_scalar_and_bulk_groups() {
    let native = backend(Policy::default(), cpu_contracts());
    for ordinary in [
        Value::Bn254G1(G1::identity()),
        Value::Bn254G2(Bn254G2::identity()),
        Value::Bn254G1Vector(vec![G1::identity()].into()),
        Value::Bn254G2Vector(vec![Bn254G2::identity()].into()),
    ] {
        let ty = physical(ordinary.ty(), ordinary.physical_type().logical().identity());
        let bytes = native.encode_native_value(&ordinary).unwrap();
        for signed in [false, true] {
            let mut alias = bytes.clone();
            if signed {
                *alias.last_mut().unwrap() |= 0x80;
            } else {
                alias[if ordinary.ty() == Type::Groups { 10 } else { 6 }] = 1;
            }
            assert!(matches!(
                native.decode_native_value(&ty, &alias),
                Err(NativeWireError::Invalid(_))
            ));
        }
    }
}
