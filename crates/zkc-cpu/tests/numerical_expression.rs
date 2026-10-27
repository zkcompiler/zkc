//! Numerical expression calls through independent admission and reached native
//! invocation, including immutable preparation and per-call resource boundaries.
#[path = "domains/support.rs"]
mod support;

use p3_field::BasedVectorSpace;
use serde_json::{Value as Json, json};
use std::{
    fmt::Debug,
    mem::size_of,
    ops::{Add, Mul, Neg},
};
use support::{Controlled, assert_value, backend, one};
use zkc_cpu::{
    Bn254Scalar, CpuBackend, CpuCall, CpuOperation, KoalaBear, KoalaBearExt4, KoalaBearExt8,
    Policy, RistrettoScalar, Scalar, Value, domains,
};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Backend, BackendError, Frame, FrameExit, Identity, InstalledOperation, Invocation,
    OperationBinding, PreparationLimits, PreparedComputations, Program,
};

fn binding(domain: domains::NativeDomain, mode: &str, mask: &str) -> OperationBinding {
    OperationBinding {
        contract: format!("numerical.{mode}"),
        arguments: vec![domain.field.name().into(), mask.into()],
        implementation: format!("{}/numerical.{mode}", domain.provider),
        physical_arguments: vec![],
    }
}

fn body(field: Identity, inputs: usize, nodes: Json, output: usize) -> String {
    json!(["zkc.ring/0", vec![field.name(); inputs], nodes, [output]]).to_string()
}

fn shared_capture_body(field: Identity) -> String {
    // Interleave varying nodes with a shared invariant k = -(capture*capture+1).
    body(
        field,
        3,
        json!([
            ["input", 0],
            ["input", 1],
            ["input", 2],
            ["constant", field.name(), "1"],
            ["mul", 0, 0],
            ["mul", 1, 1],
            ["add", 5, 3],
            ["neg", 6],
            ["add", 7, 4],
            ["add", 2, 7],
            ["neg", 9],
            ["mul", 8, 10]
        ]),
        11,
    )
}

fn constant_body_with_bytes(bytes: usize) -> (String, Scalar) {
    // Use the runtime admission fixture's connected negation chain and vary a
    // canonical decimal literal to reach the exact byte length without padding.
    for count in 1..400 {
        let mut nodes = vec![json!(["constant", "bls12-381.fr", "1"])];
        nodes.extend((0..count).map(|i| json!(["neg", i])));
        let mut expression = json!(["zkc.ring/0", [], nodes, [count]]);
        let length = expression.to_string().len();
        if let Some(extra) = bytes.checked_sub(length).filter(|n| *n < 69) {
            let literal = "1".repeat(1 + extra);
            let value = literal.bytes().fold(Scalar::from(0), |value, _| {
                value * Scalar::from(10) + Scalar::from(1)
            });
            expression[2][0][2] = json!(literal);
            return (
                expression.to_string(),
                if count % 2 == 0 { value } else { -value },
            );
        }
    }
    panic!("missing canonical body byte-boundary fixture");
}

fn exercise<F>(
    domain: domains::NativeDomain,
    samples: [F; 4],
    zero: F,
    identity: F,
    field: fn(F) -> Value,
    vector: fn(Vec<F>) -> Value,
) where
    F: Copy + Debug + PartialEq + Add<Output = F> + Mul<Output = F> + Neg<Output = F>,
{
    // Independent scalar formula: (x*x + k) * -(aliased_x + k).
    let expression = shared_capture_body(domain.field);
    let invariant = -(samples[3] * samples[3] + identity);
    for rows in [
        0usize, 1, 3, 17, 31, 32, 33, 127, 128, 129, 255, 256, 257, 1025,
    ] {
        let values: Vec<_> = (0..rows).map(|i| samples[i % samples.len()]).collect();
        let input = vector(values.clone());
        let terms: Vec<_> = values
            .iter()
            .map(|x| (*x * *x + invariant) * -(*x + invariant))
            .collect();
        for mode in ["map", "sum", "product"] {
            let expected = match mode {
                "map" => vector(terms.clone()),
                "sum" => field(terms.iter().fold(zero, |acc, x| acc + *x)),
                "product" => field(terms.iter().fold(identity, |acc, x| acc * *x)),
                _ => unreachable!(),
            };
            let (result, native) = one(
                backend(Policy::default()).with_ring_work_limit(0),
                binding(domain, mode, "101"),
                &[&expression],
                vec![
                    Value::Index(rows as u64),
                    input.clone(),
                    field(samples[3]),
                    input.clone(),
                ],
            );
            let result = result.unwrap();
            assert_eq!(result.len(), 1);
            assert_value(&result[0], &expected);
            assert_eq!(native.ring_work_spent(), 0);
            assert_eq!(native.active_frames(), 0);
            assert_value(&input, &vector(values.clone()));
        }
        // A later ordinary kernel reads the same published aliases.
        let add = OperationBinding {
            contract: "vector.add".into(),
            arguments: vec![domain.field.name().into()],
            implementation: format!("{}/vector.add", domain.provider),
            physical_arguments: vec![],
        };
        let output = one(
            backend(Policy::default()),
            add,
            &[],
            vec![input.clone(), input.clone()],
        )
        .0
        .unwrap();
        assert_value(
            &output[0],
            &vector(values.iter().map(|x| *x + *x).collect()),
        );
        assert_value(&input, &vector(values));
    }

    // Dense kernels and expression nodes share destination arithmetic. Check
    // their public boundaries with full extension coordinates and scalar tails.
    for rows in [0, 1, 7, 8, 15, 16, 17, 257] {
        let a: Vec<_> = (0..rows).map(|i| samples[i % 4]).collect();
        let b: Vec<_> = (0..rows).map(|i| samples[(i + 1) % 4]).collect();
        for operation in ["sub", "mul", "scale"] {
            let expected: Vec<_> = a
                .iter()
                .zip(&b)
                .map(|(a, b)| match operation {
                    "sub" => *a + -*b,
                    "mul" => *a * *b,
                    _ => *a * samples[2],
                })
                .collect();
            let args = if operation == "scale" {
                vec![vector(a.clone()), field(samples[2])]
            } else {
                vec![vector(a.clone()), vector(b.clone())]
            };
            let binding = OperationBinding {
                contract: format!("vector.{operation}"),
                arguments: vec![domain.field.name().into()],
                implementation: format!("{}/vector.{operation}", domain.provider),
                physical_arguments: vec![],
            };
            let result = one(backend(Policy::default()), binding, &[], args)
                .0
                .unwrap();
            assert_value(&result[0], &vector(expected));
        }
    }

    // Empty mask, capture-only body, and two leading scalar bits are distinct
    // signatures. Neither constants nor captures require broadcast vectors.
    for mask in ["", "0", "001"] {
        let nodes = if mask.is_empty() {
            json!([["constant", domain.field.name(), "1"]])
        } else {
            json!([["input", 0]])
        };
        let expression = body(domain.field, mask.len(), nodes, 0);
        for rows in [0, 3] {
            let term = if mask.is_empty() {
                identity
            } else {
                samples[2]
            };
            let mut args = vec![Value::Index(rows)];
            for bit in mask.bytes() {
                args.push(if bit == b'0' {
                    field(samples[2])
                } else {
                    vector(vec![samples[0]; rows as usize])
                });
            }
            for mode in ["map", "sum", "product"] {
                let expected = match mode {
                    "map" => vector(vec![term; rows as usize]),
                    "sum" => field((0..rows).fold(zero, |acc, _| acc + term)),
                    _ => field((0..rows).fold(identity, |acc, _| acc * term)),
                };
                let output = one(
                    backend(Policy::default()),
                    binding(domain, mode, mask),
                    &[&expression],
                    args.clone(),
                )
                .0
                .unwrap();
                assert_value(&output[0], &expected);
            }
        }
    }
}

#[test]
fn all_eight_fields_use_exact_arithmetic_and_immutable_inputs() {
    exercise(
        domains::BN254_G1,
        [2u64, 3, 5, 7].map(Bn254Scalar::from),
        Bn254Scalar::from(0),
        Bn254Scalar::from(1),
        Value::Bn254Field,
        |v| Value::Bn254Vector(v.into()),
    );
    exercise(
        domains::BLS,
        [2u64, 3, 5, 7].map(Scalar::from),
        Scalar::from(0),
        Scalar::from(1),
        Value::Field,
        |v| Value::Vector(v.into()),
    );
    exercise(
        domains::RISTRETTO,
        [2u64, 3, 5, 7].map(RistrettoScalar::from),
        RistrettoScalar::ZERO,
        RistrettoScalar::ONE,
        Value::RistrettoField,
        |v| Value::RistrettoVector(v.into()),
    );
    exercise(
        domains::KOALA_BEAR,
        [2, 3, 5, 7].map(KoalaBear::new),
        KoalaBear::new(0),
        KoalaBear::new(1),
        Value::KoalaBearField,
        |v| Value::KoalaBearVector(v.into()),
    );
    exercise(
        domains::KOALA_BEAR_EXT4,
        [2, 3, 5, 7].map(|s| {
            KoalaBearExt4::from_basis_coefficients_fn(|i| KoalaBear::new(s + 11 * i as u32))
        }),
        KoalaBearExt4::from(KoalaBear::new(0)),
        KoalaBearExt4::from(KoalaBear::new(1)),
        Value::KoalaBearExt4Field,
        |v| Value::KoalaBearExt4Vector(v.into()),
    );
    exercise(
        domains::KOALA_BEAR_EXT8,
        [2, 3, 5, 7].map(|s| {
            KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(s + 11 * i as u32))
        }),
        KoalaBearExt8::from(KoalaBear::new(0)),
        KoalaBearExt8::from(KoalaBear::new(1)),
        Value::KoalaBearExt8Field,
        |v| Value::KoalaBearExt8Vector(v.into()),
    );
    use zkc_kernels::plonky3::binary::ext3_from_bits;
    use zkc_kernels::plonky3::binary::from_bits;
    exercise(
        domains::BINARY64,
        [2, 3, 0x8100_0000_0000_0005, 7].map(from_bits),
        from_bits(0),
        from_bits(1),
        Value::Binary64Field,
        |v| Value::Binary64Vector(v.into()),
    );
    exercise(
        domains::BINARY64_EXT3,
        [2, 3, 5, 7].map(|s| ext3_from_bits([s, s + 11, s + 17])),
        ext3_from_bits([0, 0, 0]),
        ext3_from_bits([1, 0, 0]),
        Value::Binary64Ext3Field,
        |v| Value::Binary64Ext3Vector(v.into()),
    );
}

#[test]
fn native_advertisements_close_fields_modes_masks_and_providers_independently() {
    let native = backend(Policy::default());
    for domain in [
        domains::BN254_G1,
        domains::BLS,
        domains::RISTRETTO,
        domains::KOALA_BEAR,
        domains::KOALA_BEAR_EXT4,
        domains::KOALA_BEAR_EXT8,
        domains::BINARY64,
        domains::BINARY64_EXT3,
    ] {
        for mode in ["map", "sum", "product"] {
            for mask in ["", "00101"] {
                let binding = binding(domain, mode, mask);
                let operation = native.prepare_binding(&binding).unwrap();
                assert_eq!(operation.signature(), &binding.signature().unwrap());
                assert!(operation.deterministic());
                for provider in ["arkworks", "dalek", "plonky3", "missing"] {
                    let wrong = OperationBinding {
                        implementation: format!("{provider}/numerical.{mode}"),
                        ..binding.clone()
                    };
                    assert_eq!(
                        native.prepare_binding(&wrong).is_some(),
                        provider == domain.provider
                    );
                }
                for arguments in [
                    vec![],
                    vec![domain.field.name().into()],
                    vec![domain.field.name().into(), "2".into()],
                    vec![domain.field.name().into(), "0".repeat(1024)],
                    vec!["bls12-381.g1".into(), "1".into()],
                    vec![domain.field.name().into(), "０".into()],
                ] {
                    assert!(
                        native
                            .prepare_binding(&OperationBinding {
                                arguments,
                                ..binding.clone()
                            })
                            .is_none()
                    );
                }
                let wrong_mode = OperationBinding {
                    implementation: format!(
                        "{}/numerical.{}",
                        domain.provider,
                        if mode == "map" { "sum" } else { "map" }
                    ),
                    ..binding
                };
                assert!(native.prepare_binding(&wrong_mode).is_none());
            }
        }
    }
}

/// Exercise the public direct/prepared backend boundary with altered facts after
/// program admission. The wrapper retains no resource authority of its own.
struct Caller {
    inner: CpuBackend,
    call: Option<CpuCall>,
    prepared: bool,
    attributes: Option<Vec<String>>,
    arguments: Option<Vec<Value>>,
    output_limit: Option<usize>,
    attempts: usize,
    outputs: Vec<Vec<Value>>,
}
impl Caller {
    fn new(policy: Policy, prepared: bool) -> Self {
        Self {
            inner: backend(policy),
            call: None,
            prepared,
            attributes: None,
            arguments: None,
            output_limit: None,
            attempts: 0,
            outputs: vec![],
        }
    }
}
impl Backend for Caller {
    type Call = ();
    type Checkpoint = ();
    type Value = Value;
    type Operation = CpuOperation;
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<Self::Operation> {
        self.inner.prepare_binding(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(frame, args)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[Value],
    ) -> Result<(), BackendError> {
        self.inner.leave_frame(frame, exit, outputs)
    }
    fn apply(
        &mut self,
        operation: &CpuOperation,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.attempts += 1;
        let numerical = i.binding.declaration().contract.starts_with("numerical.");
        let invocation = Invocation {
            context: zkc_runtime::vm::CallContext {
                attributes: if numerical {
                    self.attributes.as_deref().unwrap_or(i.attributes)
                } else {
                    i.attributes
                },
                ..i.context
            },
            max_output_bytes: self.output_limit.unwrap_or(i.max_output_bytes),
            ..*i
        };
        let args = if numerical {
            self.arguments.as_deref().unwrap_or(args)
        } else {
            args
        };
        let result = if self.prepared {
            self.inner
                .apply_prepared(operation, &mut self.call, &invocation, args)
        } else {
            self.inner.apply(operation, &invocation, args)
        };
        if let Ok(values) = &result {
            self.outputs.push(values.clone());
        }
        result
    }
}

#[test]
fn shared_invariants_use_current_captures_when_preparation_is_reused() {
    let expression = shared_capture_body(Identity::Bls12381Fr);
    for prepared in [false, true] {
        for mode in ["map", "sum", "product"] {
            // The same body can have mixed or entirely invariant dependencies.
            for mask in ["101", "000"] {
                let mut caller = Caller::new(Policy::default(), prepared);
                for (rows, capture) in [(3, 7u64), (3, 19), (0, 23), (1, 2), (5, 11)] {
                    let left: Vec<_> = (0..rows)
                        .map(|row| Scalar::from(if mask == "000" { 2 } else { row + 2 }))
                        .collect();
                    let right: Vec<_> = (0..rows)
                        .map(|row| Scalar::from(if mask == "000" { 5 } else { row + 5 }))
                        .collect();
                    let capture = Scalar::from(capture);
                    let invariant = -(capture * capture + Scalar::from(1));
                    let terms: Vec<_> = left
                        .iter()
                        .zip(&right)
                        .map(|(x, y)| (*x * *x + invariant) * -(*y + invariant))
                        .collect();
                    let expected = match mode {
                        "map" => Value::Vector(terms.clone().into()),
                        "sum" => Value::Field(terms.iter().copied().sum()),
                        _ => Value::Field(terms.iter().copied().product()),
                    };
                    let args = vec![
                        Value::Index(rows),
                        if mask == "000" {
                            Value::Field(Scalar::from(2))
                        } else {
                            Value::Vector(left.into())
                        },
                        Value::Field(capture),
                        if mask == "000" {
                            Value::Field(Scalar::from(5))
                        } else {
                            Value::Vector(right.into())
                        },
                    ];
                    caller.outputs.clear();
                    let (result, next) = one(
                        caller,
                        binding(domains::BLS, mode, mask),
                        &[&expression],
                        args,
                    );
                    assert_value(&result.unwrap()[0], &expected);
                    assert_eq!(next.outputs.len(), 1);
                    assert_eq!(next.call.is_some(), prepared);
                    assert_eq!(next.inner.active_frames(), 0);
                    caller = next;
                }
                assert_eq!(caller.attempts, 5);
            }
        }
    }
}

#[test]
fn invariant_only_empty_calls_still_check_unused_columns_before_resources() {
    let expression = body(
        Identity::Bls12381Fr,
        2,
        json!([
            ["input", 0],
            ["mul", 0, 0],
            ["constant", "bls12-381.fr", "1"],
            ["add", 1, 2],
            ["neg", 3]
        ]),
        4,
    );
    for prepared in [false, true] {
        for mode in ["map", "sum", "product"] {
            let mut caller = Caller::new(Policy::default(), prepared);
            // Reach the same static body with rows before probing an empty call.
            let (result, next) = one(
                caller,
                binding(domains::BLS, mode, "01"),
                &[&expression],
                vec![
                    Value::Index(1),
                    Value::Field(Scalar::from(2)),
                    Value::Vector(vec![Scalar::from(7)].into()),
                ],
            );
            let expected = if mode == "map" {
                Value::Vector(vec![-Scalar::from(5)].into())
            } else {
                Value::Field(-Scalar::from(5))
            };
            assert_value(&result.unwrap()[0], &expected);
            caller = next;
            // Conflicting refusals distinguish shape, output, work and memory
            // precedence even when the entire arithmetic body is invariant.
            for (column_rows, output_limit, error) in [
                (1, Some(0), "refused:numerical-shape"),
                (0, Some(0), "exhausted:output-bytes"),
                (0, None, "exhausted:numerical-work"),
            ] {
                caller.inner = backend(Policy {
                    max_numerical_work: 0,
                    max_numerical_bytes: 0,
                    ..Policy::default()
                });
                caller.output_limit = output_limit;
                caller.outputs.clear();
                let (result, next) = one(
                    caller,
                    binding(domains::BLS, mode, "01"),
                    &[&expression],
                    vec![
                        Value::Index(0),
                        Value::Field(Scalar::from(19)),
                        Value::Vector(vec![Scalar::from(7); column_rows].into()),
                    ],
                );
                assert_eq!(result.unwrap_err(), error);
                assert!(next.outputs.is_empty());
                assert_eq!(next.call.is_some(), prepared);
                assert_eq!(next.inner.active_frames(), 0);
                caller = next;
            }
            // Failed empty calls leave the prior preparation usable with new
            // captures and ordinary empty map/reduction identities.
            caller.inner = backend(Policy::default());
            caller.output_limit = None;
            for rows in [0, 2] {
                caller.outputs.clear();
                let (result, next) = one(
                    caller,
                    binding(domains::BLS, mode, "01"),
                    &[&expression],
                    vec![
                        Value::Index(rows),
                        Value::Field(Scalar::from(23)),
                        Value::Vector(vec![Scalar::from(7); rows as usize].into()),
                    ],
                );
                let term = -Scalar::from(530);
                let expected = match mode {
                    "map" => Value::Vector(vec![term; rows as usize].into()),
                    "sum" => Value::Field((0..rows).fold(Scalar::from(0), |acc, _| acc + term)),
                    _ => Value::Field((0..rows).fold(Scalar::from(1), |acc, _| acc * term)),
                };
                assert_value(&result.unwrap()[0], &expected);
                assert_eq!(next.outputs.len(), 1);
                assert_eq!(next.call.is_some(), prepared);
                caller = next;
            }
            assert_eq!(caller.attempts, 6);
            assert_eq!(caller.inner.active_frames(), 0);
        }
    }
}

#[test]
fn reached_direct_and_prepared_callers_refuse_body_tampering() {
    let valid = body(Identity::KoalaBear, 1, json!([["input", 0]]), 0);
    let invalid = [
        vec![],
        vec![valid.clone(), valid.clone()],
        vec!["broken".into()],
        vec![format!(" {valid}")],
        vec![" ".repeat(4097)],
        vec![valid.replace("\"input\",0", "\"input\",1")],
        vec![valid.replace("koala-bear", "bls12-381.fr")],
        vec![json!(["zkc.ring/0", ["koala-bear"], [["input", 0]], [0, 0]]).to_string()],
        vec![json!(["zkc.ring/0", [], [["constant", "koala-bear", "1"]], [0]]).to_string()],
        vec![
            json!([
                "zkc.ring/0",
                ["koala-bear"],
                [["constant", "bls12-381.fr", "1"]],
                [0]
            ])
            .to_string(),
        ],
        vec![
            json!([
                "zkc.ring/0",
                ["koala-bear"],
                [["constant", "koala-bear", "01"]],
                [0]
            ])
            .to_string(),
        ],
        vec![
            json!([
                "zkc.ring/0",
                ["koala-bear"],
                [["input", 0], ["inverse", 0]],
                [1]
            ])
            .to_string(),
        ],
    ];
    for prepared in [false, true] {
        for parameters in &invalid {
            let expected = if parameters.first().is_some_and(|p| p.len() > 4096) {
                "refused:numerical-expression-bytes"
            } else {
                "refused:numerical-expression"
            };
            let mut caller = Caller::new(Policy::default(), prepared);
            caller.attributes = Some(parameters.clone());
            let (result, caller) = one(
                caller,
                binding(domains::KOALA_BEAR, "map", "1"),
                &[&valid],
                vec![
                    Value::Index(1),
                    Value::KoalaBearVector(vec![KoalaBear::new(7)].into()),
                ],
            );
            assert_eq!(result.unwrap_err(), expected);
            assert_eq!(caller.attempts, 1);
            assert!(caller.outputs.is_empty());
            assert_eq!(caller.inner.active_frames(), 0);
        }
    }
    // An explicit base-to-extension Ring embedding is valid Ring syntax but
    // cannot relax this consumer's exact extension slot contract.
    let valid = body(Identity::KoalaBearExt4, 1, json!([["input", 0]]), 0);
    let mut caller = Caller::new(Policy::default(), true);
    caller.attributes = Some(vec![
        json!([
            "zkc.ring/0",
            ["koala-bear"],
            [["input", 0], ["embed", "koala-bear.ext4-binomial3", 0]],
            [1]
        ])
        .to_string(),
    ]);
    assert_eq!(
        one(
            caller,
            binding(domains::KOALA_BEAR_EXT4, "map", "1"),
            &[&valid],
            vec![Value::Index(0), Value::KoalaBearExt4Vector(vec![].into())]
        )
        .0
        .unwrap_err(),
        "refused:numerical-expression"
    );
}

#[test]
fn reached_direct_and_prepared_callers_enforce_canonical_body_byte_boundary() {
    let (exact, expected) = constant_body_with_bytes(4096);
    let (over, _) = constant_body_with_bytes(4097);
    for (expression, bytes) in [(&exact, 4096), (&over, 4097)] {
        assert_eq!(expression.len(), bytes);
        let parsed = zkc_runtime::ring::Expression::parse(expression).unwrap();
        assert_eq!(parsed.canonical(), *expression);
        assert!(parsed.inputs().is_empty());
        assert_eq!(parsed.outputs().len(), 1);
        assert!(
            parsed
                .facts()
                .iter()
                .all(|fact| fact.field == Identity::Bls12381Fr)
        );
    }

    for prepared in [false, true] {
        let mut caller = Caller::new(Policy::default(), prepared);
        for expression in [&exact, &exact, &over, &exact] {
            // Keep the admitted body valid and change only the reached native
            // attributes, so the 4097-byte refusal comes from the backend.
            caller.attributes = Some(vec![expression.clone()]);
            caller.outputs.clear();
            let (result, next) = one(
                caller,
                binding(domains::BLS, "map", ""),
                &[&exact],
                vec![Value::Index(1)],
            );
            if expression.len() == 4096 {
                assert_value(&result.unwrap()[0], &Value::Vector(vec![expected].into()));
                assert_eq!(next.outputs.len(), 1);
            } else {
                assert_eq!(result.unwrap_err(), "refused:numerical-expression-bytes");
                assert!(next.outputs.is_empty());
            }
            assert_eq!(next.call.is_some(), prepared);
            assert_eq!(next.inner.active_frames(), 0);
            caller = next;
        }
        assert_eq!(caller.attempts, 4);
    }
}

#[test]
fn binary_ring_constants_refuse_two_and_hexadecimal_bit_patterns() {
    use zkc_kernels::plonky3::binary::ext3_from_bits;
    use zkc_kernels::plonky3::binary::from_bits;

    for domain in [domains::BINARY64, domains::BINARY64_EXT3] {
        let valid = body(
            domain.field,
            0,
            json!([["constant", domain.field.name(), "1"]]),
            0,
        );
        for prepared in [false, true] {
            let mut caller = Caller::new(Policy::default(), prepared);
            for literal in ["0", "1", "2", "0x2", "0x8100000000000005", "1"] {
                caller.attributes = Some(vec![body(
                    domain.field,
                    0,
                    json!([["constant", domain.field.name(), literal]]),
                    0,
                )]);
                caller.outputs.clear();
                let (result, next) = one(
                    caller,
                    binding(domain, "map", ""),
                    &[&valid],
                    vec![Value::Index(1)],
                );
                if matches!(literal, "0" | "1") {
                    let bits = u64::from(literal == "1");
                    let expected = if domain.field == Identity::Binary64 {
                        Value::Binary64Vector(vec![from_bits(bits)].into())
                    } else {
                        Value::Binary64Ext3Vector(vec![ext3_from_bits([bits, 0, 0])].into())
                    };
                    assert_value(&result.unwrap()[0], &expected);
                    assert_eq!(next.outputs.len(), 1);
                } else {
                    assert_eq!(result.unwrap_err(), "refused:numerical-expression");
                    assert!(next.outputs.is_empty());
                }
                assert_eq!(next.call.is_some(), prepared);
                assert_eq!(next.inner.active_frames(), 0);
                caller = next;
            }
        }
    }
}

#[test]
fn reached_operand_checks_preserve_nominal_types_and_unused_column_extents() {
    let valid = body(Identity::KoalaBear, 2, json!([["input", 0]]), 0);
    for prepared in [false, true] {
        let vector = || Value::KoalaBearVector(vec![KoalaBear::new(7); 3].into());
        for (args, expected) in [
            (
                vec![
                    Value::Index(3),
                    vector(),
                    Value::KoalaBearVector(vec![].into()),
                ],
                "refused:numerical-shape",
            ),
            (
                vec![Value::Index(2), vector(), vector()],
                "refused:numerical-shape",
            ),
            (
                vec![Value::Index(0), vector(), vector()],
                "refused:numerical-shape",
            ),
            (
                vec![Value::Index(1_048_577), vector(), vector()],
                "refused:numerical-rows",
            ),
            (
                vec![Value::Index(u64::MAX), vector(), vector()],
                "refused:numerical-rows",
            ),
            (
                vec![
                    Value::Index(3),
                    Value::KoalaBearField(KoalaBear::new(7)),
                    vector(),
                ],
                "refused:kernel-operands",
            ),
            (
                vec![
                    Value::Index(3),
                    Value::Vector(vec![Scalar::from(7); 3].into()),
                    vector(),
                ],
                "refused:kernel-operands",
            ),
            (vec![Value::Index(3), vector()], "refused:kernel-operands"),
        ] {
            let mut caller = Caller::new(Policy::default(), prepared);
            caller.arguments = Some(args);
            let (result, caller) = one(
                caller,
                binding(domains::KOALA_BEAR, "sum", "11"),
                &[&valid],
                vec![Value::Index(3), vector(), vector()],
            );
            assert_eq!(result.unwrap_err(), expected);
            assert!(caller.outputs.is_empty());
        }
    }
}

#[test]
fn extension_operands_never_promote_and_a_different_installed_handle_refuses() {
    let expression = body(
        Identity::KoalaBearExt4,
        2,
        json!([["input", 0], ["input", 1], ["add", 0, 1]]),
        2,
    );
    let extension = KoalaBearExt4::from_basis_coefficients_fn(|i| KoalaBear::new(2 + i as u32));
    let valid = || {
        vec![
            Value::Index(1),
            Value::KoalaBearExt4Field(extension),
            Value::KoalaBearExt4Vector(vec![extension].into()),
        ]
    };
    for operands in [
        vec![
            Value::Index(1),
            Value::KoalaBearField(KoalaBear::new(2)),
            Value::KoalaBearExt4Vector(vec![extension].into()),
        ],
        vec![
            Value::Index(1),
            Value::KoalaBearExt4Field(extension),
            Value::KoalaBearVector(vec![KoalaBear::new(2)].into()),
        ],
        vec![
            Value::Index(1),
            Value::KoalaBearExt4Vector(vec![extension].into()),
            Value::KoalaBearExt4Field(extension),
        ],
    ] {
        let mut caller = Caller::new(Policy::default(), true);
        caller.arguments = Some(operands);
        let (result, caller) = one(
            caller,
            binding(domains::KOALA_BEAR_EXT4, "map", "01"),
            &[&expression],
            valid(),
        );
        assert_eq!(result.unwrap_err(), "refused:kernel-operands");
        assert!(caller.outputs.is_empty());
    }
    let mut driver = Controlled::new(backend(Policy::default()));
    driver.binding = Some(binding(domains::KOALA_BEAR_EXT4, "sum", "01"));
    let (result, driver) = one(
        driver,
        binding(domains::KOALA_BEAR_EXT4, "map", "01"),
        &[&expression],
        valid(),
    );
    assert_eq!(result.unwrap_err(), "refused:kernel-binding");
    assert!(driver.outputs.is_empty());
}

#[test]
fn scalar_only_reduction_admits_the_hard_row_boundary_and_keeps_setup_on_empty() {
    let expression = body(
        Identity::KoalaBear,
        0,
        json!([["constant", "koala-bear", "1"]]),
        0,
    );
    let result = one(
        backend(Policy::default()),
        binding(domains::KOALA_BEAR, "sum", ""),
        &[&expression],
        vec![Value::Index(1_048_576)],
    )
    .0
    .unwrap();
    assert_value(
        &result[0],
        &Value::KoalaBearField(KoalaBear::new(1_048_576)),
    );
    for (rows, expected) in [
        (0, "exhausted:numerical-work"),
        (1_048_577, "refused:numerical-rows"),
    ] {
        let policy = Policy {
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        };
        let (result, driver) = one(
            Controlled::new(backend(policy)),
            binding(domains::KOALA_BEAR, "product", ""),
            &[&expression],
            vec![Value::Index(rows)],
        );
        assert_eq!(result.unwrap_err(), expected);
        assert!(driver.outputs.is_empty());
    }
}

#[test]
fn cold_and_warm_empty_calls_require_identical_exact_work_allowances() {
    let expression = body(
        Identity::Bls12381Fr,
        2,
        json!([["input", 0], ["input", 1], ["add", 0, 1], ["neg", 2]]),
        3,
    );
    // R = 0, I = 2 and N = 4 still require the complete fixed setup surcharge.
    let work = 8 * expression.len() as u64 + 2 * 2 + 2 * 4 + 1;
    let args = || {
        vec![
            Value::Index(0),
            Value::Field(Scalar::from(7)),
            Value::Vector(vec![].into()),
        ]
    };
    for mode in ["map", "sum", "product"] {
        let expected = match mode {
            "map" => Value::Vector(vec![].into()),
            "sum" => Value::Field(Scalar::from(0)),
            _ => Value::Field(Scalar::from(1)),
        };
        for prepared in [false, true] {
            for warmed in [false, true] {
                for allowance in [work, work - 1] {
                    let mut caller = Caller::new(Policy::default(), prepared);
                    if warmed {
                        let (result, next) = one(
                            caller,
                            binding(domains::BLS, mode, "01"),
                            &[&expression],
                            args(),
                        );
                        assert_value(&result.unwrap()[0], &expected);
                        caller = next;
                    }
                    caller.inner = backend(Policy {
                        max_numerical_work: allowance,
                        ..Policy::default()
                    });
                    caller.outputs.clear();
                    let (result, caller) = one(
                        caller,
                        binding(domains::BLS, mode, "01"),
                        &[&expression],
                        args(),
                    );
                    if allowance == work {
                        assert_value(&result.unwrap()[0], &expected);
                        assert_eq!(caller.outputs.len(), 1);
                    } else {
                        assert_eq!(result.unwrap_err(), "exhausted:numerical-work");
                        assert!(caller.outputs.is_empty());
                    }
                    // Cold preparation can fill the slot even when evaluation
                    // admission refuses; direct calls discard their local slot.
                    assert_eq!(caller.call.is_some(), prepared);
                    assert_eq!(caller.attempts, if warmed { 2 } else { 1 });
                    assert_eq!(caller.inner.active_frames(), 0);
                }
            }
        }
    }
}

#[test]
fn numerical_scope_has_exact_work_output_and_managed_memory_boundaries() {
    // One constant node and no operands make this a storage-independent memory
    // boundary: native node scratch + map staging/final, or inline scalar final.
    let expression = body(
        Identity::Bls12381Fr,
        0,
        json!([["constant", "bls12-381.fr", "1"]]),
        0,
    );
    for rows in [0usize, 3, 9] {
        for mode in ["map", "sum", "product"] {
            let map = mode == "map";
            let output = if map {
                256 + rows * size_of::<Scalar>()
            } else {
                512
            };
            let memory =
                size_of::<Scalar>() + output + if map { rows * size_of::<Scalar>() } else { 0 };
            let work = 8 * expression.len() as u64 + 3 + rows as u64 * 6;
            let exact = Policy {
                max_numerical_bytes: memory,
                max_numerical_work: work,
                ..Policy::default()
            };
            for (policy, allowance, error) in [
                (exact, output, None),
                (
                    Policy {
                        max_value_bytes: output,
                        ..exact
                    },
                    output,
                    None,
                ),
                (exact, output - 1, Some("exhausted:output-bytes")),
                (
                    Policy {
                        max_numerical_work: work - 1,
                        ..exact
                    },
                    output,
                    Some("exhausted:numerical-work"),
                ),
                (
                    Policy {
                        max_numerical_bytes: memory - 1,
                        ..exact
                    },
                    output,
                    Some("exhausted:numerical-bytes"),
                ),
                (
                    Policy {
                        max_value_bytes: output - 1,
                        ..exact
                    },
                    output,
                    Some("exhausted:output-bytes"),
                ),
            ] {
                // The leading Index requires a 512-byte per-value allowance.
                // The map at nine rows separately tests the tuple ceiling;
                // every result size tests the invocation's output allowance.
                if policy.max_value_bytes < 512 {
                    continue;
                }
                let mut driver = Controlled::new(backend(policy));
                driver.output_limit = Some(allowance);
                let (result, driver) = one(
                    driver,
                    binding(domains::BLS, mode, ""),
                    &[&expression],
                    vec![Value::Index(rows as u64)],
                );
                if let Some(error) = error {
                    assert_eq!(result.unwrap_err(), error);
                    assert!(driver.outputs.is_empty());
                } else {
                    let expected = if map {
                        Value::Vector(vec![Scalar::from(1); rows].into())
                    } else {
                        Value::Field(Scalar::from(if mode == "sum" { rows as u64 } else { 1 }))
                    };
                    assert_value(&result.unwrap()[0], &expected);
                }
                assert_eq!(driver.inner.active_frames(), 0);
            }
        }
    }
}

#[test]
fn even_unused_scalar_slots_reserve_typed_operand_storage() {
    let expression = body(
        Identity::Bls12381Fr,
        1,
        json!([["constant", "bls12-381.fr", "1"]]),
        0,
    );
    let policy = Policy {
        max_numerical_bytes: 512 + size_of::<Scalar>(),
        ..Policy::default()
    };
    let (result, driver) = one(
        Controlled::new(backend(policy)),
        binding(domains::BLS, "sum", "0"),
        &[&expression],
        vec![Value::Index(0), Value::Field(Scalar::from(7))],
    );
    assert_eq!(result.unwrap_err(), "exhausted:numerical-bytes");
    assert!(driver.outputs.is_empty());
}

#[test]
fn varying_calls_agree_at_minimum_intermediate_and_full_workspace() {
    let rows = 513;
    let input: Vec<_> = (0..rows).map(|i| Scalar::from(i as u64 + 1)).collect();
    for deep in [false, true] {
        let mut nodes = vec![
            json!(["input", 0]),
            json!(["input", 1]),
            json!(["mul", 1, 1]),
            json!(["add", 0, 2]),
        ];
        if deep {
            // A long dependency chain shrinks the chunk size without selecting
            // a different operation or field-specific evaluator.
            for _ in 0..120 {
                nodes.push(json!(["neg", nodes.len() - 1]));
            }
        }
        let expression = body(Identity::Bls12381Fr, 2, json!(nodes), nodes.len() - 1);
        for mode in ["map", "sum", "product"] {
            let args = |capture| {
                vec![
                    Value::Index(rows as u64),
                    Value::Vector(input.clone().into()),
                    Value::Field(Scalar::from(capture)),
                ]
            };
            let run = |budget| {
                one(
                    Caller::new(
                        Policy {
                            max_numerical_bytes: budget,
                            ..Policy::default()
                        },
                        true,
                    ),
                    binding(domains::BLS, mode, "10"),
                    &[&expression],
                    args(7),
                )
                .0
            };
            // Locate the public admission boundary without depending on the
            // private Operand enum's ABI. Every lower budget must refuse memory.
            let (mut low, mut high) = (0, Policy::default().max_numerical_bytes);
            assert!(run(high).is_ok());
            while low + 1 < high {
                let middle = low + (high - low) / 2;
                match run(middle) {
                    Ok(_) => high = middle,
                    Err(error) => {
                        assert_eq!(error, "exhausted:numerical-bytes");
                        low = middle;
                    }
                }
            }
            assert_eq!(run(high - 1).unwrap_err(), "exhausted:numerical-bytes");
            let row_bytes = nodes.len() * size_of::<Scalar>();
            for budget in [
                high,
                high + row_bytes * 6,
                Policy::default().max_numerical_bytes,
            ] {
                let mut caller = Caller::new(
                    Policy {
                        max_numerical_bytes: budget,
                        ..Policy::default()
                    },
                    true,
                );
                for capture in [7u64, 19, 0] {
                    let terms: Vec<_> = input
                        .iter()
                        .map(|x| *x + Scalar::from(capture * capture))
                        .collect();
                    let expected = match mode {
                        "map" => Value::Vector(terms.into()),
                        "sum" => Value::Field(terms.iter().copied().sum()),
                        _ => Value::Field(terms.iter().copied().product()),
                    };
                    let (result, next) = one(
                        caller,
                        binding(domains::BLS, mode, "10"),
                        &[&expression],
                        args(capture),
                    );
                    assert_value(&result.unwrap()[0], &expected);
                    assert_eq!(next.inner.active_frames(), 0);
                    caller = next;
                }
            }
        }
    }
}

#[test]
fn prepared_calls_recheck_inputs_static_identity_and_live_policy() {
    let expression = body(Identity::Bls12381Fr, 1, json!([["input", 0]]), 0);
    let mut caller = Caller::new(Policy::default(), true);
    for (mode, mask, values, expected) in [
        (
            "map",
            "0",
            vec![Value::Field(Scalar::from(7))],
            Value::Vector(vec![Scalar::from(7); 3].into()),
        ),
        (
            "map",
            "0",
            vec![Value::Field(Scalar::from(19))],
            Value::Vector(vec![Scalar::from(19); 3].into()),
        ),
        (
            "map",
            "1",
            vec![Value::Vector(
                [2u64, 5, 11].map(Scalar::from).to_vec().into(),
            )],
            Value::Vector([2u64, 5, 11].map(Scalar::from).to_vec().into()),
        ),
        (
            "sum",
            "1",
            vec![Value::Vector(
                [2u64, 5, 11].map(Scalar::from).to_vec().into(),
            )],
            Value::Field(Scalar::from(18)),
        ),
    ] {
        let args = [vec![Value::Index(3)], values].concat();
        let (result, next) = one(
            caller,
            binding(domains::BLS, mode, mask),
            &[&expression],
            args,
        );
        assert_value(&result.unwrap()[0], &expected);
        caller = next;
    }
    // Reusing a plan across backend instances does not reuse their authority or
    // reserve: all of the current instance's dynamic limits still apply.
    for (policy, allowance, expected) in [
        (
            Policy {
                max_numerical_work: 0,
                ..Policy::default()
            },
            None,
            "exhausted:numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            None,
            "exhausted:numerical-bytes",
        ),
        (Policy::default(), Some(511), "exhausted:output-bytes"),
    ] {
        caller.inner = backend(policy);
        caller.output_limit = allowance;
        caller.outputs.clear();
        let (result, next) = one(
            caller,
            binding(domains::BLS, "sum", "1"),
            &[&expression],
            vec![
                Value::Index(3),
                Value::Vector([2u64, 5, 11].map(Scalar::from).to_vec().into()),
            ],
        );
        assert_eq!(result.unwrap_err(), expected);
        assert!(next.outputs.is_empty());
        assert_eq!(next.inner.active_frames(), 0);
        caller = next;
    }
    caller.inner = backend(Policy::default());
    caller.output_limit = None;
    caller.attributes = Some(vec![format!(" {expression}")]);
    let (result, caller) = one(
        caller,
        binding(domains::BLS, "sum", "1"),
        &[&expression],
        vec![Value::Index(0), Value::Vector(vec![].into())],
    );
    assert_eq!(result.unwrap_err(), "refused:numerical-expression");
    assert!(caller.outputs.is_empty());
}

fn expression_program(binding: &OperationBinding, expression: &str, conditional: bool) -> Vec<u8> {
    let signature = binding.signature().unwrap();
    let mut ports: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, t)| json!([format!("a{i}"), t.spelling()]))
        .collect();
    let mut names: Vec<_> = (0..ports.len()).map(|i| format!("a{i}")).collect();
    let op = json!(["op", "evaluate", "expr", [expression], names, ["value"]]);
    let body = if conditional {
        ports.push(json!(["condition", "bool@native.bool/0"]));
        names.push("condition".into());
        json!([
            [
                "if",
                "choose",
                "condition",
                ["a0", "a1"],
                [op, ["yield", ["value"]]],
                [["yield", ["a1"]]],
                ["chosen"]
            ],
            ["return", ["chosen"]]
        ])
    } else {
        json!([op, ["return", ["value"]]])
    };
    let output = signature.outputs[0].spelling();
    serde_json::to_vec(&json!([
        "zkc.program/0",
        [[
            "expr",
            binding.contract,
            binding.arguments,
            binding.implementation,
            binding.physical_arguments
        ]],
        [[
            "function",
            "evaluate",
            ports,
            [output],
            body,
            ["evaluate", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            ports,
            [output],
            [
                ["local", "local", "evaluate", names, ["result"]],
                ["return", ["result"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}

#[test]
fn dormant_numerical_calls_do_not_decode_or_spend_live_capacity() {
    let expression = body(Identity::Bls12381Fr, 1, json!([["input", 0]]), 0);
    let program = expression_program(&binding(domains::BLS, "map", "1"), &expression, true);
    for prepared in [false, true] {
        for reached in [false, true] {
            let mut caller = Caller::new(
                Policy {
                    max_numerical_work: 0,
                    max_numerical_bytes: 0,
                    ..Policy::default()
                },
                prepared,
            );
            caller.attributes = Some(vec!["malformed reached body".into()]);
            let vector = Value::Vector(vec![Scalar::from(7); 3].into());
            let (result, caller) = support::run_program(
                caller,
                &program,
                vec![Value::Index(3), vector.clone(), Value::Bool(reached)],
            );
            if reached {
                assert_eq!(result.unwrap_err(), "refused:numerical-expression");
                assert_eq!(caller.attempts, 1);
            } else {
                assert_value(&result.unwrap()[0], &vector);
                assert_eq!(caller.attempts, 0);
                assert!(caller.call.is_none());
            }
            assert!(caller.outputs.is_empty());
            assert_eq!(caller.inner.active_frames(), 0);
        }
    }
}

#[test]
fn failure_preserves_an_earlier_random_draw_and_publishes_no_expression_result() {
    let expression = body(Identity::Bls12381Fr, 1, json!([["input", 0]]), 0);
    let expr = binding(domains::BLS, "map", "1");
    let draw = OperationBinding {
        contract: "random.draw".into(),
        arguments: vec![Identity::Bls12381Fr.name().into()],
        implementation: "arkworks/random.draw".into(),
        physical_arguments: vec![],
    };
    let mut inputs = expr.signature().unwrap().inputs;
    inputs.push(draw.signature().unwrap().inputs[0].clone());
    let outputs = vec![
        expr.signature().unwrap().outputs[0].clone(),
        inputs[2].clone(),
    ];
    let program = support::program(
        &[expr, draw],
        &inputs,
        vec![
            json!(["op", "draw", "b1", [], ["a2"], ["sample", "next"]]),
            json!([
                "op",
                "evaluate",
                "b0",
                [expression],
                ["a0", "a1"],
                ["value"]
            ]),
        ],
        &outputs,
        &["value".into(), "next".into()],
    );
    for prepared in [false, true] {
        let mut caller = Caller::new(Policy::default(), prepared);
        let rng = caller
            .inner
            .issue_rng_for(Identity::Bls12381Fr, support::domain(), 3)
            .unwrap();
        let outside = caller
            .inner
            .issue_rng_for(Identity::Bls12381Fr, support::domain(), 7)
            .unwrap();
        let Value::Rng(root) = &rng else {
            panic!("rng")
        };
        let Value::Rng(other) = &outside else {
            panic!("rng")
        };
        let before = caller.inner.observe(other).unwrap();
        let (result, caller) = support::run_program(
            caller,
            &program,
            vec![
                Value::Index(2),
                Value::Vector(vec![Scalar::from(7); 3].into()),
                rng.clone(),
            ],
        );
        assert_eq!(result.unwrap_err(), "refused:numerical-shape");
        let after = caller.inner.observe(root).unwrap();
        assert_eq!(
            (after.generation, after.draw_count, after.budget),
            (1, 1, 2)
        );
        assert_eq!(caller.inner.observe(other).unwrap(), before);
        assert_eq!(caller.outputs.len(), 1); // Only the completed random.draw tuple.
        assert_eq!(caller.inner.active_frames(), 0);
    }
}

#[test]
fn reusable_computations_preserve_results_and_reject_changed_numerical_policy() {
    let expression = body(
        Identity::Bls12381Fr,
        1,
        json!([["input", 0], ["mul", 0, 0], ["add", 1, 0]]),
        2,
    );
    let admitted = Program::decode(
        &expression_program(&binding(domains::BLS, "map", "0"), &expression, false),
        zkc_cpu::cpu_contracts(),
    )
    .unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    // Computation reuse accepts bounded scalar parameters, not vector content
    // keys. Exercise a captured scalar without extending that cache contract.
    let args = || vec![Value::Index(3), Value::Field(Scalar::from(2))];
    for prepared in [false, true, true] {
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend(Policy::default()),
            args(),
        )
        .unwrap_or_else(|error| panic!("{}", error.error));
        if prepared {
            runner.prepare_computations(cache.clone(), &[0, 1]).unwrap();
        }
        let (result, native) = support::drive(runner);
        assert_value(
            &result.unwrap()[0],
            &Value::Vector(vec![Scalar::from(6); 3].into()),
        );
        assert_eq!(native.ring_work_spent(), 0);
        assert_eq!(native.active_frames(), 0);
    }
    assert_eq!(cache.stats().hits, 1);
    for (policy, expected) in [
        (
            Policy {
                max_numerical_work: 0,
                ..Policy::default()
            },
            "exhausted:numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            "exhausted:numerical-bytes",
        ),
    ] {
        let mut runner = Runner::new(&admitted, "main", "P", "session", backend(policy), args())
            .unwrap_or_else(|error| panic!("{}", error.error));
        runner.prepare_computations(cache.clone(), &[0, 1]).unwrap();
        let (result, native) = support::drive(runner);
        let stop = result.unwrap_err();
        assert_eq!(support::code(&stop), expected);
        assert_eq!(native.active_frames(), 0);
        assert_eq!(cache.stats().hits, 1);
    }
}
