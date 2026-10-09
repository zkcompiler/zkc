//! Independent admission and provider extension witnesses over unchanged ports.
#[path = "domains/support.rs"]
mod support;
use serde_json::json;
use support::{backend, binding, one, program, vector};
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::{
    Backend, BackendError, BoundSignature, ErrorCode, Frame, FrameExit, Invocation,
    OperationBinding, PhysicalType, admit_supplied,
};

#[test]
fn same_ports_distinct_dot_algorithms_preserve_results_and_refusals() {
    let normal = binding(false, "vector.dot");
    let alternate = OperationBinding {
        implementation: "arkworks-pairwise/vector.dot".into(),
        ..normal.clone()
    };
    let native = backend(Policy::default());
    assert_eq!(normal.signature().unwrap(), alternate.signature().unwrap());
    assert_eq!(
        native.binding_signature(&alternate),
        Some(alternate.signature().unwrap())
    );
    for n in [0, 1, 2, 3, 17, 1024] {
        let a: Vec<_> = (0..n).map(|i| (i * 3 + 1) as u64).collect();
        let b: Vec<_> = (0..n).map(|i| (i * 7 + 2) as u64).collect();
        let inputs = vec![vector(false, &a), vector(false, &b)];
        let x = one(
            backend(Policy::default()),
            normal.clone(),
            &[],
            inputs.clone(),
        )
        .0
        .unwrap();
        let y = one(backend(Policy::default()), alternate.clone(), &[], inputs)
            .0
            .unwrap();
        assert_eq!(
            native.encode_native_value(&x[0]).unwrap(),
            native.encode_native_value(&y[0]).unwrap()
        );
    }
    for b in [normal, alternate] {
        assert_eq!(
            one(
                backend(Policy::default()),
                b.clone(),
                &[],
                vec![vector(false, &[1]), vector(false, &[])]
            )
            .0
            .unwrap_err(),
            "refused:length-mismatch"
        );
        let mut combined = support::Controlled::new(backend(Policy::default()));
        combined.output_limit = Some(511);
        assert_eq!(
            one(
                combined,
                b.clone(),
                &[],
                vec![vector(false, &[1]), vector(false, &[])]
            )
            .0
            .unwrap_err(),
            "exhausted:output-bytes"
        );
        let mut limited = support::Controlled::new(backend(Policy::default()));
        limited.output_limit = Some(511);
        assert_eq!(
            one(
                limited,
                b,
                &[],
                vec![vector(false, &[]), vector(false, &[])]
            )
            .0
            .unwrap_err(),
            "exhausted:output-bytes"
        );
    }
}

// Deliberately independently authored false advertisements: neither fixture
// derives its ports from runtime admission or the native signature table.
struct Divergent {
    input: bool,
}
impl Backend for Divergent {
    type Value = Value;
    fn validate_value(&self, _: &Value) -> Result<(), BackendError> {
        unreachable!()
    }
    fn binding_signature(&self, _: &OperationBinding) -> Option<BoundSignature> {
        Some(BoundSignature {
            inputs: if self.input {
                vec![PhysicalType::parse("vector:bls12-381.fr@arkworks.fr-vector/0").unwrap()]
            } else {
                vec![PhysicalType::parse("vector:bls12-381.fr@arkworks.fr-vector/0").unwrap(); 2]
            },
            outputs: vec![
                PhysicalType::parse(if self.input {
                    "field:bls12-381.fr@arkworks.fr/0"
                } else {
                    "bool@native.bool/0"
                })
                .unwrap(),
            ],
            attributes: zkc_runtime::interactive::AttributeRule::None,
        })
    }
    fn enter_frame(&mut self, _: &Frame, _: &[Value]) -> Result<(), BackendError> {
        unreachable!()
    }
    fn leave_frame(&mut self, _: &Frame, _: FrameExit, _: &[Value]) -> Result<(), BackendError> {
        unreachable!()
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[Value]) -> Result<Vec<Value>, BackendError> {
        unreachable!()
    }
}
#[test]
fn runtime_backend_signature_divergence_is_refused_at_admission() {
    let b = binding(false, "vector.dot");
    let sig = b.signature().unwrap();
    let bytes = program(
        &[b],
        &sig.inputs,
        vec![json!(["op", "dot", "b0", [], ["a0", "a1"], ["out"]])],
        &sig.outputs,
        &["out".into()],
    );
    for input in [false, true] {
        let error = admit_supplied(&bytes, &Divergent { input }).unwrap_err();
        assert_eq!(error.code, ErrorCode::Backend);
        assert_eq!(
            error.detail,
            "installed signature mismatch: arkworks/vector.dot"
        );
    }
}
#[test]
fn unused_retained_bindings_still_require_independent_physical_admission() {
    let b = binding(false, "vector.dot");
    let bytes = program(&[b], &[], vec![], &[], &[]);
    let mut carrier: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    // A retained valid declaration needs no reachable kernel advertisement.
    admit_supplied(&bytes, &Divergent { input: true }).unwrap();
    carrier[1][0][3] = json!("artifact-authorized/vector.dot");
    let error = admit_supplied(
        &serde_json::to_vec(&carrier).unwrap(),
        &Divergent { input: true },
    )
    .unwrap_err();
    assert_eq!(error.code, ErrorCode::Signature);
    carrier[1][0][3] = json!("arkworks-pairwise/vector.dot");
    admit_supplied(
        &serde_json::to_vec(&carrier).unwrap(),
        &backend(Policy::default()),
    )
    .unwrap();
    carrier[1][0][2] = json!(["koala-bear"]);
    let error = admit_supplied(
        &serde_json::to_vec(&carrier).unwrap(),
        &Divergent { input: true },
    )
    .unwrap_err();
    assert_eq!(error.code, ErrorCode::Signature);
}
#[test]
fn unknown_implementations_and_extra_authority_facets_are_refused() {
    let b = OperationBinding {
        contract: "curve.msm".into(),
        arguments: vec!["ristretto255.group".into()],
        implementation: "invalid/curve.msm".into(),
    };
    assert!(b.signature().is_err());
    assert!(backend(Policy::default()).binding_signature(&b).is_none());
    let b = OperationBinding {
        implementation: "dalek/curve.msm".into(),
        ..b
    };
    let sig = b.signature().unwrap();
    let mut bytes: serde_json::Value =
        serde_json::from_slice(&program(&[b], &sig.inputs, vec![], &[], &[])).unwrap();
    bytes[1][0].as_array_mut().unwrap().push(json!([]));
    // An extra producer facet is a malformed record, not a security override.
    let error = admit_supplied(
        &serde_json::to_vec(&bytes).unwrap(),
        &backend(Policy::default()),
    )
    .unwrap_err();
    assert_eq!(error.code, ErrorCode::Record);
    assert_eq!(error.detail, "operation binding arity");
}

#[cfg(feature = "test-utils")]
#[test]
fn random_vector_crosses_into_group_kernel_with_one_resource_authority() {
    use zkc_backends::{Domain, RistrettoScalar};
    use zkc_runtime::interactive::Value as RuntimeValue;
    for wrong_length in [false, true] {
        let mut native = backend(Policy::default());
        let rng = native
            .issue_test_ristretto_tape(
                Domain::new("P", "session", "main", None),
                4,
                vec![RistrettoScalar::from(3u64), RistrettoScalar::from(5u64)],
            )
            .unwrap();
        let Value::Rng(original) = &rng else {
            unreachable!()
        };
        let original = original.clone();
        let groups = support::groups(true, if wrong_length { &[7] } else { &[7, 11] });
        let draw = binding(true, "random.vector");
        let msm = binding(true, "curve.msm");
        let outputs = [
            msm.signature().unwrap().outputs[0].clone(),
            rng.physical_type(),
        ];
        let bytes = program(
            &[draw, msm],
            &[rng.physical_type(), groups.physical_type()],
            vec![
                json!(["op", "draw", "b0", ["2"], ["a0"], ["scalars", "next"]]),
                json!(["op", "msm", "b1", [], ["scalars", "a1"], ["point"]]),
            ],
            &outputs,
            &["point".into(), "next".into()],
        );
        let (result, native) = support::run_program(native, &bytes, vec![rng, groups]);
        let observed = native.observe(&original).unwrap();
        assert_eq!(observed.issued_id, original.issued_id());
        assert_eq!(observed.generation, 1);
        assert_eq!(observed.draw_count, 2);
        assert_eq!(observed.budget, 2);
        assert_eq!(native.active_frames(), 0);
        // Failure after drawing does not roll back the authoritative debit.
        if wrong_length {
            assert_eq!(result.unwrap_err(), "refused:length-mismatch");
        } else {
            let outputs = result.unwrap();
            support::assert_value(
                &outputs[0],
                &Value::RistrettoGroup(
                    curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT
                        * RistrettoScalar::from(76u64),
                ),
            );
            let Value::Rng(next) = &outputs[1] else {
                panic!("same typed capability must return")
            };
            assert_eq!(next.issued_id(), original.issued_id());
            assert_eq!(next.generation(), 1);
            native.validate_value(&outputs[1]).unwrap();
            assert!(
                backend(Policy::default())
                    .validate_value(&outputs[1])
                    .is_err()
            );
        }
        assert!(native.validate_value(&Value::Rng(original)).is_err());
    }
}
