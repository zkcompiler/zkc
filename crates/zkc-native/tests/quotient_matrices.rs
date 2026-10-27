//! Prepared quotient values through installed native operations and the VM.
#[path = "domains/support.rs"]
mod support;

use support::{Controlled, backend, one};
use zkc_native::{Policy, Value};
use zkc_runtime::vm::{Backend, OperationBinding, Value as _};

fn binding(name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![],
        implementation: format!("native/{name}"),
        physical_arguments: vec![],
    }
}
fn arguments() -> Vec<Value> {
    vec![
        Value::Indices(vec![1, 2, 3, 4, 5, 6, 7, 8].into()),
        Value::Index(17),
        Value::Index(2),
        Value::Index(2),
        Value::Index(2),
        Value::Index(2),
    ]
}
fn prepared() -> Value {
    one(
        backend(Policy::default()),
        binding("quotient.prepare_matrix"),
        &[],
        arguments(),
    )
    .0
    .unwrap()
    .remove(0)
}

#[test]
fn installed_preparation_and_repeated_products_preserve_inputs_and_wire_boundary() {
    let inputs = arguments();
    let alias = inputs[0].clone();
    let (result, backend) = one(
        backend(Policy::default()),
        binding("quotient.prepare_matrix"),
        &[],
        inputs,
    );
    let matrix = result.unwrap().remove(0);
    assert!(!zkc_native::has_native_wire(&matrix.physical_type()));
    assert!(backend.encode_native_value(&matrix).is_err());
    let digits = Value::Indices(vec![1, 16, 2, 15].into());
    let mut previous_outputs: Vec<Value> = Vec::new();
    for _ in 0..3 {
        let (result, next) = one(
            support::backend(Policy::default()),
            binding("quotient.matvec"),
            &[],
            vec![matrix.clone(), digits.clone()],
        );
        let result = result.unwrap().remove(0);
        assert!(matches!(&result, Value::Indices(xs) if xs.as_ref()==[0,3,7,3]));
        assert_eq!(next.active_frames(), 0);
        // Keep previous outputs live so address reuse cannot confuse identity.
        for previous in &previous_outputs {
            assert_ne!(previous.validation_backing(), result.validation_backing());
        }
        previous_outputs.push(result);
    }
    assert!(matches!(&alias, Value::Indices(xs) if xs.as_ref()==[1,2,3,4,5,6,7,8]));
    assert!(matches!(&digits, Value::Indices(xs) if xs.as_ref()==[1,16,2,15]));
}

#[test]
fn current_policy_and_invocation_output_limits_are_rechecked() {
    let matrix = prepared();
    let tighter = backend(Policy {
        max_table_elements: 4,
        ..Policy::default()
    });
    assert_eq!(
        tighter.validate_value(&matrix).unwrap_err().code,
        "exhausted:element-limit"
    );
    for (name, args, bytes) in [
        (
            "quotient.prepare_matrix",
            arguments(),
            matrix.retained_bytes(),
        ),
        (
            "quotient.matvec",
            vec![matrix.clone(), Value::Indices(vec![1, 16, 2, 15].into())],
            4 * 8 + 256,
        ),
    ] {
        let mut driver = Controlled::new(backend(Policy::default()));
        driver.output_limit = Some(bytes - 1);
        let (result, driver) = one(driver, binding(name), &[], args.clone());
        assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
        assert!(driver.outputs.is_empty());
        assert_eq!(driver.inner.active_frames(), 0);
        let mut driver = Controlled::new(backend(Policy::default()));
        driver.output_limit = Some(bytes);
        let (result, driver) = one(driver, binding(name), &[], args);
        assert!(result.is_ok());
        assert_eq!(driver.outputs.len(), 1);
        assert_eq!(driver.inner.active_frames(), 0);
    }
}

#[test]
fn failed_digit_admission_publishes_nothing_and_releases_frames() {
    let matrix = prepared();
    for (digits, code) in [
        (vec![3; 4], "quotient-digit-bound"),
        (vec![17; 4], "quotient-residue"),
        (vec![0; 3], "quotient-shape"),
    ] {
        let (result, driver) = one(
            Controlled::new(backend(Policy::default())),
            binding("quotient.matvec"),
            &[],
            vec![matrix.clone(), Value::Indices(digits.into())],
        );
        assert_eq!(result.unwrap_err(), format!("refused:{code}"));
        assert!(driver.outputs.is_empty());
        assert_eq!(driver.inner.active_frames(), 0);
        assert_eq!(driver.inner.live_resource_units(), 0);
    }
}
