//! Complete native invocation, including output validation and frame cleanup.
#[path = "domains/support.rs"]
mod support;

use support::{Controlled, backend, binding, one, vector};
use zkc_cpu::{Policy, Scalar, Value};

#[test]
fn ordered_search_admits_its_complete_result_before_work() {
    let policy = Policy {
        max_numerical_work: 4,
        max_numerical_bytes: zkc_cpu::VALUE_SLOT_BYTES,
        ..Policy::default()
    };
    for (policy, allowance, expected) in [
        (policy, zkc_cpu::VALUE_SLOT_BYTES, None),
        (
            policy,
            zkc_cpu::VALUE_SLOT_BYTES - 1,
            Some("exhausted:output-bytes"),
        ),
        (
            Policy {
                max_numerical_bytes: zkc_cpu::VALUE_SLOT_BYTES - 1,
                ..policy
            },
            zkc_cpu::VALUE_SLOT_BYTES,
            Some("exhausted:numerical-bytes"),
        ),
        (
            Policy {
                max_numerical_work: 3,
                ..policy
            },
            zkc_cpu::VALUE_SLOT_BYTES,
            Some("exhausted:numerical-work"),
        ),
        (
            Policy {
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..policy
            },
            zkc_cpu::VALUE_SLOT_BYTES - 1,
            Some("exhausted:output-bytes"),
        ),
    ] {
        let mut driver = Controlled::new(backend(policy));
        driver.output_limit = Some(allowance);
        let input = vector(false, &[3, 7, 3]);
        let alias = input.clone();
        let (result, driver) = one(
            driver,
            binding(false, "vector.find_last"),
            &[],
            vec![input.clone(), Value::Field(Scalar::from(3))],
        );
        if let Some(code) = expected {
            assert_eq!(result.unwrap_err(), code);
            assert!(driver.outputs.is_empty());
        } else {
            assert!(matches!(result.unwrap().as_slice(), [Value::Index(2)]));
            assert_eq!(driver.outputs.len(), 1);
        }
        support::assert_value(&input, &alias);
        assert_eq!(driver.inner.active_frames(), 0);
    }
}
