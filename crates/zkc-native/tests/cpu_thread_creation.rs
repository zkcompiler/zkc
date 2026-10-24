//! Trace the installed single-polynomial operations, including exited workers.
#![cfg(target_os = "linux")]
#[path = "domains/support.rs"]
mod support;

use zkc_native::{
    Bn254Scalar as F, CpuExecution, Domain, EntryPolicy, NativeBackend, Policy, SetupRegistry,
    Value,
};
use zkc_runtime::vm::OperationBinding;

const WORKERS: &str = "ZKC_NATIVE_POLYNOMIAL_WORKERS";

#[test]
#[ignore = "requires strace and ptrace permission; run this focused gate explicitly"]
fn installed_polynomial_operations_create_only_owned_workers() {
    let evidence = zkc_test_support::evidence("native-polynomial-threads");
    for workers in [1, 4] {
        let directory = evidence.nested(&format!("workers-{workers}"));
        let tasks = zkc_test_support::task_trace::test(
            directory.path(),
            "polynomial_workload_child",
            &[
                (WORKERS, workers.to_string()),
                ("RAYON_NUM_THREADS", "7".into()),
            ],
        );
        // The only non-owner task is libtest's runner thread. The mismatched
        // environment makes ambient Rayon initialization exceed this budget.
        assert_eq!(tasks, 1 + workers, "unowned tasks with {workers} workers");
    }
}

fn call(cpu: &CpuExecution, name: &str, args: Vec<Value>) -> Value {
    let policy = Policy::default();
    let backend = NativeBackend::new_with_cpu(
        policy,
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        SetupRegistry::new(vec![], &policy).unwrap(),
        cpu.clone(),
    )
    .unwrap();
    let binding = OperationBinding {
        contract: name.into(),
        arguments: vec!["bn254.fr".into()],
        implementation: format!("arkworks/{name}"),
        physical_arguments: vec![],
    };
    support::one(backend, binding, &[], args)
        .0
        .unwrap()
        .remove(0)
}

#[test]
#[ignore = "child entry point for the Linux thread-creation gate"]
fn polynomial_workload_child() {
    let Ok(workers) = std::env::var(WORKERS) else {
        return;
    };
    let cpu = CpuExecution::new(workers.parse().unwrap()).unwrap();
    let shift = F::from(7);
    // Independent linear-polynomial oracle: no upstream transform is used to
    // prepare or check this fixture, so setup cannot create ambient workers.
    let domain = zkc_kernels::arkworks::bn254::polynomial::Domain::new(1024, shift).unwrap();
    let expected: Vec<_> = domain
        .elements()
        .map(|x| F::from(3) + F::from(5) * x)
        .collect();
    let evaluated = call(
        &cpu,
        "poly.coset_evaluate",
        vec![
            Value::Bn254Polynomial(vec![F::from(3), F::from(5)].into()),
            Value::Bn254Field(shift),
            Value::Index(1024),
        ],
    );
    let Value::Bn254Vector(values) = &evaluated else {
        panic!("expected evaluations");
    };
    assert_eq!(values.as_ref(), expected);
    let recovered = call(
        &cpu,
        "poly.coset_interpolate",
        vec![evaluated.clone(), Value::Bn254Field(shift)],
    );
    let Value::Bn254Polynomial(coefficients) = recovered else {
        panic!("expected coefficients");
    };
    assert_eq!(coefficients.as_ref(), [F::from(3), F::from(5)]);
    let quotient = call(
        &cpu,
        "poly.opening_quotient",
        vec![
            evaluated,
            Value::Bn254Field(shift),
            Value::Bn254Field(F::from(0)),
            Value::Bn254Field(F::from(3)),
        ],
    );
    let Value::Bn254Vector(quotient) = quotient else {
        panic!("expected quotient");
    };
    assert_eq!(quotient.as_ref(), vec![F::from(5); 1024]);
}
