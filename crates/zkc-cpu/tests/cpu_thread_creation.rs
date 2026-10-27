//! Trace installed polynomial and resident curve calls, including exited workers.
#![cfg(target_os = "linux")]
#[path = "domains/support.rs"]
mod support;

use std::sync::Arc;
use zkc_cpu::{
    Bn254Scalar as F, CpuBackend, CpuExecution, Domain, EntryPolicy, Policy, SetupRegistry, Value,
};
use zkc_runtime::vm::OperationBinding;

const WORKERS: &str = "ZKC_NATIVE_POLYNOMIAL_WORKERS";
const RESIDENT_WORKERS: &str = "ZKC_NATIVE_RESIDENT_WORKERS";

#[test]
#[ignore = "requires strace and ptrace permission; run this focused gate explicitly"]
fn installed_polynomial_operations_create_only_owned_workers() {
    assert_owned_workers(
        "native-polynomial-threads",
        "polynomial_workload_child",
        WORKERS,
    );
}

#[test]
#[ignore = "requires strace and ptrace permission; run this focused gate explicitly"]
fn installed_resident_scaling_creates_only_owned_workers() {
    assert_owned_workers(
        "native-resident-threads",
        "resident_workload_child",
        RESIDENT_WORKERS,
    );
}

fn assert_owned_workers(stem: &str, child: &str, variable: &str) {
    let evidence = zkc_test_support::evidence(stem);
    for workers in [1, 4]
        .into_iter()
        .filter(|&n| cfg!(feature = "parallel") || n == 1)
    {
        let directory = evidence.nested(&format!("workers-{workers}"));
        let tasks = zkc_test_support::task_trace::test(
            directory.path(),
            child,
            &[
                (variable, workers.to_string()),
                ("RAYON_NUM_THREADS", "7".into()),
            ],
        );
        // The only non-owner task is libtest's runner thread. The mismatched
        // environment makes ambient Rayon initialization exceed this budget.
        assert_eq!(
            tasks,
            1 + if cfg!(feature = "parallel") {
                workers
            } else {
                0
            },
            "unowned tasks with {workers} workers"
        );
    }
}

fn call(cpu: &CpuExecution, name: &str, args: Vec<Value>) -> Value {
    let binding = OperationBinding {
        contract: name.into(),
        arguments: vec!["bn254.fr".into()],
        implementation: format!("arkworks/{name}"),
        physical_arguments: vec![],
    };
    installed(cpu, Policy::default(), binding, args)
}

fn installed(
    cpu: &CpuExecution,
    policy: Policy,
    binding: OperationBinding,
    args: Vec<Value>,
) -> Value {
    let backend = CpuBackend::new_with_cpu(
        policy,
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        SetupRegistry::new(vec![], &policy).unwrap(),
        cpu.clone(),
    )
    .unwrap();
    support::one(backend, binding, &[], args)
        .0
        .unwrap()
        .remove(0)
}

#[test]
#[ignore = "child entry point for the Linux thread-creation gate"]
fn resident_workload_child() {
    let Ok(workers) = std::env::var(RESIDENT_WORKERS) else {
        return;
    };
    let cpu = CpuExecution::new(workers.parse().unwrap()).unwrap();
    macro_rules! check {
        ($kernel:path, $provider:literal, $domain:literal, $group:ident, $bulk:ident,
         $points:ident, $scalars:ident, $scalar:ident) => {{
            use $kernel as kernel;
            const LEN: usize = 65; // Cross the existing 32-element worker grain.
            let point = kernel::$group::generator();
            let expected = point.add(&point);
            let points = Value::$points(Arc::new(
                kernel::$bulk::try_from_fn(LEN, |_| Ok(point)).unwrap(),
            ));
            let scalars = Value::$scalars(Arc::new(
                kernel::ScalarVector::try_from_fn(LEN, |_| Ok(kernel::Scalar::from(2))).unwrap(),
            ));
            for direct in [false, true] {
                let policy = Policy {
                    max_numerical_bytes: if direct {
                        256 + LEN * size_of::<kernel::$group>()
                    } else {
                        Policy::default().max_numerical_bytes
                    },
                    ..Policy::default()
                };
                for (name, args) in [
                    ("curve.scale_each", vec![scalars.clone(), points.clone()]),
                    (
                        "curve.vector_scale",
                        vec![points.clone(), Value::$scalar(kernel::Scalar::from(2))],
                    ),
                ] {
                    let binding = OperationBinding {
                        contract: name.into(),
                        arguments: vec![$domain.into()],
                        implementation: format!("{}/resident/{name}", $provider),
                        physical_arguments: vec![],
                    };
                    let Value::$points(result) = installed(&cpu, policy, binding, args) else {
                        panic!("changed resident provider or group");
                    };
                    assert_eq!(result.len(), LEN);
                    for index in 0..LEN {
                        assert_eq!(result.get(index).unwrap(), expected);
                    }
                }
            }
        }};
    }
    check!(
        zkc_kernels::blst::bls12_381,
        "blst",
        "bls12-381.g1",
        G1,
        G1Vector,
        BlstG1Vector,
        BlstVector,
        BlstField
    );
    check!(
        zkc_kernels::blst::bls12_381,
        "blst",
        "bls12-381.g2",
        G2,
        G2Vector,
        BlstG2Vector,
        BlstVector,
        BlstField
    );
    check!(
        zkc_kernels::halo2curves::bn254,
        "halo2curves-axiom",
        "bn254.g1",
        G1,
        G1Vector,
        HaloG1Vector,
        HaloVector,
        HaloField
    );
    check!(
        zkc_kernels::halo2curves::bn254,
        "halo2curves-axiom",
        "bn254.g2",
        G2,
        G2Vector,
        HaloG2Vector,
        HaloVector,
        HaloField
    );
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
