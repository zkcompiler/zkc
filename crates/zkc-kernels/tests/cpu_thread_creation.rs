//! Explicit Linux execution gate, separate from portable correctness tests.
//! Count successful task creation over each child's entire life, so a private
//! pool cannot disappear between samples. No production instrumentation is used.
#![cfg(target_os = "linux")]

use std::path::Path;
use zkc_kernels::cpu::CpuExecution;

#[path = "support/cpu_workloads.rs"]
mod cpu_workloads;

const WORKERS: &str = "ZKC_CPU_CONFINEMENT_WORKERS";
const CALLERS: &str = "ZKC_CPU_CONFINEMENT_CALLERS";
const EXTRA_POOL: &str = "ZKC_CPU_CONFINEMENT_EXTRA_POOL";

#[test]
#[ignore = "requires strace and ptrace permission; run this focused gate explicitly"]
fn provider_workloads_create_only_owned_workers() {
    let evidence = zkc_test_support::evidence("cpu-thread-creation");
    for (workers, callers) in [(1, 1), (1, 2), (4, 1), (4, 2)] {
        let tasks = trace_child(evidence.path(), workers, callers, false);
        // One libtest runner thread, the owner's workers, and known callers.
        let budget = 1 + workers + callers;
        assert_eq!(
            tasks, budget,
            "unowned tasks: workers={workers}, callers={callers}"
        );
    }
    // Sensitivity control: one deliberately short-lived Rayon pool must exceed
    // the exact same budget even if it exits before the child returns.
    let tasks = trace_child(evidence.path(), 1, 2, true);
    assert_eq!(
        tasks,
        1 + 1 + 2 + 1,
        "the tracer missed the extra private worker"
    );
}

fn trace_child(directory: &Path, workers: usize, callers: usize, extra_pool: bool) -> usize {
    let name = format!("workers-{workers}-callers-{callers}-extra-{extra_pool}");
    let directory = directory.join(name);
    std::fs::create_dir_all(&directory).unwrap();
    zkc_test_support::task_trace::test(
        &directory,
        "provider_workload_child",
        &[
            (WORKERS, workers.to_string()),
            (CALLERS, callers.to_string()),
            (EXTRA_POOL, if extra_pool { "1" } else { "0" }.into()),
            ("RAYON_NUM_THREADS", "7".into()),
        ],
    )
}

#[test]
#[ignore = "child entry point for the Linux thread-creation gate"]
fn provider_workload_child() {
    // An explicit test filter without the parent environment does no work.
    let Ok(workers) = std::env::var(WORKERS) else {
        return;
    };
    let workers: usize = workers.parse().unwrap();
    let callers: usize = std::env::var(CALLERS).unwrap().parse().unwrap();
    let cpu = CpuExecution::new(workers).unwrap();
    let pcs = cpu_workloads::PcsFixture::new(&cpu);
    let expected = cpu.enter(|| pcs.check());
    let barrier = std::sync::Barrier::new(callers);
    std::thread::scope(|scope| {
        for _ in 0..callers {
            let cpu = cpu.clone();
            let (pcs, expected, barrier) = (&pcs, &expected, &barrier);
            scope.spawn(move || {
                barrier.wait();
                cpu.enter(|| {
                    for _ in 0..2 {
                        cpu_workloads::full_width_msms();
                        assert_eq!(&pcs.check(), expected);
                    }
                });
            });
        }
    });
    if std::env::var(EXTRA_POOL).unwrap() == "1" {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        pool.broadcast(|_| ());
        drop(pool);
    }
}
