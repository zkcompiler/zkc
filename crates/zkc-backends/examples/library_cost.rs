//! Fixed-selection runtime overhead experiment, not a protocol benchmark.
//! ZKC_COMPILER_BIN=/path/to/compiler/bin cargo run --release -p zkc-backends --example library_cost
use std::{hint::black_box, path::PathBuf, process::Command, sync::Arc, time::Instant};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Scalar, Value};
use zkc_runtime::interactive::{Action, Admitted, Runner, admit_supplied};

fn backend(policy: Policy) -> NativeBackend {
    NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("P", "bench", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
fn execute(
    program: &Admitted,
    policy: Policy,
    table: &Arc<zkc_arkworks::Table>,
    r: Scalar,
) -> Arc<zkc_arkworks::Table> {
    let mut runner = Runner::new(
        program,
        "main",
        "P",
        "bench",
        backend(policy),
        vec![Value::Table(table.clone()), Value::Field(r)],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Local(action) = runner.poll() else {
        panic!("expected local")
    };
    runner.execute_local(&action.cut).unwrap();
    let Action::Returned(values) = runner.poll() else {
        panic!("execution stopped")
    };
    let [Value::Table(output)] = values.as_slice() else {
        panic!("invalid result")
    };
    output.clone()
}
fn direct(
    msb: bool,
    table: &zkc_arkworks::Table,
    r: Scalar,
    policy: Policy,
) -> zkc_arkworks::Table {
    if msb {
        zkc_arkworks::MsbTable::from_lsb(table, &policy.ark_bounds())
            .unwrap()
            .restrict_first(r)
            .unwrap()
            .to_lsb(&policy.ark_bounds())
            .unwrap()
    } else {
        table.restrict_first(r).unwrap()
    }
}
fn median_ns<T>(iterations: usize, mut f: impl FnMut() -> T) -> u128 {
    for _ in 0..3 {
        black_box(f());
    }
    let mut times = Vec::new();
    for _ in 0..7 {
        let start = Instant::now();
        for _ in 0..iterations {
            black_box(f());
        }
        times.push(start.elapsed().as_nanos() / iterations as u128);
    }
    times.sort();
    times[times.len() / 2]
}
fn main() {
    let compiler = zkc_test_support::compiler();
    let policy = Policy::default();
    let mut rows = Vec::new();
    for msb in [false, true] {
        let implementation = if msb {
            "arkworks-msb/poly.fold"
        } else {
            "arkworks/poly.fold"
        };
        let source = format!(
            r#"module {{
  fn Fold<F: Field>(a: table:F, r: field:F) -> (table:F) requires (CommRing(F)) {{
    [fold] (out) = poly.fold<F>(a, r); return (out);
  }}
  configure Chosen = Fold(F = bls12-381.fr) using (fold = "{implementation}");
  protocol FoldOnce {{
    roles (P); inputs (P a: table:bls12-381.fr, P r: field:bls12-381.fr);
    outputs (P table:bls12-381.fr);
    local [fold] P: (out) = Chosen(a, r); return (out);
  }}
  instance concrete: FoldOnce {{ roles (P = P); }} entry main = concrete;
}}"#
        );
        let path: PathBuf =
            std::env::temp_dir().join(format!("zkc-library-cost-{}-{msb}.pir", std::process::id()));
        std::fs::write(&path, source).unwrap();
        let start = Instant::now();
        let output = Command::new(&compiler)
            .arg("protocol-compile")
            .arg(&path)
            .output()
            .unwrap();
        let compile_ns = start.elapsed().as_nanos();
        std::fs::remove_file(&path).unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let start = Instant::now();
        let admitted = admit_supplied(&output.stdout, &backend(policy)).unwrap();
        let admission_ns = start.elapsed().as_nanos();
        for rank in [1u32, 6, 10, 14] {
            let values: Vec<_> = (0..1u64 << rank)
                .map(|i| Scalar::from((i * i + 3 * i + 11) % 1009))
                .collect();
            let table =
                Arc::new(zkc_arkworks::Table::from_logical(&values, &policy.ark_bounds()).unwrap());
            let r = Scalar::from(7);
            let half = values.len() / 2;
            let expected: Vec<_> = (0..half)
                .map(|i| values[i] + r * (values[i + half] - values[i]))
                .collect();
            assert_eq!(
                direct(msb, &table, r, policy).logical_values().unwrap(),
                expected
            );
            assert_eq!(
                execute(&admitted, policy, &table, r)
                    .logical_values()
                    .unwrap(),
                expected
            );
            let iterations = if rank < 10 { 200 } else { 30 };
            let direct_ns = median_ns(iterations, || direct(msb, &table, r, policy));
            let runtime_ns = median_ns(iterations, || execute(&admitted, policy, &table, r));
            rows.push(
                serde_json::json!({"implementation": implementation, "rank": rank,
                "iterations_per_sample": iterations, "samples": 7, "direct_ns": direct_ns,
                "runtime_ns": runtime_ns, "compile_process_ns": compile_ns,
                "admission_ns": admission_ns, "candidate_bytes": output.stdout.len(),
                "conversions": if msb { 2 } else { 0 }}),
            );
        }
    }
    println!("{}", serde_json::to_string_pretty(&serde_json::json!({
        "format": "zkc.library-cost/1", "baseline": "direct identical selected Arkworks kernel sequence",
        "scope": "one local fold; runtime includes runner creation, validation, frames and cleanup; no Lean checker; no protocol security/performance claim",
        "rows": rows
    })).unwrap());
}
