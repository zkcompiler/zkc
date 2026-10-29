//! Execute generated virtual position/answer functions as ordinary mathematics.
//! Query execution and continuation control are checked separately.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::host::joint::*;

fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("V", "oracle_virtual_functions", "main", None),
            None,
        ),
        Default::default(),
    )
    .unwrap()
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("virtual function fixture directory");
    let bytes = std::fs::read(Path::new(&directory).join("virtual-functions.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend(),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    let mut cases = 0;
    for (parameter, position) in [(0, 0), (0, u64::MAX), (u64::MAX, 0), (7, 13)] {
        for (left, right) in [(false, false), (false, true), (true, false), (true, true)] {
            for choice in [false, true] {
                let input = RoleInput {
                    role: "V".to_owned(),
                    backend: backend(),
                    values: vec![
                        Value::Index(parameter),
                        Value::Bool(choice),
                        Value::Index(position),
                        Value::Bool(left),
                        Value::Bool(right),
                    ],
                };
                let report = run(
                    &bundle,
                    "oracle_virtual_functions",
                    vec![input],
                    RunLimits::default(),
                    &mut NoHooks,
                )
                .unwrap();
                assert!(matches!(report.outcome, Outcome::Completed));
                let actual = &report.roles[0].outputs;
                assert_eq!(actual.len(), 3);
                assert!(matches!(&actual[0], Value::Index(n) if *n == position));
                assert!(matches!(&actual[1], Value::Index(n) if *n == parameter));
                assert!(
                    matches!(&actual[2], Value::Bool(b) if *b == if choice { left } else { right })
                );
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0);
                }
                cases += 1;
            }
        }
    }
    println!("{cases} native virtual position/answer function controls passed");
}
