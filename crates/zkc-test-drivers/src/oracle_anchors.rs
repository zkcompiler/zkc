//! Generated ordinary anchor stores: actual reference identity and checked lookup.
//! This exercises storage primitives, not complete oracle realization.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::host::joint::*;

fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "oracle_anchors", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn main() {
    let directory = std::env::args().nth(1).expect("anchor fixture directory");
    let bytes = std::fs::read(Path::new(&directory).join("anchors.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend(),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    let mut cases = 0;
    for (left, right, tag, instance, expected) in [
        (vec![11, 22], vec![33], 0, 0, Some(vec![11, 22])),
        (vec![11, 22], vec![33], 0, 1, Some(vec![33])),
        (vec![11], vec![11], 0, 0, Some(vec![11])),
        (vec![11], vec![11], 0, 1, Some(vec![11])),
        (vec![], vec![33], 0, 0, Some(vec![])),
        (vec![11], vec![], 0, 1, Some(vec![])),
        (vec![11], vec![33], 1, 0, None),
        (vec![11], vec![33], u64::MAX, 0, None),
        (vec![11], vec![33], 0, 2, None),
        (vec![11], vec![33], 0, u64::MAX, None),
    ] {
        let input = RoleInput {
            role: "P".to_owned(),
            backend: backend(),
            values: vec![
                Value::Indices(left.into()),
                Value::Indices(right.into()),
                Value::Index(tag),
                Value::Index(instance),
            ],
        };
        let report = run(
            &bundle,
            "oracle_anchors",
            vec![input],
            RunLimits::default(),
            &mut NoHooks,
        )
        .unwrap();
        match expected {
            Some(values) => {
                assert!(matches!(report.outcome, Outcome::Completed));
                let actual = &report.roles[0].outputs;
                assert_eq!(actual.len(), 4);
                assert!(matches!(&actual[0],Value::Index(n) if *n==values.len() as u64));
                assert!(matches!(&actual[1],Value::Indices(xs) if xs.as_ref()==values.as_slice()));
                assert!(matches!(&actual[2], Value::Index(0)));
                assert!(matches!(&actual[3], Value::Index(1)));
            }
            None => assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. })),
        }
        for (_, native) in &report.backends {
            assert_eq!(native.active_frames(), 0);
        }
        cases += 1;
    }
    println!("{cases} native anchor allocation/reference controls passed");
}
