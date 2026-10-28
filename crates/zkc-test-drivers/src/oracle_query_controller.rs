//! Execute generated ordinary continuations, including recurrent and mixed-kind
//! anchors. This is a controller test, not a complete source realization check.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Sequence, Value};
use zkc_runtime::host::joint::*;

fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("V", "oracle_query_controller", "main", None),
            None,
        ),
        Default::default(),
    )
    .unwrap()
}
#[derive(Default)]
struct Prefix(Vec<Vec<u8>>);
impl Hooks<CpuBackend> for Prefix {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert_eq!(exchange.site, "opening");
        assert!(bytes.len() <= limit);
        self.0.push(bytes.to_vec());
        Ok(None)
    }
}
struct Reference {
    variant: u64,
    lengths: [u64; 2],
    rows: u64,
    mapped: u64,
}
impl Reference {
    fn query(&self, constructor: u64, instance: u64, position: u64, root: bool) -> Option<u64> {
        let Self {
            variant,
            lengths,
            rows,
            mapped,
        } = *self;
        match constructor {
            0 | 1 if instance == 0 => {
                if (root && variant == 2 && constructor == 1)
                    || position >= lengths[constructor as usize]
                {
                    None
                } else {
                    Some(10 * (constructor + 1) + position)
                }
            }
            2 if instance < 3 && position < rows => {
                if variant == 1 {
                    return Some(9);
                }
                let (child, index) = if instance == 0 {
                    (0, 0)
                } else {
                    (2, instance - 1)
                };
                let first = self.query(child, index, position, false)?;
                self.query(1, 0, mapped, false)?;
                Some(first)
            }
            _ => None,
        }
    }
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("controller fixture directory");
    let mut cases = 0;
    for variant in 0..3 {
        let bytes =
            std::fs::read(Path::new(&directory).join(format!("controller-{variant}.bundle")))
                .unwrap();
        let bundle = Bundle::admit(
            &bytes,
            &backend(),
            zkc_cpu::cpu_contracts(),
            BundleLimits::default(),
        )
        .unwrap();
        for lengths in [[0, 0], [4, 4], [4, 1], [1, 4]] {
            for rows in [0, 4] {
                for position in [0, 1, 3, 4] {
                    for mapped in [0, 1, 4] {
                        for (constructor, instance) in
                            [(0, 0), (1, 0), (2, 0), (2, 2), (2, 3), (3, 0)]
                        {
                            let left = Value::Indices(
                                (0..lengths[0]).map(|i| 10 + i).collect::<Vec<_>>().into(),
                            );
                            let right = if variant == 2 {
                                let ty = zkc_cpu::cpu_contracts()
                                    .physical_type("sequence<bool>@logical.sequence/0")
                                    .unwrap();
                                Value::Sequence(
                                    Sequence::new(
                                        ty,
                                        (0..lengths[1]).map(|i| Value::Bool(i % 2 == 0)).collect(),
                                        &Policy::default(),
                                    )
                                    .unwrap(),
                                )
                            } else {
                                Value::Indices(
                                    (0..lengths[1]).map(|i| 20 + i).collect::<Vec<_>>().into(),
                                )
                            };
                            let report = run(
                                &bundle,
                                "oracle_query_controller",
                                vec![RoleInput {
                                    role: "V".to_owned(),
                                    backend: backend(),
                                    values: vec![
                                        left,
                                        right,
                                        Value::Index(rows),
                                        Value::Index(mapped),
                                        Value::Index(constructor),
                                        Value::Index(instance),
                                        Value::Index(position),
                                    ],
                                }],
                                RunLimits::default(),
                                &mut NoHooks,
                            )
                            .unwrap();
                            let wanted = Reference {
                                variant,
                                lengths,
                                rows,
                                mapped,
                            }
                            .query(
                                constructor,
                                instance,
                                position,
                                true,
                            );
                            let label = format!(
                                "{variant}/{lengths:?}/{rows}/{mapped}/{constructor}:{instance}/{position}"
                            );
                            match wanted {
                                Some(answer) => {
                                    assert!(
                                        matches!(report.outcome, Outcome::Completed),
                                        "{label}: {:?}",
                                        report.outcome
                                    );
                                    assert_eq!(report.roles[0].outputs.len(), 1);
                                    assert!(
                                        matches!(&report.roles[0].outputs[0], Value::Index(x) if *x == answer),
                                        "{label}"
                                    );
                                }
                                None => {
                                    assert!(
                                        matches!(
                                            report.outcome,
                                            Outcome::ParticipantStopped { .. }
                                        ),
                                        "{label}: {:?}",
                                        report.outcome
                                    );
                                    assert!(
                                        !format!("{:?}", report.outcome).contains("exhausted"),
                                        "resource exhaustion substituted for domain stop: {label}"
                                    );
                                }
                            }
                            for (_, native) in &report.backends {
                                assert_eq!(native.active_frames(), 0, "{label}");
                            }
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    let bytes = std::fs::read(Path::new(&directory).join("controller-3.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend(),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    for mutation in 0..6 {
        let mut checkpoint = vec![Value::Index(0); 5];
        if mutation < 5 {
            checkpoint[mutation] = Value::Index(1);
        }
        let mut values = vec![
            Value::Indices(vec![10, 11, 12, 13].into()),
            Value::Indices(vec![20, 21, 22, 23].into()),
            Value::Index(4),
            Value::Index(0),
            Value::Index(0),
            Value::Index(0),
            Value::Index(0),
        ];
        values.extend(checkpoint);
        values.push(Value::Index(37));
        let report = run(
            &bundle,
            "oracle_query_controller",
            vec![RoleInput {
                role: "V".to_owned(),
                backend: backend(),
                values,
            }],
            RunLimits::default(),
            &mut NoHooks,
        )
        .unwrap();
        if mutation == 5 {
            assert!(
                matches!(report.outcome, Outcome::Completed),
                "resume: {:?}",
                report.outcome
            );
            assert!(matches!(&report.roles[0].outputs[0], Value::Index(37)));
        } else {
            assert!(
                matches!(report.outcome, Outcome::ParticipantStopped { .. }),
                "wrong coordinate {mutation} resumed"
            );
        }
        for (_, native) in &report.backends {
            assert_eq!(native.active_frames(), 0);
        }
        cases += 1;
    }
    let bytes = std::fs::read(Path::new(&directory).join("controller-4.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend(),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    for length in [0, 4] {
        for rows in [0, 2, 4] {
            for mapped in [0, 2, 4] {
                for position in [0, 2, 4] {
                    for instance in [0, 2] {
                        let input = vec![
                            Value::Indices((0..length).map(|i| 10 + i).collect::<Vec<_>>().into()),
                            Value::Indices(vec![20, 21, 22, 23].into()),
                            Value::Index(rows),
                            Value::Index(mapped),
                            Value::Index(3),
                            Value::Index(instance),
                            Value::Index(position),
                            Value::Index(10 + position),
                        ];
                        let inputs = bundle
                            .roles()
                            .iter()
                            .map(|role| {
                                let owner = &role.entry.role;
                                let native = CpuBackend::new(
                                    Policy::default(),
                                    EntryPolicy::new(
                                        Domain::new(owner, "oracle_query_controller", "main", None),
                                        None,
                                    ),
                                    Default::default(),
                                )
                                .unwrap();
                                RoleInput {
                                    role: owner.clone(),
                                    backend: native,
                                    values: if owner == "V" { input.clone() } else { vec![] },
                                }
                            })
                            .collect();
                        let mut prefix = Prefix::default();
                        let report = run(
                            &bundle,
                            "oracle_query_controller",
                            inputs,
                            RunLimits::default(),
                            &mut prefix,
                        )
                        .unwrap();
                        let first = position < 4 && position < length;
                        let complete = first && mapped < rows;
                        let label =
                            format!("prefix/{length}/{rows}/{mapped}/{position}/{instance}");
                        assert_eq!(
                            matches!(report.outcome, Outcome::Completed),
                            complete,
                            "{label}: {:?}",
                            report.outcome
                        );
                        if !complete {
                            assert!(
                                matches!(report.outcome, Outcome::ParticipantStopped { .. }),
                                "{label}"
                            );
                            assert!(
                                !format!("{:?}", report.outcome).contains("exhausted"),
                                "resource exhaustion substituted for domain stop: {label}"
                            );
                        }
                        assert_eq!(prefix.0.len(), usize::from(first), "{label}");
                        if first {
                            let expected =
                                [b"ZKCV\x00\x1f".as_slice(), &u64::to_le_bytes(position)].concat();
                            assert_eq!(prefix.0[0], expected, "{label}");
                        }
                        if complete {
                            let verifier =
                                report.roles.iter().find(|role| role.role == "V").unwrap();
                            assert!(
                                matches!(&verifier.outputs[0], Value::Index(x) if *x == 10 + position),
                                "{label}"
                            );
                        }
                        for (_, native) in &report.backends {
                            assert_eq!(native.active_frames(), 0, "{label}");
                        }
                        cases += 1;
                    }
                }
            }
        }
    }
    println!("{cases} native oracle continuation controls passed");
}
