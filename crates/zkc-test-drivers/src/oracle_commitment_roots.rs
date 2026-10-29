//! Common oracle roots use the selected scheme and preserve receiver shape custody.
use std::path::Path;
use zkc_cpu::merkle::Scheme;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, KoalaBear, KoalaBearExt4, Policy, Value};
use zkc_kernels::plonky3::{
    merkle::{commit, poseidon2::Quartic},
    oracle::Shape,
};
use zkc_runtime::host::joint::*;

fn backend(role: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "oracle_roots", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn scalar(n: u64) -> KoalaBearExt4 {
    KoalaBearExt4::from([n as u32 + 11, 3, n as u32 + 17, 7].map(KoalaBear::new))
}
#[derive(Default)]
struct Messages {
    values: Vec<Vec<u8>>,
}
impl Hooks<CpuBackend> for Messages {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        assert_eq!((exchange.sender, exchange.receiver), ("P", "V"));
        self.values.push(bytes.to_vec());
        Ok(None)
    }
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("common root fixtures directory");
    let directory = Path::new(&directory);
    let mut cases = 0;
    for input in [false, true] {
        for fixed in [false, true] {
            let name = format!(
                "root-{}-{}",
                if input { "input" } else { "send" },
                if fixed { "fixed" } else { "dynamic" }
            );
            let bundle = Bundle::admit(
                &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
                &backend("V"),
                zkc_cpu::cpu_contracts(),
                BundleLimits::default(),
            )
            .unwrap();
            let mut trial = |length: u64, holder_rows: u64, receiver_rows: u64, complete: bool| {
                let mut holder = vec![Value::KoalaBearExt4Vector(
                    (0..length).map(scalar).collect::<Vec<_>>().into(),
                )];
                let mut receiver = vec![];
                if input {
                    // Canonical but unrelated root: construction must not infer
                    // its height or impose equality with the holder's Data.
                    receiver.push(Value::MerkleDigest(
                        Scheme::Poseidon2KoalaBearExt4,
                        vec![0; 32].into(),
                    ));
                    if !fixed {
                        receiver.push(Value::Index(receiver_rows));
                    }
                } else {
                    holder.push(Value::Index(holder_rows));
                    receiver.push(Value::Index(receiver_rows));
                }
                let mut messages = Messages::default();
                let report = run(
                    &bundle,
                    "oracle_roots",
                    vec![
                        RoleInput {
                            role: "P".into(),
                            backend: backend("P"),
                            values: holder,
                        },
                        RoleInput {
                            role: "V".into(),
                            backend: backend("V"),
                            values: receiver,
                        },
                    ],
                    RunLimits::default(),
                    &mut messages,
                )
                .unwrap();
                for (_, native) in &report.backends {
                    assert_eq!(native.active_frames(), 0);
                }
                assert_eq!(
                    matches!(report.outcome, Outcome::Completed),
                    complete,
                    "{name}/{length}/{holder_rows}/{receiver_rows}: {:?}",
                    report.outcome
                );
                let verifier = report.roles.iter().find(|r| r.role == "V").unwrap();
                if complete {
                    assert_eq!(verifier.outputs.len(), 1);
                    let expected_rows = if fixed { 8 } else { receiver_rows };
                    assert!(
                        matches!(verifier.outputs[0], Value::Index(rows) if rows == expected_rows)
                    );
                    assert_eq!(messages.values.len(), usize::from(!input));
                    if !input {
                        // Independently arrange antipodal pairs, then use the
                        // kernel API to check the compiler-generated delivery.
                        let arranged = (0..length / 2)
                            .flat_map(|i| [scalar(i), scalar(i + length / 2)])
                            .collect();
                        let (root, _) = commit::<Quartic>(
                            arranged,
                            Shape::new(2, length as usize / 2, 64).unwrap(),
                            1 << 20,
                        )
                        .unwrap();
                        let expected = backend("V")
                            .encode_native_value(&Value::MerkleDigest(
                                Scheme::Poseidon2KoalaBearExt4,
                                root.into(),
                            ))
                            .unwrap();
                        assert_eq!(messages.values[0], expected);
                    }
                } else {
                    assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                    assert!(verifier.outputs.is_empty());
                }
                cases += 1;
            };
            for rows in [2, 4, 8, 16] {
                trial(rows, rows, rows, !fixed || rows == 8);
            }
            for rows in [0, 1, 3, 6, 32] {
                trial(rows, rows, rows, false);
            }
            for rows in [0, 1, 3, 6, 32] {
                if !input || !fixed {
                    trial(8, 8, rows, false);
                }
            }
            if !fixed {
                trial(8, 8, 4, true);
            }
            if !input {
                trial(8, 4, 8, false);
                trial(8, 16, 8, false);
            }
        }
    }
    println!("{cases} native selected-root, shape-custody and refusal controls passed");
}
