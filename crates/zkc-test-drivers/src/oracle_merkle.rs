//! Native execution of checked Merkle helpers, including layout and hostile wire
//! values. This is primitive evidence, not whole oracle-realization simulation.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, KoalaBear, KoalaBearExt4, Policy, Value};
use zkc_runtime::host::joint::*;

fn backend(role: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "oracle_merkle", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn load(directory: &Path, name: &str) -> Bundle {
    Bundle::admit(
        &std::fs::read(directory.join(name)).unwrap(),
        &backend("V"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap()
}
#[derive(Default)]
struct Messages {
    tamper: &'static str,
    sites: Vec<String>,
}
impl Hooks<CpuBackend> for Messages {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        self.sites.push(exchange.site.to_owned());
        if exchange.site == self.tamper {
            let mut changed = bytes.to_vec();
            *changed.last_mut().unwrap() ^= 1;
            Ok(Some(changed))
        } else {
            Ok(None)
        }
    }
}
fn execute(
    bundle: &Bundle,
    values: Vec<(&str, Vec<Value>)>,
    hooks: &mut Messages,
) -> Report<CpuBackend> {
    let inputs = values
        .into_iter()
        .map(|(role, values)| RoleInput {
            role: role.to_owned(),
            backend: backend(role),
            values,
        })
        .collect();
    let report = run(bundle, "oracle_merkle", inputs, RunLimits::default(), hooks).unwrap();
    for (_, native) in &report.backends {
        assert_eq!(native.active_frames(), 0);
    }
    report
}
fn scalar(n: u64) -> KoalaBearExt4 {
    KoalaBearExt4::from([n as u32 + 11, 3, n as u32 + 17, 7].map(KoalaBear::new))
}
fn mapped(n: u64, q: u64, paired: bool, reversed: bool) -> [u64; 3] {
    let height = n / if paired { 2 } else { 1 };
    let logical = q % height;
    let bits = height.trailing_zeros();
    let leaf = if reversed && bits != 0 {
        logical.reverse_bits() >> (64 - bits)
    } else {
        logical
    };
    [height, leaf, q / height]
}
fn main() {
    let directory = std::env::args().nth(1).expect("Merkle fixtures directory");
    let directory = Path::new(&directory);
    let mut cases = 0;
    for paired in [false, true] {
        for reversed in [false, true] {
            let name = format!("{}-{}", u8::from(paired), u8::from(reversed));
            let positions = load(directory, &format!("positions-{name}.bundle"));
            for power in u32::from(paired)..64 {
                let n = 1u64 << power;
                for q in [0, n / 2, n - 1] {
                    let report = execute(
                        &positions,
                        vec![("V", vec![Value::Index(n), Value::Index(q)])],
                        &mut Messages::default(),
                    );
                    assert!(
                        matches!(report.outcome, Outcome::Completed),
                        "{name} {n}/{q}: {:?}",
                        report.outcome
                    );
                    let expected = mapped(n, q, paired, reversed);
                    assert_eq!(report.roles[0].outputs.len(), 3);
                    for (value, expected) in report.roles[0].outputs.iter().zip(expected) {
                        assert!(matches!(value, Value::Index(actual) if *actual == expected));
                    }
                    cases += 1;
                }
            }
            for (n, q) in [
                (0, 0),
                (3, 0),
                (6, 1),
                (10, 9),
                (8, 8),
                (8, u64::MAX),
                (u64::MAX, 0),
            ] {
                let report = execute(
                    &positions,
                    vec![("V", vec![Value::Index(n), Value::Index(q)])],
                    &mut Messages::default(),
                );
                assert!(
                    matches!(report.outcome, Outcome::ParticipantStopped { .. }),
                    "{name} {n}/{q}"
                );
                cases += 1;
            }
            if paired {
                let report = execute(
                    &positions,
                    vec![("V", vec![Value::Index(1), Value::Index(0)])],
                    &mut Messages::default(),
                );
                assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
                cases += 1;
            }
            let merkle = load(directory, &format!("merkle-{name}.bundle"));
            let mut trial = |length: u64,
                             rows: u64,
                             query: u64,
                             received_rows: u64,
                             received_query: u64,
                             tamper,
                             complete: bool| {
                let mut messages = Messages {
                    tamper,
                    ..Default::default()
                };
                let report = execute(
                    &merkle,
                    vec![
                        (
                            "P",
                            vec![
                                Value::KoalaBearExt4Vector(
                                    (0..length).map(scalar).collect::<Vec<_>>().into(),
                                ),
                                Value::Index(rows),
                                Value::Index(query),
                            ],
                        ),
                        (
                            "V",
                            vec![Value::Index(received_rows), Value::Index(received_query)],
                        ),
                    ],
                    &mut messages,
                );
                assert_eq!(
                    matches!(report.outcome, Outcome::Completed),
                    complete,
                    "{name} {length}/{rows}/{query}/{received_rows}/{received_query}/{tamper}: {:?}",
                    report.outcome
                );
                if !complete {
                    let receiver = report.roles.iter().find(|role| role.role == "V").unwrap();
                    assert!(
                        receiver.outputs.is_empty(),
                        "failed authentication returned an answer"
                    );
                    assert!(
                        matches!(report.outcome, Outcome::ParticipantStopped { .. }),
                        "unexpected refusal: {name}/{tamper}: {:?}",
                        report.outcome
                    );
                }
                if complete {
                    let outputs = &report.roles.iter().find(|r| r.role == "V").unwrap().outputs;
                    assert_eq!(outputs.len(), 1);
                    assert!(
                        matches!(outputs[0], Value::KoalaBearExt4Field(value) if value == scalar(received_query))
                    );
                    assert_eq!(messages.sites, ["root", "row", "proof"]);
                }
                cases += 1;
            };
            for power in u32::from(paired)..=4 {
                let rows = 1u64 << power;
                for query in 0..rows {
                    trial(rows, rows, query, rows, query, "", true);
                    if rows > 2 {
                        trial(rows, rows, query, rows, (query + 1) % rows, "", false);
                    }
                    if paired {
                        // A complete antipodal row authenticates both of its
                        // logical slots; changing only the slot remains valid.
                        trial(rows, rows, query, rows, (query + rows / 2) % rows, "", true);
                    }
                }
            }
            for target in ["root", "row", "proof"] {
                trial(8, 8, 2, 8, 2, target, false);
            }
            for (length, rows, q, vr, vq) in [
                (7, 8, 0, 8, 0),
                (9, 8, 0, 8, 0),
                (0, 0, 0, 0, 0),
                (6, 6, 0, 6, 0),
                (8, 8, 8, 8, 0),
                (8, 8, 2, 4, 2),
                (8, 8, 2, 16, 2),
                (8, 8, 2, 8, 8),
            ] {
                trial(length, rows, q, vr, vq, "", false);
            }
        }
    }
    println!("{cases} native Merkle layout, opening and hostile-wire controls passed");
}
