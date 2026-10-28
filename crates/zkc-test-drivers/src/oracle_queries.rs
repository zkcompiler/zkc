//! Execute generated read primitives with the installed VM and real wire hooks.
//! This tests primitives and their stop prefix, not complete oracle realization.
use std::path::Path;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_runtime::host::joint::*;

fn backend(role: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "oracle_queries", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
#[derive(Default)]
struct Messages(Vec<(String, Vec<u8>)>);
impl Hooks<CpuBackend> for Messages {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        limit: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        assert!(bytes.len() <= limit);
        self.0.push((exchange.site.to_owned(), bytes.to_vec()));
        Ok(None)
    }
}
fn main() {
    let directory = std::env::args().nth(1).expect("query fixture directory");
    let bytes = std::fs::read(Path::new(&directory).join("ordered.bundle")).unwrap();
    let bundle = Bundle::admit(
        &bytes,
        &backend("V"),
        zkc_cpu::cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap();
    let mut cases = 0;
    for (data, rows, first, second, expected, complete) in [
        (vec![11, 22, 33], 3, 0, 2, vec![11, 33], true),
        (vec![11, 22, 33], 3, 1, 1, vec![22, 22], true),
        (vec![11, 22, 33], 2, 0, 2, vec![11], false),
        (vec![11, 22, 33], 2, 2, 0, vec![], false),
        (vec![11, 22, 33], 0, 0, 0, vec![], false),
        (vec![], 0, 0, 0, vec![], false),
        (vec![11], 1, 0, u64::MAX, vec![11], false),
    ] {
        let inputs = bundle
            .roles()
            .iter()
            .map(|role| {
                let name = &role.entry.role;
                RoleInput {
                    role: name.clone(),
                    backend: backend(name),
                    values: if name == "V" {
                        vec![
                            Value::Indices(data.clone().into()),
                            Value::Index(rows),
                            Value::Index(first),
                            Value::Index(second),
                        ]
                    } else {
                        vec![]
                    },
                }
            })
            .collect();
        let mut observed = Messages::default();
        let report = run(
            &bundle,
            "oracle_queries",
            inputs,
            RunLimits::default(),
            &mut observed,
        )
        .unwrap();
        assert_eq!(
            matches!(report.outcome, Outcome::Completed),
            complete,
            "{rows}/{first}/{second}"
        );
        if !complete {
            assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
        }
        assert_eq!(observed.0.len(), expected.len());
        for (i, ((site, bytes), answer)) in observed.0.iter().zip(expected).enumerate() {
            assert_eq!(site, &format!("answer_{i}"));
            let wire = [b"ZKCV\x00\x1f".as_slice(), &u64::to_le_bytes(answer)].concat();
            assert_eq!(*bytes, wire);
        }
        if complete {
            let observer = report.roles.iter().find(|r| r.role == "Observer").unwrap();
            assert_eq!(observer.outputs.len(), 2);
            assert!(matches!(&observer.outputs[0], Value::Index(x) if *x == data[first as usize]));
            assert!(matches!(&observer.outputs[1], Value::Index(x) if *x == data[second as usize]));
        }
        for (_, native) in &report.backends {
            assert_eq!(native.active_frames(), 0);
        }
        cases += 1;
    }
    println!("{cases} native oracle query domain/prefix controls passed");
}
