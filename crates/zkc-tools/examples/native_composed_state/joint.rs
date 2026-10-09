//! The same authored programs also use the ordinary interactive runner.
use super::{data, reference};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, Scalar, Value,
    services::ServiceRegistry,
};
use zkc_tools::run::*;
fn backend(role: &str, entry: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "composed", entry, None), None),
        Default::default(),
    )
    .unwrap()
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scenario {
    Honest,
    AlteredGroups,
    AlteredLastGroups,
    ShortGroups,
    MalformedGroups,
    ZeroChallenge,
    CountMismatch,
    WireLimit,
}
struct Audit {
    scenario: Scenario,
    received: usize,
}
impl Hooks<NativeBackend> for Audit {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        _: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        if exchange.site == "received" {
            self.received += 1;
            if self.received == 1 && self.scenario == Scenario::MalformedGroups {
                return Ok(Some(bytes[..bytes.len() - 1].to_vec()));
            }
            if self.received == 1 && self.scenario == Scenario::ShortGroups {
                let mut changed = bytes.to_vec();
                let count = u32::from_le_bytes(changed[6..10].try_into().unwrap());
                assert!(count > 0);
                changed[6..10].copy_from_slice(&(count - 1).to_le_bytes());
                changed.truncate(changed.len() - 48);
                return Ok(Some(changed));
            }
            if (self.received == 1 && self.scenario == Scenario::AlteredGroups)
                || (self.received == 2 && self.scenario == Scenario::AlteredLastGroups)
            {
                let mut changed = bytes.to_vec();
                // Keep canonical length and type, replace a valid group element.
                changed[10..58].copy_from_slice(&GroupPoint::identity().to_bytes().unwrap());
                return Ok(Some(changed));
            }
        }
        Ok(None)
    }
}
pub fn run(directory: &Path, family: &str, mode: &str) {
    let bytes = std::fs::read(directory.join(format!("{family}_{mode}.bundle"))).unwrap();
    let raw: Json = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(raw["format"], "zkc.run/1");
    let b = Bundle::admit(&bytes, &backend("P", family), BundleLimits::default()).unwrap();
    for format in ["invalid.run", ""] {
        let mut bad = raw.clone();
        bad["format"] = json!(format);
        assert!(
            Bundle::admit(
                &serde_json::to_vec(&bad).unwrap(),
                &backend("P", family),
                BundleLimits::default()
            )
            .is_err()
        );
    }
    let mut missing = raw.clone();
    let segment = missing["steps"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|step| step.get("loop").is_some())
        .unwrap();
    segment["body"].as_array_mut().unwrap().remove(0);
    assert!(
        Bundle::admit(
            &serde_json::to_vec(&missing).unwrap(),
            &backend("P", family),
            BundleLimits::default()
        )
        .is_err()
    );
    for scenario in [
        Scenario::Honest,
        Scenario::AlteredGroups,
        Scenario::AlteredLastGroups,
        Scenario::ShortGroups,
        Scenario::MalformedGroups,
        Scenario::ZeroChallenge,
        Scenario::CountMismatch,
        Scenario::WireLimit,
    ] {
        let (a, g) = data(if family == "fold" { 4 } else { 2 });
        let registry = ServiceRegistry::new(Policy::default());
        let coins = registry
            .issue_test_tape(
                "V",
                2,
                vec![
                    Scalar::from(2),
                    Scalar::from(if scenario == Scenario::ZeroChallenge {
                        0
                    } else {
                        5
                    }),
                ],
            )
            .unwrap();
        let mut p = backend("P", family);
        let rng = p
            .issue_test_tape(
                Domain::new("P", "composed", family, None),
                3,
                vec![Scalar::from(3), Scalar::from(7), Scalar::from(8)],
            )
            .unwrap();
        let v = backend("V", family)
            .with_services(
                registry.clone(),
                BTreeMap::from([(
                    b.roles()
                        .iter()
                        .find(|r| r.entry.role == "V")
                        .unwrap()
                        .entry
                        .services[0]
                        .name
                        .clone(),
                    coins.clone(),
                )]),
            )
            .unwrap();
        let inputs = vec![
            RoleInput {
                role: "P".into(),
                backend: p,
                values: vec![
                    Value::Index(2),
                    Value::Groups(g.clone().into()),
                    Value::Vector(a.clone().into()),
                    rng,
                ],
            },
            RoleInput {
                role: "V".into(),
                backend: v,
                values: vec![
                    Value::Index(if scenario == Scenario::CountMismatch {
                        1
                    } else {
                        2
                    }),
                    Value::Groups(g.clone().into()),
                    Value::Curve(reference::msm(&a, &g)),
                ],
            },
        ];
        let mut audit = Audit {
            scenario,
            received: 0,
        };
        let mut limits = RunLimits::default();
        if scenario == Scenario::WireLimit {
            limits.wire_bytes = 54;
        }
        let report = zkc_tools::run::run(&b, "composed", inputs, limits, &mut audit).unwrap();
        let observed = registry.observe(&coins).unwrap();
        assert!(!observed.leased);
        if scenario == Scenario::WireLimit {
            assert!(
                matches!(report.outcome, Outcome::DriverFailed(ref e) if e.kind == FailureKind::Limit)
            );
            assert_eq!(observed.state.as_ref().unwrap().draw_count, 1);
        } else if scenario == Scenario::CountMismatch {
            assert!(matches!(&report.outcome, Outcome::DriverFailed(f)
                if f.kind == FailureKind::Contract && f.detail.text == "loop-count-disagreement"));
            assert_eq!(audit.received, 0);
            assert_eq!(observed.state.as_ref().unwrap().draw_count, 0);
        } else if matches!(
            scenario,
            Scenario::AlteredGroups
                | Scenario::AlteredLastGroups
                | Scenario::ShortGroups
                | Scenario::MalformedGroups
        ) || (scenario == Scenario::ZeroChallenge && family == "fold")
        {
            assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
            assert_eq!(
                observed.state.as_ref().unwrap().draw_count,
                if matches!(
                    scenario,
                    Scenario::ZeroChallenge | Scenario::AlteredLastGroups
                ) {
                    2
                } else {
                    1
                }
            );
        } else {
            assert_eq!(
                report.outcome,
                Outcome::Completed,
                "{family}/{mode} {scenario:?}: {:?}",
                report.roles
            );
            assert!(matches!(
                report.roles.iter().find(|r| r.role == "V").unwrap().outputs[0],
                Value::Bool(true)
            ));
            assert_eq!(audit.received, 2);
            assert_eq!(observed.state.as_ref().unwrap().draw_count, 2);
        }
        if matches!(
            scenario,
            Scenario::AlteredGroups | Scenario::AlteredLastGroups | Scenario::ShortGroups
        ) || (scenario == Scenario::ZeroChallenge && family == "fold")
        {
            assert!(
                matches!(&report.roles[1].before, State::Stopped(stop)
                if matches!(&stop.cause, StopCause::Explicit(reason) if reason.text == "reject")),
                "{:?}",
                report.roles[1].before
            );
        }
        if scenario == Scenario::MalformedGroups {
            assert!(
                matches!(&report.roles[1].before, State::Stopped(stop) if matches!(stop.cause, StopCause::Decode(_)))
            );
        }
        assert!(
            report
                .backends
                .iter()
                .all(|(_, backend)| backend.active_frames() == 0)
        );
        for role in &report.roles {
            for state in [&role.before, &role.after] {
                if let State::Stopped(stop) = state {
                    assert!(stop.cleanup_errors.is_empty());
                }
            }
        }
    }
}
