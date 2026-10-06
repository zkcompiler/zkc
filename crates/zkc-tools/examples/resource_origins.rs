//! Execute fresh compiler carriers through the shared participant interpreter.
//! Resource counts are derived from the authored loops, not the exported plan.
use std::path::Path;
use zkc_backends::{Capability, Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
use zkc_runtime::interactive::PathElement;
use zkc_tools::protocol::run::*;

fn domain() -> Domain {
    Domain::new("P", "origins", "main", None)
}
fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(domain(), None, PublicInputs::LocalOnly),
        None,
    )
    .unwrap()
}
fn token(value: &Value) -> &Capability {
    match value {
        Value::Rng(token) | Value::Transcript(token) => token,
        _ => panic!("expected affine resource"),
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Return,
    Stop,
    StopAfter,
    StopZero,
    Cancel,
    RngFailure,
    TranscriptFailure,
}
struct Audit {
    cancel: bool,
    roots: Vec<Capability>,
    before: Vec<zkc_backends::CapabilityObservation>,
    after: Vec<zkc_backends::CapabilityObservation>,
}
impl Hooks<NativeBackend> for Audit {
    fn cancel_before(&mut self, _: usize, _: &Step, path: &[PathElement]) -> Option<String> {
        if self.cancel
            && path
                .iter()
                .any(|p| matches!(p, PathElement::Loop { site, iteration: 1 } if site == "outer"))
        {
            Some("cancel after the first completed outer iteration".into())
        } else {
            None
        }
    }
    fn observe(
        &mut self,
        _: &str,
        backend: &NativeBackend,
        phase: Phase,
    ) -> Result<Option<String>, String> {
        let observations = self
            .roots
            .iter()
            .map(|r| backend.observe(r).unwrap())
            .collect();
        match phase {
            Phase::BeforeCancellation => self.before = observations,
            Phase::AfterCancellation => {
                assert_eq!(backend.active_frames(), 0);
                self.after = observations;
            }
        }
        Ok(None)
    }
}
fn execute(directory: &Path, suffix: &str, mode: Mode, outer: u64, inner: u64, go: bool) {
    let name = match mode {
        Mode::Stop => "stop",
        Mode::StopAfter | Mode::StopZero => "nested_stop",
        _ => "execution",
    };
    let bytes = std::fs::read(directory.join(format!("{name}{suffix}.bundle"))).unwrap();
    let bundle = Bundle::admit(&bytes, &backend(), BundleLimits::default()).unwrap();
    let mut native = backend();
    let rng_budget = if mode == Mode::RngFailure { 1 } else { 64 };
    let transcript_budget = if mode == Mode::TranscriptFailure {
        1
    } else {
        64
    };
    let rng = native.issue_rng(domain(), rng_budget).unwrap();
    let root = zkc_runtime::logical::encode_tree(&serde_json::json!(["origin-test"])).unwrap();
    let transcript = native
        .issue_transcript(domain(), transcript_budget, &root)
        .unwrap();
    let mut audit = Audit {
        cancel: mode == Mode::Cancel,
        roots: vec![token(&rng).clone(), token(&transcript).clone()],
        before: vec![],
        after: vec![],
    };
    let report = run(
        &bundle,
        "origins",
        vec![RoleInput {
            role: "P".into(),
            backend: native,
            values: vec![
                Value::Index(outer),
                rng.clone(),
                transcript.clone(),
                Value::Bool(go),
                Value::Index(0),
                Value::Index(inner),
            ],
        }],
        RunLimits::default(),
        &mut audit,
    )
    .unwrap();
    match mode {
        Mode::Return | Mode::StopZero => {
            assert_eq!(report.outcome, Outcome::Completed);
            let values = &report.roles[0].outputs;
            assert_eq!(values.len(), 2);
            let expected = outer * if go { inner } else { 1 };
            for (value, original, generations) in [
                (&values[0], &rng, expected),
                (&values[1], &transcript, 2 * expected),
            ] {
                assert_eq!(token(value).issued_id(), token(original).issued_id());
                assert_eq!(token(value).generation(), generations);
            }
        }
        Mode::Cancel => assert!(matches!(report.outcome, Outcome::HostCancelled(_))),
        _ => assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 0 }),
    }
    assert_eq!(report.roles[0].cancelled, mode == Mode::Cancel);
    if !matches!(mode, Mode::Return | Mode::StopZero) {
        assert!(report.roles[0].outputs.is_empty());
        let State::Stopped(stop) = &report.roles[0].after else {
            panic!("expected stop")
        };
        assert!(stop.cleanup_errors.is_empty());
        assert_eq!(stop.omitted_errors, 0);
        match (&stop.cause, mode) {
            (StopCause::Explicit(text), Mode::Stop | Mode::StopAfter) => {
                assert_eq!(text.text, "abort")
            }
            (StopCause::Cancelled, Mode::Cancel) => (),
            (StopCause::Backend(error), Mode::RngFailure | Mode::TranscriptFailure) => {
                assert!(error.text.contains("resource-budget"), "{error:?}")
            }
            _ => panic!("unexpected stop: {stop:?}"),
        }
    }
    assert_eq!(audit.before, audit.after);
    let (rng_count, transcript_count) = match mode {
        Mode::Return | Mode::StopZero => {
            let n = outer * if go { inner } else { 1 };
            (n, 2 * n)
        }
        Mode::Stop => (0, 0),
        Mode::StopAfter => (1, 2),
        Mode::Cancel => (inner, 2 * inner),
        // Failed scalar consumption installs its generation/counter first;
        // successful earlier transitions survive the failed invocation.
        Mode::RngFailure => (2, 2),
        Mode::TranscriptFailure => (1, 2),
    };
    for (original, count, budget) in [
        (&rng, rng_count, rng_budget),
        (&transcript, transcript_count, transcript_budget),
    ] {
        let after = report.backends[0].1.observe(token(original)).unwrap();
        assert_eq!(after.issued_id, token(original).issued_id());
        assert_eq!(after.generation, count);
        assert_eq!(after.draw_count, count);
        assert_eq!(after.budget, budget.saturating_sub(count));
    }
    assert_eq!(report.backends[0].1.active_frames(), 0);
    assert_eq!(report.backends[0].1.live_resource_units(), 0);
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("generated fixture directory");
    let directory = Path::new(&directory);
    let mut count = 0;
    for suffix in ["", "_plain", "_release"] {
        for outer in [0, 1, 3] {
            for inner in [0, 1, 3] {
                for go in [false, true] {
                    execute(directory, suffix, Mode::Return, outer, inner, go);
                    count += 1;
                }
            }
        }
        for (mode, outer, inner, go) in [
            (Mode::Stop, 3, 2, false),
            (Mode::StopAfter, 3, 2, true),
            (Mode::StopZero, 3, 0, true),
            (Mode::Cancel, 3, 2, true),
            (Mode::RngFailure, 3, 1, true),
            (Mode::TranscriptFailure, 1, 1, true),
        ] {
            execute(directory, suffix, mode, outer, inner, go);
            count += 1;
        }
    }
    println!("{count} resource executions: roots, generations, transitions and cleanup passed");
}
