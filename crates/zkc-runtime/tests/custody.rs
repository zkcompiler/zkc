mod support;
use serde_json::json;
use support::{binding_with, decl, program, state};
use zkc_runtime::{
    AdmittedJob, Budget, Error, Outcome, Stop,
    buffer::PackedBuffers,
    table::{
        ChallengeProvider, Domain, FieldKernel, SmallPrimeKernel, TableBindings, TapeProvider,
    },
};

fn binding() -> TableBindings {
    binding_with(PackedBuffers::new().unwrap())
}

#[test]
fn reserve_failure_returns_custody_without_drawing() {
    let p = program(
        json!(["apply", ["draw"], [], ["return", 0]]),
        json!([]),
        json!(["scalar", "f7"]),
    );
    let retained = p.retained_bytes().0.to_vec();
    let job = AdmittedJob::bind(p, json!([]), binding()).unwrap_or_else(|e| panic!("{}", e.reason));
    let failure = match job.reserve(Budget {
        steps: 0,
        ..Budget::default()
    }) {
        Err(e) => e,
        Ok(_) => panic!("unexpected start"),
    };
    assert_eq!(failure.reason, Error("preflight-work-limit"));
    assert_eq!(
        failure.job.bindings().state_json(),
        json!([0, 0, 0, [], [3, 6]])
    );
    assert!(failure.job.bindings().events().is_empty());
    let (p, inputs, b) = failure.job.into_parts();
    assert_eq!(p.retained_bytes().0, retained);
    let completed = AdmittedJob::bind(p, inputs, b)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert_eq!(completed.bindings().state_json(), json!([0, 0, 0, [], [6]]));
}
#[test]
fn missing_capture_is_an_input_error() {
    let p = program(
        json!(["return", 0]),
        json!([
            decl("flag", json!(["bool"])),
            decl("dormant", json!(["digest"]))
        ]),
        json!(["bool"]),
    );
    let failure = match AdmittedJob::bind(p, json!([["flag", ["bool"], true]]), binding()) {
        Err(e) => e,
        Ok(_) => panic!("missing capture accepted"),
    };
    assert_eq!(failure.reason, Error("input-count"));
    assert_eq!(failure.bindings.state_json(), json!([0, 0, 0, [], [3, 6]]));
}
struct InvalidKernel;
impl FieldKernel for InvalidKernel {
    fn add(&self, _: Domain, _: u8, _: u8) -> u8 {
        7
    }
    fn sub(&self, d: Domain, a: u8, b: u8) -> u8 {
        SmallPrimeKernel.sub(d, a, b)
    }
    fn mul(&self, d: Domain, a: u8, b: u8) -> u8 {
        SmallPrimeKernel.mul(d, a, b)
    }
}
#[test]
fn kernel_violation_is_interrupted_after_the_actual_prefix() {
    let p = program(
        json!([
            "apply",
            ["record", "f7"],
            [0],
            ["apply", ["add", "f7"], [1, 1], ["return", 0]]
        ]),
        json!([decl("x", json!(["scalar", "f7"]))]),
        json!(["scalar", "f7"]),
    );
    let b = TableBindings::new(InvalidKernel, TapeProvider::new(vec![]).unwrap(), state()).unwrap();
    let c = AdmittedJob::bind(p, json!([["x", ["scalar", "f7"], 3]]), b)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert!(matches!(
        c.outcome(),
        Err(Error("field-contract-violation"))
    ));
    assert_eq!(c.bindings().state_json(), json!([0, 3, 1, [], []]));
    assert_eq!(c.bindings().events(), &[json!(["write", "f7", 3])]);
}
struct BudgetedProvider {
    tape: TapeProvider,
    left: usize,
}
impl ChallengeProvider for BudgetedProvider {
    fn draw(&mut self) -> Result<Outcome<u8>, Error> {
        if self.left == 0 {
            Ok(Outcome::Stopped(Stop::Incomplete))
        } else {
            self.left -= 1;
            self.tape.draw()
        }
    }
    fn remaining(&self) -> &[u8] {
        self.tape.remaining()
    }
}
#[test]
fn substituted_provider_keeps_its_stop_and_remaining_state() {
    let p = program(
        json!([
            "apply",
            ["draw"],
            [],
            [
                "apply",
                ["draw"],
                [],
                ["apply", ["draw"], [], ["return", 0]]
            ]
        ]),
        json!([]),
        json!(["scalar", "f7"]),
    );
    let b = TableBindings::new(
        SmallPrimeKernel,
        BudgetedProvider {
            tape: TapeProvider::new(vec![3, 6]).unwrap(),
            left: 1,
        },
        state(),
    )
    .unwrap();
    let c = AdmittedJob::bind(p, json!([]), b)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert!(matches!(
        c.outcome(),
        Ok(Outcome::Stopped(Stop::Incomplete))
    ));
    assert_eq!(c.bindings().state_json(), json!([0, 0, 0, [], [6]]));
    assert_eq!(c.bindings().events(), &[json!(["drawn", 3])]);
}
#[test]
fn numeric_tokens_are_not_repaired() {
    assert_eq!(zkc_runtime::format::parse(b"[-0,0]"), Ok(json!([0, 0])));
    for text in [
        b"[1-0]".as_slice(),
        b"[00]",
        b"[1e0]",
        b"[1.0]",
        b"[-1]",
        b"[1]null",
    ] {
        assert!(zkc_runtime::format::parse(text).is_err(), "{text:?}");
    }
}

#[test]
fn a_new_invocation_has_its_own_event_trace() {
    let p = program(
        json!(["apply", ["draw"], [], ["return", 0]]),
        json!([]),
        json!(["scalar", "f7"]),
    );
    let first = AdmittedJob::bind(p.clone(), json!([]), binding())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert_eq!(first.bindings().events(), &[json!(["drawn", 3])]);
    let (_, bindings) = first.into_parts();
    let job = AdmittedJob::bind(p, json!([]), bindings).unwrap_or_else(|e| panic!("{}", e.reason));
    let failed = match job.reserve(Budget {
        steps: 0,
        ..Budget::default()
    }) {
        Ok(_) => panic!("empty budget unexpectedly admitted"),
        Err(failed) => failed,
    };
    assert_eq!(failed.job.bindings().events(), &[json!(["drawn", 3])]);
    assert_eq!(
        failed.job.bindings().state_json(),
        json!([0, 0, 0, [], [6]])
    );
    let second = failed
        .job
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert_eq!(second.bindings().events(), &[json!(["drawn", 6])]);
    assert_eq!(second.bindings().state_json(), json!([0, 0, 0, [], []]));
}
