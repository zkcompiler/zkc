//! Independent operation library: no table domains or canonical Boolean spelling.
use serde_json::{Value, json};
use std::{cell::Cell, rc::Rc};
use zkc_runtime::{
    AdmittedJob, AdmittedProgram, Bindings, Budget, CheckFailure, CheckRequest, Checker, Error,
    Library, Outcome, PhaseEvidence, Resources, Sort,
};

struct Exact;
impl Checker for Exact {
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure> {
        assert!(request.phase.is_none());
        let (source, candidate) = (request.source, request.candidate);
        let s: Value = serde_json::from_slice(source).unwrap();
        let p: Value = serde_json::from_slice(candidate).unwrap();
        if s[5] == p[9] {
            Ok(())
        } else {
            Err(CheckFailure::NotEstablished("unchecked-plan".into()))
        }
    }
}
struct Predicates {
    revision: &'static str,
    calls: usize,
    corrupt: bool,
    entry_valid: Rc<Cell<bool>>,
    started: bool,
}
impl Predicates {
    fn new(revision: &'static str) -> Self {
        Self {
            revision,
            calls: 0,
            corrupt: false,
            entry_valid: Rc::new(Cell::new(true)),
            started: false,
        }
    }
}
impl Library for Predicates {
    type Operation = ();
    fn condition_sort(&self) -> Sort {
        Sort(json!(["predicate"]))
    }
    fn sort(&self, value: &Value) -> Result<Sort, Error> {
        if value == &json!(["predicate"]) {
            Ok(Sort(value.clone()))
        } else {
            Err(Error("unknown-type"))
        }
    }
    fn operation(&self, value: &Value) -> Result<(), Error> {
        if value == &json!(["flip"]) {
            Ok(())
        } else {
            Err(Error("unknown-operation"))
        }
    }
    fn signature(&self, _: &()) -> (Vec<Sort>, Sort) {
        let p = Sort(json!(["predicate"]));
        (vec![p.clone()], p)
    }
    fn dependencies(&self) -> Value {
        json!([["predicates", self.revision]])
    }
}
impl Bindings for Predicates {
    type Value = bool;
    type Bound = ();
    fn validate_entry(&self, _: &str, _: Option<&PhaseEvidence>) -> Result<(), Error> {
        if self.entry_valid.get() {
            Ok(())
        } else {
            Err(Error("entry-invalidated"))
        }
    }
    fn validate_result(&self, _: &(), args: &[bool], result: &bool) -> Result<(), Error> {
        if let [arg] = args
            && *result != *arg
        {
            Ok(())
        } else {
            Err(Error("invalid-operation-result"))
        }
    }
    fn input(&mut self, _: &Sort, value: &Value) -> Result<bool, Error> {
        value.as_bool().ok_or(Error("invalid-value"))
    }
    fn validate(&self, sort: &Sort, _: &bool) -> Result<(), Error> {
        self.sort(&sort.0).map(|_| ())
    }
    fn condition(&self, value: &bool) -> Result<bool, Error> {
        Ok(*value)
    }
    fn bound(&self, _: &bool) -> Result<(), Error> {
        Ok(())
    }
    fn top(&self, _: &Sort, _: &Budget) -> Result<(), Error> {
        Ok(())
    }
    fn join(&self, _: &(), _: &()) {}
    fn estimate(&self, _: &(), _: &[()], _: &Budget) -> Result<((), Resources), Error> {
        Ok(((), Resources::default()))
    }
    fn reserve(&mut self, _: Resources, _: &Budget) -> Result<(), Error> {
        Ok(())
    }
    fn begin_execution(&mut self) {
        self.started = true;
    }
    fn invoke(&mut self, _: &(), values: &[bool]) -> Result<Outcome<bool>, Error> {
        self.calls += 1;
        Ok(Outcome::Returned(if self.corrupt {
            values[0]
        } else {
            !values[0]
        }))
    }
}
fn program_with_format(body: Value, format: &str) -> std::sync::Arc<AdmittedProgram<()>> {
    let context = json!([
        "owner",
        [["x", ["predicate"], ["shared"], "argument"]],
        ["predicate"],
        [["predicates", "1"]]
    ]);
    let source = json!(["zkc-request", 1, format, context, [], body]);
    let plan = json!([
        "zkc-plan",
        1,
        format,
        [],
        "direct-logical-plan",
        "direct-lowering",
        [
            "equality",
            "logical-outcome-state-events",
            "all-inputs-and-handlers"
        ],
        context,
        [],
        body
    ]);
    AdmittedProgram::admit(
        source.to_string().into_bytes(),
        plan.to_string().into_bytes(),
        None,
        &Predicates::new("1"),
        &Exact,
    )
    .unwrap_or_else(|e| panic!("{}", e.reason))
}
fn program(body: Value) -> std::sync::Arc<AdmittedProgram<()>> {
    program_with_format(body, "finite-source-1")
}
#[test]
fn regions_use_library_sorts_and_skip_stopped_suffixes() {
    for (body, expected) in [
        (
            json!([
                "bind",
                ["predicate"],
                ["apply", ["flip"], [0], ["return", 0]],
                ["if", 0, ["return", 0], ["return", 1]]
            ]),
            Outcome::Returned(true),
        ),
        (
            json!([
                "bind",
                ["predicate"],
                ["stop", "reject"],
                ["apply", ["flip"], [1], ["return", 0]]
            ]),
            Outcome::Stopped(zkc_runtime::Stop::Reject),
        ),
    ] {
        let p = program_with_format(body, "region-source-1");
        let done = AdmittedJob::bind(p, json!([["x", ["predicate"], true]]), Predicates::new("1"))
            .unwrap_or_else(|e| panic!("{}", e.reason))
            .reserve(Budget::default())
            .unwrap_or_else(|e| panic!("{}", e.reason))
            .execute();
        assert_eq!(done.outcome(), &Ok(expected));
    }
}
#[test]
fn branch_condition_belongs_to_the_library() {
    let p = program(json!([
        "if",
        0,
        ["apply", ["flip"], [0], ["return", 0]],
        ["return", 0]
    ]));
    let done = AdmittedJob::bind(p, json!([["x", ["predicate"], true]]), Predicates::new("1"))
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert_eq!(done.outcome(), &Ok(Outcome::Returned(false)));
}
#[test]
fn binding_rejects_another_library_revision() {
    let p = program(json!(["return", 0]));
    let result = AdmittedJob::bind(p, json!([["x", ["predicate"], true]]), Predicates::new("2"));
    assert!(matches!(result,Err(e) if e.reason == Error("library-mismatch")));
}

#[test]
fn invalid_operation_result_retains_state_and_skips_continuation() {
    let p = program(json!([
        "apply",
        ["flip"],
        [0],
        ["apply", ["flip"], [0], ["return", 0]]
    ]));
    let mut bindings = Predicates::new("1");
    bindings.corrupt = true;
    let done = AdmittedJob::bind(p, json!([["x", ["predicate"], true]]), bindings)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert_eq!(done.outcome(), &Err(Error("invalid-operation-result")));
    assert_eq!(done.bindings().calls, 1);
}

#[test]
fn entry_is_rechecked_before_reservation_and_start() {
    for invalidate_before_reserve in [true, false] {
        let p = program(json!(["apply", ["flip"], [0], ["return", 0]]));
        let b = Predicates::new("1");
        let valid = b.entry_valid.clone();
        let job = AdmittedJob::bind(p, json!([["x", ["predicate"], true]]), b)
            .unwrap_or_else(|e| panic!("{}", e.reason));
        if invalidate_before_reserve {
            valid.set(false);
            let failure = job.reserve(Budget::default()).err().unwrap();
            assert_eq!(failure.reason, Error("entry-invalidated"));
            assert_eq!(failure.job.bindings().calls, 0);
            assert!(!failure.job.bindings().started);
        } else {
            let session = job
                .reserve(Budget::default())
                .unwrap_or_else(|e| panic!("{}", e.reason));
            valid.set(false);
            let done = session.execute();
            assert_eq!(done.outcome(), &Err(Error("entry-invalidated")));
            assert_eq!(done.bindings().calls, 0);
            assert!(!done.bindings().started);
            assert!(!done.started());
        }
    }
}
