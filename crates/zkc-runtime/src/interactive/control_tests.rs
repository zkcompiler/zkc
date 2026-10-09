//! General control and cleanup contracts, using a noncryptographic backend.
use super::*;
use serde_json::{Value as Json, json};
const BOOL: &str = "bool@native.bool/0";
const INDEX: &str = "index@native.index/0";
const RNG: &str = "rng:bls12-381.fr@host.resource/0";
#[derive(Clone, Debug)]
struct Datum {
    ty: PhysicalType,
    value: u64,
}
impl Datum {
    fn new(ty: &str, value: u64) -> Self {
        Self {
            ty: PhysicalType::parse(ty).unwrap(),
            value,
        }
    }
}
impl Value for Datum {
    fn physical_type(&self) -> PhysicalType {
        self.ty.clone()
    }
    fn retained_bytes(&self) -> usize {
        1
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn control_bool(&self) -> Result<bool, BackendError> {
        Ok(self.value != 0)
    }
    fn control_index(&self) -> Result<u64, BackendError> {
        Ok(self.value)
    }
    fn from_control_index(value: u64) -> Result<Self, BackendError> {
        Ok(Self::new(INDEX, value))
    }
    fn from_control_bool(value: bool) -> Result<Self, BackendError> {
        Ok(Self::new(BOOL, u64::from(value)))
    }
}
#[derive(Default, Debug)]
struct Store {
    frames: Vec<u64>,
    leaves: Vec<(u64, FrameExit, Vec<u64>)>,
    fail: Option<u64>,
}
impl Backend for Store {
    type Value = Datum;
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn validate_value(&self, _: &Datum) -> Result<(), BackendError> {
        Ok(())
    }
    fn enter_frame(&mut self, f: &Frame, _: &[Datum]) -> Result<(), BackendError> {
        self.frames.push(f.id().get());
        Ok(())
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        exit: FrameExit,
        values: &[Datum],
    ) -> Result<(), BackendError> {
        assert_eq!(self.frames.pop(), Some(f.id().get()));
        self.leaves
            .push((f.id().get(), exit, values.iter().map(|v| v.value).collect()));
        if self.fail == Some(f.id().get()) {
            Err(BackendError::new("injected-leave"))
        } else {
            Ok(())
        }
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[Datum]) -> Result<Vec<Datum>, BackendError> {
        panic!("unreached kernel")
    }
}
fn artifact(body: Json, functions: Json) -> Json {
    json!([
        "zkc.program/0",
        [],
        functions,
        [[
            "participant",
            "p",
            "root",
            "P",
            [["c", BOOL], ["n", INDEX], ["r", RNG]],
            [BOOL, RNG],
            body,
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ])
}
fn body(nested: bool) -> Json {
    if !nested {
        return json!([
            ["return_if", "exit", "c", ["c", "r"], ["next"]],
            ["return", ["c", "next"]]
        ]);
    }
    json!([
        [
            "loop",
            "outer",
            ["value", "n", "4", "i"],
            [["outer_r", "r"]],
            ["c", "n"],
            [
                [
                    "loop",
                    "inner",
                    ["value", "n", "4", "j"],
                    [["inner_r", "outer_r"]],
                    ["c"],
                    [
                        ["return_if", "exit", "c", ["c", "inner_r"], ["next"]],
                        ["yield", ["next"]]
                    ],
                    ["inner_out"]
                ],
                ["yield", ["inner_out"]]
            ],
            ["out"]
        ],
        ["return", ["c", "out"]]
    ])
}
fn runner(nested: bool, taken: bool, fail: Option<u64>, total: usize) -> Runner<Store> {
    let store = Store {
        fail,
        ..Store::default()
    };
    let admitted = admit_supplied(
        &serde_json::to_vec(&artifact(body(nested), json!([]))).unwrap(),
        &store,
    )
    .unwrap();
    Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "test",
        store,
        vec![
            Datum::new(BOOL, u64::from(taken)),
            Datum::new(INDEX, 3),
            Datum::new(RNG, 7),
        ],
        ValueBudget {
            live_bytes: 1000,
            total_bytes: total,
        },
    )
    .unwrap()
}
#[test]
fn conditional_return_preserves_tuple_and_unwinds_only_reached_frames() {
    for nested in [false, true] {
        let mut r = runner(nested, true, None, 1000);
        while r.advance_local_control().unwrap() {}
        assert_eq!(
            r.returned_values()
                .unwrap()
                .iter()
                .map(|v| v.value)
                .collect::<Vec<_>>(),
            [1, 7]
        );
        assert_eq!(r.usage().iterations, if nested { 2 } else { 0 });
        let (origin, site) = r.early_return().unwrap();
        assert_eq!(site, "exit");
        assert_eq!(origin.path.len(), if nested { 2 } else { 0 });
        assert_eq!(r.backend().leaves.len(), if nested { 3 } else { 1 });
        assert!(r.backend().frames.is_empty());
        for (_, exit, values) in &r.backend().leaves {
            assert_eq!(*exit, FrameExit::Returned);
            assert_eq!(values, &[1, 7]);
        }
    }
}
#[test]
fn continuing_resources_stay_single_use_and_controls_are_explicit() {
    let mut r = runner(false, false, None, 1000);
    let usage = r.usage();
    let origin = r.root_origin().clone();
    assert!(matches!(
        r.inspect_program().unwrap(),
        ProgramState::ReturnIf { site: "exit" }
    ));
    assert_eq!(r.return_if(&origin, "wrong"), Err(RuntimeError::WrongCut));
    assert_eq!(r.usage(), usage);
    r.return_if(&origin, "exit").unwrap();
    assert!(matches!(r.poll(), Action::Returned(_)));
    assert!(r.early_return().is_none());
    let mut invalid = artifact(body(false), json!([]));
    invalid[3][0][6][1][1][1] = json!("r");
    assert!(admit_supplied(&serde_json::to_vec(&invalid).unwrap(), &Store::default()).is_err());
    let mut r = runner(false, true, None, 1000);
    assert!(matches!(r.poll(), Action::Stopped(_))); // poll must not silently cross control
}
#[test]
fn early_return_failures_never_publish_outputs() {
    for failure in [1, 2, 3] {
        let mut r = runner(true, true, Some(failure), 1000);
        while r.advance_local_control().unwrap() {}
        assert!(r.returned_values().is_none());
        assert!(r.early_return().is_none());
        assert!(matches!(r.stop().unwrap().kind, StopKind::Backend(_)));
        assert!(r.backend().frames.is_empty());
        assert_eq!(r.backend().leaves.len(), 3);
        assert_eq!(r.stop().unwrap().site.as_deref(), Some("exit"));
    }
    let mut r = runner(false, true, None, 3); // inputs fit, root result retention does not
    r.advance_local_control().unwrap();
    assert!(matches!(r.stop().unwrap().kind, StopKind::Limit));
    assert!(r.returned_values().is_none());
    assert!(r.backend().frames.is_empty());
    assert_eq!(r.backend().leaves[0].1, FrameExit::Stopped);
}
#[test]
fn bounded_local_condition_skips_unreached_iterations() {
    for conditional in [false, true] {
        let functions = json!([[
            "function",
            "search",
            [["lo", INDEX], ["hi", INDEX], ["state", RNG]],
            [RNG],
            [
                [
                    if conditional { "for_while" } else { "for" },
                    "search",
                    "i",
                    "lo",
                    "hi",
                    [["r", "state"]],
                    [],
                    [
                        ["bool_constant", "done", "no", false],
                        [
                            "yield",
                            if conditional {
                                vec!["no", "r"]
                            } else {
                                vec!["r"]
                            }
                        ]
                    ],
                    ["out"]
                ],
                ["return", ["out"]]
            ],
            ["search", []]
        ]]);
        let mut program = artifact(
            json!([
                ["local", "search", "search", ["n", "hi", "r"], ["out"]],
                ["return", ["c", "out"]]
            ]),
            functions,
        );
        program[3][0][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["hi", INDEX]));
        let admitted =
            admit_supplied(&serde_json::to_vec(&program).unwrap(), &Store::default()).unwrap();
        for upper in [0, 1, 4] {
            let mut r = Runner::new_with_budgets(
                &admitted,
                "main",
                "P",
                "test",
                Store::default(),
                vec![
                    Datum::new(BOOL, 1),
                    Datum::new(INDEX, 0),
                    Datum::new(RNG, 7),
                    Datum::new(INDEX, upper),
                ],
                ValueBudget::default(),
                WorkBudget {
                    iterations: 1,
                    ..WorkBudget::default()
                },
            )
            .unwrap();
            let Action::Local(local) = r.poll() else {
                panic!("local")
            };
            r.execute_local(&local.cut).unwrap();
            if conditional || upper <= 1 {
                let Action::Returned(values) = r.poll() else {
                    panic!("expected loop result")
                };
                assert_eq!(values[1].value, 7);
            } else {
                assert!(matches!(r.stop().unwrap().kind, StopKind::Limit));
            }
            assert_eq!(r.usage().iterations, u64::from(upper > 0));
        }
        if conditional {
            let mut changed = program.clone();
            changed[2][0][4][0][7][1][1] = json!(["r"]);
            assert!(
                admit_supplied(&serde_json::to_vec(&changed).unwrap(), &Store::default()).is_err()
            );
            changed = program.clone();
            changed[2][0][4][0][7][1][1] = json!(["i", "r"]);
            assert!(
                admit_supplied(&serde_json::to_vec(&changed).unwrap(), &Store::default()).is_err()
            );
            changed = program.clone();
            changed[2][0][4][0][7] = json!([["stop", "halt", "abort"]]);
            let error = admit_supplied(&serde_json::to_vec(&changed).unwrap(), &Store::default())
                .unwrap_err();
            assert!(error.to_string().contains("local-control-yield"));
            changed = program.clone();
            changed[0] = json!("invalid.program");
            assert!(
                admit_supplied(&serde_json::to_vec(&changed).unwrap(), &Store::default()).is_err()
            );
        }
    }
}

#[test]
fn false_exits_preserve_iterations_and_malformed_records_refuse() {
    let mut r = runner(true, false, None, 1000);
    while r.advance_local_control().unwrap() {}
    assert!(matches!(r.poll(), Action::Returned(_)));
    assert_eq!(r.usage().iterations, 12);
    assert!(r.early_return().is_none());
    for tag in ["invalid.program", ""] {
        let mut program = artifact(body(false), json!([]));
        program[0] = json!(tag);
        assert!(admit_supplied(&serde_json::to_vec(&program).unwrap(), &Store::default()).is_err());
    }
    for changed in [
        json!(["return_if", "exit", "n", ["c", "r"], ["next"]]),
        json!(["return_if", "exit", "c", ["r", "c"], ["next"]]),
        json!(["return_if", "exit", "c", ["c", "r"], []]),
        json!(["return_if", "exit", "c", ["c", "r"], ["r"]]),
    ] {
        let mut program = artifact(body(false), json!([]));
        program[3][0][6][0] = changed;
        assert!(admit_supplied(&serde_json::to_vec(&program).unwrap(), &Store::default()).is_err());
    }
}

#[test]
fn extra_participant_fields_and_malformed_instructions_refuse() {
    let base = artifact(body(false), json!([]));
    for parameters in [json!([["n", "2"]]), json!([["n", ["ingress", "8", []]]])] {
        let mut program = base.clone();
        program[3][0].as_array_mut().unwrap().insert(4, parameters);
        let error =
            admit_supplied(&serde_json::to_vec(&program).unwrap(), &Store::default()).unwrap_err();
        assert_eq!(error.code, ErrorCode::Record);
    }
    for instruction in [
        json!(["call", "child", "other", [], []]),
        json!(["loop", "fixed", "2", [], [], [["yield", []]], []]),
        json!(["loop", "parameterized", "n", [], [], [["yield", []]], []]),
        json!(["incomplete", "end"]),
    ] {
        let mut program = base.clone();
        program[3][0][6] = json!([instruction, ["return", []]]);
        assert!(admit_supplied(&serde_json::to_vec(&program).unwrap(), &Store::default()).is_err());
    }
}
