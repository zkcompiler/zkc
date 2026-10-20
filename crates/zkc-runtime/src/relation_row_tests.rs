//! Behavior of the full deterministic and staged row evaluators.
use super::*;
use std::cell::RefCell;

const F: Identity = Identity::KoalaBear;
const E: Identity = Identity::KoalaBearExt8;

fn columns(values: &[u64]) -> Columns {
    values.iter().map(u64::to_string).collect()
}

fn read(group: u32, offset: i32, column: u32) -> Input {
    Input::Read {
        group,
        offset,
        column,
    }
}

fn staged_read(phase: u32, group: u32, offset: i32, column: u32) -> StagedInput {
    StagedInput::Read {
        phase,
        group,
        offset,
        column,
    }
}

fn assertions(model: ReadModel) -> Vec<Assertion> {
    [
        (3, active_scope(model)),
        (1, Scope::Last),
        (0, Scope::Interval(2, 4)),
        (1, Scope::First),
        (2, Scope::Interior(1, 0)),
        (1, Scope::All),
    ]
    .into_iter()
    .map(|(output, scope)| Assertion { output, scope })
    .collect()
}

fn active_scope(model: ReadModel) -> Scope {
    match model {
        ReadModel::Finite => Scope::Interior(1, 1),
        ReadModel::Cyclic => Scope::All,
    }
}

fn table(arena: Expression, inputs: Vec<Input>, assertions: Vec<Assertion>) -> Table {
    Table {
        name: "rows".into(),
        optional: false,
        height: Height {
            authority: HeightAuthority::Fixed,
            min: 6,
            max: 6,
            power_of_two: false,
        },
        read_model: ReadModel::Finite,
        groups: vec![],
        arena,
        inputs,
        assertions,
        interactions: vec![],
    }
}

fn carriers(bundle: &Bundle) -> (Configuration, Instance, Witness) {
    let relation = bundle.identity().to_string();
    (
        Configuration {
            relation: relation.clone(),
            tables: vec![(None, vec![])],
        },
        Instance {
            relation: relation.clone(),
            publics: vec![],
            tables: vec![Some((None, vec![]))],
        },
        Witness {
            relation,
            tables: vec![Some(vec![])],
        },
    )
}

fn empty_arena() -> Expression {
    Expression::new(vec![], vec![], vec![]).unwrap()
}

fn mixed_rows(model: ReadModel) -> (Bundle, Configuration, Instance, Witness) {
    let arena = Expression::new(
        vec![F; 5],
        vec![
            Node::Input(4),
            Node::Constant(F, "2".into()),
            Node::Input(0),
            Node::Input(4),
            Node::Add(0, 3),
            Node::Input(2),
            Node::Add(4, 5),
            Node::Input(3),
            Node::Add(6, 7),
            Node::Input(1),
            Node::Add(8, 9),
            Node::Mul(10, 1),
            Node::Input(4),
            Node::Neg(12),
            Node::Add(11, 13),
            Node::Add(14, 2),
        ],
        vec![15, 0, 14, 15, 1],
    )
    .unwrap();
    let mut t = table(
        arena,
        vec![
            read(0, 1, 1),
            Input::Public(0),
            read(1, -1, 0),
            read(2, 0, 0),
            read(0, 0, 0),
        ],
        assertions(model),
    );
    t.read_model = model;
    t.groups = [
        ("witness", Authority::Witness, 2),
        ("configuration", Authority::Config, 1),
        ("public", Authority::Public, 1),
    ]
    .into_iter()
    .map(|(name, authority, width)| Group {
        name: name.into(),
        authority,
        field: F,
        width,
    })
    .collect();
    t.interactions = [Side::Push, Side::Pull]
        .into_iter()
        .map(|side| Interaction::Multiset {
            channel: 0,
            locality: Locality::Local(7),
            scope: active_scope(model),
            side,
            tuple: vec![3, 0, 1, 1],
            multiplicity: 4,
            bound: 2,
        })
        .collect();
    t.interactions.push(Interaction::FieldBalance {
        channel: 1,
        locality: Locality::Global,
        scope: Scope::All,
        tuple: vec![4, 4],
        count: 1,
        declared: None,
    });
    let bundle = Bundle::new(
        vec![Slot {
            name: "public-slot".into(),
            field: F,
        }],
        vec![
            Channel {
                name: "copies".into(),
                kind: ChannelKind::Multiset,
                tuple: vec![F; 4],
                count: F,
            },
            Channel {
                name: "sum".into(),
                kind: ChannelKind::FieldBalance,
                tuple: vec![F; 2],
                count: F,
            },
        ],
        vec![t],
    )
    .unwrap();
    let (mut c, mut i, mut w) = carriers(&bundle);
    c.tables[0].1 = vec![columns(&[1, 2, 3, 4, 5, 6])];
    i.publics = vec![columns(&[9])];
    i.tables[0] = Some((None, vec![columns(&[7, 8, 9, 10, 11, 12])]));
    w.tables[0] = Some(vec![columns(&[
        10, 100, 20, 200, 30, 300, 40, 400, 50, 500, 60, 600,
    ])]);
    (bundle, c, i, w)
}

/// Expected records are in assertion declaration order, then row order.
fn expected_rows(model: ReadModel, staged: bool) -> Vec<(usize, u32, Columns)> {
    // Deterministic interior expression: 3*x + 2*config(r-1) + 2*public(r) + 18.
    // Staged interior expression: 6*q + 3*z(r-1) + claim + public(r) + 9 + config(r-1).
    // The first assertion additionally reads witness column 1 at r+1.
    let (middle, interior, current): (&[u64], &[u64], &[u64]) = if staged {
        (
            &[18293, 3395, 6503, 9611, 12719, 15227],
            &[3095, 6103, 9111, 12119, 15127],
            &[11, 12, 13, 14, 15, 16],
        )
    } else {
        (
            &[274, 396, 530, 664, 798, 332],
            &[96, 130, 164, 198, 232],
            &[10, 20, 30, 40, 50, 60],
        )
    };
    let active = match model {
        ReadModel::Finite => 1..5,
        ReadModel::Cyclic => 0..6,
    };
    let mut result = Vec::new();
    for (assertion, rows) in [active, 5..6, 2..4, 0..1, 1..6, 0..6]
        .into_iter()
        .enumerate()
    {
        for row in rows {
            let value = match assertion {
                0 | 2 => middle[row],
                4 => interior[row - 1],
                _ => current[row],
            };
            result.push((assertion, row as u32, columns(&[value])));
        }
    }
    result
}

#[test]
fn bundle_rows_preserve_scopes_authority_offsets_and_repeated_emissions() {
    for model in [ReadModel::Finite, ReadModel::Cyclic] {
        let (bundle, c, i, w) = mixed_rows(model);
        let result = bundle.evaluate(&c, &i, &w, &Reference).unwrap();
        assert!(!result.satisfied);
        assert_eq!(result.work, 186);
        assert_eq!(
            result
                .residuals
                .iter()
                .map(|r| {
                    assert_eq!(r.table, 0);
                    (r.assertion, r.row, r.value.clone())
                })
                .collect::<Vec<_>>(),
            expected_rows(model, false)
        );
        let tuples: &[u64] = match model {
            ReadModel::Finite => &[396, 530, 664, 798],
            ReadModel::Cyclic => &[274, 396, 530, 664, 798, 332],
        };
        assert_eq!(result.balances.len(), tuples.len() + 1);
        let start = if model == ReadModel::Finite { 1 } else { 0 };
        for (row, value) in tuples.iter().enumerate() {
            let x = 10 * (start + row as u64 + 1);
            let tuple = vec![
                columns(&[*value]),
                columns(&[*value]),
                columns(&[x]),
                columns(&[x]),
            ];
            let b = result.balances.iter().find(|b| b.tuple == tuple).unwrap();
            assert_eq!(
                (b.kind, b.channel, b.local),
                (ChannelKind::Multiset, 0, Some((0, 7)))
            );
            assert_eq!((b.push, b.pull, b.balanced), (2, 2, true));
            assert!(b.sum.is_empty());
        }
        let sum = result.balances.iter().find(|b| b.channel == 1).unwrap();
        assert_eq!((sum.kind, sum.local), (ChannelKind::FieldBalance, None));
        assert_eq!(sum.tuple, vec![columns(&[2]); 2]);
        assert_eq!(sum.sum, columns(&[210]));
        assert_eq!((sum.push, sum.pull, sum.balanced), (0, 0, false));
        assert!(result.range_failures.is_empty());
    }
}

#[test]
fn staged_rows_preserve_scopes_phase_reads_slots_and_repeated_emissions() {
    for model in [ReadModel::Finite, ReadModel::Cyclic] {
        let (bundle, c, i, w) = mixed_rows(model);
        let arena = Expression::new(
            vec![F; 8],
            vec![
                Node::Input(5),
                Node::Input(1),
                Node::Input(0),
                Node::Input(4),
                Node::Add(0, 3),
                Node::Input(5),
                Node::Add(4, 5),
                Node::Input(6),
                Node::Mul(6, 7),
                Node::Input(7),
                Node::Add(8, 9),
                Node::Input(2),
                Node::Add(10, 11),
                Node::Input(3),
                Node::Add(12, 13),
                Node::Add(14, 2),
                Node::Add(15, 1),
            ],
            vec![16, 0, 15, 16],
        )
        .unwrap();
        let staged = Staged::new(
            &bundle,
            vec![
                StagedPhase {
                    challenges: vec![Slot {
                        name: "alpha".into(),
                        field: F,
                    }],
                    claims: vec![],
                    tables: vec![StagedTable {
                        groups: vec![("z".into(), F, 1)],
                        arena: empty_arena(),
                        inputs: vec![],
                        assertions: vec![],
                    }],
                },
                StagedPhase {
                    challenges: vec![],
                    claims: vec![Slot {
                        name: "beta".into(),
                        field: F,
                    }],
                    tables: vec![StagedTable {
                        groups: vec![("q".into(), F, 1)],
                        arena,
                        inputs: vec![
                            staged_read(0, 1, -1, 0),
                            staged_read(0, 0, 1, 1),
                            staged_read(0, 2, 0, 0),
                            StagedInput::Public(0),
                            staged_read(1, 0, -1, 0),
                            staged_read(2, 0, 0, 0),
                            StagedInput::Challenge { phase: 1, index: 0 },
                            StagedInput::Claim { phase: 2, index: 0 },
                        ],
                        assertions: assertions(model),
                    }],
                },
            ],
            (
                Expression::new(
                    vec![F; 2],
                    vec![Node::Input(0), Node::Input(1), Node::Add(0, 1)],
                    vec![2],
                )
                .unwrap(),
                vec![
                    StagedInput::Challenge { phase: 1, index: 0 },
                    StagedInput::Claim { phase: 2, index: 0 },
                ],
                vec![0, 0],
            ),
            vec![],
        )
        .unwrap();
        let assignment = StagedAssignment {
            program: staged.identity().into(),
            phases: vec![
                StagedPhaseAssignment {
                    challenges: vec![columns(&[3])],
                    claims: vec![],
                    tables: vec![Some(vec![columns(&[1000, 2000, 3000, 4000, 5000, 6000])])],
                },
                StagedPhaseAssignment {
                    challenges: vec![],
                    claims: vec![columns(&[5])],
                    tables: vec![Some(vec![columns(&[11, 12, 13, 14, 15, 16])])],
                },
            ],
        };
        let result = staged
            .evaluate(&bundle, &c, &i, &w, &assignment, &Reference)
            .unwrap();
        assert!(!result.satisfied);
        assert_eq!(result.work, 192);
        assert_eq!(
            result
                .residuals
                .iter()
                .map(|r| {
                    assert_eq!((r.phase, r.table), (2, 0));
                    (r.assertion, r.row, r.value.clone())
                })
                .collect::<Vec<_>>(),
            expected_rows(model, true)
        );
        assert_eq!(result.global, vec![columns(&[8]); 2]);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Value(u64),
    Constant(u64),
    Add,
    Mul,
    Neg,
    Embed,
    Emit(u64),
}

#[derive(Default)]
struct Recording {
    events: RefCell<Vec<Event>>,
    fail_at: Option<usize>,
}
impl Recording {
    fn reach(&self, event: Event, error: &'static str) -> Result<()> {
        let mut events = self.events.borrow_mut();
        events.push(event);
        if Some(events.len()) == self.fail_at {
            Err(Error(error))
        } else {
            Ok(())
        }
    }
}
impl Algebra for Recording {
    type Value = Vec<u64>;
    fn value(&self, field: Identity, c: &[String]) -> Result<Self::Value> {
        self.reach(Event::Value(c[0].parse().unwrap()), "row-test-value")?;
        Reference.value(field, c)
    }
    fn constant(&self, field: Identity, literal: &str) -> Result<Self::Value> {
        self.reach(
            Event::Constant(literal.parse().unwrap()),
            "row-test-constant",
        )?;
        Reference.constant(field, literal)
    }
    fn add(&self, field: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value {
        self.events.borrow_mut().push(Event::Add);
        Reference.add(field, a, b)
    }
    fn mul(&self, field: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value {
        self.events.borrow_mut().push(Event::Mul);
        Reference.mul(field, a, b)
    }
    fn neg(&self, field: Identity, a: &Self::Value) -> Self::Value {
        self.events.borrow_mut().push(Event::Neg);
        Reference.neg(field, a)
    }
    fn embed(&self, from: Identity, to: Identity, a: &Self::Value) -> Result<Self::Value> {
        self.reach(Event::Embed, "row-test-embed")?;
        Reference.embed(from, to, a)
    }
    fn coordinates(&self, field: Identity, a: &Self::Value) -> Columns {
        self.events.borrow_mut().push(Event::Emit(a[0]));
        Reference.coordinates(field, a)
    }
}

fn check_fallible_rows(staged_path: bool) {
    let arena = Expression::new(
        vec![F; 3],
        vec![
            Node::Input(1),
            Node::Constant(F, "2".into()),
            Node::Input(0),
            Node::Input(1),
            Node::Add(0, 3),
            Node::Mul(4, 2),
            Node::Add(5, 1),
            Node::Embed(E, 6),
            Node::Input(2),
            Node::Embed(E, 8),
            Node::Add(7, 9),
            Node::Constant(F, "9".into()),
            Node::Embed(E, 11),
        ],
        vec![12, 10, 7, 10],
    )
    .unwrap();
    let checks: Vec<_> = [
        (1, Scope::All),
        (3, Scope::All),
        (2, Scope::All),
        (0, Scope::Last),
    ]
    .into_iter()
    .map(|(output, scope)| Assertion { output, scope })
    .collect();
    let bindings: Vec<_> = [1, 0, 2]
        .into_iter()
        .map(|column| read(0, 0, column))
        .collect();
    let mut t = table(arena.clone(), bindings.clone(), checks.clone());
    t.height.min = 3;
    t.height.max = 3;
    t.groups = vec![Group {
        name: "values".into(),
        authority: Authority::Witness,
        field: F,
        width: 3,
    }];
    let bundle = Bundle::new(vec![], vec![], vec![t]).unwrap();
    let (c, i, mut w) = carriers(&bundle);
    w.tables[0] = Some(vec![columns(&[3, 4, 17, 5, 7, 19, 11, 13, 23])]);
    let staged = Staged::new(
        &bundle,
        vec![StagedPhase {
            challenges: vec![],
            claims: vec![],
            tables: vec![StagedTable {
                groups: vec![],
                arena,
                inputs: bindings
                    .iter()
                    .map(|input| match *input {
                        Input::Read {
                            group,
                            offset,
                            column,
                        } => staged_read(0, group, offset, column),
                        _ => unreachable!(),
                    })
                    .collect(),
                assertions: checks,
            }],
        }],
        (empty_arena(), vec![], vec![]),
        vec![],
    )
    .unwrap();
    let assignment = StagedAssignment {
        program: staged.identity().into(),
        phases: vec![StagedPhaseAssignment {
            challenges: vec![],
            claims: vec![],
            tables: vec![Some(vec![])],
        }],
    };
    let evaluate = |recording: &Recording| -> Result<Vec<Columns>> {
        if staged_path {
            Ok(staged
                .evaluate(&bundle, &c, &i, &w, &assignment, recording)?
                .residuals
                .into_iter()
                .map(|r| r.value)
                .collect())
        } else {
            Ok(bundle
                .evaluate(&c, &i, &w, recording)?
                .residuals
                .into_iter()
                .map(|r| r.value)
                .collect())
        }
    };
    use Event::*;
    // Handwritten node-order trace, including output emission after all selected
    // nodes finish. The late constant's output is first in arena output order.
    let expected = vec![
        Value(3),
        Constant(2),
        Value(4),
        Add,
        Mul,
        Add,
        Embed,
        Value(17),
        Embed,
        Add,
        Emit(43),
        Emit(43),
        Emit(26),
        Value(5),
        Constant(2),
        Value(7),
        Add,
        Mul,
        Add,
        Embed,
        Value(19),
        Embed,
        Add,
        Emit(91),
        Emit(91),
        Emit(72),
        Value(11),
        Constant(2),
        Value(13),
        Add,
        Mul,
        Add,
        Embed,
        Value(23),
        Embed,
        Add,
        Constant(9),
        Embed,
        Emit(311),
        Emit(311),
        Emit(288),
        Emit(9),
    ];
    let recording = Recording::default();
    let extension = |n: u64| {
        let mut v = vec!["0".to_string(); 8];
        v[0] = n.to_string();
        v
    };
    assert_eq!(
        evaluate(&recording).unwrap(),
        [43u64, 91, 311, 43, 91, 311, 26, 72, 288, 9]
            .into_iter()
            .map(extension)
            .collect::<Vec<_>>()
    );
    assert_eq!(*recording.events.borrow(), expected);
    for (fail_at, error) in [
        (1, "row-test-value"),
        (15, "row-test-constant"),
        (16, "row-test-value"),
        (20, "row-test-embed"),
        (21, "row-test-value"),
        (22, "row-test-embed"),
        (37, "row-test-constant"),
        (38, "row-test-embed"),
    ] {
        let recording = Recording {
            fail_at: Some(fail_at),
            ..Recording::default()
        };
        assert_eq!(evaluate(&recording).unwrap_err(), Error(error));
        assert_eq!(*recording.events.borrow(), expected[..fail_at]);
    }
}

#[test]
fn bundle_rows_keep_per_row_fallible_operations_and_stop_at_the_first_refusal() {
    check_fallible_rows(false);
}

#[test]
fn staged_rows_keep_per_row_fallible_operations_and_stop_at_the_first_refusal() {
    check_fallible_rows(true);
}

#[test]
fn bundle_and_staged_skip_empty_inactive_and_absent_tables() {
    for (present, empty, scope) in [
        (true, true, Scope::All),
        (true, false, Scope::Interior(3, 3)),
        (false, false, Scope::All),
    ] {
        let arena = if empty {
            empty_arena()
        } else {
            Expression::new(
                vec![],
                vec![Node::Constant(F, "2".into()), Node::Embed(E, 0)],
                vec![1],
            )
            .unwrap()
        };
        let checks = if empty {
            vec![]
        } else {
            vec![Assertion { output: 0, scope }]
        };
        let mut t = table(arena.clone(), vec![], checks.clone());
        t.optional = true;
        let bundle = Bundle::new(vec![], vec![], vec![t]).unwrap();
        let (c, mut i, mut w) = carriers(&bundle);
        if !present {
            i.tables[0] = None;
            w.tables[0] = None;
        }
        let staged = Staged::new(
            &bundle,
            vec![StagedPhase {
                challenges: vec![],
                claims: vec![],
                tables: vec![StagedTable {
                    groups: vec![],
                    arena,
                    inputs: vec![],
                    assertions: checks,
                }],
            }],
            (empty_arena(), vec![], vec![]),
            vec![],
        )
        .unwrap();
        let assignment = StagedAssignment {
            program: staged.identity().into(),
            phases: vec![StagedPhaseAssignment {
                challenges: vec![],
                claims: vec![],
                tables: vec![present.then(Vec::new)],
            }],
        };
        let recording = Recording {
            fail_at: Some(1),
            ..Recording::default()
        };
        let full = bundle.evaluate(&c, &i, &w, &recording).unwrap();
        let phased = staged
            .evaluate(&bundle, &c, &i, &w, &assignment, &recording)
            .unwrap();
        assert!(full.satisfied && phased.satisfied);
        assert!(
            full.residuals.is_empty() && full.balances.is_empty() && full.range_failures.is_empty()
        );
        assert!(phased.residuals.is_empty() && phased.global.is_empty());
        assert!(recording.events.borrow().is_empty());
    }
}
