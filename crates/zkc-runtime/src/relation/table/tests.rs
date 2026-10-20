use super::*;
use std::cell::RefCell;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Constant(Identity, String),
    Fetch(usize),
    Add,
    Mul,
    Neg,
    Embed(Identity, Identity),
}
fn constant(field: Identity, literal: &str) -> Event {
    Event::Constant(field, literal.into())
}

/// Handwritten integer arithmetic plus an exact trace of reached operations.
/// Values in these fixtures are small enough to avoid modular reduction.
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
    type Value = i64;
    fn value(&self, _: Identity, c: &[String]) -> Result<i64> {
        c[0].parse().map_err(|_| Error("test-value"))
    }
    fn constant(&self, field: Identity, literal: &str) -> Result<i64> {
        self.reach(constant(field, literal), "test-constant")?;
        literal.parse().map_err(|_| Error("test-literal"))
    }
    fn add(&self, _: Identity, a: &i64, b: &i64) -> i64 {
        self.events.borrow_mut().push(Event::Add);
        a + b
    }
    fn mul(&self, _: Identity, a: &i64, b: &i64) -> i64 {
        self.events.borrow_mut().push(Event::Mul);
        a * b
    }
    fn neg(&self, _: Identity, a: &i64) -> i64 {
        self.events.borrow_mut().push(Event::Neg);
        -a
    }
    fn embed(&self, from: Identity, to: Identity, a: &i64) -> Result<i64> {
        self.reach(Event::Embed(from, to), "test-embed")?;
        Ok(*a)
    }
    fn coordinates(&self, _: Identity, a: &i64) -> Vec<String> {
        vec![a.to_string()]
    }
}

#[test]
fn compact_scratch_fetches_distinct_inputs_in_first_use_order_and_reuses_storage() {
    let f = Identity::KoalaBear;
    let e = Identity::KoalaBearExt8;
    let arena = Expression::new(
        vec![f; 65_536],
        vec![
            Node::Input(65_535),
            Node::Constant(f, "2".into()),
            Node::Input(7),
            Node::Input(65_535),
            Node::Add(0, 3),
            Node::Mul(4, 2),
            Node::Add(5, 1),
            Node::Embed(e, 6),
        ],
        vec![7, 7],
    )
    .unwrap();
    let trace = vec![
        Event::Fetch(65_535),
        constant(f, "2"),
        Event::Fetch(7),
        Event::Add,
        Event::Mul,
        Event::Add,
        Event::Embed(f, e),
    ];
    let recording = Recording::default();
    let mut scratch = RowInterpreter::new(&arena);
    assert_eq!(scratch.input_sources, [0, 2, 0]);
    assert_eq!(scratch.values.capacity(), arena.nodes().len());
    assert!(recording.events.borrow().is_empty());
    let pointer = scratch.values.as_ptr();
    for (a, b, expected) in [(3, 4, 26), (5, 7, 72)] {
        let values = scratch
            .evaluate(&recording, &mut |input| {
                recording.reach(Event::Fetch(input), "test-fetch")?;
                Ok(if input == 7 { b } else { a })
            })
            .unwrap();
        // (a + a) * b + 2, independently of the evaluator's output path.
        assert_eq!(values[7], expected);
        assert_eq!(scratch.values.as_ptr(), pointer);
        assert_eq!(scratch.values.len(), 8);
        assert_eq!(*recording.events.borrow(), trace);
        recording.events.borrow_mut().clear();
    }
    for (fail_at, error) in [(2, "test-constant"), (3, "test-fetch"), (7, "test-embed")] {
        let recording = Recording {
            fail_at: Some(fail_at),
            ..Recording::default()
        };
        assert_eq!(
            scratch
                .evaluate(&recording, &mut |input| {
                    recording.reach(Event::Fetch(input), "test-fetch")?;
                    Ok(3)
                })
                .unwrap_err(),
            Error(error)
        );
        assert_eq!(*recording.events.borrow(), trace[..fail_at]);
        assert_eq!(scratch.values.as_ptr(), pointer);
    }
    assert_eq!(
        scratch
            .evaluate(&Recording::default(), &mut |input| {
                Ok(if input == 7 { 4 } else { 3 })
            })
            .unwrap()[7],
        26
    );
    assert_eq!(scratch.values.as_ptr(), pointer);
    // The existing one-row API shares the loop, while its oracle is the
    // hand-derived integer result rather than another evaluator invocation.
    assert_eq!(
        interpret(&arena, &Recording::default(), &mut |input| {
            Ok(if input == 7 { 4 } else { 3 })
        })
        .unwrap(),
        [26, 26]
    );
}

fn table(arena: Expression, inputs: Vec<Input>, assertions: Vec<Assertion>) -> Table {
    Table {
        name: "trace".into(),
        optional: false,
        height: Height {
            authority: HeightAuthority::Fixed,
            min: 4,
            max: 4,
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

fn actual_bundle(cyclic: bool) -> Bundle {
    let f = Identity::KoalaBear;
    let read = |group, offset| Input::Read {
        group,
        offset,
        column: 0,
    };
    let mut t = table(
        Expression::new(
            vec![f; 6],
            vec![
                Node::Input(5),
                Node::Input(2),
                Node::Neg(1),
                Node::Add(0, 2),
                Node::Input(1),
                Node::Input(0),
                Node::Mul(4, 5),
                Node::Input(3),
                Node::Input(4),
                Node::Add(7, 8),
                Node::Input(2),
                Node::Add(1, 10),
            ],
            vec![3, 6, 9, 11],
        )
        .unwrap(),
        vec![
            Input::Public(0),
            read(1, 0),
            read(0, 0),
            read(2, 0),
            read(3, 0),
            read(0, 1),
        ],
        vec![
            Assertion {
                output: 1,
                scope: Scope::All,
            },
            Assertion {
                output: 0,
                scope: if cyclic {
                    Scope::All
                } else {
                    Scope::Interior(0, 1)
                },
            },
            Assertion {
                output: 2,
                scope: Scope::First,
            },
            Assertion {
                output: 0,
                scope: Scope::Interval(1, 3),
            },
            Assertion {
                output: 3,
                scope: Scope::Last,
            },
            Assertion {
                output: 1,
                scope: Scope::All,
            },
        ],
    );
    t.read_model = if cyclic {
        ReadModel::Cyclic
    } else {
        ReadModel::Finite
    };
    t.groups = [
        Authority::Witness,
        Authority::Config,
        Authority::Public,
        Authority::Witness,
    ]
    .into_iter()
    .enumerate()
    .map(|(i, authority)| Group {
        name: format!("column{i}"),
        authority,
        field: f,
        width: 1,
    })
    .collect();
    Bundle::new(
        vec![Slot {
            name: "scale".into(),
            field: f,
        }],
        vec![],
        vec![t],
    )
    .unwrap()
}

#[test]
fn actual_rows_preserve_scopes_authority_offsets_repeated_roots_and_declaration_order() {
    let witness = [2, 3, 5, 11, 13, 17, 19, 23];
    let configuration = [3, 5, 7, 11];
    let public_data = [7, 29, 31, 37, 41];
    for cyclic in [false, true] {
        let bundle = actual_bundle(cyclic);
        let view = bundle.table_view(0, Identity::KoalaBear).unwrap();
        assert_eq!(view.work(4), 125);
        assert_eq!(view.lengths(4).unwrap().results, 24);
        // Rows: [config*scale, next-current, public+aux on first,
        // next-current on [1,3), twice current on last, config*scale].
        let mut expected = vec![
            21, 1, 42, 0, 0, 21, 35, 2, 0, 2, 0, 35, 49, 6, 0, 6, 0, 49, 77, 0, 0, 0, 22, 77,
        ];
        if cyclic {
            expected[19] = -9;
        }
        assert_eq!(
            view.evaluate(
                4,
                &witness,
                &configuration,
                &public_data,
                &Recording::default()
            )
            .unwrap(),
            expected
        );
        // Change each authority independently; keep the residual oracle explicit.
        for (w, c, p, slots) in [
            (
                [4, 3, 5, 11, 13, 17, 19, 23],
                configuration,
                public_data,
                vec![(1, -1), (19, -7)],
            ),
            (witness, [9, 5, 7, 11], public_data, vec![(0, 63), (5, 63)]),
            (witness, configuration, [7, 43, 31, 37, 41], vec![(2, 56)]),
        ] {
            let mut changed = expected.clone();
            for (slot, value) in slots {
                if slot != 19 || cyclic {
                    changed[slot] = value;
                }
            }
            assert_eq!(
                view.evaluate(4, &w, &c, &p, &Recording::default()).unwrap(),
                changed
            );
        }
        for (height, w, c, p, error) in [
            (0, &[][..], &[][..], &[][..], "bundle-height"),
            (4, &[][..], &[][..], &[][..], "relation-table-witness-shape"),
            (
                4,
                &witness[..],
                &[][..],
                &[][..],
                "relation-table-configuration-shape",
            ),
            (
                4,
                &witness[..],
                &configuration[..],
                &[][..],
                "relation-table-public-shape",
            ),
        ] {
            let recording = Recording::default();
            assert_eq!(
                view.evaluate(height, w, c, p, &recording).unwrap_err(),
                Error(error)
            );
            assert!(recording.events.borrow().is_empty());
        }
    }
}

#[test]
fn dormant_constants_and_empty_assertion_sets_are_not_interpreted() {
    let f = Identity::KoalaBear;
    for empty in [false, true] {
        let (nodes, outputs, assertions) = if empty {
            (vec![], vec![], vec![])
        } else {
            (
                vec![Node::Constant(f, "9".into())],
                vec![0],
                vec![Assertion {
                    output: 0,
                    scope: Scope::Interior(4, 0),
                }],
            )
        };
        let t = table(
            Expression::new(vec![], nodes, outputs).unwrap(),
            vec![],
            assertions,
        );
        let bundle = Bundle::new(vec![], vec![], vec![t]).unwrap();
        let view = bundle.table_view(0, f).unwrap();
        let recording = Recording {
            fail_at: Some(2),
            ..Recording::default()
        };
        assert_eq!(
            view.evaluate(4, &[], &[], &[], &recording).unwrap(),
            vec![0; if empty { 0 } else { 4 }]
        );
        assert_eq!(*recording.events.borrow(), [constant(f, "0")]);
    }
}

#[test]
fn selected_actual_rows_keep_high_input_numbers_and_zero_dormant_slots() {
    let f = Identity::KoalaBear;
    let count = 257;
    let mut assertions = vec![Assertion {
        output: count - 1,
        scope: Scope::All,
    }];
    assertions.extend((0..count - 1).map(|output| Assertion {
        output,
        scope: Scope::Interval(0, 0),
    }));
    assertions.push(Assertion {
        output: count - 1,
        scope: Scope::All,
    });
    let mut t = table(
        Expression::new(
            vec![f; count],
            (0..count).map(Node::Input).collect(),
            (0..count).collect(),
        )
        .unwrap(),
        (0..count)
            .map(|column| Input::Read {
                group: 0,
                offset: 0,
                column: column as u32,
            })
            .collect(),
        assertions,
    );
    t.groups.push(Group {
        name: "wide".into(),
        authority: Authority::Witness,
        field: f,
        width: count as u32,
    });
    let bundle = Bundle::new(vec![], vec![], vec![t]).unwrap();
    let view = bundle.table_view(0, f).unwrap();
    let witness: Vec<_> = (1..=4 * count as i64).collect();
    let result = view
        .evaluate(4, &witness, &[], &[], &Recording::default())
        .unwrap();
    for row in 0..4 {
        let mut expected = vec![0; count + 1];
        expected[0] = witness[row * count + count - 1];
        expected[count] = expected[0];
        assert_eq!(
            &result[row * (count + 1)..(row + 1) * (count + 1)],
            expected
        );
    }
}

#[test]
fn actual_rows_keep_fallible_constants_and_embeddings_in_each_row() {
    let f = Identity::KoalaBear;
    let e = Identity::KoalaBearExt8;
    let t = table(
        Expression::new(
            vec![],
            vec![Node::Constant(f, "2".into()), Node::Embed(e, 0)],
            vec![1],
        )
        .unwrap(),
        vec![],
        vec![Assertion {
            output: 0,
            scope: Scope::All,
        }],
    );
    let bundle = Bundle::new(vec![], vec![], vec![t]).unwrap();
    let view = bundle.table_view(0, e).unwrap();
    let expected = vec![
        constant(e, "0"),
        constant(f, "2"),
        Event::Embed(f, e),
        constant(f, "2"),
        Event::Embed(f, e),
        constant(f, "2"),
        Event::Embed(f, e),
        constant(f, "2"),
        Event::Embed(f, e),
    ];
    for (fail_at, error) in [
        (1, "test-constant"),
        (4, "test-constant"),
        (5, "test-embed"),
    ] {
        let recording = Recording {
            fail_at: Some(fail_at),
            ..Recording::default()
        };
        assert_eq!(
            view.evaluate(4, &[], &[], &[], &recording).unwrap_err(),
            Error(error)
        );
        assert_eq!(*recording.events.borrow(), expected[..fail_at]);
    }
    let recording = Recording::default();
    assert_eq!(view.evaluate(4, &[], &[], &[], &recording).unwrap(), [2; 4]);
    assert_eq!(*recording.events.borrow(), expected);
}
