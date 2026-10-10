//! The interaction view against hand-derived descriptors, the reference
//! Bundle evaluator's balances and an independent integer model of
//! `koala-bear.ext8-binomial3`.
use super::*;
use crate::{KoalaBearExt8, ring::Budget};
use std::collections::BTreeMap;
use zkc_runtime::relation::{
    Assertion, Authority, Channel, ChannelKind, Columns, Group, Height, HeightAuthority, Input,
    Interaction, InteractionDescriptor, Locality, ReadModel, Scope, Side, Slot, Table,
};
use zkc_runtime::ring::{Expression, Node};

const P: u64 = 2_130_706_433;
const KB: Identity = Identity::KoalaBear;
const EXT: Identity = Identity::KoalaBearExt8;

/// F_p[X]/(X^8 - 3) in the ascending basis, with machine integers only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Ext([u64; 8]);
impl Ext {
    fn base(n: u64) -> Self {
        let mut c = [0; 8];
        c[0] = n % P;
        Self(c)
    }
    fn mul(self, o: Self) -> Self {
        let mut wide = [0u128; 15];
        for i in 0..8 {
            for j in 0..8 {
                wide[i + j] += u128::from(self.0[i]) * u128::from(o.0[j]);
            }
        }
        Self(std::array::from_fn(|k| {
            let high = if k < 7 { wide[k + 8] } else { 0 };
            ((wide[k] + 3 * high) % u128::from(P)) as u64
        }))
    }
    fn native(self) -> KoalaBearExt8 {
        KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::from_u64(self.0[i]))
    }
    fn of(value: KoalaBearExt8) -> Self {
        let c: &[KoalaBear] = value.as_basis_coefficients_slice();
        Self(std::array::from_fn(|i| u64::from(c[i].as_canonical_u32())))
    }
}
fn samples(seed: u64, n: usize) -> Vec<Ext> {
    let mut state = seed;
    (0..n)
        .map(|_| {
            Ext(std::array::from_fn(|_| {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                (state >> 33) % P
            }))
        })
        .collect()
}
fn code<T: std::fmt::Debug>(result: Result<T>) -> String {
    result.unwrap_err().code
}
fn records<S: crate::ring::Carrier>(
    view: &InteractionView<'_>,
    assignments: &[S],
    rows: u64,
    budget: &mut Budget,
) -> Result<Vec<S>> {
    points(
        view,
        assignments,
        rows,
        true,
        &Policy::default(),
        budget,
        usize::MAX,
    )
}

/// Every interaction form: a local key 0 and the largest key, a field balance
/// with no declared bound, a declared 0 and a declared 2^64-1, multiset
/// pushes and pulls with bounds 1, 3 and p-1 (the largest below the KoalaBear
/// characteristic), an empty tuple, every scope kind, an Ext8 tuple output
/// over KoalaBear columns, outputs shared by several records, a read windowed
/// only by an interaction, and a public slot that only the assertion reads.
fn assorted(height: Height) -> Bundle {
    let read = |group, offset, column| Input::Read {
        group,
        offset,
        column,
    };
    let field_balance = |locality, scope, count, declared| Interaction::FieldBalance {
        channel: 0,
        locality,
        scope,
        tuple: vec![0, 1],
        count,
        declared,
    };
    let multiset = |channel, locality, scope, side, tuple, bound| Interaction::Multiset {
        channel,
        locality,
        scope,
        side,
        tuple,
        multiplicity: 5,
        bound,
    };
    Bundle::new(
        vec![Slot {
            name: "s".into(),
            field: KB,
        }],
        vec![
            Channel {
                name: "balance".into(),
                kind: ChannelKind::FieldBalance,
                tuple: vec![EXT, KB],
                count: KB,
            },
            Channel {
                name: "bag".into(),
                kind: ChannelKind::Multiset,
                tuple: vec![KB],
                count: KB,
            },
            Channel {
                name: "flag".into(),
                kind: ChannelKind::Multiset,
                tuple: vec![],
                count: KB,
            },
        ],
        vec![Table {
            name: "mixed".into(),
            optional: true,
            height,
            read_model: ReadModel::Finite,
            groups: vec![
                Group {
                    name: "w".into(),
                    authority: Authority::Witness,
                    field: KB,
                    width: 3,
                },
                Group {
                    name: "q".into(),
                    authority: Authority::Public,
                    field: KB,
                    width: 1,
                },
            ],
            arena: Expression::new(
                vec![KB; 7],
                vec![
                    Node::Input(0),                 // 0 w1
                    Node::Embed(EXT, 0),            // 1 out 0: w1 in Ext8
                    Node::Mul(0, 0),                // 2 out 1: w1^2
                    Node::Input(3),                 // 3 out 2: q
                    Node::Constant(KB, "1".into()), // 4 out 3: 1
                    Node::Input(4),                 // 5 out 4: w0@1
                    Node::Input(5),                 // 6 out 5: w2
                    Node::Input(6),                 // 7 out 6: w0@-1
                    Node::Input(2),                 // 8 w0
                    Node::Mul(8, 0),                // 9
                    Node::Input(1),                 // 10 s
                    Node::Neg(10),                  // 11
                    Node::Add(9, 11),               // 12 out 7: w0*w1 - s
                ],
                vec![1, 2, 3, 4, 5, 6, 7, 12],
            )
            .unwrap(),
            inputs: vec![
                read(0, 0, 1),
                Input::Public(0),
                read(0, 0, 0),
                read(1, 0, 0),
                read(0, 1, 0),
                read(0, 0, 2),
                read(0, -1, 0),
            ],
            assertions: vec![Assertion {
                output: 7,
                scope: Scope::All,
            }],
            interactions: vec![
                field_balance(Locality::Local(0), Scope::Interior(1, 1), 2, None),
                field_balance(Locality::Global, Scope::Interval(1, 4), 3, Some(0)),
                multiset(1, Locality::Global, Scope::First, Side::Pull, vec![4], 3),
                multiset(
                    1,
                    Locality::Local(4096),
                    Scope::Interval(0, 4),
                    Side::Push,
                    vec![4],
                    1,
                ),
                multiset(2, Locality::Global, Scope::All, Side::Push, vec![], P - 1),
                field_balance(Locality::Global, Scope::Last, 6, Some(u64::MAX)),
            ],
        }],
    )
    .unwrap()
}
fn instance_height(min: u32, max: u32, power_of_two: bool) -> Height {
    Height {
        authority: HeightAuthority::Instance,
        min,
        max,
        power_of_two,
    }
}
#[allow(clippy::too_many_arguments)] // One argument per descriptor field.
fn descriptor(
    kind: ChannelKind,
    channel: u64,
    side: Option<Side>,
    local: Option<u32>,
    (begin, end): (u64, u64),
    arity: u64,
    bound: Option<u64>,
    (tuple_degree, count_degree): (u64, u64),
) -> InteractionDescriptor {
    InteractionDescriptor {
        kind,
        channel,
        side,
        local,
        begin,
        end,
        arity,
        bound,
        tuple_degree,
        count_degree,
    }
}

#[test]
fn descriptors_represent_every_interaction_form() {
    use ChannelKind::{FieldBalance, Multiset};
    let bundle = assorted(instance_height(2, 64, false));
    let view = bundle.interaction_view(0, EXT).unwrap();
    // Arities 2, 2, 1, 1, 0, 2 plus one count each.
    assert_eq!(view.interactions(8).unwrap(), (6, 14));
    let expected = [
        descriptor(FieldBalance, 0, None, Some(0), (1, 7), 2, None, (2, 1)),
        descriptor(FieldBalance, 0, None, None, (1, 4), 2, Some(0), (2, 0)),
        descriptor(
            Multiset,
            1,
            Some(Side::Pull),
            None,
            (0, 1),
            1,
            Some(3),
            (1, 1),
        ),
        descriptor(
            Multiset,
            1,
            Some(Side::Push),
            Some(4096),
            (0, 4),
            1,
            Some(1),
            (1, 1),
        ),
        descriptor(
            Multiset,
            2,
            Some(Side::Push),
            None,
            (0, 8),
            0,
            Some(P - 1),
            (0, 1),
        ),
        descriptor(
            FieldBalance,
            0,
            None,
            None,
            (7, 8),
            2,
            Some(u64::MAX),
            (2, 1),
        ),
    ];
    for (i, d) in expected.iter().enumerate() {
        assert_eq!(
            view.interaction(8, i as u64).unwrap(),
            *d,
            "interaction {i}"
        );
    }
    assert_eq!(
        view.interaction(8, 6).unwrap_err().0,
        "relation-table-interaction-index"
    );
    assert_eq!(
        view.interaction(8, u64::MAX).unwrap_err().0,
        "relation-table-interaction-index"
    );
    // Nodes 13, inputs 7, groups 2, publics 1, assertions 1, width 14,
    // assertion reads 2 and record reads 3+2+2+2+1+3, plus 1; a record row
    // adds nodes, inputs, width and 1.
    assert_eq!((view.work(), view.point_work()), (54, 35));
    // Interior(1, 1) keeps its rows at the largest height.
    assert_eq!(view.interaction(64, 0).unwrap().end, 63);
}

#[test]
fn interaction_windows_and_heights_are_checked_before_any_descriptor() {
    let bundle = assorted(instance_height(2, 64, false));
    let view = bundle.interaction_view(0, EXT).unwrap();
    // Interval(1, 4) needs height 4; Interval(0, 4) reading row + 1 needs 5.
    // The assertion alone admits every height, as the polynomial view does.
    assert_eq!(view.interactions(2), Err(Error("bundle-scope-height")));
    assert_eq!(view.interactions(4), Err(Error("bundle-window")));
    assert_eq!(view.interaction(4, 5), Err(Error("bundle-window")));
    let polynomial = bundle.polynomial_view(0, KB).unwrap();
    assert!(polynomial.shape(2).is_ok() && polynomial.shape(4).is_ok());
    for (height, cause) in [
        (0, "bundle-height"),
        (1, "bundle-height"),
        (128, "bundle-height"),
        (1 << 32, "bundle-height"),
    ] {
        assert_eq!(view.interactions(height), Err(Error(cause)), "{height}");
        assert_eq!(view.interaction(height, 0), Err(Error(cause)), "{height}");
    }
    assert!(view.interactions(6).is_ok());
    assert!(view.interactions(64).is_ok());
}

#[test]
fn metadata_admits_single_rows_and_non_power_of_two_heights() {
    let original = assorted(instance_height(2, 64, false));
    for power_of_two in [false, true] {
        let mut table = original.tables()[0].clone();
        table.height = instance_height(1, 16, power_of_two);
        table.read_model = ReadModel::Cyclic;
        for interaction in &mut table.interactions {
            match interaction {
                Interaction::FieldBalance { scope, .. } | Interaction::Multiset { scope, .. } => {
                    *scope = Scope::All;
                }
            }
        }
        let bundle = Bundle::new(
            original.publics().to_vec(),
            original.channels().to_vec(),
            vec![table],
        )
        .unwrap();
        let view = bundle.interaction_view(0, EXT).unwrap();
        for height in [1, 2, 3, 6, 12, 16] {
            if power_of_two && !u64::is_power_of_two(height) {
                assert_eq!(view.interactions(height), Err(Error("bundle-height")));
            } else {
                assert_eq!(view.interactions(height).unwrap(), (6, 14));
                let descriptor = view.interaction(height, 0).unwrap();
                assert_eq!((descriptor.begin, descriptor.end), (0, height));
            }
        }
    }
}

#[test]
fn interaction_views_use_declared_policies_without_polynomial_premises() {
    // A fixed height of 12 has no two-adic domain. Interaction substitution
    // and descriptors still admit it, while polynomial kernels refuse it.
    let fixed = assorted(Height {
        authority: HeightAuthority::Fixed,
        min: 12,
        max: 12,
        power_of_two: false,
    });
    let view = fixed.interaction_view(0, EXT).unwrap();
    assert_eq!(
        view.policy(),
        (
            true,
            Height {
                authority: HeightAuthority::Fixed,
                min: 12,
                max: 12,
                power_of_two: false
            }
        )
    );
    assert_eq!(view.work(), 54);
    assert_eq!(view.interactions(12).unwrap(), (6, 14));
    assert_eq!(
        fixed.polynomial_view(0, EXT).unwrap_err().0,
        "bundle-polynomial-two-adic"
    );
    // A range keeps its declared bounds, not its two-adic sub-range.
    let range = assorted(instance_height(3, 20, true));
    assert_eq!(
        range.interaction_view(0, EXT).unwrap().policy().1,
        instance_height(3, 20, true)
    );
    assert!(range.interaction_view(0, EXT).is_ok());
    // The Ext8 tuple output: the whole-table admission refuses KoalaBear for
    // the policy and the interaction kernels; the assertion-only polynomial
    // admission does not visit it.
    let bundle = assorted(instance_height(2, 64, false));
    assert!(bundle.polynomial_view(0, KB).is_ok());
    assert_eq!(
        bundle.interaction_view(0, KB).unwrap_err().0,
        "relation-table-carrier"
    );
    for carrier in [Identity::Bls12381Fr, Identity::None] {
        assert_eq!(
            bundle.interaction_view(0, carrier).unwrap_err().0,
            "relation-table-carrier"
        );
    }
    assert_eq!(
        bundle.interaction_view(1, EXT).unwrap_err().0,
        "relation-table-index"
    );
}

/// The record of one row written from the bundle's definition: inputs w1, s,
/// w0, q, w0@1, w2, w0@-1.
fn assorted_reference(v: &[Ext]) -> Vec<Ext> {
    let [w1, _s, _w0, q, next, w2, previous] = v.try_into().unwrap();
    let square = w1.mul(w1);
    let one = Ext::base(1);
    vec![
        w1, square, q, w1, square, one, next, w2, next, w2, w2, w1, square, previous,
    ]
}

#[test]
fn record_points_match_the_integer_model_and_keep_input_numbering() {
    let bundle = assorted(instance_height(2, 64, false));
    let view = bundle.interaction_view(0, EXT).unwrap();
    let rows = 5;
    let values = samples(17, rows * 7);
    let assignments: Vec<_> = values.iter().map(|e| e.native()).collect();
    let mut budget = Budget::default();
    let got = records(&view, &assignments, rows as u64, &mut budget).unwrap();
    assert_eq!(budget.spent, 54 + rows as u64 * 35);
    let expected: Vec<_> = values.chunks(7).flat_map(assorted_reference).collect();
    assert_eq!(got.into_iter().map(Ext::of).collect::<Vec<_>>(), expected);
    // The public slot only the assertion reads keeps its column; its value is
    // ignored.
    let mut changed = assignments.clone();
    changed[1] = KoalaBearExt8::from(KoalaBear::from_u64(99));
    assert_eq!(
        records(&view, &changed, rows as u64, &mut Budget::default()).unwrap(),
        records(&view, &assignments, rows as u64, &mut Budget::default()).unwrap()
    );
    // One row equals the corresponding row of the batch.
    let single = records(&view, &assignments[14..21], 1, &mut Budget::default()).unwrap();
    assert_eq!(
        single.into_iter().map(Ext::of).collect::<Vec<_>>(),
        expected[28..42]
    );
}

#[test]
fn record_batches_check_shape_storage_and_work_before_preparation() {
    let bundle = assorted(instance_height(2, 64, false));
    let view = bundle.interaction_view(0, EXT).unwrap();
    let values: Vec<_> = samples(3, 15).iter().map(|e| e.native()).collect();
    let assignments = &values[..14];
    for (len, rows) in [(13, 2), (15, 2), (14, 3), (14, u64::MAX), (0, 1 << 62)] {
        let mut budget = Budget::default();
        assert_eq!(
            code(records(&view, &values[..len], rows, &mut budget)),
            "refused:relation-table-point-shape"
        );
        assert_eq!(budget.spent, 0);
    }
    // Zero rows are empty but still charged.
    let mut budget = Budget::default();
    assert!(
        records::<KoalaBearExt8>(&view, &[], 0, &mut budget)
            .unwrap()
            .is_empty()
    );
    assert_eq!(budget.spent, 54);
    // The work charge is one charge, refused whole.
    let mut budget = Budget {
        limit: 54 + 2 * 35 - 1,
        spent: 0,
    };
    assert_eq!(
        code(records(&view, assignments, 2, &mut budget)),
        "exhausted:ring-work"
    );
    assert_eq!(budget.spent, 0);
    let run = |policy: &Policy, available| {
        points(
            &view,
            assignments,
            2,
            true,
            policy,
            &mut Budget::default(),
            available,
        )
        .map(|v| v.len())
        .map_err(|e| e.code)
    };
    // The result alone must fit the allowance.
    let result = crate::value::size(28, 32).unwrap();
    assert_eq!(
        run(&Policy::default(), result - 1),
        Err("exhausted:output-bytes".into())
    );
    assert_eq!(run(&Policy::default(), result), Ok(28));
    // Result, scratch and the prepared record sub-DAG, bounded by the arena's
    // admission charge and one output per record slot, must fit together.
    let arena = &view.definition().arena;
    let cells =
        crate::ring::scratch_cells::<KoalaBearExt8>(arena.nodes().len(), true).unwrap() + 28;
    let peak = crate::value::size(cells, 32).unwrap() + arena_bytes(arena) + 14 * OUTPUT_BYTES;
    for (bytes, expected) in [
        (peak - 1, Err("exhausted:output-bytes".into())),
        (peak, Ok(28)),
    ] {
        let policy = Policy {
            max_value_bytes: bytes,
            ..Policy::default()
        };
        assert_eq!(run(&policy, usize::MAX), expected);
    }
    let policy = Policy {
        max_table_elements: cells - 1,
        ..Policy::default()
    };
    assert_eq!(
        run(&policy, usize::MAX),
        Err("exhausted:element-limit".into())
    );
}

#[test]
fn tables_without_interactions_have_empty_records() {
    let bundle = Bundle::parse(include_str!(
        "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle.json"
    ))
    .unwrap();
    for carrier in [KB, EXT] {
        let view = bundle.interaction_view(0, carrier).unwrap();
        assert_eq!(view.interactions(8).unwrap(), (0, 0));
        assert_eq!(
            view.interaction(8, 0).unwrap_err().0,
            "relation-table-interaction-index"
        );
        // Nodes, inputs 11, groups 2, publics 3, assertions 9 and their reads
        // (x y p | x | y | acc | x' y | y' p k | acc' acc p x k | acc | x'),
        // plus 1; a row adds nodes, inputs and 1.
        let nodes = view.definition().arena.nodes().len() as u64;
        let reads: u64 = 3 + 1 + 1 + 1 + 2 + 3 + 5 + 1 + 1;
        assert_eq!(view.work(), nodes + 11 + 2 + 3 + 9 + reads + 1);
        assert_eq!(view.point_work(), nodes + 11 + 1);
    }
    let view = bundle.interaction_view(0, KB).unwrap();
    let mut budget = Budget::default();
    let zeros = vec![KoalaBear::ZERO; 3 * 11];
    assert!(records(&view, &zeros, 3, &mut budget).unwrap().is_empty());
    assert_eq!(budget.spent, view.work() + 3 * view.point_work());
    // An empty record width still checks the assignment shape.
    assert_eq!(
        code(records(&view, &zeros, 2, &mut Budget::default())),
        "refused:relation-table-point-shape"
    );
}

/// Rows of every arena input of a present table on its own data, read
/// directly through the bundle's bindings.
fn actual_assignments(
    bundle: &Bundle,
    table: usize,
    height: u32,
    groups: &[&Columns],
    publics: &[Columns],
) -> Vec<KoalaBear> {
    let t = &bundle.tables()[table];
    let mut values = Vec::new();
    for row in 0..height {
        for input in &t.inputs {
            let text = match *input {
                Input::Public(slot) => &publics[slot as usize][0],
                Input::Read {
                    group,
                    offset,
                    column,
                } => {
                    let width = t.groups[group as usize].width;
                    let r = (i64::from(row) + i64::from(offset)).rem_euclid(i64::from(height));
                    &groups[group as usize][(r as u32 * width + column) as usize]
                }
            };
            values.push(KoalaBear::from_u64(text.parse().unwrap()));
        }
    }
    values
}

#[test]
fn machine_records_on_the_subgroup_aggregate_to_the_reference_balances() {
    let directory = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../compiler/adapters/accumulator-machine/fixtures"
    );
    let read = |name: &str| std::fs::read_to_string(format!("{directory}/{name}")).unwrap();
    let bundle = Bundle::parse(&read("bundle.json")).unwrap();
    for run in ["store-load", "arithmetic-only", "store-load-initial-seven"] {
        let parse = |name: &str| -> serde_json::Value {
            serde_json::from_str(&read(&format!("{run}/{name}"))).unwrap()
        };
        let configuration = bundle
            .decode_configuration(&parse("bundle-configuration.json"))
            .unwrap();
        let instance = bundle
            .decode_instance(&parse("bundle-instance.json"))
            .unwrap();
        let witness = bundle
            .decode_witness(&parse("bundle-witness.json"))
            .unwrap();
        let evaluation = bundle
            .evaluate(
                &configuration,
                &instance,
                &witness,
                &Arithmetic::<KoalaBear>(PhantomData),
            )
            .unwrap();
        assert!(evaluation.satisfied, "{run}");
        let admitted = bundle.admit(&configuration, &instance, &witness).unwrap();
        // (channel, tuple) -> (push, pull), only from the subgroup records
        // inside each scope, multiplicities read as canonical naturals here.
        let mut totals: BTreeMap<(u64, Vec<u32>), (u64, u64)> = BTreeMap::new();
        for (t, table) in bundle.tables().iter().enumerate() {
            if !admitted.present[t] {
                continue;
            }
            let height = admitted.heights[t];
            let mut next = [0usize; 3];
            let groups: Vec<&Columns> = table
                .groups
                .iter()
                .map(|g| match g.authority {
                    Authority::Config => {
                        next[0] += 1;
                        &configuration.tables[t].1[next[0] - 1]
                    }
                    Authority::Public => {
                        next[1] += 1;
                        &instance.tables[t].as_ref().unwrap().1[next[1] - 1]
                    }
                    Authority::Witness => {
                        next[2] += 1;
                        &witness.tables[t].as_ref().unwrap()[next[2] - 1]
                    }
                })
                .collect();
            let view = bundle.interaction_view(t, KB).unwrap();
            let (count, width) = view.interactions(u64::from(height)).unwrap();
            let assignments = actual_assignments(&bundle, t, height, &groups, &instance.publics);
            let values = records(
                &view,
                &assignments,
                u64::from(height),
                &mut Budget::default(),
            )
            .unwrap();
            assert_eq!(values.len() as u64, u64::from(height) * width);
            let mut column = 0;
            for i in 0..count {
                let d = view.interaction(u64::from(height), i).unwrap();
                assert_eq!(
                    (d.kind, d.local, d.bound),
                    (ChannelKind::Multiset, None, Some(1))
                );
                for row in d.begin..d.end {
                    let at = (row * width) as usize + column;
                    let tuple: Vec<u32> = values[at..at + d.arity as usize]
                        .iter()
                        .map(|v| v.as_canonical_u32())
                        .collect();
                    let n = u64::from(values[at + d.arity as usize].as_canonical_u32());
                    let entry = totals.entry((d.channel, tuple)).or_default();
                    if d.side == Some(Side::Push) {
                        entry.0 += n;
                    } else {
                        entry.1 += n;
                    }
                }
                column += d.arity as usize + 1;
            }
            assert_eq!(column as u64, width);
        }
        let reference: BTreeMap<(u64, Vec<u32>), (u64, u64)> = evaluation
            .balances
            .iter()
            .map(|b| {
                (
                    (
                        b.channel as u64,
                        b.tuple.iter().map(|v| v[0].parse().unwrap()).collect(),
                    ),
                    (b.push, b.pull),
                )
            })
            .collect();
        assert_eq!(totals, reference, "{run}");
    }
}

#[test]
fn registry_references_and_signatures_cover_the_interaction_kernels() {
    let bundle = assorted(Height {
        authority: HeightAuthority::Fixed,
        min: 12,
        max: 12,
        power_of_two: false,
    });
    let body = bundle.encode().to_string();
    let mut registry = Registry::default();
    registry.insert(bundle.identity(), &body).unwrap();
    assert!(
        registry
            .interaction_reference(bundle.identity(), 0, EXT)
            .is_ok()
    );
    for (identity, table, carrier, expected) in [
        (bundle.identity(), 0, KB, "refused:relation-table-carrier"),
        ("missing", 0, EXT, "refused:relation-asset-missing"),
        (
            bundle.identity(),
            u64::MAX,
            EXT,
            "refused:relation-table-index",
        ),
    ] {
        assert_eq!(
            code(registry.interaction_reference(identity, table, carrier)),
            expected
        );
    }
    let index = crate::domains::KOALA_BEAR.physical(Type::Index).unwrap();
    for (contract, inputs, outputs) in [
        ("relation.table_policy", 0, 5),
        ("relation.table_interactions", 1, 2),
        ("relation.table_interaction", 2, 12),
    ] {
        for (field, table, accepted) in [
            ("koala-bear", "0", true),
            ("koala-bear.ext8-binomial3", "1048576", true),
            ("koala-bear", "1048577", false),
            ("bls12-381.fr", "0", false),
        ] {
            let binding = OperationBinding {
                contract: contract.into(),
                arguments: vec![field.into(), table.into()],
                implementation: format!("plonky3/{contract}"),
            };
            let got = signature(&binding);
            assert_eq!(got.is_some(), accepted);
            if let Some(got) = got {
                assert_eq!(got.inputs, vec![index.clone(); inputs]);
                assert_eq!(got.outputs, vec![index.clone(); outputs]);
                assert_eq!(got, binding.signature().unwrap());
            }
        }
    }
    for field in ["koala-bear", "koala-bear.ext8-binomial3"] {
        let binding = OperationBinding {
            contract: "relation.table_record_points".into(),
            arguments: vec![field.into(), "0".into()],
            implementation: "plonky3/relation.table_record_points".into(),
        };
        let got = signature(&binding).unwrap();
        assert_eq!((got.inputs.len(), got.outputs.len()), (2, 1));
        assert_eq!(got.inputs[0], got.outputs[0]);
        assert_eq!(got.inputs[1], index);
        assert_eq!(got, binding.signature().unwrap());
    }
}

#[test]
fn huge_row_counts_without_inputs_are_refused_before_any_charge() {
    // No arena inputs: an empty assignment matches every row count, so the
    // result size alone bounds the batch.
    let bundle = Bundle::parse(
        r#"["zkc.relation-bundle/0",[],[["flag","multiset",["koala-bear"],"koala-bear"]],
        [["c","required",["fixed",2],"finite",[],
        ["zkc.ring/0",[],[["constant","koala-bear","5"],["constant","koala-bear","1"]],[0,1]],
        [],[],[["multiset",0,["global"],["first"],"push",[0],1,1]]]]]"#,
    )
    .unwrap();
    let view = bundle.interaction_view(0, KB).unwrap();
    // Nodes 2, record width 2, plus 1; a row adds nodes, width and 1.
    assert_eq!((view.work(), view.point_work()), (5, 5));
    let mut budget = Budget::default();
    assert_eq!(
        records::<KoalaBear>(&view, &[], 2, &mut budget).unwrap(),
        [5, 1, 5, 1].map(KoalaBear::from_u64)
    );
    assert_eq!(budget.spent, 5 + 2 * 5);
    for rows in [1 << 40, u64::MAX] {
        let mut budget = Budget::default();
        assert_eq!(
            code(records::<KoalaBear>(&view, &[], rows, &mut budget)),
            "exhausted:element-limit"
        );
        assert_eq!(budget.spent, 0);
    }
}
