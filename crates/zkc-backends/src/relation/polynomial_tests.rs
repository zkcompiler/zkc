//! The polynomial view against hand-derived descriptors, the dense table view
//! and an independent integer model of `koala-bear.ext8-binomial3`.
use super::*;
use crate::{KoalaBearExt8, ring::Budget};
use zkc_runtime::relation::{
    Assertion, Authority, Channel, ChannelKind, Columns, Group, Height, HeightAuthority, Input,
    Interaction, Locality, PolynomialInput, PolynomialShape, ReadModel, Scope, Slot, Table,
};
use zkc_runtime::ring::{Expression, Node};

const P: u64 = 2_130_706_433;

/// F_p[X]/(X^8 - 3) in the ascending basis, with machine integers only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Ext([u64; 8]);
impl Ext {
    fn base(n: u64) -> Self {
        let mut c = [0; 8];
        c[0] = n % P;
        Self(c)
    }
    fn add(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| (self.0[i] + o.0[i]) % P))
    }
    fn sub(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| (self.0[i] + P - o.0[i]) % P))
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
/// Deterministic extension values with every coordinate in use.
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
fn kb(values: &[u64]) -> Vec<KoalaBear> {
    values.iter().map(|n| KoalaBear::from_u64(*n)).collect()
}
fn recurrence() -> Bundle {
    Bundle::parse(include_str!(
        "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle.json"
    ))
    .unwrap()
}
fn code<T: std::fmt::Debug>(result: Result<T>) -> String {
    result.unwrap_err().code
}

/// The recurrence constraints written from the AIR's definition, not from
/// its exported arena: columns x, y, p, acc; next-row x', y', acc'; fixed k;
/// publics x0, y0 and the final accumulator.
fn recurrence_reference(v: &[Ext]) -> Vec<Ext> {
    let [x, y, p, acc, x1, y1, acc1, k, x0, y0, last] = v.try_into().unwrap();
    let step = Ext::base(123_456_789);
    vec![
        p.sub(x.mul(y)),
        x.sub(x0),
        y.sub(y0),
        acc,
        x1.sub(y),
        y1.sub(p.add(k).add(step)),
        acc1.sub(acc.add(p.mul(x).mul(k))),
        acc.sub(last),
        x1.sub(x0),
    ]
}

#[test]
fn recurrence_shape_descriptors_and_scopes_follow_the_bundle() {
    let bundle = recurrence();
    for carrier in [Identity::KoalaBear, Identity::KoalaBearExt8] {
        let view = bundle.polynomial_view(0, carrier).unwrap();
        // Degrees 2, 1, 1, 1 | 1, 1, 3 | 1, 1 on h = 8: the cubic transition
        // has quotient degree 3*7 - 7 = 14, so two chunks of length 8.
        assert_eq!(
            view.shape(8).unwrap(),
            PolynomialShape {
                witness_width: 4,
                config_width: 1,
                public_width: 0,
                public_slots: 3,
                inputs: 11,
                assertions: 9,
                quotient_chunks: 2,
            }
        );
        let descriptors: Vec<_> = (0..11)
            .map(|i| {
                let d = view.input(8, i).unwrap();
                (d.kind, d.column, d.rotation)
            })
            .collect();
        assert_eq!(
            descriptors,
            [
                (1, 0, 0),
                (1, 1, 0),
                (1, 2, 0),
                (1, 3, 0),
                (1, 0, 1),
                (1, 1, 1),
                (1, 3, 1),
                (2, 0, 0),
                (0, 0, 0),
                (0, 1, 0),
                (0, 2, 0)
            ]
        );
        let scopes: Vec<_> = (0..9).map(|a| view.scope(8, a).unwrap()).collect();
        assert_eq!(
            scopes,
            [
                (0, 8),
                (0, 1),
                (0, 1),
                (0, 1),
                (0, 7),
                (0, 7),
                (0, 7),
                (7, 8),
                (7, 8)
            ]
        );
        assert_eq!(
            view.input(8, 11).unwrap_err().0,
            "relation-table-input-index"
        );
        assert_eq!(
            view.input(8, u64::MAX).unwrap_err().0,
            "relation-table-input-index"
        );
        assert_eq!(
            view.scope(8, 9).unwrap_err().0,
            "relation-table-assertion-index"
        );
        for height in [0, 1, 3, 6, 7, 9, u64::MAX] {
            assert_eq!(
                view.shape(height).unwrap_err().0,
                "bundle-polynomial-two-adic"
            );
            assert_eq!(
                view.input(height, 0).unwrap_err().0,
                "bundle-polynomial-two-adic"
            );
            assert_eq!(
                view.scope(height, 0).unwrap_err().0,
                "bundle-polynomial-two-adic"
            );
        }
        for height in [2, 4, 16, 1 << 40] {
            assert_eq!(view.shape(height).unwrap_err().0, "bundle-height");
            assert_eq!(view.input(height, 0).unwrap_err().0, "bundle-height");
            assert_eq!(view.scope(height, 0).unwrap_err().0, "bundle-height");
        }
    }
}

#[test]
fn recurrence_extension_points_match_an_independent_integer_model() {
    let bundle = recurrence();
    let ext = bundle.polynomial_view(0, Identity::KoalaBearExt8).unwrap();
    let base = bundle.polynomial_view(0, Identity::KoalaBear).unwrap();
    for seed in 1..=4 {
        // Out-of-domain points: every substituted input is a full extension
        // element, including the fixed and public columns.
        let v = samples(seed, 11);
        let native: Vec<_> = v.iter().map(|e| e.native()).collect();
        let mut budget = Budget::default();
        let got = points(
            &ext,
            &native,
            1,
            false,
            &Policy::default(),
            &mut budget,
            usize::MAX,
        )
        .unwrap();
        assert_eq!(
            got.into_iter().map(Ext::of).collect::<Vec<_>>(),
            recurrence_reference(&v)
        );
        assert_eq!(budget.spent, ext.work() + ext.point_work());
        // Base-field points agree with their embedding in Ext8.
        let small: Vec<_> = v.iter().map(|e| e.0[0]).collect();
        let lifted: Vec<_> = small.iter().map(|n| Ext::base(*n)).collect();
        let got = points(
            &base,
            &kb(&small),
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX,
        )
        .unwrap();
        assert_eq!(
            got.iter()
                .map(|x| Ext::base(u64::from(x.as_canonical_u32())))
                .collect::<Vec<_>>(),
            recurrence_reference(&lifted)
        );
    }
    let short = samples(9, 10)
        .iter()
        .map(|e| e.native())
        .collect::<Vec<_>>();
    assert_eq!(
        code(points(
            &ext,
            &short,
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )),
        "refused:relation-table-point-shape"
    );
    assert_eq!(
        code(points(
            &ext,
            &kb(&[0; 11]),
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )),
        "refused:relation-table-carrier"
    );
}

/// The recurrence's honest data with a changed first x, as combined witness,
/// configuration and public-data matrices, and its dense residuals at h = 8.
/// The change makes residuals nonzero on the first and, through the wrapping
/// next-row read, the last row.
fn changed_recurrence() -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<KoalaBear>) {
    let bundle = recurrence();
    let fixture = |text: &str| -> serde_json::Value { serde_json::from_str(text).unwrap() };
    let c = bundle
        .decode_configuration(&fixture(include_str!(
            "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle-configuration.json"
        )))
        .unwrap();
    let i = bundle
        .decode_instance(&fixture(include_str!(
            "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle-instance.json"
        )))
        .unwrap();
    let mut w = bundle
        .decode_witness(&fixture(include_str!(
            "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle-witness.json"
        )))
        .unwrap();
    w.tables[0].as_mut().unwrap()[0][0] = "3".into();
    let rows_view = bundle.table_view(0, Identity::KoalaBear).unwrap();
    let data = rows_view.slice(&c, &i, &w).unwrap();
    let parse = |s: &Columns| -> Vec<u64> { s.iter().map(|v| v.parse().unwrap()).collect() };
    let (witness, configuration, public) = (
        parse(&data.witness),
        parse(&data.configuration),
        parse(&data.public_data),
    );
    let dense = rows(
        rows_view,
        8,
        &kb(&witness),
        &kb(&configuration),
        &kb(&public),
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    (witness, configuration, public, dense)
}
/// One row's assignment of every arena input, read from combined matrices
/// through the descriptors alone. A public group is the last matrix.
fn assignment(view: &PolynomialView<'_>, h: u64, row: u64, matrices: [&[u64]; 4]) -> Vec<u64> {
    let shape = view.shape(h).unwrap();
    let widths = [shape.witness_width, shape.config_width, shape.public_width];
    (0..shape.inputs)
        .map(|slot| {
            let PolynomialInput {
                kind,
                column,
                rotation,
            } = view.input(h, slot).unwrap();
            match kind {
                0 => matrices[0][column as usize],
                k => {
                    let k = k as usize;
                    matrices[k][(((row + rotation) % h) * widths[k - 1] + column) as usize]
                }
            }
        })
        .collect()
}

#[test]
fn descriptors_reproduce_dense_residuals_at_every_scope_boundary() {
    let (witness, configuration, public, dense) = changed_recurrence();
    let bundle = recurrence();
    let view = &bundle.polynomial_view(0, EXT).unwrap();
    let shape = view.shape(8).unwrap();
    let mut nonzero = 0;
    for a in 0..shape.assertions {
        let (begin, end) = view.scope(8, a).unwrap();
        let mut boundary = vec![begin, end - 1];
        boundary.dedup();
        for row in boundary {
            let assignment: Vec<_> =
                assignment(view, 8, row, [&public, &witness, &configuration, &[]])
                    .into_iter()
                    .map(|n| Ext::base(n).native())
                    .collect();
            let values = points(
                view,
                &assignment,
                1,
                false,
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX,
            )
            .unwrap();
            let expected = dense[(row * shape.assertions + a) as usize];
            assert_eq!(values[a as usize], KoalaBearExt8::from(expected));
            nonzero += usize::from(expected != KoalaBear::ZERO);
        }
    }
    assert!(nonzero >= 2);
}

const KB: Identity = Identity::KoalaBear;
const EXT: Identity = Identity::KoalaBearExt8;

/// A finite table with two groups per witness and configuration authority, a
/// public group, a negative offset, assertion order unlike arena order,
/// repeated outputs and an Ext8 interaction-only output whose input is never
/// needed by an assertion.
fn layered(model: ReadModel, height: Height) -> std::result::Result<Bundle, Error> {
    let group = |name: &str, authority, width| Group {
        name: name.into(),
        authority,
        field: KB,
        width,
    };
    let read = |group, offset, column| Input::Read {
        group,
        offset,
        column,
    };
    let assertion = |output, scope| Assertion { output, scope };
    Bundle::new(
        vec![Slot {
            name: "s".into(),
            field: KB,
        }],
        vec![Channel {
            name: "lookup".into(),
            kind: ChannelKind::FieldBalance,
            tuple: vec![EXT],
            count: KB,
        }],
        vec![Table {
            name: "t".into(),
            optional: false,
            height,
            read_model: model,
            groups: vec![
                group("a", Authority::Witness, 2),
                group("k", Authority::Config, 1),
                group("b", Authority::Witness, 3),
                group("q", Authority::Public, 1),
                group("m", Authority::Config, 2),
            ],
            arena: Expression::new(
                vec![KB; 7],
                vec![
                    Node::Input(1),                 // 0 a0
                    Node::Input(0),                 // 1 b1@-1
                    Node::Mul(0, 1),                // 2
                    Node::Input(2),                 // 3 s
                    Node::Neg(3),                   // 4
                    Node::Add(2, 4),                // 5 out0 = a0*b1@-1 - s
                    Node::Input(3),                 // 6 m1@2
                    Node::Input(5),                 // 7 k@1
                    Node::Input(4),                 // 8 q
                    Node::Mul(7, 8),                // 9
                    Node::Add(6, 9),                // 10 out1 = m1@2 + k@1*q
                    Node::Input(6),                 // 11 b2
                    Node::Embed(EXT, 11),           // 12 out2, interaction only
                    Node::Constant(KB, "1".into()), // 13 out3, interaction count
                    Node::Mul(0, 0),                // 14
                    Node::Mul(14, 0),               // 15 out4 = a0^3
                ],
                vec![5, 10, 12, 13, 15],
            )?,
            inputs: vec![
                read(2, -1, 1),
                read(0, 0, 0),
                Input::Public(0),
                read(4, 2, 1),
                read(3, 0, 0),
                read(1, 1, 0),
                read(2, 0, 2),
            ],
            assertions: vec![
                assertion(1, Scope::First),
                assertion(4, Scope::Interval(1, 5)),
                assertion(0, Scope::Interior(1, 0)),
                assertion(1, Scope::Interior(0, 2)),
                assertion(0, Scope::Last),
                assertion(4, Scope::All),
                assertion(1, Scope::Interior(3, 6)),
            ],
            interactions: vec![Interaction::FieldBalance {
                channel: 0,
                locality: Locality::Global,
                scope: Scope::All,
                tuple: vec![2],
                count: 3,
                declared: None,
            }],
        }],
    )
}
fn configured_height(min: u32, max: u32) -> Height {
    Height {
        authority: HeightAuthority::Config,
        min,
        max,
        power_of_two: false,
    }
}

#[test]
fn grouped_authorities_flatten_columns_and_rotate_negative_offsets() {
    let bundle = layered(ReadModel::Finite, configured_height(2, 64)).unwrap();
    for carrier in [KB, EXT] {
        let view = bundle.polynomial_view(0, carrier).unwrap();
        // Degrees: out0 2, out1 2, out4 3. At h = 8 the interval assertion
        // (1, 5) has quotient degree 3*7 - 4 = 17, three chunks of length 8.
        assert_eq!(
            view.shape(8).unwrap(),
            PolynomialShape {
                witness_width: 5,
                config_width: 3,
                public_width: 1,
                public_slots: 1,
                inputs: 7,
                assertions: 7,
                quotient_chunks: 3,
            }
        );
        let at = |h| {
            (0..7)
                .map(|i| {
                    let d = view.input(h, i).unwrap();
                    (d.kind, d.column, d.rotation)
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            at(8),
            [
                (1, 3, 7),
                (1, 0, 0),
                (0, 0, 0),
                (2, 2, 2),
                (3, 0, 0),
                (2, 0, 1),
                (1, 4, 0)
            ]
        );
        assert_eq!(at(64)[0], (1, 3, 63));
        let scopes = |h| {
            (0..7)
                .map(|a| view.scope(h, a).unwrap())
                .collect::<Vec<_>>()
        };
        // First, interval, interior(1,0), interior(0,2), last, all and an
        // interior scope that is empty at 8 but not at 16.
        assert_eq!(
            scopes(8),
            [(0, 1), (1, 5), (1, 8), (0, 6), (7, 8), (0, 8), (0, 0)]
        );
        assert_eq!(
            scopes(16),
            [(0, 1), (1, 5), (1, 16), (0, 14), (15, 16), (0, 16), (3, 10)]
        );
        // The first-row read two rows ahead is undefined at height 2, and the
        // interval stops beyond a table of height 4.
        assert_eq!(view.shape(2).unwrap_err().0, "bundle-window");
        assert_eq!(view.scope(2, 6).unwrap_err().0, "bundle-window");
        assert_eq!(view.input(4, 0).unwrap_err().0, "bundle-scope-height");
        assert_eq!(view.shape(128).unwrap_err().0, "bundle-height");
        assert_eq!(view.shape(6).unwrap_err().0, "bundle-polynomial-two-adic");
    }
    // A cyclic table has no window refusal, but an interval still has to
    // stop within the table.
    let cyclic = layered(ReadModel::Cyclic, configured_height(2, 64)).unwrap();
    let view = cyclic.polynomial_view(0, KB).unwrap();
    assert_eq!(view.shape(2).unwrap_err().0, "bundle-scope-height");
    assert_eq!(view.input(8, 0).unwrap().rotation, 7);
    assert_eq!(view.shape(8).unwrap().quotient_chunks, 3);
}

#[test]
fn combined_authority_matrices_reproduce_dense_per_group_residuals() {
    let bundle = layered(ReadModel::Finite, configured_height(2, 64)).unwrap();
    let h = 8u64;
    let values =
        |seed: u64, n: usize| -> Vec<u64> { samples(seed, n).iter().map(|e| e.0[0]).collect() };
    // Group values, each row-major: a (2), k (1), b (3), q (1), m (2), slot s.
    let (a, k, b, q, m, s) = (
        values(11, 16),
        values(12, 8),
        values(13, 24),
        values(14, 8),
        values(15, 16),
        values(16, 1),
    );
    let dense = rows(
        bundle.table_view(0, KB).unwrap(),
        h,
        &kb(&[a.clone(), b.clone()].concat()),
        &kb(&[k.clone(), m.clone()].concat()),
        &kb(&[s.clone(), q.clone()].concat()),
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    // One combined row-major matrix per authority over the sum of widths.
    let combine = |groups: &[(&[u64], usize)]| -> Vec<u64> {
        (0..h as usize)
            .flat_map(|r| {
                groups
                    .iter()
                    .flat_map(move |(g, w)| g[r * w..(r + 1) * w].iter().copied())
            })
            .collect()
    };
    let witness = combine(&[(&a, 2), (&b, 3)]);
    let configuration = combine(&[(&k, 1), (&m, 2)]);
    let view = bundle.polynomial_view(0, EXT).unwrap();
    let shape = view.shape(h).unwrap();
    let mut checked = 0;
    for assertion in 0..shape.assertions {
        let (begin, end) = view.scope(h, assertion).unwrap();
        for row in begin..end {
            let assignment: Vec<_> = (0..shape.inputs)
                .map(|slot| {
                    let d = view.input(h, slot).unwrap();
                    let at = |matrix: &[u64], width: u64| {
                        matrix[(((row + d.rotation) % h) * width + d.column) as usize]
                    };
                    Ext::base(match d.kind {
                        0 => s[d.column as usize],
                        1 => at(&witness, shape.witness_width),
                        2 => at(&configuration, shape.config_width),
                        _ => at(&q, shape.public_width),
                    })
                    .native()
                })
                .collect();
            let got = points(
                &view,
                &assignment,
                1,
                false,
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX,
            )
            .unwrap();
            let expected = dense[(row * shape.assertions + assertion) as usize];
            assert_ne!(expected, KoalaBear::ZERO);
            assert_eq!(got[assertion as usize], KoalaBearExt8::from(expected));
            checked += 1;
        }
    }
    // 1 + 4 + 7 + 6 + 1 + 8 + 0 scoped rows.
    assert_eq!(checked, 27);
}

#[test]
fn points_follow_assertion_order_and_ignore_interaction_only_inputs() {
    let bundle = layered(ReadModel::Finite, configured_height(2, 64)).unwrap();
    let view = bundle.polynomial_view(0, EXT).unwrap();
    let v = samples(7, 7);
    let [b1, a0, s, m1, q, k, _b2] = v.clone().try_into().unwrap();
    let out0 = a0.mul(b1).sub(s);
    let out1 = m1.add(k.mul(q));
    let out4 = a0.mul(a0).mul(a0);
    let expected = vec![out1, out4, out0, out1, out0, out4, out1];
    let evaluate = |v: &[Ext]| {
        let native: Vec<_> = v.iter().map(|e| e.native()).collect();
        points(
            &view,
            &native,
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX,
        )
        .unwrap()
        .into_iter()
        .map(Ext::of)
        .collect::<Vec<_>>()
    };
    assert_eq!(evaluate(&v), expected);
    let mut changed = v.clone();
    changed[6] = samples(8, 1)[0];
    assert_eq!(evaluate(&changed), expected);
    // The interaction output is Ext8, so the dense KoalaBear view rejects
    // nothing either; only assertion sub-DAGs are carrier checked.
    assert!(bundle.table_view(0, KB).is_ok());
}

#[test]
fn static_premises_refuse_carriers_and_heights_without_a_two_adic_domain() {
    let fixed = |h| Height {
        authority: HeightAuthority::Fixed,
        min: h,
        max: h,
        power_of_two: false,
    };
    for height in [
        fixed(1),
        fixed(3),
        fixed(12),
        configured_height(1, 1),
        configured_height(5, 7),
    ] {
        let bundle = layered(ReadModel::Cyclic, height).unwrap();
        assert_eq!(
            bundle.polynomial_view(0, KB).unwrap_err().0,
            "bundle-polynomial-two-adic"
        );
    }
    for height in [
        fixed(2),
        fixed(16),
        configured_height(1, 2),
        configured_height(5, 8),
    ] {
        assert!(
            layered(ReadModel::Cyclic, height)
                .unwrap()
                .polynomial_view(0, KB)
                .is_ok()
        );
    }
    let bundle = layered(ReadModel::Finite, configured_height(2, 64)).unwrap();
    assert_eq!(
        bundle.polynomial_view(1, KB).unwrap_err().0,
        "relation-table-index"
    );
    for carrier in [Identity::Bls12381Fr, Identity::Bn254Fr] {
        assert_eq!(
            bundle.polynomial_view(0, carrier).unwrap_err().0,
            "relation-table-carrier"
        );
    }
    // An extension arena is not narrowed to its base field.
    let extension = Bundle::new(
        vec![],
        vec![],
        vec![Table {
            name: "e".into(),
            optional: false,
            height: fixed(4),
            read_model: ReadModel::Finite,
            groups: vec![Group {
                name: "x".into(),
                authority: Authority::Witness,
                field: EXT,
                width: 1,
            }],
            arena: Expression::new(vec![EXT], vec![Node::Input(0), Node::Mul(0, 0)], vec![1])
                .unwrap(),
            inputs: vec![Input::Read {
                group: 0,
                offset: 0,
                column: 0,
            }],
            assertions: vec![Assertion {
                output: 0,
                scope: Scope::All,
            }],
            interactions: vec![],
        }],
    )
    .unwrap();
    assert_eq!(
        extension.polynomial_view(0, KB).unwrap_err().0,
        "relation-table-carrier"
    );
    let view = extension.polynomial_view(0, EXT).unwrap();
    let x = samples(3, 1)[0];
    assert_eq!(
        points(
            &view,
            &[x.native()],
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )
        .unwrap()
        .into_iter()
        .map(Ext::of)
        .collect::<Vec<_>>(),
        [x.mul(x)]
    );
    // A base-field table whose assertion embeds into Ext8 needs the extension.
    let embedded = Bundle::parse(
        r#"["zkc.relation-bundle/0",[],[],[["e","required",["fixed",2],"finite",
        [["x","witness","koala-bear",1]],
        ["zkc.ring/0",["koala-bear"],[["input",0],["embed","koala-bear.ext8-binomial3",0]],[1]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]]"#,
    )
    .unwrap();
    assert_eq!(
        embedded.polynomial_view(0, KB).unwrap_err().0,
        "relation-table-carrier"
    );
    assert!(embedded.polynomial_view(0, EXT).is_ok());
}

/// Bundle with an assertion-free table whose only output is an interaction.
const INTERACTIONS: &str = r#"["zkc.relation-bundle/0",[["start","koala-bear"],["final","koala-bear"]],[["trace","multiset",["koala-bear","koala-bear"],"koala-bear"]],
 [["log","optional",["instance",1,16,false],"finite",[["pairs","witness","koala-bear",2]],
 ["zkc.ring/0",["koala-bear","koala-bear"],[["input",0],["input",1],["constant","koala-bear","1"]],[0,1,2]],
 [["read",0,"0",0],["read",0,"0",1]],[],[["multiset",0,["global"],["all"],"pull",[0,1],2,1]]]]]"#;

#[test]
fn empty_assertion_lists_still_charge_and_report_one_chunk() {
    let bundle = Bundle::parse(INTERACTIONS).unwrap();
    let view = bundle.polynomial_view(0, EXT).unwrap();
    assert_eq!(
        view.shape(16).unwrap(),
        PolynomialShape {
            witness_width: 2,
            config_width: 0,
            public_width: 0,
            public_slots: 2,
            inputs: 2,
            assertions: 0,
            quotient_chunks: 1,
        }
    );
    assert_eq!(view.input(2, 1).unwrap().column, 1);
    assert_eq!(
        view.scope(2, 0).unwrap_err().0,
        "relation-table-assertion-index"
    );
    // Nodes 3, inputs 2, groups 1, publics 2, assertions 0, reads 0, plus 1;
    // the substitution adds nodes 3, inputs 2 and 1.
    assert_eq!((view.work(), view.point_work()), (9, 6));
    let assignment = samples(5, 2).iter().map(|e| e.native()).collect::<Vec<_>>();
    let mut budget = Budget {
        limit: 14,
        spent: 0,
    };
    assert_eq!(
        code(points(
            &view,
            &assignment,
            1,
            false,
            &Policy::default(),
            &mut budget,
            usize::MAX
        )),
        "exhausted:ring-work"
    );
    assert_eq!(budget.spent, 0);
    budget.limit = 15;
    assert!(
        points(
            &view,
            &assignment,
            1,
            false,
            &Policy::default(),
            &mut budget,
            usize::MAX
        )
        .unwrap()
        .is_empty()
    );
    assert_eq!(budget.spent, 15);
}

#[test]
fn shape_bounds_data_work_and_quotient_size_before_any_allocation() {
    // Width 65,536 at height 64 declares 2^22 coordinates plus a public slot.
    let wide = Bundle::parse(
        r#"["zkc.relation-bundle/0",[["s","koala-bear"]],[],[["w","required",["instance",2,1024,false],"finite",
        [["x","witness","koala-bear",65536]],
        ["zkc.ring/0",["koala-bear"],[["input",0]],[0]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]]"#,
    )
    .unwrap();
    let view = wide.polynomial_view(0, KB).unwrap();
    assert!(view.shape(32).is_ok());
    assert_eq!(view.shape(64).unwrap_err().0, "bundle-data-limit");
    // A 2^16-fold product has degree 2^16; at height 2^9 its quotient needs
    // 2^16 chunks, beyond 2^24 coefficients.
    let mut nodes = String::from(r#"["input",0]"#);
    for i in 0..16 {
        nodes += &format!(r#",["mul",{i},{i}]"#);
    }
    let deep = Bundle::parse(&format!(
        r#"["zkc.relation-bundle/0",[],[],[["d","required",["instance",2,1048576,false],"finite",
        [["x","witness","koala-bear",1]],
        ["zkc.ring/0",["koala-bear"],[{nodes}],[16]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]]"#
    ))
    .unwrap();
    let view = deep.polynomial_view(0, KB).unwrap();
    // (2^16 * (h - 1) - h) / h + 1 chunks: 2^16 - 2^16/h.
    assert_eq!(view.shape(64).unwrap().quotient_chunks, 64_512);
    assert_eq!(view.shape(256).unwrap().quotient_chunks, 65_280);
    assert_eq!(view.shape(512).unwrap_err().0, "bundle-polynomial-limit");
    // Height times (nodes + inputs + assertions + 1) is at most 2^26.
    let mut nodes = String::from(r#"["input",0]"#);
    for i in 0..100 {
        nodes += &format!(r#",["add",{i},0]"#);
    }
    let long = Bundle::parse(&format!(
        r#"["zkc.relation-bundle/0",[],[],[["l","required",["instance",2,1048576,false],"finite",
        [["x","witness","koala-bear",1]],
        ["zkc.ring/0",["koala-bear"],[{nodes}],[100]],
        [["read",0,"0",0]],[[0,["all"]]],[]]]]"#
    ))
    .unwrap();
    let view = long.polynomial_view(0, KB).unwrap();
    assert_eq!(view.shape(1 << 19).unwrap().quotient_chunks, 1);
    assert_eq!(view.shape(1 << 20).unwrap_err().0, "bundle-work-limit");
}

#[test]
fn registry_references_and_signatures_cover_the_polynomial_kernels() {
    let bundle = recurrence();
    let body = bundle.encode().to_string();
    let mut registry = Registry::default();
    registry.insert(bundle.identity(), &body).unwrap();
    assert!(
        registry
            .polynomial_reference(bundle.identity(), 0, EXT)
            .is_ok()
    );
    for (identity, table, carrier, expected) in [
        ("missing", 0, KB, "refused:relation-asset-missing"),
        (bundle.identity(), 1, KB, "refused:relation-table-index"),
        (
            bundle.identity(),
            u64::MAX,
            KB,
            "refused:relation-table-index",
        ),
        (
            bundle.identity(),
            0,
            Identity::Bls12381Fr,
            "refused:relation-table-carrier",
        ),
    ] {
        assert_eq!(
            code(registry.polynomial_reference(identity, table, carrier)),
            expected
        );
    }
    let index = crate::domains::KOALA_BEAR.physical(Type::Index).unwrap();
    for (contract, inputs, outputs) in [
        ("relation.table_shape", 1, 7),
        ("relation.table_input", 2, 3),
        ("relation.table_scope", 2, 2),
    ] {
        for (field, table, accepted) in [
            ("koala-bear", "0", true),
            ("koala-bear.ext8-binomial3", "1048576", true),
            ("koala-bear", "1048577", false),
            ("bls12-381.fr", "0", false),
        ] {
            let mut binding = OperationBinding {
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
            binding.implementation = "plonky3/relation.table_rows".into();
            assert!(signature(&binding).is_none());
        }
    }
    for field in ["koala-bear", "koala-bear.ext8-binomial3"] {
        for (contract, inputs) in [("relation.table_point", 1), ("relation.table_points", 2)] {
            let binding = OperationBinding {
                contract: contract.into(),
                arguments: vec![field.into(), "0".into()],
                implementation: format!("plonky3/{contract}"),
            };
            let got = signature(&binding).unwrap();
            assert_eq!((got.inputs.len(), got.outputs.len()), (inputs, 1));
            assert_eq!(got.inputs[0], got.outputs[0]);
            assert_eq!(got.inputs.get(1), (inputs == 2).then_some(&index));
            assert_eq!(got, binding.signature().unwrap());
        }
    }
}

/// A batch and its rows one at a time; the batch charges the static work once
/// and one point per row.
fn batch_and_rows<S: crate::ring::Carrier>(
    view: &PolynomialView<'_>,
    matrix: &[S],
    rows: usize,
) -> (Vec<S>, Vec<S>) {
    let inputs = view.input_count();
    let mut budget = Budget::default();
    let batch = points(
        view,
        matrix,
        rows as u64,
        true,
        &Policy::default(),
        &mut budget,
        usize::MAX,
    )
    .unwrap();
    assert_eq!(budget.spent, view.work() + rows as u64 * view.point_work());
    let singles = (0..rows)
        .flat_map(|r| {
            points(
                view,
                &matrix[r * inputs..(r + 1) * inputs],
                1,
                false,
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX,
            )
            .unwrap()
        })
        .collect();
    (batch, singles)
}

#[test]
fn batches_match_scalar_points_and_dense_rows_on_the_subgroup() {
    let (witness, configuration, public, dense) = changed_recurrence();
    let bundle = recurrence();
    let view = bundle.polynomial_view(0, KB).unwrap();
    let matrix: Vec<u64> = (0..8)
        .flat_map(|row| assignment(&view, 8, row, [&public, &witness, &configuration, &[]]))
        .collect();
    let (batch, singles) = batch_and_rows(&view, &kb(&matrix), 8);
    assert_eq!(batch, singles);
    // Dense rows are zero outside a scope; the substitution is unmasked.
    let mut nonzero = 0;
    for a in 0..9 {
        let (begin, end) = view.scope(8, a).unwrap();
        for row in begin..end {
            let at = (row * 9 + a) as usize;
            assert_eq!(batch[at], dense[at]);
            nonzero += usize::from(dense[at] != KoalaBear::ZERO);
        }
    }
    assert!(nonzero >= 2);
    // The same rows lifted into Ext8 give the embedded values.
    let ext = bundle.polynomial_view(0, EXT).unwrap();
    let lifted: Vec<_> = kb(&matrix).into_iter().map(KoalaBearExt8::from).collect();
    let (extended, singles) = batch_and_rows(&ext, &lifted, 8);
    assert_eq!(extended, singles);
    assert_eq!(
        extended,
        batch
            .into_iter()
            .map(KoalaBearExt8::from)
            .collect::<Vec<_>>()
    );
}

/// The recurrence over Ext8 slots, groups, inputs and constants.
fn extension_recurrence() -> Bundle {
    Bundle::parse(
        &include_str!("../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle.json")
            .replace("\"koala-bear\"", "\"koala-bear.ext8-binomial3\""),
    )
    .unwrap()
}

#[test]
fn extension_batches_keep_every_coordinate() {
    let bundle = extension_recurrence();
    assert_eq!(
        bundle.polynomial_view(0, KB).unwrap_err().0,
        "relation-table-carrier"
    );
    let view = bundle.polynomial_view(0, EXT).unwrap();
    // Thirteen rows exercise both the packed lanes and the scalar tail.
    let rows: Vec<Vec<Ext>> = (0..13).map(|r| samples(100 + r, 11)).collect();
    let matrix: Vec<_> = rows.iter().flatten().map(|e| e.native()).collect();
    let (batch, singles) = batch_and_rows(&view, &matrix, 13);
    assert_eq!(batch, singles);
    let expected: Vec<_> = rows.iter().flat_map(|v| recurrence_reference(v)).collect();
    assert_eq!(batch.into_iter().map(Ext::of).collect::<Vec<_>>(), expected);
}

#[test]
fn batches_keep_input_numbering_and_assertion_order() {
    let bundle = layered(ReadModel::Finite, configured_height(2, 64)).unwrap();
    let view = bundle.polynomial_view(0, EXT).unwrap();
    let rows: Vec<Vec<Ext>> = (0..3).map(|r| samples(40 + r, 7)).collect();
    let expected: Vec<_> = rows
        .iter()
        .flat_map(|v| {
            let [b1, a0, s, m1, q, k, _b2] = v.clone().try_into().unwrap();
            let (out0, out1) = (a0.mul(b1).sub(s), m1.add(k.mul(q)));
            let out4 = a0.mul(a0).mul(a0);
            [out1, out4, out0, out1, out0, out4, out1]
        })
        .collect();
    let run = |rows: &[Vec<Ext>]| {
        let matrix: Vec<_> = rows.iter().flatten().map(|e| e.native()).collect();
        let (batch, singles) = batch_and_rows(&view, &matrix, rows.len());
        assert_eq!(batch, singles);
        batch.into_iter().map(Ext::of).collect::<Vec<_>>()
    };
    assert_eq!(run(&rows), expected);
    // The interaction-only input keeps its column, and its value is unused.
    let mut changed = rows.clone();
    for (r, row) in changed.iter_mut().enumerate() {
        row[6] = samples(60 + r as u64, 1)[0];
    }
    assert_eq!(run(&changed), expected);
    // Without the unused column the shape is refused.
    let short: Vec<_> = rows
        .iter()
        .flat_map(|v| v[..6].iter().map(|e| e.native()))
        .collect();
    assert_eq!(
        code(points(
            &view,
            &short,
            3,
            true,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )),
        "refused:relation-table-point-shape"
    );
}

#[test]
fn batch_shape_storage_and_work_are_checked_before_preparation() {
    let bundle = recurrence();
    let view = bundle.polynomial_view(0, KB).unwrap();
    let (static_work, unit) = (view.work(), view.point_work());
    let run = |values: &[KoalaBear], rows: u64, policy: &Policy, budget: &mut Budget, available| {
        points(&view, values, rows, true, policy, budget, available)
    };
    // No rows: nothing is prepared, and only the static work is charged.
    let mut budget = Budget::default();
    assert!(
        run(&[], 0, &Policy::default(), &mut budget, usize::MAX)
            .unwrap()
            .is_empty()
    );
    assert_eq!(budget.spent, static_work);
    let values = kb(&[1; 33]);
    for (rows, length) in [(2, 33), (3, 32), (u64::MAX, 0), (u64::MAX / 4, 33)] {
        assert_eq!(
            code(run(
                &values[..length],
                rows,
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX
            )),
            "refused:relation-table-point-shape"
        );
    }
    // The full charge is atomic.
    let mut budget = Budget {
        limit: static_work + 3 * unit - 1,
        spent: 0,
    };
    assert_eq!(
        code(run(&values, 3, &Policy::default(), &mut budget, usize::MAX)),
        "exhausted:ring-work"
    );
    assert_eq!(budget.spent, 0);
    budget.limit += 1;
    assert_eq!(
        run(&values, 3, &Policy::default(), &mut budget, usize::MAX)
            .unwrap()
            .len(),
        27
    );
    // The result alone must fit the allowance.
    let result = crate::value::size(27, 4).unwrap();
    for (available, accepted) in [(result - 1, false), (result, true)] {
        let got = run(
            &values,
            3,
            &Policy::default(),
            &mut Budget::default(),
            available,
        );
        assert_eq!(got.is_ok(), accepted);
    }
    // Result, scratch and the prepared sub-DAG together must fit the policy.
    let t = view.definition();
    let cells = crate::ring::scratch_cells::<KoalaBear>(t.arena.nodes().len(), true).unwrap() + 27;
    let peak = crate::value::size(cells, 4).unwrap() + arena_bytes(&t.arena) + 9 * OUTPUT_BYTES;
    for (bytes, accepted) in [(peak - 1, false), (peak, true)] {
        let policy = Policy {
            max_value_bytes: bytes,
            ..Policy::default()
        };
        let got = run(&values, 3, &policy, &mut Budget::default(), usize::MAX);
        assert_eq!(
            got.map(|v| v.len()).map_err(|e| e.code),
            if accepted {
                Ok(27)
            } else {
                Err("exhausted:output-bytes".into())
            }
        );
    }
    let policy = Policy {
        max_table_elements: cells - 1,
        ..Policy::default()
    };
    assert_eq!(
        code(run(&values, 3, &policy, &mut Budget::default(), usize::MAX)),
        "exhausted:element-limit"
    );
    // Without inputs any row count has a shape: results and work bound it.
    let none: &[KoalaBear] = &[];
    let constant = Bundle::parse(
        r#"["zkc.relation-bundle/0",[],[],[["c","required",["fixed",2],"finite",[],
        ["zkc.ring/0",[],[["constant","koala-bear","5"]],[0]],[],[[0,["all"]]],[]]]]"#,
    )
    .unwrap();
    let view = constant.polynomial_view(0, KB).unwrap();
    assert_eq!(
        points(
            &view,
            none,
            3,
            true,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )
        .unwrap(),
        kb(&[5, 5, 5])
    );
    for rows in [1 << 40, u64::MAX] {
        assert_eq!(
            code(points(
                &view,
                none,
                rows,
                true,
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX
            )),
            "exhausted:element-limit"
        );
    }
    // Without inputs or assertions only the work charge bounds the count.
    let silent = Bundle::parse(
        r#"["zkc.relation-bundle/0",[],[["c","multiset",["koala-bear"],"koala-bear"]],
        [["k","required",["fixed",2],"finite",[],
        ["zkc.ring/0",[],[["constant","koala-bear","1"]],[0]],[],[],
        [["multiset",0,["global"],["all"],"pull",[0],0,1]]]]]"#,
    )
    .unwrap();
    let view = silent.polynomial_view(0, KB).unwrap();
    let mut budget = Budget::default();
    assert!(
        points(
            &view,
            none,
            1 << 20,
            true,
            &Policy::default(),
            &mut budget,
            usize::MAX
        )
        .unwrap()
        .is_empty()
    );
    assert_eq!(budget.spent, view.work() + (1 << 20) * view.point_work());
    for rows in [1 << 40, u64::MAX] {
        assert_eq!(
            code(points(
                &view,
                none,
                rows,
                true,
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX
            )),
            "exhausted:ring-work"
        );
    }
}

#[test]
fn shapes_report_at_least_one_chunk_of_the_shared_analysis_fixture() {
    // The C++ analysis reads this file and expects exactly these chunks; the
    // runtime shape reports max(1, chunks), so zero becomes one.
    let fixture: serde_json::Value = serde_json::from_str(include_str!(
        "../../../../compiler/test/fixtures/relation/polynomial-chunks.json"
    ))
    .unwrap();
    let mut checked = 0;
    for entry in fixture.as_array().unwrap() {
        let bundle = Bundle::parse(&entry["bundle"].to_string()).unwrap();
        for pair in entry["chunks"].as_array().unwrap() {
            let (height, chunks) = (pair[0].as_u64().unwrap(), pair[1].as_u64().unwrap());
            for carrier in [KB, EXT] {
                let shape = bundle.polynomial_view(0, carrier).unwrap().shape(height);
                assert_eq!(
                    shape.unwrap().quotient_chunks,
                    chunks.max(1),
                    "{} at {height}",
                    entry["name"]
                );
            }
            checked += 1;
        }
    }
    assert_eq!(checked, 14);
}
