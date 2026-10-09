//! Exported arenas through the native `zkc.ring/0` admission and the installed
//! KoalaBear/Ext8 provider, compared with direct `Air::eval` and the pinned
//! upstream debug checker. Requires the `native` feature.

mod common;

use common::*;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use zkc_backends::plonky3::PACKING_WIDTH;
use zkc_backends::ring::{self, Budget, Registry};
use zkc_backends::{KoalaBear, KoalaBearExt8, Policy};
use zkc_plonky3_air::field::{Ext8, F, generator};
use zkc_plonky3_air::reference::{
    open_table, point_residuals, row_residuals, upstream_accepts, upstream_failures,
};
use zkc_plonky3_air::view::{SelectorLaw, violations};
use zkc_plonky3_air::{Export, Openings};
use zkc_plonky3_air_client::{CounterAir, RecurrenceAir};
use zkc_plonky3_air_driver::{files, fixtures};
use zkc_runtime::interactive::Identity;
use zkc_runtime::ring::Expression;

// The adapter and the native provider must name the same pinned field types.
const _: fn(F) -> KoalaBear = |x| x;
const _: fn(Ext8) -> KoalaBearExt8 = |x| x;

fn policy() -> Policy {
    Policy {
        max_table_elements: 1 << 20,
        ..Default::default()
    }
}

/// Native admission of the exported arena; its canonical text must be the
/// exporter's byte for byte.
fn native(export: &Export) -> Expression {
    let text = export.arena_text();
    let expression = Expression::parse(&text).unwrap();
    assert_eq!(expression.canonical(), text);
    expression
}

fn rows<S: ring::Carrier>(
    expression: &Expression,
    inputs: &[S],
    count: usize,
    packed: bool,
) -> (Vec<S>, u64) {
    let mut budget = Budget::default();
    let result = ring::rows(
        expression,
        S::IDENTITY,
        inputs,
        count,
        packed,
        &policy(),
        &mut budget,
        usize::MAX,
    )
    .unwrap();
    (result, budget.spent)
}

/// Scalar and packed native rows agree, including their logical work.
fn native_rows(expression: &Expression, inputs: &[F], count: usize) -> Vec<F> {
    let (scalar, scalar_work) = rows(expression, inputs, count, false);
    let (packed, packed_work) = rows(expression, inputs, count, true);
    assert_eq!(scalar, packed, "scalar and packed rows");
    assert_eq!(
        scalar_work, packed_work,
        "logical work is independent of packing"
    );
    scalar
}

fn recurrence(log_height: usize) -> (RecurrenceAir, Export, RowMajorMatrix<F>, Vec<F>) {
    let air = RecurrenceAir { log_height };
    let export = zkc_plonky3_air::export(&air, "recurrence").unwrap();
    let (trace, publics) = air.generate(F::from_u32(2), F::from_u32(5));
    (air, export, trace, publics)
}

fn cases(trace: &RowMajorMatrix<F>, publics: &[F]) -> Vec<(String, RowMajorMatrix<F>, Vec<F>)> {
    let mut cases = vec![("honest".to_string(), trace.clone(), publics.to_vec())];
    for (name, t) in perturbations(trace) {
        cases.push((name, t, publics.to_vec()));
    }
    let mut wrong = publics.to_vec();
    wrong[2] += F::ONE;
    cases.push(("final public".into(), trace.clone(), wrong));
    cases
}

struct Empty;
impl<T> BaseAir<T> for Empty {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: AirBuilder> Air<AB> for Empty {
    fn eval(&self, _: &mut AB) {}
}

#[test]
fn exported_arenas_are_admitted_under_their_identity() {
    let mut registry = Registry::default();
    for fixture in fixtures().unwrap() {
        let digest = fixture.export.arena.sha256();
        let text = files(&fixture)
            .into_iter()
            .find(|(f, _)| *f == "arena.json")
            .unwrap()
            .1;
        assert_eq!(text, native(&fixture.export).canonical());
        registry.insert(&digest, &text).unwrap();
        assert_eq!(
            registry.insert(&digest, &text).unwrap_err().code,
            "refused:ring-asset-duplicate"
        );
        let mut other = Registry::default();
        assert_eq!(
            other.insert(&"0".repeat(64), &text).unwrap_err().code,
            "refused:ring-asset-identity"
        );
    }
    let (_, export, _, _) = recurrence(3);
    let tampered = export
        .arena_text()
        .replace("\"123456789\"", "\"123456790\"");
    assert!(Expression::parse(&tampered).is_ok());
    assert_eq!(
        Registry::default()
            .insert(&export.arena.sha256(), &tampered)
            .unwrap_err()
            .code,
        "refused:ring-asset-identity"
    );
    // Native degree analysis with the view's weights agrees with the export.
    let expression = native(&export);
    for height in [1, 8, 1 << 16] {
        let weights: Vec<u32> = export
            .slots
            .iter()
            .map(|s| zkc_plonky3_air::model::polynomial_weight(s, height) as u32)
            .collect();
        let degrees = expression.degrees(&weights).unwrap();
        let native: Vec<u64> = expression
            .outputs()
            .iter()
            .map(|o| degrees[*o] as u64)
            .collect();
        assert_eq!(native, export.polynomial_degrees(height).unwrap());
    }
    let multiples: Vec<u32> = export
        .slots
        .iter()
        .map(|s| zkc_plonky3_air::model::degree_multiple_weight(s) as u32)
        .collect();
    let degrees = expression.degrees(&multiples).unwrap();
    for (assertion, output) in export.assertions.iter().zip(expression.outputs()) {
        assert_eq!(assertion.degree_multiple, degrees[*output] as u64);
    }
    // An AIR without assertions exports the empty arena.
    let empty = zkc_plonky3_air::export(&Empty, "empty").unwrap();
    assert_eq!(empty.arena_text(), r#"["zkc.ring/0",[],[],[]]"#);
    assert!(rows(&native(&empty), &[] as &[F], 4, true).0.is_empty());
}

/// A build may state its expected SIMD width; portable builds pack one lane.
#[test]
fn packing_width_is_the_expected_one() {
    if let Ok(expected) = std::env::var("ZKC_PLONKY3_PACKING_WIDTH") {
        assert_eq!(PACKING_WIDTH.to_string(), expected);
    }
}

#[test]
fn native_rows_match_direct_evaluation_and_upstream_under_both_laws() {
    for log_height in 0..=6 {
        let (air, export, trace, publics) = recurrence(log_height);
        let expression = native(&export);
        let height = trace.height();
        for (name, trace, publics) in cases(&trace, &publics) {
            let view = bind(&export, height, &publics);
            let mut zero_loci = vec![];
            for law in [SelectorLaw::RowIndicator, SelectorLaw::TwoAdicLagrange] {
                let inputs = view.row_inputs(&trace, law).unwrap();
                let native = native_rows(&expression, &inputs, height);
                assert_eq!(
                    native,
                    view.residuals(&inputs).unwrap(),
                    "height {height}, {name}, {law:?}: adapter"
                );
                assert_eq!(
                    native,
                    row_residuals(&air, &trace, &publics, law).unwrap(),
                    "height {height}, {name}, {law:?}"
                );
                zero_loci.push(violations(&native, 9));
            }
            let upstream = upstream_failures(&air, &trace, &publics);
            assert_eq!(zero_loci[0], upstream, "height {height}, {name}");
            assert_eq!(zero_loci[1], upstream, "height {height}, {name}");
            assert_eq!(upstream_accepts(&air, &trace, &publics), name == "honest");
        }
    }
    for height in [1, 2, 4, 8, 16] {
        let trace = CounterAir::generate(height);
        for guarded in [false, true] {
            let air = CounterAir { guarded };
            let export = zkc_plonky3_air::export(&air, "counter").unwrap();
            let inputs = bind(&export, height, &[])
                .row_inputs(&trace, SelectorLaw::RowIndicator)
                .unwrap();
            let native = native_rows(&native(&export), &inputs, height);
            assert_eq!(
                violations(&native, 1),
                upstream_failures(&air, &trace, &[]),
                "height {height}"
            );
        }
    }
}

#[test]
fn a_large_trace_runs_natively_within_declared_limits() {
    let (air, export, trace, publics) = recurrence(16);
    let expression = native(&export);
    let height = trace.height();
    let view = bind(&export, height, &publics);
    for (name, trace) in [
        ("honest", trace.clone()),
        ("middle", perturb(&trace, height / 2 + 3, 3)),
    ] {
        let inputs = view.row_inputs(&trace, SelectorLaw::RowIndicator).unwrap();
        let native = native_rows(&expression, &inputs, height);
        assert_eq!(
            native,
            row_residuals(&air, &trace, &publics, SelectorLaw::RowIndicator).unwrap(),
            "{name}"
        );
        assert_eq!(
            violations(&native, 9),
            upstream_failures(&air, &trace, &publics),
            "{name}"
        );
    }
    // The default element ceiling refuses the same table before evaluation.
    let inputs = view.row_inputs(&trace, SelectorLaw::RowIndicator).unwrap();
    let mut budget = Budget::default();
    let refused = ring::rows(
        &expression,
        Identity::KoalaBear,
        &inputs,
        height,
        true,
        &Policy::default(),
        &mut budget,
        usize::MAX,
    );
    assert!(refused.unwrap_err().code.starts_with("exhausted:"));
    assert_eq!(budget.spent, 0);
    let mut small = Budget {
        limit: 1000,
        spent: 0,
    };
    let refused = ring::rows(
        &expression,
        Identity::KoalaBear,
        &inputs,
        height,
        true,
        &policy(),
        &mut small,
        usize::MAX,
    );
    assert_eq!(refused.unwrap_err().code, "exhausted:ring-work");
}

#[test]
fn native_extension_points_match_direct_evaluation() {
    for log_height in 0..=5 {
        let (air, export, trace, publics) = recurrence(log_height);
        let expression = native(&export);
        let fixed = export.layout.preprocessed.as_ref().unwrap();
        for (name, trace, publics) in cases(&trace, &publics) {
            let view = bind(&export, trace.height(), &publics);
            let mut all_inputs = vec![];
            let mut all_direct = vec![];
            for point in points() {
                let (main_current, main_next) =
                    open_table(&trace.values, trace.width(), point).unwrap();
                let (preprocessed_current, preprocessed_next) =
                    open_table(&fixed.values, fixed.width, point).unwrap();
                let openings = Openings {
                    main_current,
                    main_next,
                    preprocessed_current,
                    preprocessed_next,
                };
                all_inputs.extend(view.point_inputs(point, &openings).unwrap());
                all_direct.extend(point_residuals(&air, &trace, &publics, point).unwrap());
            }
            let count = points().len();
            let (scalar, _) = rows::<Ext8>(&expression, &all_inputs, count, false);
            let (packed, _) = rows::<Ext8>(&expression, &all_inputs, count, true);
            assert_eq!(scalar, packed);
            assert_eq!(scalar, all_direct, "height {}, {name}", trace.height());
        }
    }
    // Base inputs promoted to Ext8 evaluate as their embeddings.
    let (_, export, trace, publics) = recurrence(3);
    let expression = native(&export);
    let inputs = bind(&export, 8, &publics)
        .row_inputs(&trace, SelectorLaw::TwoAdicLagrange)
        .unwrap();
    let promoted: Vec<Ext8> = inputs.iter().map(|v| Ext8::from(*v)).collect();
    let base = native_rows(&expression, &inputs, 8);
    assert_eq!(
        rows(&expression, &promoted, 8, true).0,
        base.iter().map(|v| Ext8::from(*v)).collect::<Vec<_>>()
    );
    let mut budget = Budget::default();
    let wrong = ring::rows(
        &expression,
        Identity::KoalaBear,
        &promoted,
        8,
        false,
        &policy(),
        &mut budget,
        usize::MAX,
    );
    assert_eq!(wrong.unwrap_err().code, "refused:ring-carrier");
}

/// Remainder modulo `X^n - 1`.
fn reduce(coefficients: &[F], n: usize) -> Vec<F> {
    let mut remainder = vec![F::ZERO; n];
    for (k, c) in coefficients.iter().enumerate() {
        remainder[k % n] += *c;
    }
    remainder
}

#[test]
fn native_coefficients_give_the_two_adic_constraint_polynomials() {
    for log_height in 1..=4 {
        let (air, export, trace, publics) = recurrence(log_height);
        let expression = native(&export);
        let height = trace.height();
        let g = generator(log_height);
        let bounds = export.polynomial_degrees(height).unwrap();
        for (name, trace, publics) in cases(&trace, &publics) {
            let view = bind(&export, height, &publics);
            let (inputs, width) = view.coefficient_inputs(&trace).unwrap();
            let mut budget = Budget::default();
            let output = ring::coefficients(
                &expression,
                Identity::KoalaBear,
                &inputs,
                width,
                &policy(),
                &mut budget,
                usize::MAX,
            )
            .unwrap();
            let output_width = output.len() / 9;
            let on_domain =
                row_residuals(&air, &trace, &publics, SelectorLaw::TwoAdicLagrange).unwrap();
            let failing: Vec<usize> = upstream_failures(&air, &trace, &publics)
                .iter()
                .map(|(_, c)| *c)
                .collect();
            let at_points: Vec<Vec<Ext8>> = points()
                .into_iter()
                .map(|p| point_residuals(&air, &trace, &publics, p).unwrap())
                .collect();
            for j in 0..9 {
                let c = &output[j * output_width..(j + 1) * output_width];
                for row in 0..height {
                    let x = Ext8::from(g.exp_u64(row as u64));
                    assert_eq!(
                        horner(c, x),
                        Ext8::from(on_domain[row * 9 + j]),
                        "{name}: C_{j}(g^{row})"
                    );
                }
                for (p, point) in points().into_iter().enumerate() {
                    assert_eq!(
                        horner(c, point),
                        at_points[p][j],
                        "{name}: C_{j} off the domain"
                    );
                }
                let divisible = reduce(c, height).iter().all(|r| *r == F::ZERO);
                assert_eq!(
                    divisible,
                    !failing.contains(&j),
                    "{name}: Z_H divides C_{j}"
                );
                let degree = c.iter().rposition(|v| *v != F::ZERO).unwrap_or(0) as u64;
                assert!(degree <= bounds[j], "{name}: degree of C_{j}");
            }
        }
    }
    // Beyond the provider's degree limit the evaluation refuses; it never truncates.
    let (_, export, trace, publics) = recurrence(5);
    let (inputs, width) = bind(&export, 32, &publics)
        .coefficient_inputs(&trace)
        .unwrap();
    let mut budget = Budget::default();
    let refused = ring::coefficients(
        &native(&export),
        Identity::KoalaBear,
        &inputs,
        width,
        &policy(),
        &mut budget,
        usize::MAX,
    );
    assert_eq!(refused.unwrap_err().code, "refused:ring-coefficient-degree");
}

#[test]
fn native_affine_sums_over_row_pairs_match_the_adapter_interpreter() {
    let (_, export, trace, publics) = recurrence(4);
    let expression = native(&export);
    let height = trace.height();
    let half = height / 2;
    let slots = export.slots.len();
    for (name, trace, publics) in cases(&trace, &publics) {
        let view = bind(&export, height, &publics);
        let inputs = view.row_inputs(&trace, SelectorLaw::RowIndicator).unwrap();
        let (low, high) = inputs.split_at(half * slots);
        let mut budget = Budget::default();
        let sum = ring::affine_sum(
            &expression,
            Identity::KoalaBear,
            low,
            high,
            half,
            &policy(),
            &mut budget,
            usize::MAX,
        )
        .unwrap();
        let width = sum.len() / 9;
        for r in [F::ZERO, F::ONE, F::from_u32(7), F::NEG_ONE] {
            let mut expected = [F::ZERO; 9];
            for row in 0..half {
                let bound: Vec<F> = (0..slots)
                    .map(|s| {
                        low[row * slots + s] + r * (high[row * slots + s] - low[row * slots + s])
                    })
                    .collect();
                for (e, v) in expected.iter_mut().zip(export.arena.evaluate(|s| bound[s])) {
                    *e += v;
                }
            }
            for (j, e) in expected.iter().enumerate() {
                let c = &sum[j * width..(j + 1) * width];
                assert_eq!(
                    horner(c, Ext8::from(r)),
                    Ext8::from(*e),
                    "{name}: output {j} at {r}"
                );
            }
        }
        // Extension-carrier sums of embedded inputs embed the base sums.
        let (lo, hi): (Vec<Ext8>, Vec<Ext8>) = (
            low.iter().map(|v| Ext8::from(*v)).collect(),
            high.iter().map(|v| Ext8::from(*v)).collect(),
        );
        let mut budget = Budget::default();
        let extension = ring::affine_sum(
            &expression,
            Identity::KoalaBearExt8,
            &lo,
            &hi,
            half,
            &policy(),
            &mut budget,
            usize::MAX,
        )
        .unwrap();
        assert_eq!(
            extension,
            sum.iter().map(|v| Ext8::from(*v)).collect::<Vec<_>>()
        );
    }
}

#[test]
fn derived_bundle_arenas_are_admitted_and_evaluate_natively() {
    use zkc_plonky3_air::Slot;
    use zkc_plonky3_air::bundle::BundleView;
    for log_height in [0, 3, 6] {
        let (_, export, trace, publics) = recurrence(log_height);
        let bundle = BundleView::derive(&export).unwrap();
        let text = bundle.arena().canonical();
        let expression = Expression::parse(&text).unwrap();
        assert_eq!(expression.canonical(), text);
        let height = trace.height();
        for (name, trace, publics) in cases(&trace, &publics) {
            let inputs = bind(&export, height, &publics)
                .row_inputs(&trace, SelectorLaw::RowIndicator)
                .unwrap();
            let kept: Vec<usize> = (0..export.slots.len())
                .filter(|s| !matches!(export.slots[*s], Slot::Selector(_)))
                .collect();
            let bundle_inputs: Vec<F> = (0..height)
                .flat_map(|r| kept.iter().map(move |s| (r, *s)))
                .map(|(r, s)| inputs[r * export.slots.len() + s])
                .collect();
            let native = native_rows(&expression, &bundle_inputs, height);
            for (row, assertion, value) in bundle.residuals(&trace, &publics).unwrap() {
                assert_eq!(native[row * 9 + assertion], value, "{name}");
            }
        }
    }
}
