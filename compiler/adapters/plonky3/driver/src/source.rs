//! Entry input maps for the maintained `.zkc` source client in
//! `examples/projects/imported-air`, with direct `Air::eval` expectations.
//!
//! Trace inputs keep witness, configuration and public values separate;
//! the native Bundle view supplies their read bindings. Polynomial inputs
//! contain prepared assignments under the fixture's selected export. The
//! expectations come from `Air::eval` through the reference builders, never
//! from the exported arena. The adapter's arena interpreter and the upstream
//! debug checker only gate generation.

use p3_air::{Air, DebugConstraintBuilder};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde_json::{Map, Value, json};
use zkc_plonky3_air::artifact::canonical;
use zkc_plonky3_air::field::{Ext8, F, decimal, ext_from_coordinates, generator};
use zkc_plonky3_air::reference::{
    PointBuilder, RowBuilder, open_table, point_residuals, row_residuals, upstream_failures,
};
use zkc_plonky3_air::view::{ClosedView, Openings, SelectorLaw, violations};
use zkc_plonky3_air::{Export, Instance, Refusal};

fn coordinates(value: &Ext8) -> impl Iterator<Item = u32> + '_ {
    BasedVectorSpace::<F>::as_basis_coefficients_slice(value)
        .iter()
        .map(|c| c.as_canonical_u32())
}

fn decimals(values: &[F]) -> Value {
    values.iter().map(|v| Value::String(decimal(*v))).collect()
}

fn extension_decimals(values: &[Ext8]) -> Value {
    values
        .iter()
        .map(|v| Value::from_iter(coordinates(v).map(|c| c.to_string())))
        .collect()
}

fn law_name(law: SelectorLaw) -> &'static str {
    match law {
        SelectorLaw::RowIndicator => "row-indicator",
        SelectorLaw::TwoAdicLagrange => "two-adic-lagrange",
    }
}

/// Values of ascending coefficients at `point`.
fn horner(coefficients: &[F], point: F) -> F {
    coefficients
        .iter()
        .rev()
        .fold(F::ZERO, |sum, c| sum * point + *c)
}

/// `ring.rows` over the row-major closed view of one trace on its domain.
fn rows_case<A>(
    air: &A,
    export: &Export,
    instance: &Instance,
    trace: &RowMajorMatrix<F>,
    law: SelectorLaw,
) -> Result<(String, Value), Refusal>
where
    A: for<'a> Air<RowBuilder<'a>> + for<'a> Air<DebugConstraintBuilder<'a, F>>,
{
    let view = ClosedView::bind(export, instance)?;
    let assignments = view.row_inputs(trace, law)?;
    let direct = row_residuals(air, trace, &instance.public_values, law)?;
    assert_eq!(
        view.residuals(&assignments)?,
        direct,
        "arena interpreter and Air::eval disagree"
    );
    // Both selector laws vanish exactly on the rows the debug checker accepts.
    let failures = upstream_failures(air, trace, &instance.public_values);
    assert_eq!(
        violations(&direct, export.assertions.len()),
        failures,
        "zero locus differs from the upstream debug checker"
    );
    Ok((
        canonical(
            &json!({"assignments": decimals(&assignments), "rows": trace.height().to_string()}),
        ),
        json!({
            "entry": "RowResiduals",
            "law": law_name(law),
            "residuals": decimals(&direct),
            "upstream_failures": failures,
        }),
    ))
}

/// Actual trace inputs for the Bundle table kernel, without expanded reads or
/// caller-supplied selector values. The expected residuals come directly from
/// the AIR under row-indicator semantics.
fn trace_case<A>(
    air: &A,
    export: &Export,
    instance: &Instance,
    trace: &RowMajorMatrix<F>,
) -> Result<(String, Value), Refusal>
where
    A: for<'a> Air<RowBuilder<'a>> + for<'a> Air<DebugConstraintBuilder<'a, F>>,
{
    let (_, mut expected) = rows_case(air, export, instance, trace, SelectorLaw::RowIndicator)?;
    expected["entry"] = json!("TraceResiduals");
    let configuration = export
        .layout
        .preprocessed
        .as_ref()
        .map(|table| table.values.as_slice())
        .unwrap_or(&[]);
    Ok((
        canonical(&json!({
            "trace": decimals(&trace.values),
            "configuration": decimals(configuration),
            "public_data": decimals(&instance.public_values),
            "height": trace.height().to_string(),
        })),
        expected,
    ))
}

/// `ring.coefficients` over the slot polynomials of one trace. The expected
/// values are direct evaluations at the trace domain, under two-adic Lagrange
/// selectors, and at as many points off the domain as the provider's output
/// width, so the off-domain points alone determine each output polynomial.
fn coefficients_case<A>(
    air: &A,
    export: &Export,
    instance: &Instance,
    trace: &RowMajorMatrix<F>,
) -> Result<(String, Value), Refusal>
where
    A: for<'a> Air<RowBuilder<'a>> + for<'a> Air<PointBuilder<'a>>,
{
    let view = ClosedView::bind(export, instance)?;
    let (coefficients, width) = view.coefficient_inputs(trace)?;
    let assertions = export.assertions.len();
    let publics = &instance.public_values;
    // The provider weights every input by `width - 1`.
    let degrees = export
        .arena
        .degrees(&vec![width as u64 - 1; export.slots.len()])?;
    let output_width = 1 + export
        .arena
        .outputs()
        .iter()
        .map(|o| degrees[*o])
        .max()
        .unwrap_or(0) as usize;
    let height = trace.height();
    let g = generator(height.trailing_zeros() as usize);
    let on_domain = row_residuals(air, trace, publics, SelectorLaw::TwoAdicLagrange)?;
    let mut points: Vec<F> = (0..height).map(|row| g.exp_u64(row as u64)).collect();
    let mut evaluations: Vec<Vec<F>> = on_domain.chunks(assertions).map(<[F]>::to_vec).collect();
    for j in 0..output_width {
        let point = F::from_u32(2 + j as u32);
        let direct = point_residuals(air, trace, publics, Ext8::from(point))?;
        let base: Vec<F> = direct
            .iter()
            .map(|v| {
                let c = BasedVectorSpace::<F>::as_basis_coefficients_slice(v);
                assert!(
                    c[1..].iter().all(|x| *x == F::ZERO),
                    "base point, base value"
                );
                c[0]
            })
            .collect();
        points.push(point);
        evaluations.push(base);
    }
    // The submitted slot polynomials, substituted pointwise, agree with Air::eval.
    for (point, expected) in points.iter().zip(&evaluations) {
        let slot = |s: usize| horner(&coefficients[s * width..(s + 1) * width], *point);
        assert_eq!(
            &export.arena.evaluate(slot),
            expected,
            "slot polynomials and Air::eval disagree at {point}"
        );
    }
    Ok((
        canonical(&json!({"coefficients": decimals(&coefficients), "width": width.to_string()})),
        json!({
            "entry": "CoefficientResiduals",
            "evaluations": evaluations.iter().map(|e| decimals(e)).collect::<Vec<_>>(),
            "points": decimals(&points),
        }),
    ))
}

/// `ring.rows` over Ext8 assignments at points off the trace domain: one
/// assignment per point, from barycentric openings of the trace and fixed
/// columns, with closed-form two-adic Lagrange selectors.
fn points_case<A>(
    air: &A,
    export: &Export,
    instance: &Instance,
    trace: &RowMajorMatrix<F>,
) -> Result<(String, Value), Refusal>
where
    A: for<'a> Air<PointBuilder<'a>>,
{
    let view = ClosedView::bind(export, instance)?;
    let points: Vec<Ext8> = (0..4)
        .map(|j| ext_from_coordinates([2 + j, 7, 0, 1, 0, 0, 0, 5 * j]))
        .collect();
    let (mut assignments, mut direct) = (vec![], vec![]);
    for point in &points {
        let (main_current, main_next) = open_table(&trace.values, trace.width(), *point)?;
        let (preprocessed_current, preprocessed_next) = match &export.layout.preprocessed {
            Some(p) => open_table(&p.values, p.width, *point)?,
            None => (vec![], vec![]),
        };
        let inputs = view.point_inputs(
            *point,
            &Openings {
                main_current,
                main_next,
                preprocessed_current,
                preprocessed_next,
            },
        )?;
        let expected = point_residuals(air, trace, &instance.public_values, *point)?;
        assert_eq!(
            export.arena.evaluate(|s| inputs[s]),
            expected,
            "arena interpreter and Air::eval disagree off the domain"
        );
        assignments.extend(inputs);
        direct.extend(expected);
    }
    Ok((
        canonical(
            &json!({"assignments": extension_decimals(&assignments), "points": points.len().to_string()}),
        ),
        json!({
            "entry": "PointResiduals",
            "points": extension_decimals(&points),
            "residuals": extension_decimals(&direct),
        }),
    ))
}

/// Input maps `source-CASE.json` and their expectations `source-expected.json`.
///
/// The changed trace adds one to `x` on row zero, which the last row also reads
/// through the wrap; the changed statement adds one to the public `x0`.
pub fn files<A>(
    air: &A,
    export: &Export,
    instance: &Instance,
    trace: &RowMajorMatrix<F>,
) -> Result<Vec<(&'static str, String)>, Refusal>
where
    A: for<'a> Air<RowBuilder<'a>>
        + for<'a> Air<PointBuilder<'a>>
        + for<'a> Air<DebugConstraintBuilder<'a, F>>,
{
    let mut changed_trace = trace.clone();
    changed_trace.values[0] += F::ONE;
    let mut changed_statement = instance.clone();
    changed_statement.public_values[0] += F::ONE;
    let rows = |instance, trace, law| rows_case(air, export, instance, trace, law);
    let (row_law, two_adic) = (SelectorLaw::RowIndicator, SelectorLaw::TwoAdicLagrange);
    let cases = [
        (
            "trace-honest",
            "source-trace-honest.json",
            trace_case(air, export, instance, trace)?,
        ),
        (
            "trace-changed-trace",
            "source-trace-changed-trace.json",
            trace_case(air, export, instance, &changed_trace)?,
        ),
        (
            "trace-changed-public",
            "source-trace-changed-public.json",
            trace_case(air, export, &changed_statement, trace)?,
        ),
        (
            "rows-honest",
            "source-rows-honest.json",
            rows(instance, trace, row_law)?,
        ),
        (
            "rows-changed-trace",
            "source-rows-changed-trace.json",
            rows(instance, &changed_trace, row_law)?,
        ),
        (
            "rows-changed-public",
            "source-rows-changed-public.json",
            rows(&changed_statement, trace, row_law)?,
        ),
        (
            "rows-two-adic",
            "source-rows-two-adic.json",
            rows(instance, &changed_trace, two_adic)?,
        ),
        (
            "coefficients-honest",
            "source-coefficients-honest.json",
            coefficients_case(air, export, instance, trace)?,
        ),
        (
            "coefficients-changed-trace",
            "source-coefficients-changed-trace.json",
            coefficients_case(air, export, instance, &changed_trace)?,
        ),
        (
            "points-honest",
            "source-points-honest.json",
            points_case(air, export, instance, trace)?,
        ),
    ];
    let mut expected = Map::new();
    let mut files = vec![];
    for (name, file, (request, expectation)) in cases {
        expected.insert(name.into(), expectation);
        files.push((file, request));
    }
    files.push(("source-expected.json", canonical(&Value::Object(expected))));
    Ok(files)
}
