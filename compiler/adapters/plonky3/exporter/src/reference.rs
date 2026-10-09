//! References that evaluate the AIR itself, never the exported arena.
//!
//! - [`row_residuals`] and [`point_residuals`] call `Air::eval` with concrete
//!   builders that record every asserted value under a stated selector law.
//! - [`upstream_failures`] and [`upstream_accepts`] run the pinned upstream
//!   `DebugConstraintBuilder` and `check_constraints`, which report only
//!   whether each value is zero, with the row-indicator selector convention.
//! - [`open`] and [`lagrange_selectors_at`] evaluate trace interpolants and
//!   unnormalized Lagrange selectors at a point by direct products and
//!   barycentric sums, independently of the inverse DFT in the closed view.

use crate::field::{Ext8, F, generator};
use crate::refusal::{Result, ensure};
use crate::view::SelectorLaw;
use p3_air::{Air, AirBuilder, DebugConstraintBuilder, RowWindow, check_constraints};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::ViewPair;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// Concrete builder over KoalaBear rows; records every asserted value.
pub struct RowBuilder<'a> {
    main: RowWindow<'a, F>,
    preprocessed: RowWindow<'a, F>,
    public_values: &'a [F],
    selectors: [F; 3],
    pub residuals: Vec<F>,
}

impl<'a> AirBuilder for RowBuilder<'a> {
    type F = F;
    type Expr = F;
    type Var = F;
    type PreprocessedWindow = RowWindow<'a, F>;
    type MainWindow = RowWindow<'a, F>;
    type PublicVar = F;

    fn main(&self) -> Self::MainWindow {
        self.main
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.preprocessed
    }
    fn is_first_row(&self) -> F {
        self.selectors[0]
    }
    fn is_last_row(&self) -> F {
        self.selectors[1]
    }
    fn is_transition_window(&self, size: usize) -> F {
        assert_eq!(size, 2, "only two-row windows are captured");
        self.selectors[2]
    }
    fn assert_zero<I: Into<F>>(&mut self, x: I) {
        self.residuals.push(x.into());
    }
    fn public_values(&self) -> &[F] {
        self.public_values
    }
}

/// Concrete builder at an extension point: reads are interpolant values,
/// publics stay in the base field.
pub struct PointBuilder<'a> {
    main: RowWindow<'a, Ext8>,
    preprocessed: RowWindow<'a, Ext8>,
    public_values: &'a [F],
    selectors: [Ext8; 3],
    pub residuals: Vec<Ext8>,
}

impl<'a> AirBuilder for PointBuilder<'a> {
    type F = F;
    type Expr = Ext8;
    type Var = Ext8;
    type PreprocessedWindow = RowWindow<'a, Ext8>;
    type MainWindow = RowWindow<'a, Ext8>;
    type PublicVar = F;

    fn main(&self) -> Self::MainWindow {
        self.main
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.preprocessed
    }
    fn is_first_row(&self) -> Ext8 {
        self.selectors[0]
    }
    fn is_last_row(&self) -> Ext8 {
        self.selectors[1]
    }
    fn is_transition_window(&self, size: usize) -> Ext8 {
        assert_eq!(size, 2, "only two-row windows are captured");
        self.selectors[2]
    }
    fn assert_zero<I: Into<Ext8>>(&mut self, x: I) {
        self.residuals.push(x.into());
    }
    fn public_values(&self) -> &[F] {
        self.public_values
    }
}

/// Selector values on the trace domain from their polynomial definitions:
/// `first = sum_k x^k`, `last = sum_k g^-(n-1-k) x^k`, `transition = x - g^-1`.
/// Quadratic in the height; intended for small reference tables.
pub fn two_adic_selectors_on_domain(height: usize) -> Vec<[F; 3]> {
    let g = generator(height.trailing_zeros() as usize);
    let a = g.inverse();
    (0..height)
        .map(|row| {
            let x = g.exp_u64(row as u64);
            let (mut first, mut last, mut power) = (F::ZERO, F::ZERO, F::ONE);
            for k in 0..height {
                first += power;
                last += a.exp_u64((height - 1 - k) as u64) * power;
                power *= x;
            }
            [first, last, x - a]
        })
        .collect()
}

fn row_selectors(height: usize, law: SelectorLaw) -> Vec<[F; 3]> {
    match law {
        SelectorLaw::RowIndicator => (0..height)
            .map(|i| {
                [
                    F::from_bool(i == 0),
                    F::from_bool(i == height - 1),
                    F::from_bool(i != height - 1),
                ]
            })
            .collect(),
        SelectorLaw::TwoAdicLagrange => two_adic_selectors_on_domain(height),
    }
}

/// Every asserted value on every row, row-major, by direct `Air::eval`.
/// The preprocessed table is the AIR's own `preprocessed_trace`.
pub fn row_residuals<A>(
    air: &A,
    trace: &RowMajorMatrix<F>,
    public_values: &[F],
    law: SelectorLaw,
) -> Result<Vec<F>>
where
    A: for<'a> Air<RowBuilder<'a>>,
{
    let height = trace.height();
    ensure(
        height > 0 && trace.width() == air.width(),
        "plonky3-trace-width",
        || "trace shape".into(),
    )?;
    let preprocessed = air.preprocessed_trace();
    let empty: [F; 0] = [];
    let selectors = row_selectors(height, law);
    let width = trace.width();
    let mut residuals = Vec::new();
    for (row, selectors) in selectors.into_iter().enumerate() {
        let next = (row + 1) % height;
        let fixed = |r: usize| {
            preprocessed
                .as_ref()
                .map_or(&empty[..], |p| &p.values[r * p.width..(r + 1) * p.width])
        };
        let mut builder = RowBuilder {
            main: RowWindow::from_two_rows(
                &trace.values[row * width..(row + 1) * width],
                &trace.values[next * width..(next + 1) * width],
            ),
            preprocessed: RowWindow::from_two_rows(fixed(row), fixed(next)),
            public_values,
            selectors,
            residuals: Vec::new(),
        };
        air.eval(&mut builder);
        residuals.extend(builder.residuals);
    }
    Ok(residuals)
}

/// Unnormalized Lagrange selectors at a point outside the trace domain, from
/// products over the domain: `prod_{j != 0} (x - g^j)`, `prod_{j != n-1} (x - g^j)`.
pub fn lagrange_selectors_at(point: Ext8, height: usize) -> Result<[Ext8; 3]> {
    let g = generator(height.trailing_zeros() as usize);
    let (mut first, mut last, mut power) = (Ext8::ONE, Ext8::ONE, F::ONE);
    for j in 0..height {
        let factor = point - Ext8::from(power);
        ensure(factor != Ext8::ZERO, "plonky3-point-on-domain", || {
            "evaluation point lies in the trace domain".into()
        })?;
        if j != 0 {
            first *= factor;
        }
        if j != height - 1 {
            last *= factor;
        }
        power *= g;
    }
    Ok([first, last, point - Ext8::from(g.inverse())])
}

/// Barycentric value at `point` of the interpolant through `(g^i, values[i])`.
pub fn open(values: &[F], point: Ext8) -> Result<Ext8> {
    let n = values.len();
    let g = generator(n.trailing_zeros() as usize);
    let vanishing = point.exp_u64(n as u64) - Ext8::ONE;
    ensure(vanishing != Ext8::ZERO, "plonky3-point-on-domain", || {
        "evaluation point lies in the trace domain".into()
    })?;
    let mut sum = Ext8::ZERO;
    let mut power = F::ONE;
    for value in values {
        sum += (point - Ext8::from(power)).inverse() * (*value * power);
        power *= g;
    }
    Ok(sum * vanishing * F::from_u32(n as u32).inverse())
}

/// Openings of all columns of a row-major table at `point` and `g point`.
pub fn open_table(values: &[F], width: usize, point: Ext8) -> Result<(Vec<Ext8>, Vec<Ext8>)> {
    if width == 0 {
        return Ok((vec![], vec![]));
    }
    let height = values.len() / width;
    let g = generator(height.trailing_zeros() as usize);
    let column = |c: usize| -> Vec<F> { (0..height).map(|r| values[r * width + c]).collect() };
    let current = (0..width)
        .map(|c| open(&column(c), point))
        .collect::<Result<Vec<_>>>()?;
    let next = (0..width)
        .map(|c| open(&column(c), point * g))
        .collect::<Result<Vec<_>>>()?;
    Ok((current, next))
}

/// Every asserted value at an out-of-domain point by direct `Air::eval`, with
/// the two-adic selectors and the AIR's own preprocessed table.
pub fn point_residuals<A>(
    air: &A,
    trace: &RowMajorMatrix<F>,
    public_values: &[F],
    point: Ext8,
) -> Result<Vec<Ext8>>
where
    A: for<'a> Air<PointBuilder<'a>>,
{
    let height = trace.height();
    let (main_current, main_next) = open_table(&trace.values, trace.width(), point)?;
    let preprocessed = air.preprocessed_trace();
    let (fixed_current, fixed_next) = match &preprocessed {
        Some(p) => open_table(&p.values, p.width, point)?,
        None => (vec![], vec![]),
    };
    let mut builder = PointBuilder {
        main: RowWindow::from_two_rows(&main_current, &main_next),
        preprocessed: RowWindow::from_two_rows(&fixed_current, &fixed_next),
        public_values,
        selectors: lagrange_selectors_at(point, height)?,
        residuals: Vec::new(),
    };
    air.eval(&mut builder);
    Ok(builder.residuals)
}

/// `(row, constraint)` pairs the pinned upstream debug builder reports as
/// nonzero, visiting every row (`check_constraints` stops at the first).
pub fn upstream_failures<A>(
    air: &A,
    trace: &RowMajorMatrix<F>,
    public_values: &[F],
) -> Vec<(usize, usize)>
where
    A: for<'a> Air<DebugConstraintBuilder<'a, F>>,
{
    let (height, width) = (trace.height(), trace.width());
    let preprocessed = air.preprocessed_trace();
    let mut failures = Vec::new();
    for row in 0..height {
        let next = (row + 1) % height;
        let main = ViewPair::new(
            RowMajorMatrixView::new_row(&trace.values[row * width..(row + 1) * width]),
            RowMajorMatrixView::new_row(&trace.values[next * width..(next + 1) * width]),
        );
        let fixed = match &preprocessed {
            Some(p) => ViewPair::new(
                RowMajorMatrixView::new_row(&p.values[row * p.width..(row + 1) * p.width]),
                RowMajorMatrixView::new_row(&p.values[next * p.width..(next + 1) * p.width]),
            ),
            None => ViewPair::new(
                RowMajorMatrixView::new(&[], 0),
                RowMajorMatrixView::new(&[], 0),
            ),
        };
        let mut builder = DebugConstraintBuilder::new(
            row,
            main,
            fixed,
            public_values,
            F::from_bool(row == 0),
            F::from_bool(row == height - 1),
            F::from_bool(row != height - 1),
        );
        air.eval(&mut builder);
        failures.extend(builder.failures().iter().map(|f| (f.row, f.constraint)));
    }
    failures
}

/// The pinned upstream `check_constraints` verdict; a panic is rejection.
pub fn upstream_accepts<A>(air: &A, trace: &RowMajorMatrix<F>, public_values: &[F]) -> bool
where
    A: for<'a> Air<DebugConstraintBuilder<'a, F>>,
{
    catch_unwind(AssertUnwindSafe(|| {
        check_constraints(air, trace, public_values)
    }))
    .is_ok()
}
