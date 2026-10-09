//! Closed view: binds an export to an authorized instance and maps every arena
//! input to a value under a selected substitution.
//!
//! Reads are cyclic on a table of height `n = 2^k`: offset one on row `n - 1`
//! reads row zero. Selector slots have two laws, which give different residual
//! values and are never equated:
//!
//! ```text
//! row indicator      first = [i = 0], last = [i = n-1], transition = [i != n-1]
//! two-adic Lagrange  first = Z_H(x)/(x-1), last = Z_H(x)/(x-g^-1), transition = x-g^-1
//! ```
//!
//! The first is the upstream debug checker's convention; the second is the
//! upstream two-adic STARK's. Export admission has checked that selectors
//! occur only in guard position, so both laws vanish on the same rows.

use crate::artifact::Instance;
use crate::field::{Ext8, F, generator, height_scalar};
use crate::model::{Export, SelectorKind, Slot};
use crate::refusal::{Result, ensure};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelectorLaw {
    RowIndicator,
    TwoAdicLagrange,
}

/// Values of every main and preprocessed column at an evaluation point `x`
/// (`current`) and at `g x` (`next`).
#[derive(Clone, Debug)]
pub struct Openings {
    pub main_current: Vec<Ext8>,
    pub main_next: Vec<Ext8>,
    pub preprocessed_current: Vec<Ext8>,
    pub preprocessed_next: Vec<Ext8>,
}

#[derive(Clone, Debug)]
pub struct ClosedView<'a> {
    pub export: &'a Export,
    pub height: usize,
    pub log_height: usize,
    pub generator: F,
    pub public_values: Vec<F>,
}

impl<'a> ClosedView<'a> {
    /// The instance must select exactly this export and supply its full statement.
    pub fn bind(export: &'a Export, instance: &Instance) -> Result<Self> {
        ensure(
            instance.export_sha256 == export.sha256(),
            "plonky3-export-identity",
            || "instance selects a different export".into(),
        )?;
        let log_height = export.layout.admits_height(instance.height)?;
        ensure(
            instance.public_values.len() == export.layout.public_values,
            "plonky3-public-values",
            || {
                format!(
                    "{} public values, export declares {}",
                    instance.public_values.len(),
                    export.layout.public_values
                )
            },
        )?;
        Ok(Self {
            export,
            height: instance.height,
            log_height,
            generator: generator(log_height),
            public_values: instance.public_values.clone(),
        })
    }

    pub fn check_trace(&self, trace: &RowMajorMatrix<F>) -> Result<()> {
        ensure(
            trace.width() == self.export.layout.main_width,
            "plonky3-trace-width",
            || {
                format!(
                    "trace width {}, export declares {}",
                    trace.width(),
                    self.export.layout.main_width
                )
            },
        )?;
        ensure(trace.height() == self.height, "plonky3-height", || {
            format!(
                "trace height {}, instance declares {}",
                trace.height(),
                self.height
            )
        })
    }

    fn preprocessed(&self) -> &[F] {
        self.export
            .layout
            .preprocessed
            .as_ref()
            .map_or(&[], |p| &p.values)
    }

    /// Selector values on row `i` of the trace domain. Two-adic values use the
    /// closed forms `n` at `x = 1`, `n g` at `x = g^-1`, and `g^i - g^-1`.
    pub fn selector_on_row(&self, kind: SelectorKind, row: usize, law: SelectorLaw) -> F {
        let last = self.height - 1;
        match (law, kind) {
            (SelectorLaw::RowIndicator, SelectorKind::FirstRow) => F::from_bool(row == 0),
            (SelectorLaw::RowIndicator, SelectorKind::LastRow) => F::from_bool(row == last),
            (SelectorLaw::RowIndicator, SelectorKind::Transition) => F::from_bool(row != last),
            (SelectorLaw::TwoAdicLagrange, SelectorKind::FirstRow) => {
                if row == 0 {
                    height_scalar(self.height)
                } else {
                    F::ZERO
                }
            }
            (SelectorLaw::TwoAdicLagrange, SelectorKind::LastRow) => {
                if row == last {
                    height_scalar(self.height) * self.generator
                } else {
                    F::ZERO
                }
            }
            (SelectorLaw::TwoAdicLagrange, SelectorKind::Transition) => {
                self.generator.exp_u64(row as u64) - self.generator.inverse()
            }
        }
    }

    /// Row-major assignment with one column per arena input.
    pub fn row_inputs(&self, trace: &RowMajorMatrix<F>, law: SelectorLaw) -> Result<Vec<F>> {
        self.check_trace(trace)?;
        let (n, slots) = (self.height, &self.export.slots);
        let width = self.export.layout.main_width;
        let fixed = self.preprocessed();
        let fixed_width = self
            .export
            .layout
            .preprocessed
            .as_ref()
            .map_or(0, |p| p.width);
        let mut inputs = Vec::with_capacity(n * slots.len());
        for row in 0..n {
            for slot in slots {
                inputs.push(match *slot {
                    Slot::Main { offset, column } => {
                        trace.values[((row + offset) % n) * width + column]
                    }
                    Slot::Preprocessed { offset, column } => {
                        fixed[((row + offset) % n) * fixed_width + column]
                    }
                    Slot::Public(i) => self.public_values[i],
                    Slot::Selector(kind) => self.selector_on_row(kind, row, law),
                });
            }
        }
        Ok(inputs)
    }

    /// Slot values at a point outside the trace domain, two-adic law.
    pub fn point_inputs(&self, point: Ext8, openings: &Openings) -> Result<Vec<Ext8>> {
        let layout = &self.export.layout;
        let fixed_width = layout.preprocessed.as_ref().map_or(0, |p| p.width);
        ensure(
            openings.main_current.len() == layout.main_width
                && openings.main_next.len() == layout.main_width
                && openings.preprocessed_current.len() == fixed_width
                && openings.preprocessed_next.len() == fixed_width,
            "plonky3-opening-shape",
            || "openings do not match the layout".into(),
        )?;
        let vanishing = point.exp_power_of_2(self.log_height) - Ext8::ONE;
        ensure(vanishing != Ext8::ZERO, "plonky3-point-on-domain", || {
            "evaluation point lies in the trace domain".into()
        })?;
        let last = Ext8::from(self.generator.inverse());
        Ok(self
            .export
            .slots
            .iter()
            .map(|slot| match *slot {
                Slot::Main { offset: 0, column } => openings.main_current[column],
                Slot::Main { column, .. } => openings.main_next[column],
                Slot::Preprocessed { offset: 0, column } => openings.preprocessed_current[column],
                Slot::Preprocessed { column, .. } => openings.preprocessed_next[column],
                Slot::Public(i) => Ext8::from(self.public_values[i]),
                Slot::Selector(SelectorKind::FirstRow) => vanishing / (point - Ext8::ONE),
                Slot::Selector(SelectorKind::LastRow) => vanishing / (point - last),
                Slot::Selector(SelectorKind::Transition) => point - last,
            })
            .collect())
    }

    /// Slot-major coefficient polynomials with a common width `max(n, 2)`.
    /// A next-row read is the shifted interpolant `T(g X)`; selectors are the
    /// two-adic Lagrange polynomials. Interpolation is a direct inverse DFT.
    pub fn coefficient_inputs(&self, trace: &RowMajorMatrix<F>) -> Result<(Vec<F>, usize)> {
        self.check_trace(trace)?;
        let n = self.height;
        let width = n.max(2);
        let g = self.generator;
        let column = |values: &[F], stride: usize, column: usize| -> Vec<F> {
            let points: Vec<F> = (0..n).map(|r| values[r * stride + column]).collect();
            inverse_dft(&points, g)
        };
        let shift = |mut c: Vec<F>| -> Vec<F> {
            let mut power = F::ONE;
            for coefficient in &mut c {
                *coefficient *= power;
                power *= g;
            }
            c
        };
        let fixed_width = self
            .export
            .layout
            .preprocessed
            .as_ref()
            .map_or(0, |p| p.width);
        let a = g.inverse();
        let mut result = Vec::with_capacity(width * self.export.slots.len());
        for slot in &self.export.slots {
            let mut polynomial = match *slot {
                Slot::Main { offset, column: c } => {
                    let p = column(&trace.values, self.export.layout.main_width, c);
                    if offset == 0 { p } else { shift(p) }
                }
                Slot::Preprocessed { offset, column: c } => {
                    let p = column(self.preprocessed(), fixed_width, c);
                    if offset == 0 { p } else { shift(p) }
                }
                Slot::Public(i) => vec![self.public_values[i]],
                Slot::Selector(SelectorKind::FirstRow) => vec![F::ONE; n],
                Slot::Selector(SelectorKind::LastRow) => {
                    (0..n).map(|k| a.exp_u64((n - 1 - k) as u64)).collect()
                }
                Slot::Selector(SelectorKind::Transition) => vec![-a, F::ONE],
            };
            polynomial.resize(width, F::ZERO);
            result.extend(polynomial);
        }
        Ok((result, width))
    }

    /// Residuals of all assertions on every row with the adapter's own arena
    /// interpreter, row-major.
    pub fn residuals(&self, inputs: &[F]) -> Vec<F> {
        let slots = self.export.slots.len();
        (0..self.height)
            .flat_map(|row| self.export.arena.evaluate(|s| inputs[row * slots + s]))
            .collect()
    }
}

/// Ascending coefficients of the polynomial through `(g^i, values[i])`.
pub fn inverse_dft(values: &[F], generator: F) -> Vec<F> {
    let n = values.len();
    let n_inverse = F::from_u32(n as u32).inverse();
    let g_inverse = generator.inverse();
    (0..n)
        .map(|k| {
            let step = g_inverse.exp_u64(k as u64);
            let mut power = F::ONE;
            let mut sum = F::ZERO;
            for value in values {
                sum += *value * power;
                power *= step;
            }
            sum * n_inverse
        })
        .collect()
}

/// Nonzero residual positions `(row, assertion)` of a row-major residual table.
pub fn violations<T: PartialEq + PrimeCharacteristicRing>(
    residuals: &[T],
    assertions: usize,
) -> Vec<(usize, usize)> {
    if assertions == 0 {
        return vec![];
    }
    residuals
        .iter()
        .enumerate()
        .filter(|(_, r)| **r != T::ZERO)
        .map(|(i, _)| (i / assertions, i % assertions))
        .collect()
}
