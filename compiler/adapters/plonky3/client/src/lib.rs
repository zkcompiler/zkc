//! Ordinary Plonky3 0.5.1 AIRs maintained as external clients of the zkc
//! adapter. This crate depends only on upstream Plonky3 crates. Its trace
//! generators are witness tools; they are not part of any exported relation.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_koala_bear::KoalaBear;
use p3_matrix::dense::RowMajorMatrix;

pub mod refused;

pub type F = KoalaBear;

/// Added to every recurrence step; a constant above 2^26 exercises canonical
/// encoding rather than a small literal that internal forms might preserve.
pub const STEP_CONSTANT: u32 = 123_456_789;

/// A two-row nonlinear recurrence with a fixed column and public boundaries.
///
/// Main columns are `x`, `y`, `p` and `acc`; the preprocessed column is `k`.
/// Public values are `x0`, `y0` and the final accumulator.
///
/// ```text
/// every row   p = x * y
/// first row   x = x0, y = y0, acc = 0
/// transition  x' = y, y' = p + k + STEP_CONSTANT, acc' = acc + p * x * k
/// last row    acc = acc_final, x' = x0   (x' wraps to row zero)
/// ```
#[derive(Clone, Debug)]
pub struct RecurrenceAir {
    pub log_height: usize,
}

pub const RECURRENCE_WIDTH: usize = 4;

impl RecurrenceAir {
    pub fn height(&self) -> usize {
        1 << self.log_height
    }

    /// The fixed column is a deterministic function of the row index.
    pub fn round_constant(row: usize) -> u32 {
        let i = row as u64;
        ((i * i + 7 * i + 3) % 2_130_706_433) as u32
    }

    /// Honest trace and public values for initial values `x0` and `y0`.
    pub fn generate(&self, x0: F, y0: F) -> (RowMajorMatrix<F>, Vec<F>) {
        let height = self.height();
        let mut values = Vec::with_capacity(height * RECURRENCE_WIDTH);
        let (mut x, mut y, mut acc) = (x0, y0, F::ZERO);
        for row in 0..height {
            let p = x * y;
            values.extend([x, y, p, acc]);
            let k = F::from_u32(Self::round_constant(row));
            (x, y, acc) = (y, p + k + F::from_u32(STEP_CONSTANT), acc + p * x * k);
        }
        let last = values[(height - 1) * RECURRENCE_WIDTH + 3];
        (
            RowMajorMatrix::new(values, RECURRENCE_WIDTH),
            vec![x0, y0, last],
        )
    }
}

impl<T: Field> BaseAir<T> for RecurrenceAir {
    fn width(&self) -> usize {
        RECURRENCE_WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<T>> {
        let column = (0..self.height())
            .map(|row| T::from_u32(Self::round_constant(row)))
            .collect();
        Some(RowMajorMatrix::new(column, 1))
    }

    fn num_public_values(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F: Field>> Air<AB> for RecurrenceAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice().to_vec();
        let next = main.next_slice().to_vec();
        let k: AB::Expr = builder.preprocessed().current_slice()[0].into();
        let publics = builder.public_values().to_vec();
        let (x, y, p, acc) = (local[0], local[1], local[2], local[3]);
        let (p_expr, acc_expr): (AB::Expr, AB::Expr) = (p.into(), acc.into());

        builder.assert_eq(p, x * y);

        let mut first = builder.when_first_row();
        first.assert_eq(x, publics[0]);
        first.assert_eq(y, publics[1]);
        first.assert_zero(acc);

        let mut transition = builder.when_transition();
        transition.assert_eq(next[0], y);
        transition.assert_eq(
            next[1],
            p_expr + k.clone() + AB::Expr::from_u32(STEP_CONSTANT),
        );
        transition.assert_eq(next[3], acc_expr + p * x * k);

        let mut last = builder.when_last_row();
        last.assert_eq(acc, publics[2]);
        last.assert_eq(next[0], publics[0]);
    }
}

/// A one-column counter whose step constraint is either guarded by the
/// transition selector or applies on every row, including the wrapped row.
#[derive(Clone, Debug)]
pub struct CounterAir {
    pub guarded: bool,
}

impl<T> BaseAir<T> for CounterAir {
    fn width(&self) -> usize {
        1
    }
}

impl<AB: AirBuilder> Air<AB> for CounterAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (local, next) = (main.current_slice()[0], main.next_slice()[0]);
        let (next, local): (AB::Expr, AB::Expr) = (next.into(), local.into());
        let step = next - local - AB::Expr::ONE;
        if self.guarded {
            builder.when_transition().assert_zero(step);
        } else {
            builder.assert_zero(step);
        }
    }
}

impl CounterAir {
    pub fn generate(height: usize) -> RowMajorMatrix<F> {
        RowMajorMatrix::new((0..height as u32).map(F::new).collect(), 1)
    }
}
