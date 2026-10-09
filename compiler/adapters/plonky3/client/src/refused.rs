//! Upstream AIRs whose meaning the adapter cannot preserve, or whose metadata
//! contradicts their evaluation. Each is a control for a named refusal; none is
//! a supported relation.

use core::sync::atomic::{AtomicU32, Ordering};
use p3_air::{
    Air, AirBuilder, BaseAir, ExtensionBuilder, PeriodicAirBuilder, PermutationAirBuilder,
    WindowAccess,
};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;

/// Reads a periodic column, which the capture does not represent.
pub struct PeriodicAir;
impl<T> BaseAir<T> for PeriodicAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: PeriodicAirBuilder> Air<AB> for PeriodicAir {
    fn eval(&self, builder: &mut AB) {
        let x = builder.main().current_slice()[0];
        let period = builder.periodic_values()[0];
        builder.assert_eq(x, period);
    }
}

/// Asserts a constraint over the extension field.
pub struct ExtensionConstraintAir;
impl<T> BaseAir<T> for ExtensionConstraintAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: ExtensionBuilder> Air<AB> for ExtensionConstraintAir {
    fn eval(&self, builder: &mut AB) {
        let x: AB::Expr = builder.main().current_slice()[0].into();
        builder.assert_zero_ext(AB::ExprEF::from(x));
    }
}

/// Which permutation-argument surface an AIR reads.
#[derive(Clone, Copy, Debug)]
pub enum PermutationSurface {
    Column,
    Challenge,
    ExpectedValue,
}

/// Reads one permutation-argument surface and asserts it is zero.
pub struct PermutationAir(pub PermutationSurface);
impl<T> BaseAir<T> for PermutationAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: PermutationAirBuilder> Air<AB> for PermutationAir {
    fn eval(&self, builder: &mut AB) {
        let value: AB::ExprEF = match self.0 {
            PermutationSurface::Column => builder.permutation().current_slice()[0].into(),
            PermutationSurface::Challenge => builder.permutation_randomness()[0].into(),
            PermutationSurface::ExpectedValue => builder.permutation_values()[0].clone().into(),
        };
        builder.assert_zero_ext(value);
    }
}

/// How a selector reaches an assertion outside guard position.
#[derive(Clone, Copy, Debug)]
pub enum SelectorMisuse {
    /// `is_first_row + x`: the debug checker accepts `x = -1` on row zero,
    /// while the two-adic polynomial view requires `x = -n` there.
    AddedFirstRow,
    /// `x - is_last_row`.
    SubtractedLastRow,
    /// One shared guarded product is asserted, then also added to `x`.
    SharedProduct,
}

pub struct SelectorMisuseAir(pub SelectorMisuse);
impl<T> BaseAir<T> for SelectorMisuseAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: AirBuilder> Air<AB> for SelectorMisuseAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let x: AB::Expr = main.current_slice()[0].into();
        let next: AB::Expr = main.next_slice()[0].into();
        match self.0 {
            SelectorMisuse::AddedFirstRow => {
                let selector = builder.is_first_row();
                builder.assert_zero(selector + x);
            }
            SelectorMisuse::SubtractedLastRow => {
                let selector = builder.is_last_row();
                builder.assert_eq(x, selector);
            }
            SelectorMisuse::SharedProduct => {
                let guarded = builder.is_transition() * (next - x.clone());
                builder.assert_zero(guarded.clone());
                builder.assert_zero(guarded + x);
            }
        }
    }
}

/// One degree-two transition `x' = x * x` with configurable metadata.
#[derive(Clone, Debug)]
pub struct MetadataAir {
    pub next_row_columns: Vec<usize>,
    pub constraint_count: Option<usize>,
    pub degree: Option<usize>,
    /// Height and width of a preprocessed table filled with ones.
    pub preprocessed: Option<(usize, usize)>,
}
impl MetadataAir {
    pub fn consistent() -> Self {
        Self {
            next_row_columns: vec![0],
            constraint_count: Some(1),
            degree: Some(2),
            preprocessed: None,
        }
    }
}
impl<T: Field> BaseAir<T> for MetadataAir {
    fn width(&self) -> usize {
        1
    }
    fn main_next_row_columns(&self) -> Vec<usize> {
        self.next_row_columns.clone()
    }
    fn num_constraints(&self) -> Option<usize> {
        self.constraint_count
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        self.degree
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<T>> {
        self.preprocessed
            .map(|(height, width)| RowMajorMatrix::new(vec![T::ONE; height * width], width))
    }
}
impl<AB: AirBuilder<F: Field>> Air<AB> for MetadataAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (x, next) = (main.current_slice()[0], main.next_slice()[0]);
        builder.when_transition().assert_eq(next, x * x);
    }
}

/// Uses a public value without declaring it in `num_public_values`.
pub struct UndeclaredPublicAir;
impl<T> BaseAir<T> for UndeclaredPublicAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: AirBuilder> Air<AB> for UndeclaredPublicAir {
    fn eval(&self, builder: &mut AB) {
        let x = builder.main().current_slice()[0];
        let public = builder.public_values()[0];
        builder.when_first_row().assert_eq(x, public);
    }
}

static EVALUATIONS: AtomicU32 = AtomicU32::new(0);

/// Emits a different constant on every evaluation.
pub struct NondeterministicAir;
impl<T> BaseAir<T> for NondeterministicAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: AirBuilder> Air<AB> for NondeterministicAir {
    fn eval(&self, builder: &mut AB) {
        let x: AB::Expr = builder.main().current_slice()[0].into();
        let count = EVALUATIONS.fetch_add(1, Ordering::Relaxed) + 2;
        builder.assert_zero(x - AB::Expr::from_u32(count));
    }
}

/// Changes its constraints when a periodic surface exists, without reading it.
pub struct ProbeDependentAir;
impl<T> BaseAir<T> for ProbeDependentAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: PeriodicAirBuilder> Air<AB> for ProbeDependentAir {
    fn eval(&self, builder: &mut AB) {
        let x: AB::Expr = builder.main().current_slice()[0].into();
        if builder.periodic_values().is_empty() {
            builder.assert_zero(x);
        } else {
            builder.assert_zero(x.clone() * x);
        }
    }
}

/// Panics during evaluation.
pub struct PanickingAir;
impl<T> BaseAir<T> for PanickingAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: AirBuilder> Air<AB> for PanickingAir {
    fn eval(&self, _builder: &mut AB) {
        panic!("deliberate evaluation failure");
    }
}

/// Requests a three-row transition window, which upstream symbolic capture rejects.
pub struct WideWindowAir;
impl<T> BaseAir<T> for WideWindowAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: AirBuilder> Air<AB> for WideWindowAir {
    fn eval(&self, builder: &mut AB) {
        let x = builder.main().current_slice()[0];
        builder.when_transition_window(3).assert_zero(x);
    }
}
