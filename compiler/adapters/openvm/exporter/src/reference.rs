//! Pinned upstream evaluation of traces: the symbolic recorder expressions
//! and verifying-key DAG through upstream's `SymbolicEvaluator`, the bus
//! multisets through upstream's logical-interaction generator, and the
//! upstream debug checkers `check_constraints` and `check_logup`.
//!
//! Only the variable lookup is supplied here. Expression evaluation,
//! selector values on each row (`is_first_row`, `is_last_row`,
//! `is_transition` as in `check_constraints`) and message collection are the
//! pinned upstream code paths.

use crate::field::F;
use crate::slice::{SC, Slice, Trace, trace_width};
use openvm_stark_backend::AirRef;
use openvm_stark_backend::air_builders::debug::{check_constraints, check_logup};
use openvm_stark_backend::air_builders::symbolic::symbolic_expression::{
    SymbolicEvaluator, SymbolicExpression,
};
use openvm_stark_backend::air_builders::symbolic::symbolic_variable::{Entry, SymbolicVariable};
use openvm_stark_backend::air_builders::symbolic::{
    SymbolicConstraints, SymbolicConstraintsDag, get_symbolic_builder,
};
use openvm_stark_backend::interaction::SymbolicInteraction;
use openvm_stark_backend::interaction::debug::{
    LogicalInteractions, generate_logical_interactions,
};
use openvm_stark_backend::p3_matrix::Matrix;
use openvm_stark_backend::p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_field::PrimeCharacteristicRing;
use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;

/// The source recorder: upstream `SymbolicRapBuilder` run over the AIR's
/// `eval`, constraints in emission order.
pub fn recorder(air: &AirRef<SC>) -> SymbolicConstraints<F> {
    get_symbolic_builder(air.as_ref(), &trace_width(air)).constraints()
}

/// Variable lookup for one row of one AIR's traces.
pub struct RowEvaluator<'a> {
    parts: Vec<&'a RowMajorMatrix<F>>,
    publics: &'a [F],
    height: usize,
    row: usize,
}

impl<'a> RowEvaluator<'a> {
    pub fn new(trace: &'a Trace, row: usize) -> Self {
        Self {
            parts: trace.parts(),
            publics: &trace.public_values,
            height: trace.height(),
            row,
        }
    }
}

impl SymbolicEvaluator<F, F> for RowEvaluator<'_> {
    fn eval_const(&self, c: F) -> F {
        c
    }
    fn eval_var(&self, var: SymbolicVariable<F>) -> F {
        match var.entry {
            Entry::Main { part_index, offset } => self.parts[part_index]
                .get((self.row + offset) % self.height, var.index)
                .expect("variable within the trace"),
            Entry::Public => self.publics[var.index],
            Entry::Preprocessed { .. } => unreachable!("the slice has no preprocessed trace"),
            Entry::Challenge => unreachable!("deterministic constraints have no challenge"),
        }
    }
    fn eval_is_first_row(&self) -> F {
        F::from_bool(self.row == 0)
    }
    fn eval_is_last_row(&self) -> F {
        F::from_bool(self.row + 1 == self.height)
    }
    fn eval_is_transition(&self) -> F {
        F::from_bool(self.row + 1 != self.height)
    }
}

/// Nonzero values of the recorder constraints on every row:
/// `(constraint, row, value)`.
pub fn recorder_residuals(
    constraints: &[SymbolicExpression<F>],
    trace: &Trace,
) -> Vec<(usize, usize, F)> {
    let mut out = vec![];
    for row in 0..trace.height() {
        let evaluator = RowEvaluator::new(trace, row);
        for (i, c) in constraints.iter().enumerate() {
            let v = evaluator.eval_expr(c);
            if v != F::ZERO {
                out.push((i, row, v));
            }
        }
    }
    out
}

/// Every DAG constraint value on every row, `(constraint position, row, value)`,
/// through upstream `eval_nodes`.
pub fn dag_values(dag: &SymbolicConstraintsDag<F>, trace: &Trace) -> Vec<(usize, usize, F)> {
    let mut out = vec![];
    for row in 0..trace.height() {
        let evaluator = RowEvaluator::new(trace, row);
        let values = evaluator.eval_nodes(&dag.constraints.nodes);
        for (position, idx) in dag.constraints.constraint_idx.iter().enumerate() {
            out.push((position, row, values[*idx]));
        }
    }
    out
}

/// Every recorder constraint value on every row (including zeros).
pub fn recorder_values(
    constraints: &[SymbolicExpression<F>],
    trace: &Trace,
) -> Vec<(usize, usize, F)> {
    let mut out = vec![];
    for row in 0..trace.height() {
        let evaluator = RowEvaluator::new(trace, row);
        for (i, c) in constraints.iter().enumerate() {
            out.push((i, row, evaluator.eval_expr(c)));
        }
    }
    out
}

fn views(trace: &Trace) -> Vec<RowMajorMatrixView<'_, F>> {
    trace.parts().into_iter().map(|m| m.as_view()).collect()
}

/// Bus multisets of the present AIRs through upstream
/// `generate_logical_interactions`, summed per `(bus, message)` as
/// `check_logup` does: the unbalanced keys with their sums.
pub fn unbalanced(
    interactions: &[Vec<SymbolicInteraction<F>>],
    traces: &[Option<Trace>],
) -> Vec<(u16, Vec<F>, F)> {
    let mut logical = LogicalInteractions::<F>::default();
    for (air, (interactions, trace)) in interactions.iter().zip(traces).enumerate() {
        let Some(trace) = trace else { continue };
        let parts = views(trace);
        generate_logical_interactions(
            air,
            interactions,
            &None,
            &parts,
            &trace.public_values,
            &mut logical,
        );
    }
    let mut out = vec![];
    for (bus, keys) in logical.at_bus {
        let keyed: BTreeMap<Vec<u32>, (Vec<F>, F)> = keys
            .into_iter()
            .map(|(fields, connections)| {
                let sum: F = connections.iter().map(|(_, c)| *c).sum();
                (
                    fields.iter().map(|f| f.as_canonical_u32()).collect(),
                    (fields, sum),
                )
            })
            .collect();
        for (_, (fields, sum)) in keyed {
            if sum != F::ZERO {
                out.push((bus, fields, sum));
            }
        }
    }
    out
}

static HOOK: Mutex<()> = Mutex::new(());

/// Run upstream code that panics on failure; `false` on a panic, silently.
fn survives(f: impl FnOnce()) -> bool {
    let _guard = HOOK.lock().unwrap_or_else(|e| e.into_inner());
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = catch_unwind(AssertUnwindSafe(f)).is_ok();
    std::panic::set_hook(previous);
    result
}

/// Upstream `check_constraints` with the pinned `DebugConstraintBuilder`:
/// `true` when every constraint vanishes on every row.
pub fn upstream_accepts(air: &AirRef<SC>, trace: &Trace) -> bool {
    survives(|| {
        let parts = views(trace);
        check_constraints::<_, SC>(
            air.as_ref(),
            &air.name(),
            &None,
            &parts,
            &trace.public_values,
        );
    })
}

/// Upstream `check_logup` over the present AIRs: `true` when every bus
/// balances. It prints its findings to standard output on failure.
pub fn upstream_balanced(
    slice: &Slice,
    interactions: &[Vec<SymbolicInteraction<F>>],
    traces: &[Option<Trace>],
) -> bool {
    survives(|| {
        let mut names = vec![];
        let mut selected = vec![];
        let mut parts = vec![];
        let mut publics = vec![];
        for (i, (air, trace)) in slice.airs().iter().zip(traces).enumerate() {
            let Some(trace) = trace else { continue };
            names.push(air.name());
            selected.push(interactions[i].clone());
            parts.push(views(trace));
            publics.push(trace.public_values.clone());
        }
        let preprocessed: Vec<Option<RowMajorMatrixView<F>>> = vec![None; parts.len()];
        check_logup(&names, &selected, &preprocessed, &parts, &publics);
    })
}

use p3_field::PrimeField32;
