//! Capture of one `Air<SymbolicAirBuilder<KoalaBear>>` through the pinned
//! upstream symbolic builder, and its lowering to the exported view.
//!
//! `Air::eval` is arbitrary host code. The capture records what that code
//! asserted for the declared layout; it is not a source-adequacy theorem.
//! Every call into the AIR runs under `catch_unwind`, is repeated to detect
//! nondeterminism, and is compared against a probe layout that gives every
//! unsupported upstream surface a nonzero width.

use crate::arena::{Arena, DEPTH_LIMIT, NODE_LIMIT, Node};
use crate::field::F;
use crate::model::{
    Assertion, Export, Layout, Origin, Preprocessed, SelectorKind, Slot, check_guards,
    degree_multiple_weight, features,
};
use crate::refusal::{Refusal, Result, ensure, refuse};
use p3_air::{
    Air, AirLayout, BaseAir, BaseEntry, BaseLeaf, ExtEntry, ExtLeaf, SymbolicAirBuilder,
    SymbolicExpr, SymbolicExpression, SymbolicExpressionExt, SymbolicVariable,
};
use p3_field::PrimeField32;
use p3_matrix::Matrix;
use std::collections::{BTreeSet, HashMap};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

/// Distinct upstream expression nodes visited per capture.
pub const VISIT_LIMIT: usize = 1 << 22;
/// Width given to each unsupported surface in the probe capture.
const PROBE_WIDTH: usize = 2;

type Base = SymbolicExpression<F>;
type Extension = SymbolicExpressionExt<F, F>;

fn guarded<T>(what: &str, call: impl FnOnce() -> T) -> Result<T> {
    catch_unwind(AssertUnwindSafe(call)).map_err(|payload| {
        let message = payload
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "non-string panic payload".into());
        Refusal {
            id: "plonky3-eval-panicked",
            detail: format!("{what}: {message}"),
        }
    })
}

/// Upstream metadata read from `BaseAir`, before any evaluation.
fn metadata<A: BaseAir<F>>(air: &A) -> Result<(Layout, Option<usize>, Option<usize>)> {
    let (width, preprocessed, main_next, preprocessed_next, publics, count, degree) =
        guarded("BaseAir metadata", || {
            (
                air.width(),
                air.preprocessed_trace(),
                air.main_next_row_columns(),
                air.preprocessed_next_row_columns(),
                air.num_public_values(),
                air.num_constraints(),
                air.max_constraint_degree(),
            )
        })?;
    let normalize = |mut columns: Vec<usize>, width: usize, what: &str| -> Result<Vec<usize>> {
        let declared = columns.len();
        columns.sort_unstable();
        columns.dedup();
        ensure(
            columns.len() == declared && columns.iter().all(|c| *c < width),
            "plonky3-next-row-metadata",
            || format!("{what} next-row columns are not distinct columns below width {width}"),
        )?;
        Ok(columns)
    };
    let preprocessed = match preprocessed {
        None => {
            ensure(
                preprocessed_next.is_empty(),
                "plonky3-next-row-metadata",
                || "preprocessed next-row columns without a preprocessed table".into(),
            )?;
            None
        }
        Some(matrix) => {
            let (w, h) = (matrix.width(), matrix.height());
            ensure(
                w > 0 && matrix.values.len() == w * h,
                "plonky3-preprocessed-shape",
                || {
                    format!(
                        "preprocessed table of width {w} with {} values",
                        matrix.values.len()
                    )
                },
            )?;
            Some(Preprocessed {
                width: w,
                height: h,
                next_row_columns: normalize(preprocessed_next, w, "preprocessed")?,
                values: matrix.values,
            })
        }
    };
    let layout = Layout {
        main_width: width,
        main_next_row_columns: normalize(main_next, width, "main")?,
        preprocessed,
        public_values: publics,
    };
    layout.check()?;
    Ok((layout, count, degree))
}

fn record<A: Air<SymbolicAirBuilder<F>>>(
    air: &A,
    layout: AirLayout,
) -> Result<(Vec<Base>, Vec<Extension>)> {
    guarded("Air::eval", || {
        let mut builder = SymbolicAirBuilder::<F>::new(layout);
        air.eval(&mut builder);
        (builder.base_constraints(), builder.extension_constraints())
    })
}

/// Unsupported features observed in a capture, by refusal identifier.
fn unsupported(base: &[Base], extension: &[Extension]) -> BTreeSet<&'static str> {
    let mut found = BTreeSet::new();
    let mut seen: std::collections::HashSet<*const Base> = Default::default();
    let mut base_stack: Vec<&Base> = base.iter().collect();
    let mut ext_stack: Vec<&Extension> = extension.iter().collect();
    let mut ext_seen: std::collections::HashSet<*const Extension> = Default::default();
    if !extension.is_empty() {
        found.insert("plonky3-extension-constraint");
    }
    while let Some(e) = ext_stack.pop() {
        if !ext_seen.insert(e) {
            continue;
        }
        match e {
            SymbolicExpr::Leaf(ExtLeaf::ExtVariable(v)) => {
                found.insert(match v.entry {
                    ExtEntry::Permutation { .. } => "plonky3-permutation-column",
                    ExtEntry::Challenge => "plonky3-permutation-challenge",
                    ExtEntry::PermutationValue => "plonky3-permutation-value",
                });
            }
            SymbolicExpr::Leaf(ExtLeaf::Base(b)) => base_stack.push(b),
            SymbolicExpr::Leaf(ExtLeaf::ExtConstant(_)) => {}
            SymbolicExpr::Add { x, y, .. }
            | SymbolicExpr::Sub { x, y, .. }
            | SymbolicExpr::Mul { x, y, .. } => {
                ext_stack.push(x);
                ext_stack.push(y);
            }
            SymbolicExpr::Neg { x, .. } => ext_stack.push(x),
        }
    }
    while let Some(e) = base_stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        match e {
            SymbolicExpr::Leaf(BaseLeaf::Variable(SymbolicVariable {
                entry: BaseEntry::Periodic,
                ..
            })) => {
                found.insert("plonky3-periodic-column");
            }
            SymbolicExpr::Leaf(_) => {}
            SymbolicExpr::Add { x, y, .. }
            | SymbolicExpr::Sub { x, y, .. }
            | SymbolicExpr::Mul { x, y, .. } => {
                base_stack.push(x);
                base_stack.push(y);
            }
            SymbolicExpr::Neg { x, .. } => base_stack.push(x),
        }
    }
    found
}

/// Refusal precedence: the most specific unsupported surface first.
const UNSUPPORTED_ORDER: [&str; 5] = [
    "plonky3-permutation-column",
    "plonky3-permutation-challenge",
    "plonky3-permutation-value",
    "plonky3-periodic-column",
    "plonky3-extension-constraint",
];

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Key {
    Constant(u32),
    Input(usize),
    Add(usize, usize),
    Mul(usize, usize),
    Neg(usize),
}

/// Iterative lowering with structural hash-consing. Upstream `Arc` sharing is
/// followed by address, so shared subtrees are lowered once; structurally
/// equal subtrees with the same origin become one arena node.
struct Lowering {
    nodes: Vec<Node>,
    origins: Vec<Origin>,
    depths: Vec<u32>,
    keys: HashMap<(Origin, Key), usize>,
    slots: Vec<Slot>,
    slot_ids: HashMap<Slot, usize>,
    memo: HashMap<*const Base, usize>,
    visits: usize,
}

impl Lowering {
    fn new() -> Self {
        Self {
            nodes: vec![],
            origins: vec![],
            depths: vec![],
            keys: HashMap::new(),
            slots: vec![],
            slot_ids: HashMap::new(),
            memo: HashMap::new(),
            visits: 0,
        }
    }

    fn node(&mut self, origin: Origin, key: Key) -> Result<usize> {
        if let Some(i) = self.keys.get(&(origin, key)) {
            return Ok(*i);
        }
        let (node, depth) = match key {
            Key::Constant(c) => (Node::Constant(c), 1),
            Key::Input(s) => (Node::Input(s), 1),
            Key::Add(a, b) => (Node::Add(a, b), self.depths[a].max(self.depths[b]) + 1),
            Key::Mul(a, b) => (Node::Mul(a, b), self.depths[a].max(self.depths[b]) + 1),
            Key::Neg(a) => (Node::Neg(a), self.depths[a] + 1),
        };
        ensure(self.nodes.len() < NODE_LIMIT, "plonky3-arena-limit", || {
            format!("more than {NODE_LIMIT} nodes")
        })?;
        ensure(depth <= DEPTH_LIMIT, "plonky3-arena-limit", || {
            format!("depth above {DEPTH_LIMIT}")
        })?;
        self.nodes.push(node);
        self.origins.push(origin);
        self.depths.push(depth);
        self.keys.insert((origin, key), self.nodes.len() - 1);
        Ok(self.nodes.len() - 1)
    }

    fn leaf(&mut self, leaf: &BaseLeaf<F>) -> Result<usize> {
        let slot = match leaf {
            BaseLeaf::Constant(c) => {
                return self.node(Origin::Leaf, Key::Constant(c.as_canonical_u32()));
            }
            BaseLeaf::IsFirstRow => Slot::Selector(SelectorKind::FirstRow),
            BaseLeaf::IsLastRow => Slot::Selector(SelectorKind::LastRow),
            BaseLeaf::IsTransition => Slot::Selector(SelectorKind::Transition),
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset } if offset <= 1 => Slot::Main {
                    offset,
                    column: v.index,
                },
                BaseEntry::Preprocessed { offset } if offset <= 1 => Slot::Preprocessed {
                    offset,
                    column: v.index,
                },
                BaseEntry::Public => Slot::Public(v.index),
                BaseEntry::Periodic => {
                    return refuse("plonky3-periodic-column", "periodic column read");
                }
                entry => {
                    return refuse(
                        "plonky3-window",
                        format!("unsupported window entry {entry:?}"),
                    );
                }
            },
        };
        let next = self.slots.len();
        let id = *self.slot_ids.entry(slot).or_insert(next);
        if id == next {
            self.slots.push(slot);
        }
        self.node(Origin::Leaf, Key::Input(id))
    }

    fn lower(&mut self, root: &Base) -> Result<usize> {
        let mut stack: Vec<(&Base, bool)> = vec![(root, false)];
        while let Some((e, expanded)) = stack.pop() {
            let address = e as *const Base;
            if self.memo.contains_key(&address) {
                continue;
            }
            self.visits += 1;
            ensure(self.visits <= VISIT_LIMIT, "plonky3-capture-limit", || {
                format!("more than {VISIT_LIMIT} upstream nodes")
            })?;
            let index = match e {
                SymbolicExpr::Leaf(leaf) => self.leaf(leaf)?,
                SymbolicExpr::Add { x, y, .. }
                | SymbolicExpr::Sub { x, y, .. }
                | SymbolicExpr::Mul { x, y, .. }
                    if !expanded =>
                {
                    stack.push((e, true));
                    stack.push((y, false));
                    stack.push((x, false));
                    continue;
                }
                SymbolicExpr::Neg { x, .. } if !expanded => {
                    stack.push((e, true));
                    stack.push((x, false));
                    continue;
                }
                SymbolicExpr::Add { x, y, .. } => {
                    let (a, b) = (self.memo[&Arc::as_ptr(x)], self.memo[&Arc::as_ptr(y)]);
                    self.node(Origin::Add, Key::Add(a, b))?
                }
                SymbolicExpr::Sub { x, y, .. } => {
                    let (a, b) = (self.memo[&Arc::as_ptr(x)], self.memo[&Arc::as_ptr(y)]);
                    let negation = self.node(Origin::SubNegation, Key::Neg(b))?;
                    self.node(Origin::Sub, Key::Add(a, negation))?
                }
                SymbolicExpr::Mul { x, y, .. } => {
                    let (a, b) = (self.memo[&Arc::as_ptr(x)], self.memo[&Arc::as_ptr(y)]);
                    self.node(Origin::Mul, Key::Mul(a, b))?
                }
                SymbolicExpr::Neg { x, .. } => {
                    let a = self.memo[&Arc::as_ptr(x)];
                    self.node(Origin::Neg, Key::Neg(a))?
                }
            };
            self.memo.insert(address, index);
        }
        Ok(self.memo[&(root as *const Base)])
    }

    /// Renumber inputs into canonical slot order.
    fn finish(mut self, outputs: Vec<usize>) -> (Vec<Node>, Vec<Origin>, Vec<Slot>, Vec<usize>) {
        let mut order: Vec<usize> = (0..self.slots.len()).collect();
        order.sort_by_key(|i| self.slots[*i]);
        let mut renumber = vec![0; order.len()];
        for (new, old) in order.iter().enumerate() {
            renumber[*old] = new;
        }
        for node in &mut self.nodes {
            if let Node::Input(s) = node {
                *s = renumber[*s];
            }
        }
        let slots = order.iter().map(|i| self.slots[*i]).collect();
        (self.nodes, self.origins, slots, outputs)
    }
}

fn lower(constraints: &[Base]) -> Result<(Arena, Vec<Origin>, Vec<Slot>)> {
    let mut lowering = Lowering::new();
    let mut outputs = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        outputs.push(lowering.lower(constraint)?);
    }
    let (nodes, origins, slots, outputs) = lowering.finish(outputs);
    let arena = Arena::new(slots.len(), nodes, outputs)?;
    Ok((arena, origins, slots))
}

/// Capture, lower and check one AIR. `name` is the caller's stable identifier
/// of the selected source; the exporter does not derive it from Rust types.
pub fn export<A>(air: &A, name: &str) -> Result<Export>
where
    A: Air<SymbolicAirBuilder<F>>,
{
    let (layout, count_hint, degree_hint) = metadata(air)?;
    let primary = AirLayout {
        preprocessed_width: layout.preprocessed.as_ref().map_or(0, |p| p.width),
        main_width: layout.main_width,
        num_public_values: layout.public_values,
        ..AirLayout::default()
    };
    let probe = AirLayout {
        permutation_width: PROBE_WIDTH,
        num_permutation_challenges: PROBE_WIDTH,
        num_permutation_values: PROBE_WIDTH,
        num_periodic_columns: PROBE_WIDTH,
        ..primary
    };
    let (probe_base, probe_extension) = record(air, probe)?;
    let found = unsupported(&probe_base, &probe_extension);
    if let Some(id) = UNSUPPORTED_ORDER.into_iter().find(|id| found.contains(id)) {
        return refuse(
            id,
            format!(
                "unsupported upstream features: {}",
                found.into_iter().collect::<Vec<_>>().join(", ")
            ),
        );
    }
    let (base, extension) = record(air, primary)?;
    ensure(extension.is_empty(), "plonky3-extension-constraint", || {
        "extension constraint without probe surfaces".into()
    })?;
    let (repeat, _) = record(air, primary)?;
    let lowered = lower(&base)?;
    ensure(
        lower(&repeat)? == lowered,
        "plonky3-nondeterministic-eval",
        || "two evaluations with the same layout asserted different constraints".into(),
    )?;
    ensure(
        lower(&probe_base)? == lowered,
        "plonky3-probe-dependent-eval",
        || "constraints change when unsupported surfaces are present".into(),
    )?;
    let (arena, origins, slots) = lowered;

    let weights: Vec<u64> = slots.iter().map(degree_multiple_weight).collect();
    let degrees = arena.degrees(&weights)?;
    for (position, constraint) in base.iter().enumerate() {
        let degree = degrees[arena.outputs()[position]];
        ensure(
            degree == constraint.degree_multiple() as u64,
            "plonky3-degree-mismatch",
            || {
                format!(
                    "constraint {position}: arena degree {degree}, upstream {}",
                    constraint.degree_multiple()
                )
            },
        )?;
    }
    if let Some(count) = count_hint {
        ensure(count == base.len(), "plonky3-constraint-count-hint", || {
            format!(
                "num_constraints() is {count}, evaluation asserted {}",
                base.len()
            )
        })?;
    }
    let maximum = base.iter().map(|c| c.degree_multiple()).max().unwrap_or(0);
    if let Some(hint) = degree_hint {
        ensure(hint >= maximum, "plonky3-degree-hint", || {
            format!("max_constraint_degree() is {hint}, evaluation reached {maximum}")
        })?;
    }
    let selectors = check_guards(&arena, &slots)?;
    let assertions = selectors
        .into_iter()
        .enumerate()
        .map(|(position, selectors)| Assertion {
            constraint: position,
            degree_multiple: degrees[arena.outputs()[position]],
            selectors,
        })
        .collect();
    let features = features(&arena, &slots, &origins);
    let export = Export {
        air: name.to_string(),
        layout,
        arena,
        slots,
        origins,
        assertions,
        features,
    };
    export.validate()?;
    Ok(export)
}

/// Rebuild upstream expressions from an export, sharing each arena node.
pub fn reconstruct(export: &Export) -> Vec<Base> {
    let mut built: Vec<Arc<Base>> = Vec::with_capacity(export.arena.nodes().len());
    let leaf = |slot: Slot| {
        SymbolicExpr::Leaf(match slot {
            Slot::Main { offset, column } => {
                BaseLeaf::Variable(SymbolicVariable::new(BaseEntry::Main { offset }, column))
            }
            Slot::Preprocessed { offset, column } => BaseLeaf::Variable(SymbolicVariable::new(
                BaseEntry::Preprocessed { offset },
                column,
            )),
            Slot::Public(i) => BaseLeaf::Variable(SymbolicVariable::new(BaseEntry::Public, i)),
            Slot::Selector(SelectorKind::FirstRow) => BaseLeaf::IsFirstRow,
            Slot::Selector(SelectorKind::LastRow) => BaseLeaf::IsLastRow,
            Slot::Selector(SelectorKind::Transition) => BaseLeaf::IsTransition,
        })
    };
    for (node, origin) in export.arena.nodes().iter().zip(&export.origins) {
        let degree = |e: &Arc<Base>| e.degree_multiple();
        let expression = match (*node, origin) {
            (Node::Constant(c), _) => SymbolicExpr::Leaf(BaseLeaf::Constant(F::new(c))),
            (Node::Input(s), _) => leaf(export.slots[s]),
            (Node::Add(a, b), Origin::Sub) => {
                // The right operand is the subtraction negation of the subtrahend.
                let SymbolicExpr::Neg { x, .. } = built[b].as_ref() else {
                    unreachable!("validated node map")
                };
                let (x, y) = (built[a].clone(), x.clone());
                let degree_multiple = degree(&x).max(degree(&y));
                SymbolicExpr::Sub {
                    x,
                    y,
                    degree_multiple,
                }
            }
            (Node::Add(a, b), _) => {
                let (x, y) = (built[a].clone(), built[b].clone());
                SymbolicExpr::Add {
                    degree_multiple: degree(&x).max(degree(&y)),
                    x,
                    y,
                }
            }
            (Node::Mul(a, b), _) => {
                let (x, y) = (built[a].clone(), built[b].clone());
                SymbolicExpr::Mul {
                    degree_multiple: degree(&x) + degree(&y),
                    x,
                    y,
                }
            }
            (Node::Neg(a), _) => {
                let x = built[a].clone();
                SymbolicExpr::Neg {
                    degree_multiple: degree(&x),
                    x,
                }
            }
        };
        built.push(Arc::new(expression));
    }
    export
        .arena
        .outputs()
        .iter()
        .map(|o| built[*o].as_ref().clone())
        .collect()
}

/// Structural equality of upstream expressions, including cached degrees.
pub fn same_expression(a: &Base, b: &Base) -> bool {
    let mut seen: std::collections::HashSet<(*const Base, *const Base)> = Default::default();
    let mut stack = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        if !seen.insert((a, b)) {
            continue;
        }
        if a.degree_multiple() != b.degree_multiple() {
            return false;
        }
        match (a, b) {
            (SymbolicExpr::Leaf(x), SymbolicExpr::Leaf(y)) => {
                let same = match (x, y) {
                    (BaseLeaf::Variable(u), BaseLeaf::Variable(v)) => {
                        u.entry == v.entry && u.index == v.index
                    }
                    (BaseLeaf::Constant(u), BaseLeaf::Constant(v)) => u == v,
                    (BaseLeaf::IsFirstRow, BaseLeaf::IsFirstRow)
                    | (BaseLeaf::IsLastRow, BaseLeaf::IsLastRow)
                    | (BaseLeaf::IsTransition, BaseLeaf::IsTransition) => true,
                    _ => false,
                };
                if !same {
                    return false;
                }
            }
            (SymbolicExpr::Add { x, y, .. }, SymbolicExpr::Add { x: u, y: v, .. })
            | (SymbolicExpr::Sub { x, y, .. }, SymbolicExpr::Sub { x: u, y: v, .. })
            | (SymbolicExpr::Mul { x, y, .. }, SymbolicExpr::Mul { x: u, y: v, .. }) => {
                stack.push((x, u));
                stack.push((y, v));
            }
            (SymbolicExpr::Neg { x, .. }, SymbolicExpr::Neg { x: u, .. }) => stack.push((x, u)),
            _ => return false,
        }
    }
    true
}

/// The pinned upstream base constraints of an AIR, for comparison.
pub fn upstream_constraints<A: Air<SymbolicAirBuilder<F>>>(air: &A) -> Result<Vec<Base>> {
    let (layout, _, _) = metadata(air)?;
    let (base, _) = record(
        air,
        AirLayout {
            preprocessed_width: layout.preprocessed.as_ref().map_or(0, |p| p.width),
            main_width: layout.main_width,
            num_public_values: layout.public_values,
            ..AirLayout::default()
        },
    )?;
    Ok(base)
}
