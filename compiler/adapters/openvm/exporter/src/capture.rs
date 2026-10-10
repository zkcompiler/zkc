//! Capture of the pinned upstream relation: the source recorder, the
//! verifying key from upstream key generation, and the lowering of both into
//! the export model.
//!
//! Three upstream readings are taken and tied together:
//!
//! 1. The **source recorder** `SymbolicRapBuilder` runs the AIR's `eval` and
//!    records constraints in emission order and interactions in push order.
//! 2. **Key generation** `MultiStarkKeygenBuilder::generate_pk` builds the
//!    verifying key: per AIR the simplified, structurally shared DAG whose
//!    constraint positions are sorted and deduplicated node ids, the
//!    `need_rot`, `unused_variables` and degree facts, and globally the
//!    trace-height linear constraints and pre-hash.
//! 3. Upstream's own `SymbolicDagBuilder` is run over the recorder output to
//!    obtain the recorder-to-DAG node map, and the result is required to be
//!    the verifying key's DAG node for node.
//!
//! The bundle lowering starts from the recorder expressions. Every upstream
//! constraint `i` is substituted on the three row classes of the
//! row-indicator selector law with the DAG builder's folding rules; classes
//! whose substituted expressions coincide share one scoped assertion, and a
//! class on which the expression folds to the constant zero asserts nothing.
//! At height at least two this is exactly the row-by-row relation
//! `check_constraints` evaluates, including constraints that use a selector
//! as a value rather than a guard. Interactions apply on every row and must
//! not mention selectors.

use crate::arena::{Arena, Builder};
use crate::field::F;
use crate::model::{
    AirExport, Assertion, Bus, Dag, DagInteraction, DagNode, Export, Group, Height, Input,
    Interaction, LinearConstraint, RowClass, Scope, VariableKind,
};
use crate::reference::recorder;
use crate::refusal::{Refusal, Result, ensure, refuse};
use crate::slice::{AIR_NAMES, REQUIRED, Slice, column_names, trace_width};
use openvm_stark_backend::air_builders::symbolic::symbolic_expression::SymbolicExpression;
use openvm_stark_backend::air_builders::symbolic::symbolic_variable::{Entry, SymbolicVariable};
use openvm_stark_backend::air_builders::symbolic::{
    SymbolicConstraints, SymbolicConstraintsDag, SymbolicDagBuilder, SymbolicExpressionNode,
};
use openvm_stark_backend::keygen::MultiStarkKeygenBuilder;
use openvm_stark_backend::keygen::types::MultiStarkVerifyingKey;
use openvm_stark_backend::p3_air::BaseAir;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use std::collections::{BTreeMap, BTreeSet, HashMap};

pub const INSTANCE_HEIGHT_LIMIT: usize = 1 << 20;
pub const INSTANCE_HEIGHT_MINIMUM: usize = 2;

/// Everything captured from upstream for the slice, before lowering.
pub struct Capture {
    pub recorder: Vec<SymbolicConstraints<F>>,
    pub vk: MultiStarkVerifyingKey<crate::slice::SC>,
    /// DAG node of every recorder constraint, per AIR.
    pub constraint_nodes: Vec<Vec<usize>>,
}

fn entry_kind(entry: Entry) -> (VariableKind, usize, usize) {
    match entry {
        Entry::Main { part_index, offset } => (VariableKind::Main, part_index, offset),
        Entry::Preprocessed { offset } => (VariableKind::Preprocessed, 0, offset),
        Entry::Public => (VariableKind::Public, 0, 0),
        Entry::Challenge => (VariableKind::Challenge, 0, 0),
    }
}

fn dag_node(node: &SymbolicExpressionNode<F>) -> DagNode {
    match *node {
        SymbolicExpressionNode::Variable(v) => {
            let (kind, part, offset) = entry_kind(v.entry);
            DagNode::Variable {
                kind,
                part,
                offset,
                index: v.index,
            }
        }
        SymbolicExpressionNode::IsFirstRow => DagNode::IsFirstRow,
        SymbolicExpressionNode::IsLastRow => DagNode::IsLastRow,
        SymbolicExpressionNode::IsTransition => DagNode::IsTransition,
        SymbolicExpressionNode::Constant(c) => DagNode::Constant(c.as_canonical_u32()),
        SymbolicExpressionNode::Add {
            left_idx,
            right_idx,
            degree_multiple,
        } => DagNode::Add(left_idx, right_idx, degree_multiple),
        SymbolicExpressionNode::Sub {
            left_idx,
            right_idx,
            degree_multiple,
        } => DagNode::Sub(left_idx, right_idx, degree_multiple),
        SymbolicExpressionNode::Neg {
            idx,
            degree_multiple,
        } => DagNode::Neg(idx, degree_multiple),
        SymbolicExpressionNode::Mul {
            left_idx,
            right_idx,
            degree_multiple,
        } => DagNode::Mul(left_idx, right_idx, degree_multiple),
    }
}

/// Run the recorder and upstream key generation and tie them together.
pub fn capture(slice: &Slice) -> Result<Capture> {
    let mut recorders = vec![];
    for air in slice.airs() {
        ensure(
            BaseAir::<F>::preprocessed_trace(air.as_ref()).is_none(),
            "openvm-preprocessed-trace",
            || format!("{} has a preprocessed trace", air.name()),
        )?;
        recorders.push(recorder(air));
    }
    let mut keygen = MultiStarkKeygenBuilder::new(slice.config.clone());
    for (i, air) in slice.airs().iter().enumerate() {
        if REQUIRED[i] {
            keygen.add_required_air(air.clone());
        } else {
            keygen.add_air(air.clone());
        }
    }
    let vk = keygen
        .generate_pk()
        .map_err(|e| Refusal {
            id: "openvm-keygen",
            detail: e.to_string(),
        })?
        .get_vk();
    ensure(
        vk.inner.per_air.len() == slice.airs().len(),
        "openvm-keygen",
        || "verifying key AIR count".into(),
    )?;
    let mut constraint_nodes = vec![];
    for (i, constraints) in recorders.iter().enumerate() {
        let mut builder = SymbolicDagBuilder::new();
        let nodes: Vec<usize> = constraints
            .constraints
            .iter()
            .map(|e| builder.add_expr(e))
            .collect();
        let interactions: Vec<_> = constraints
            .interactions
            .iter()
            .map(|x| {
                let message: Vec<usize> = x.message.iter().map(|e| builder.add_expr(e)).collect();
                let count = builder.add_expr(&x.count);
                (x.bus_index, message, count, x.count_weight)
            })
            .collect();
        let mut sorted = nodes.clone();
        sorted.sort_unstable();
        sorted.dedup();
        let dag: &SymbolicConstraintsDag<F> = &vk.inner.per_air[i].symbolic_constraints;
        let same_interactions = dag.interactions.len() == interactions.len()
            && dag.interactions.iter().zip(&interactions).all(
                |(d, (bus, message, count, weight))| {
                    d.bus_index == *bus
                        && d.message == *message
                        && d.count == *count
                        && d.count_weight == *weight
                },
            );
        ensure(
            builder.nodes == dag.constraints.nodes
                && sorted == dag.constraints.constraint_idx
                && same_interactions,
            "openvm-vk-mismatch",
            || {
                format!(
                    "{}: recorder DAG differs from the verifying key",
                    AIR_NAMES[i]
                )
            },
        )?;
        let vparams = &vk.inner.per_air[i].params;
        let width = trace_width(&slice.airs()[i]);
        ensure(
            vparams.width.cached_mains == width.cached_mains
                && vparams.width.common_main == width.common_main
                && vparams.width.preprocessed.is_none()
                && vk.inner.per_air[i].preprocessed_data.is_none()
                && vk.inner.per_air[i].is_required == REQUIRED[i],
            "openvm-vk-mismatch",
            || format!("{}: verifying key layout", AIR_NAMES[i]),
        )?;
        constraint_nodes.push(nodes);
    }
    Ok(Capture {
        recorder: recorders,
        vk,
        constraint_nodes,
    })
}

/// Lowers one expression tree into the arena builder under a row class,
/// memoized by upstream `Arc` identity.
struct Lowering<'a> {
    builder: &'a mut Builder,
    slots: &'a BTreeMap<(VariableKind, usize, usize, usize), usize>,
    class: Option<RowClass>,
    memo: HashMap<*const SymbolicExpression<F>, usize>,
    used_selector: bool,
}

impl Lowering<'_> {
    fn lower(&mut self, e: &SymbolicExpression<F>) -> Result<usize> {
        let key = e as *const SymbolicExpression<F>;
        if let Some(&i) = self.memo.get(&key) {
            return Ok(i);
        }
        let selector = |this: &mut Self, value: bool| -> Result<usize> {
            this.used_selector = true;
            match this.class {
                Some(_) => Ok(this.builder.constant(if value { F::ONE } else { F::ZERO })),
                None => refuse(
                    "openvm-interaction-selector",
                    "interaction expression uses a row selector",
                ),
            }
        };
        let i = match e {
            SymbolicExpression::Variable(v) => {
                let (kind, part, offset) = entry_kind(v.entry);
                match kind {
                    VariableKind::Main | VariableKind::Public => {}
                    VariableKind::Preprocessed => {
                        return refuse("openvm-preprocessed-trace", "preprocessed variable");
                    }
                    VariableKind::Challenge => {
                        return refuse("openvm-challenge-variable", "challenge variable");
                    }
                }
                let slot = self.slots[&(kind, part, offset, v.index)];
                self.builder.input(slot)
            }
            SymbolicExpression::IsFirstRow => {
                let (f, _, _) = self
                    .class
                    .map_or((false, false, false), RowClass::selectors);
                selector(self, f)?
            }
            SymbolicExpression::IsLastRow => {
                let (_, l, _) = self
                    .class
                    .map_or((false, false, false), RowClass::selectors);
                selector(self, l)?
            }
            SymbolicExpression::IsTransition => {
                let (_, _, t) = self
                    .class
                    .map_or((false, false, false), RowClass::selectors);
                selector(self, t)?
            }
            SymbolicExpression::Constant(c) => self.builder.constant(*c),
            SymbolicExpression::Add { x, y, .. } => {
                let a = self.lower(x)?;
                let b = self.lower(y)?;
                self.builder.add(a, b)
            }
            SymbolicExpression::Sub { x, y, .. } => {
                let a = self.lower(x)?;
                let b = self.lower(y)?;
                self.builder.sub(a, b)
            }
            SymbolicExpression::Neg { x, .. } => {
                let a = self.lower(x)?;
                self.builder.neg(a)
            }
            SymbolicExpression::Mul { x, y, .. } => {
                let a = self.lower(x)?;
                let b = self.lower(y)?;
                self.builder.mul(a, b)
            }
        };
        self.memo.insert(key, i);
        Ok(i)
    }
}

fn variables(e: &SymbolicExpression<F>, out: &mut BTreeSet<(VariableKind, usize, usize, usize)>) {
    match e {
        SymbolicExpression::Variable(v) => {
            let (kind, part, offset) = entry_kind(v.entry);
            out.insert((kind, part, offset, v.index));
        }
        SymbolicExpression::Add { x, y, .. }
        | SymbolicExpression::Sub { x, y, .. }
        | SymbolicExpression::Mul { x, y, .. } => {
            variables(x, out);
            variables(y, out);
        }
        SymbolicExpression::Neg { x, .. } => variables(x, out),
        _ => {}
    }
}

/// Lower a capture into the export model.
pub fn export(slice: &Slice, capture: &Capture) -> Result<Export> {
    // Buses in slice order with a consistent message length each.
    let mut buses: Vec<Bus> = slice
        .buses()
        .iter()
        .map(|(name, index)| Bus {
            name: name.to_string(),
            index: *index,
            arity: 0,
        })
        .collect();
    for (i, constraints) in capture.recorder.iter().enumerate() {
        for x in &constraints.interactions {
            let Some(bus) = buses.iter_mut().find(|b| b.index == x.bus_index) else {
                return refuse(
                    "openvm-bus",
                    format!("{}: bus {} is not in the slice", AIR_NAMES[i], x.bus_index),
                );
            };
            if bus.arity == 0 {
                bus.arity = x.message.len();
            }
            ensure(
                bus.arity == x.message.len() && !x.message.is_empty(),
                "openvm-bus-arity",
                || {
                    format!(
                        "{}: bus {} carries messages of different lengths",
                        AIR_NAMES[i], x.bus_index
                    )
                },
            )?;
        }
    }
    ensure(buses.iter().all(|b| b.arity > 0), "openvm-bus", || {
        "a slice bus carries no interaction".into()
    })?;

    let mut publics = vec![];
    let mut public_base = vec![];
    for (i, air) in slice.airs().iter().enumerate() {
        let n = capture.vk.inner.per_air[i].params.num_public_values;
        public_base.push(publics.len());
        for k in 0..n {
            publics.push((format!("{}.public-{k}", AIR_NAMES[i]), i, k));
        }
        debug_assert_eq!(
            n,
            openvm_stark_backend::BaseAirWithPublicValues::<F>::num_public_values(air.as_ref())
        );
    }

    let mut airs = vec![];
    for (i, air) in slice.airs().iter().enumerate() {
        let constraints = &capture.recorder[i];
        let vk = &capture.vk.inner.per_air[i];
        let width = trace_width(air);
        let mut groups: Vec<Group> = width
            .cached_mains
            .iter()
            .enumerate()
            .map(|(p, w)| Group {
                name: format!("cached-{p}"),
                authority: "config",
                width: *w,
            })
            .collect();
        if width.common_main > 0 {
            groups.push(Group {
                name: "main".into(),
                authority: "witness",
                width: width.common_main,
            });
        }
        // Inputs: every variable the recorder mentions, sorted.
        let mut used = BTreeSet::new();
        for c in &constraints.constraints {
            variables(c, &mut used);
        }
        for x in &constraints.interactions {
            variables(&x.count, &mut used);
            for m in &x.message {
                variables(m, &mut used);
            }
        }
        let mut inputs = vec![];
        let mut slots = BTreeMap::new();
        for key @ (kind, part, offset, index) in used {
            let input = match kind {
                VariableKind::Main => {
                    ensure(
                        part < groups.len() && index < groups[part].width && offset <= 1,
                        "openvm-variable",
                        || {
                            format!(
                                "{}: variable part {part} column {index} offset {offset}",
                                AIR_NAMES[i]
                            )
                        },
                    )?;
                    Input::Read {
                        group: part,
                        offset,
                        column: index,
                    }
                }
                VariableKind::Public => {
                    ensure(
                        index < vk.params.num_public_values,
                        "openvm-variable",
                        || format!("{}: public value {index}", AIR_NAMES[i]),
                    )?;
                    Input::Public(public_base[i] + index)
                }
                VariableKind::Preprocessed => {
                    return refuse("openvm-preprocessed-trace", AIR_NAMES[i]);
                }
                VariableKind::Challenge => {
                    return refuse("openvm-challenge-variable", AIR_NAMES[i]);
                }
            };
            slots.insert(key, inputs.len());
            inputs.push(input);
        }
        let weights: Vec<u64> = inputs
            .iter()
            .map(|input| match input {
                Input::Read { .. } => 1,
                Input::Public(_) => 0,
            })
            .collect();

        let mut builder = Builder::new();
        let mut outputs: Vec<usize> = vec![];
        let mut assertions_raw: Vec<(usize, Scope, usize)> = vec![];
        let mut vacuous = vec![];
        for (c, expression) in constraints.constraints.iter().enumerate() {
            let mut per_class = [0usize; 3];
            for (k, class) in RowClass::ALL.iter().enumerate() {
                let mut lowering = Lowering {
                    builder: &mut builder,
                    slots: &slots,
                    class: Some(*class),
                    memo: HashMap::new(),
                    used_selector: false,
                };
                per_class[k] = lowering.lower(expression)?;
            }
            let [first, interior, last] = per_class;
            let groups_of_classes: Vec<(Scope, usize)> = if first == interior && interior == last {
                vec![(Scope::All, first)]
            } else if first == interior {
                vec![(Scope::Transition, first), (Scope::Last, last)]
            } else if interior == last {
                vec![(Scope::First, first), (Scope::Tail, interior)]
            } else {
                vec![
                    (Scope::First, first),
                    (Scope::Interior, interior),
                    (Scope::Last, last),
                ]
            };
            for (scope, node) in groups_of_classes {
                if builder.as_constant(node) == Some(F::ZERO) {
                    vacuous.extend(
                        RowClass::ALL
                            .into_iter()
                            .filter(|class| scope.covers(*class))
                            .map(|class| (c, class)),
                    );
                    continue;
                }
                assertions_raw.push((c, scope, node));
            }
        }
        let mut interactions_raw: Vec<(usize, Vec<usize>, usize, u32)> = vec![];
        for x in &constraints.interactions {
            let bus = buses
                .iter()
                .position(|b| b.index == x.bus_index)
                .expect("bus checked");
            let mut lowering = Lowering {
                builder: &mut builder,
                slots: &slots,
                class: None,
                memo: HashMap::new(),
                used_selector: false,
            };
            let message = x
                .message
                .iter()
                .map(|m| lowering.lower(m))
                .collect::<Result<Vec<_>>>()?;
            let count = lowering.lower(&x.count)?;
            interactions_raw.push((bus, message, count, x.count_weight));
        }
        // Outputs: assertion nodes, then interaction message and count nodes.
        for (_, _, node) in &assertions_raw {
            outputs.push(*node);
        }
        let mut interaction_positions = vec![];
        for (bus, message, count, weight) in &interactions_raw {
            let base = outputs.len();
            outputs.extend(message.iter().copied());
            outputs.push(*count);
            interaction_positions.push((
                *bus,
                (base..base + message.len()).collect::<Vec<_>>(),
                base + message.len(),
                *weight,
            ));
        }
        let (arena, _) = builder.finish(inputs.len(), &outputs)?;
        let degrees = arena.degrees(&weights)?;
        let output_degree = |position: usize| degrees[arena.outputs()[position]];
        let mut assertions = vec![];
        for (position, (c, scope, _)) in assertions_raw.iter().enumerate() {
            let degree = output_degree(position);
            let upstream = constraints.constraints[*c].degree_multiple() as u64;
            ensure(degree <= upstream, "openvm-degree", || {
                format!(
                    "{}: constraint {c} lowered degree {degree} exceeds upstream {upstream}",
                    AIR_NAMES[i]
                )
            })?;
            assertions.push(Assertion {
                constraint: *c,
                scope: *scope,
                output: position,
                degree,
            });
        }
        let mut interactions = vec![];
        for (k, (bus, message, count, weight)) in interaction_positions.into_iter().enumerate() {
            let degree = message
                .iter()
                .chain(std::iter::once(&count))
                .map(|p| output_degree(*p))
                .max()
                .unwrap_or(0);
            let upstream = constraints.interactions[k]
                .message
                .iter()
                .chain(std::iter::once(&constraints.interactions[k].count))
                .map(|e| e.degree_multiple())
                .max()
                .unwrap_or(0) as u64;
            ensure(degree <= upstream, "openvm-degree", || {
                format!(
                    "{}: interaction {k} lowered degree {degree} exceeds upstream {upstream}",
                    AIR_NAMES[i]
                )
            })?;
            interactions.push(Interaction {
                bus,
                message,
                count,
                count_weight: weight,
                degree,
            });
        }
        let max_lowered = assertions
            .iter()
            .map(|a| a.degree)
            .chain(interactions.iter().map(|x| x.degree))
            .max()
            .unwrap_or(0);
        ensure(
            max_lowered <= vk.max_constraint_degree as u64,
            "openvm-degree",
            || {
                format!(
                    "{}: lowered degree {max_lowered} exceeds the verifying key's",
                    AIR_NAMES[i]
                )
            },
        )?;

        let dag = &vk.symbolic_constraints;
        let height = if !width.cached_mains.is_empty() {
            Height::Config
        } else if i == crate::slice::CONNECTOR {
            Height::Fixed(2)
        } else if i == crate::slice::RANGE {
            Height::Fixed(slice.range_table_height())
        } else {
            Height::Instance
        };
        airs.push(AirExport {
            name: AIR_NAMES[i].to_string(),
            upstream_type: air.name(),
            required: REQUIRED[i],
            groups,
            num_public_values: vk.params.num_public_values,
            column_names: column_names(slice, i),
            need_rot: vk.params.need_rot,
            max_constraint_degree: vk.max_constraint_degree,
            unused_variables: vk
                .unused_variables
                .iter()
                .map(|v: &SymbolicVariable<F>| {
                    let (kind, part, offset) = entry_kind(v.entry);
                    (kind, part, offset, v.index)
                })
                .collect(),
            dag: Dag {
                nodes: dag.constraints.nodes.iter().map(dag_node).collect(),
                constraint_idx: dag.constraints.constraint_idx.clone(),
                interactions: dag
                    .interactions
                    .iter()
                    .map(|x| DagInteraction {
                        bus: x.bus_index,
                        message: x.message.clone(),
                        count: x.count,
                        count_weight: x.count_weight,
                    })
                    .collect(),
            },
            recorder_constraints: capture.constraint_nodes[i].clone(),
            recorder_degrees: constraints
                .constraints
                .iter()
                .map(|c| c.degree_multiple())
                .collect(),
            inputs,
            arena,
            assertions,
            vacuous,
            interactions,
            height,
        });
    }
    let params = &capture.vk.inner.params;
    Ok(Export {
        parameters: slice.parameters,
        buses,
        publics,
        airs,
        trace_height_constraints: capture
            .vk
            .inner
            .trace_height_constraints
            .iter()
            .map(|c| LinearConstraint {
                coefficients: c.coefficients.clone(),
                threshold: c.threshold,
            })
            .collect(),
        vk_pre_hash: capture
            .vk
            .pre_hash
            .iter()
            .map(|x| x.as_canonical_u32())
            .collect(),
        l_skip: params.l_skip,
        max_constraint_degree: params.max_constraint_degree,
        max_interaction_count: params.logup.max_interaction_count,
        log_max_message_length: params.logup.log_max_message_length,
    })
}

impl Export {
    /// Arena of one table, for consumers that evaluate the bundle semantics.
    pub fn arena(&self, air: usize) -> &Arena {
        &self.airs[air].arena
    }
}
