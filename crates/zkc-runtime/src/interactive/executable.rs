//! Positional local code derived only after structural admission.
//!
//! This is an internal execution layout, not another artifact or protocol IR.
//! Source names remain in frame ports and diagnostics; operand lookup and region
//! input types are resolved once. Every source instruction keeps its boundary.
//! Structural admission establishes unique definitions, exact arm order, and
//! joined result types before this lowering runs. Types share their admitted Arc
//! descriptors; match arms share captures. Stored metadata is linear in admitted
//! source records/ports/operands, all bounded by the existing decoder ceilings.
use super::{FrameInputs, OperationBinding, PhysicalType, ResolvedBinding, model::*};
use std::{
    collections::BTreeMap,
    sync::{Arc, LazyLock},
};

pub(super) static BOOL_TYPE: LazyLock<PhysicalType> =
    LazyLock::new(|| PhysicalType::parse("bool@native.bool/0").expect("installed Boolean type"));
pub(super) static INDEX_TYPE: LazyLock<PhysicalType> =
    LazyLock::new(|| PhysicalType::parse("index@native.index/0").expect("installed index type"));

pub(super) type Slot = usize;

#[derive(Debug)]
pub(super) struct Executable {
    pub functions: BTreeMap<String, Arc<Function>>,
    pub bindings: Vec<Arc<ResolvedBinding>>,
    pub calls: usize,
    pub requires_boolean_literals: bool,
}
#[derive(Debug)]
pub(super) struct Function {
    pub origin: super::LogicalOrigin,
    pub body: Arc<LocalCode>,
}
#[derive(Debug)]
pub(super) struct Binding {
    pub index: usize,
    declaration: Arc<ResolvedBinding>,
}
impl std::ops::Deref for Binding {
    type Target = ResolvedBinding;
    fn deref(&self) -> &Self::Target {
        &self.declaration
    }
}
#[derive(Default)]
struct Preparation {
    indices: BTreeMap<OperationBinding, usize>,
    bindings: Vec<Arc<ResolvedBinding>>,
    requires_boolean_literals: bool,
    calls: usize,
}
impl Preparation {
    fn binding(&mut self, binding: &Arc<ResolvedBinding>) -> Binding {
        // ResolvedBinding::explicit derives all facts from this full declaration;
        // neither carrier text nor a caller can supply an independent signature.
        let index = *self
            .indices
            .entry(binding.declaration().clone())
            .or_insert_with(|| {
                let index = self.bindings.len();
                self.bindings.push(binding.clone());
                index
            });
        Binding {
            index,
            declaration: self.bindings[index].clone(),
        }
    }
}

#[derive(Debug)]
pub(super) struct LocalCode {
    pub inputs: FrameInputs,
    pub instructions: Vec<Operation>,
}
#[derive(Debug)]
pub(super) struct Arm {
    pub alternative: String,
    pub body: Arc<LocalCode>,
}
#[derive(Debug)]
pub(super) enum Operation {
    BoolConstant {
        site: String,
        output: Slot,
        value: bool,
    },
    Variant {
        site: String,
        ty: PhysicalType,
        alternative: usize,
        payload: Vec<Slot>,
        output: Slot,
    },
    Match {
        site: String,
        input: Slot,
        captures: Vec<Slot>,
        arms: Vec<Arm>,
        outputs: Vec<Slot>,
    },
    Stop {
        site: String,
        reason: String,
    },
    Conditional {
        site: String,
        condition: Slot,
        captures: Vec<Slot>,
        then_body: Arc<LocalCode>,
        else_body: Arc<LocalCode>,
        outputs: Vec<Slot>,
    },
    For {
        conditional: bool,
        site: String,
        lower: Slot,
        upper: Slot,
        carried: Vec<Slot>,
        captures: Vec<Slot>,
        body: Arc<LocalCode>,
        outputs: Vec<Slot>,
    },
    Yield(Vec<Slot>),
    Release(Vec<Slot>),
    Op {
        call: usize,
        site: String,
        binding: Binding,
        attributes: Vec<String>,
        inputs: Vec<Slot>,
        outputs: Vec<Slot>,
    },
    Return(Vec<Slot>),
}

struct Environment {
    values: BTreeMap<String, (Slot, PhysicalType)>,
}
impl Environment {
    fn new(ports: &FrameInputs) -> Self {
        Self {
            values: ports
                .iter()
                .enumerate()
                .map(|(i, (n, t))| (n.clone(), (i, t.clone())))
                .collect(),
        }
    }
    fn slot(&self, name: &str) -> Slot {
        self.values[name].0
    }
    fn slots(&self, names: &[String]) -> Vec<Slot> {
        names.iter().map(|n| self.slot(n)).collect()
    }
    fn ty(&self, name: &str) -> PhysicalType {
        self.values[name].1.clone()
    }
    fn ports(&self, names: &[String]) -> Ports {
        names.iter().map(|n| (n.clone(), self.ty(n))).collect()
    }
    fn define(&mut self, name: &str, ty: PhysicalType) -> Slot {
        let slot = self.values.len();
        assert!(
            self.values.insert(name.to_owned(), (slot, ty)).is_none(),
            "admitted SSA definition"
        );
        slot
    }
    fn outputs(&mut self, names: &[String], types: &[PhysicalType]) -> Vec<Slot> {
        assert_eq!(names.len(), types.len(), "admitted result arity");
        names
            .iter()
            .zip(types)
            .map(|(n, t)| self.define(n, t.clone()))
            .collect()
    }
}

pub(super) fn prepare(program: &Program) -> Executable {
    let mut preparation = Preparation::default();
    let functions = program
        .functions
        .iter()
        .map(|(name, f)| {
            (
                name.clone(),
                Arc::new(Function {
                    origin: f.origin.clone(),
                    body: preparation.region(&f.body, f.inputs.clone().into()).0,
                }),
            )
        })
        .collect();
    Executable {
        functions,
        bindings: preparation.bindings,
        calls: preparation.calls,
        requires_boolean_literals: preparation.requires_boolean_literals,
    }
}
impl Preparation {
    fn region(
        &mut self,
        body: &[LocalInstruction],
        ports: FrameInputs,
    ) -> (Arc<LocalCode>, Option<Vec<PhysicalType>>) {
        let mut env = Environment::new(&ports);
        let mut instructions = Vec::with_capacity(body.len());
        let mut results = None;
        for op in body {
            let prepared = match op {
                LocalInstruction::BoolConstant {
                    site,
                    output,
                    value,
                } => {
                    self.requires_boolean_literals = true;
                    Operation::BoolConstant {
                        site: site.clone(),
                        output: env.define(output, BOOL_TYPE.clone()),
                        value: *value,
                    }
                }
                LocalInstruction::Variant {
                    site,
                    ty,
                    alternative,
                    payload,
                    output,
                } => {
                    let alternative = ty
                        .logical()
                        .variant_descriptor()
                        .expect("admitted variant")
                        .alternatives()
                        .iter()
                        .position(|a| a.label() == alternative)
                        .expect("admitted alternative");
                    let payload = env.slots(payload);
                    Operation::Variant {
                        site: site.clone(),
                        ty: ty.clone(),
                        alternative,
                        payload,
                        output: env.define(output, ty.clone()),
                    }
                }
                LocalInstruction::Match {
                    site,
                    input,
                    captures,
                    arms,
                    outputs,
                } => {
                    let ty = env.ty(input);
                    let logical = ty.logical();
                    let descriptor = logical.variant_descriptor().expect("admitted variant");
                    let capture_ports: Arc<[_]> = env.ports(captures).into();
                    let mut types = None;
                    let arms: Vec<_> = arms
                        .iter()
                        .zip(descriptor.alternatives())
                        .map(|(arm, declaration)| {
                            let ports: Ports = arm
                                .payload
                                .iter()
                                .cloned()
                                .zip(declaration.payload().iter().cloned().map(|t| {
                                    PhysicalType::default_for(t).expect("admitted payload")
                                }))
                                .collect();
                            let ports = FrameInputs::with_captures(ports, capture_ports.clone());
                            let (body, outputs) = self.region(&arm.body, ports);
                            if types.is_none() {
                                types = outputs;
                            }
                            Arm {
                                alternative: arm.alternative.clone(),
                                body,
                            }
                        })
                        .collect();
                    let types = types.unwrap_or_default();
                    let input = env.slot(input);
                    let captures = env.slots(captures);
                    let outputs = env.outputs(outputs, &types);
                    Operation::Match {
                        site: site.clone(),
                        input,
                        captures,
                        arms,
                        outputs,
                    }
                }
                LocalInstruction::Stop { site, reason } => Operation::Stop {
                    site: site.clone(),
                    reason: reason.clone(),
                },
                LocalInstruction::Conditional {
                    site,
                    condition,
                    captures,
                    then_body,
                    else_body,
                    outputs,
                } => {
                    let ports: FrameInputs = env.ports(captures).into();
                    let (then_body, left) = self.region(then_body, ports.clone());
                    let (else_body, right) = self.region(else_body, ports);
                    let types = left.or(right).unwrap_or_default();
                    let condition = env.slot(condition);
                    let captures = env.slots(captures);
                    let outputs = env.outputs(outputs, &types);
                    Operation::Conditional {
                        site: site.clone(),
                        condition,
                        captures,
                        then_body,
                        else_body,
                        outputs,
                    }
                }
                LocalInstruction::For {
                    conditional,
                    site,
                    induction,
                    lower,
                    upper,
                    carried,
                    captures,
                    body,
                    outputs,
                } => {
                    let mut ports = vec![(induction.clone(), INDEX_TYPE.clone())];
                    let types: Vec<_> = carried.iter().map(|(_, n)| env.ty(n)).collect();
                    ports.extend(
                        carried
                            .iter()
                            .zip(&types)
                            .map(|((n, _), t)| (n.clone(), t.clone())),
                    );
                    ports.extend(env.ports(captures));
                    let (body, _) = self.region(body, ports.into());
                    let lower = env.slot(lower);
                    let upper = env.slot(upper);
                    let carried = carried.iter().map(|(_, n)| env.slot(n)).collect();
                    let captures = env.slots(captures);
                    let outputs = env.outputs(outputs, &types);
                    Operation::For {
                        conditional: *conditional,
                        site: site.clone(),
                        lower,
                        upper,
                        carried,
                        captures,
                        body,
                        outputs,
                    }
                }
                LocalInstruction::Op {
                    site,
                    binding,
                    attributes,
                    inputs,
                    outputs,
                } => {
                    let inputs = env.slots(inputs);
                    let outputs = env.outputs(outputs, &binding.signature().outputs);
                    let call = self.calls;
                    self.calls += 1;
                    Operation::Op {
                        call,
                        site: site.clone(),
                        binding: self.binding(binding),
                        attributes: attributes.clone(),
                        inputs,
                        outputs,
                    }
                }
                LocalInstruction::Release(names) => Operation::Release(env.slots(names)),
                LocalInstruction::Return(names) | LocalInstruction::Yield(names) => {
                    results = Some(names.iter().map(|n| env.ty(n)).collect());
                    let slots = env.slots(names);
                    if matches!(op, LocalInstruction::Return(_)) {
                        Operation::Return(slots)
                    } else {
                        Operation::Yield(slots)
                    }
                }
            };
            instructions.push(prepared);
        }
        (
            Arc::new(LocalCode {
                inputs: ports,
                instructions,
            }),
            results,
        )
    }
}
