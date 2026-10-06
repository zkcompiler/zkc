//! Immutable action layouts and observations for executable programs.
use super::{
    AdmissionError, Admitted, CutKind, EntryRole, ErrorCode, Origin, PhysicalType, Stop,
    model::{Body, Count, Instruction, Participant},
};
use std::collections::BTreeMap;

/// A descriptor of an existing admitted instruction, not an executable program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramAction {
    Local {
        site: String,
        function: String,
    },
    Query {
        site: String,
        port: String,
        method: String,
    },
    Send {
        site: String,
        schema: String,
        peer: String,
        ty: PhysicalType,
    },
    Receive {
        site: String,
        schema: String,
        peer: String,
        ty: PhysicalType,
    },
    Loop {
        site: String,
        maximum: u64,
        end: usize,
    },
    Yield {
        site: String,
    },
    ReturnIf {
        site: String,
    },
    Finish,
}
impl ProgramAction {
    pub fn kind(&self) -> Option<CutKind> {
        match self {
            Self::Local { .. } => Some(CutKind::Local),
            Self::Query { .. } => Some(CutKind::Query),
            Self::Send { .. } => Some(CutKind::Send),
            Self::Receive { .. } => Some(CutKind::Receive),
            Self::Loop { .. } | Self::Yield { .. } | Self::ReturnIf { .. } | Self::Finish => None,
        }
    }
    pub fn site(&self) -> Option<&str> {
        match self {
            Self::Local { site, .. }
            | Self::Query { site, .. }
            | Self::Send { site, .. }
            | Self::Receive { site, .. }
            | Self::Loop { site, .. }
            | Self::Yield { site }
            | Self::ReturnIf { site } => Some(site),
            Self::Finish => None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramRole {
    pub entry: EntryRole,
    /// Static preorder, including loop headers, body yields, and the final return.
    /// A loop body occurs once in this layout, independently of its runtime count.
    pub actions: Vec<ProgramAction>,
}

/// Borrowed coordinates exclude send payloads and query arguments.
#[derive(Clone, Copy, Debug)]
pub struct ProgramCut<'a> {
    pub origin: &'a Origin,
    pub role: &'a str,
    pub site: &'a str,
    pub kind: CutKind,
}
/// Inspection never prepares a cut or reads the live value environment.
#[derive(Debug)]
pub enum ProgramState<'a> {
    Unpolled {
        kind: Option<CutKind>,
        site: Option<&'a str>,
    },
    /// An unpolled loop yield, crossed only by the explicit control API.
    Yield,
    /// A conditional entry return, crossed only by the explicit control API.
    ReturnIf {
        site: &'a str,
    },
    Pending(ProgramCut<'a>),
    Returned,
    Stopped(&'a Stop),
}

impl Admitted {
    /// Inspect an admitted program entry. Role order is the candidate map's
    /// order, not the original source roster order. No correspondence is granted.
    pub fn program_entry(&self, entry: &str) -> Result<Vec<ProgramRole>, AdmissionError> {
        let refuse = |detail| AdmissionError::new(ErrorCode::Record, detail);
        if !self.format().is_program() {
            return Err(refuse("program-layout-format"));
        }
        let roles = self
            .entry(entry)
            .ok_or_else(|| refuse("program-layout-entry"))?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(roles.len())
            .map_err(|_| refuse("program-layout-allocation"))?;
        for role in roles {
            let participant = &self.program.participants[&role.participant];
            if !participant.parameters.is_empty() || !participant.families.is_empty() {
                return Err(refuse("program-layout-composition"));
            }
            let env: BTreeMap<_, _> = participant.inputs.iter().cloned().collect();
            let mut actions = Vec::new();
            actions
                .try_reserve_exact(participant.body.len())
                .map_err(|_| refuse("program-layout-allocation"))?;
            self.program_body(participant, &participant.body, env, None, &mut actions)?;
            result.push(ProgramRole {
                entry: role,
                actions,
            });
        }
        Ok(result)
    }
    fn program_body(
        &self,
        participant: &Participant,
        body: &Body,
        mut env: BTreeMap<String, PhysicalType>,
        loop_site: Option<&str>,
        actions: &mut Vec<ProgramAction>,
    ) -> Result<(), AdmissionError> {
        let refuse = |detail| AdmissionError::new(ErrorCode::Record, detail);
        for instruction in body.iter() {
            actions
                .try_reserve(1)
                .map_err(|_| refuse("program-layout-allocation"))?;
            let action = match instruction {
                Instruction::Local {
                    site,
                    function,
                    outputs,
                    ..
                } => {
                    let types = &self.program.functions[function].outputs;
                    env.extend(outputs.iter().cloned().zip(types.iter().cloned()));
                    ProgramAction::Local {
                        site: site.clone(),
                        function: function.clone(),
                    }
                }
                Instruction::Query {
                    site,
                    port,
                    method,
                    outputs,
                    ..
                } => {
                    let service = participant
                        .services
                        .iter()
                        .find(|p| &p.name == port)
                        .expect("admitted service port");
                    let signature = service
                        .contract
                        .signature(method)
                        .expect("admitted query method");
                    env.extend(outputs.iter().cloned().zip(signature.outputs));
                    ProgramAction::Query {
                        site: site.clone(),
                        port: port.clone(),
                        method: method.clone(),
                    }
                }
                Instruction::Send {
                    site,
                    schema,
                    peer,
                    input,
                } => ProgramAction::Send {
                    site: site.clone(),
                    schema: schema.clone(),
                    peer: peer.clone(),
                    ty: env.get(input).expect("admitted send operand").clone(),
                },
                Instruction::Receive {
                    site,
                    schema,
                    peer,
                    output,
                    ty,
                } => {
                    env.insert(output.clone(), ty.clone());
                    ProgramAction::Receive {
                        site: site.clone(),
                        schema: schema.clone(),
                        peer: peer.clone(),
                        ty: ty.clone(),
                    }
                }
                Instruction::Loop {
                    site,
                    count,
                    carried,
                    captures,
                    body,
                    outputs,
                } => {
                    let Count::Value {
                        value,
                        maximum,
                        induction,
                    } = count
                    else {
                        return Err(refuse("program-layout-loop-count"));
                    };
                    let start = actions.len();
                    actions.push(ProgramAction::Loop {
                        site: site.clone(),
                        maximum: *maximum,
                        end: 0,
                    });
                    let mut child = BTreeMap::new();
                    child.insert(induction.clone(), env[value].clone());
                    for (argument, initial) in carried {
                        child.insert(argument.clone(), env[initial].clone());
                    }
                    for name in captures {
                        child.insert(name.clone(), env[name].clone());
                    }
                    for ((_, initial), output) in carried.iter().zip(outputs) {
                        env.insert(output.clone(), env[initial].clone());
                    }
                    self.program_body(participant, body, child, Some(site), actions)?;
                    let end = actions.len() - 1;
                    actions[start] = ProgramAction::Loop {
                        site: site.clone(),
                        maximum: *maximum,
                        end,
                    };
                    continue;
                }
                Instruction::Yield(_) => ProgramAction::Yield {
                    site: loop_site
                        .ok_or_else(|| refuse("program-layout-yield"))?
                        .into(),
                },
                Instruction::ReturnIf {
                    site,
                    values,
                    continuations,
                    ..
                } => {
                    let types: Vec<_> = values
                        .iter()
                        .map(|name| env[name].clone())
                        .filter(PhysicalType::is_affine)
                        .collect();
                    env.extend(continuations.iter().cloned().zip(types));
                    ProgramAction::ReturnIf { site: site.clone() }
                }
                Instruction::Return(_) => ProgramAction::Finish,
                _ => return Err(refuse("program-layout-composition")),
            };
            actions.push(action);
        }
        Ok(())
    }
}
