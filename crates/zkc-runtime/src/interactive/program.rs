//! Immutable action layouts and observations for executable programs.
use super::{
    AdmissionError, Admitted, AttributeRule, CutKind, EntryRole, ErrorCode, Origin, PhysicalType,
    ResolvedBinding, Stop,
    model::{Body, Instruction, LocalInstruction, LoopCount, Participant},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

/// A static operation that names an immutable Host asset by content identity.
/// The binding is the admitted declaration and physical signature; the identity
/// is the operation's checked attribute. Nothing here says the asset exists.
#[derive(Clone, Debug)]
pub struct AssetReference {
    pub function: String,
    pub site: String,
    pub binding: Arc<ResolvedBinding>,
    pub identity: String,
}

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

fn called_functions(body: &Body, out: &mut BTreeSet<String>) {
    for instruction in body.iter() {
        match instruction {
            Instruction::Local { function, .. } => {
                out.insert(function.clone());
            }
            Instruction::Loop { body, .. } => called_functions(body, out),
            _ => {}
        }
    }
}

impl Admitted {
    /// Every asset-naming operation an entry can reach: its participants'
    /// bodies and nested loop bodies, each called function once, and every
    /// local region of those functions including branches that an execution
    /// may never choose. Admission already bounded the program, so this walk
    /// is bounded by the same limits. A function that no participant of this
    /// entry calls is not reported.
    pub fn asset_references(&self, entry: &str) -> Result<Vec<AssetReference>, AdmissionError> {
        let refuse = |detail| AdmissionError::new(ErrorCode::Record, detail);
        let roles = self
            .program
            .entries
            .get(entry)
            .ok_or_else(|| refuse("asset-references-entry"))?;
        let mut functions = BTreeSet::new();
        for symbol in roles.values() {
            called_functions(&self.program.participants[symbol].body, &mut functions);
        }
        let mut references = Vec::new();
        for name in functions {
            for instruction in LocalInstruction::walk(&self.program.functions[&name].body) {
                let LocalInstruction::Op {
                    site,
                    binding,
                    attributes,
                    ..
                } = instruction
                else {
                    continue;
                };
                if binding.signature().attributes != AttributeRule::AssetIdentity {
                    continue;
                }
                let [identity] = attributes.as_slice() else {
                    return Err(refuse("asset-references-attribute"));
                };
                references
                    .try_reserve(1)
                    .map_err(|_| refuse("asset-references-allocation"))?;
                references.push(AssetReference {
                    function: name.clone(),
                    site: site.clone(),
                    binding: binding.clone(),
                    identity: identity.clone(),
                });
            }
        }
        Ok(references)
    }
    /// Inspect an admitted program entry in its role map's canonical order.
    pub fn program_entry(&self, entry: &str) -> Result<Vec<ProgramRole>, AdmissionError> {
        let refuse = |detail| AdmissionError::new(ErrorCode::Record, detail);
        let roles = self
            .entry(entry)
            .ok_or_else(|| refuse("program-layout-entry"))?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(roles.len())
            .map_err(|_| refuse("program-layout-allocation"))?;
        for role in roles {
            let participant = &self.program.participants[&role.participant];
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
                    let LoopCount {
                        value,
                        maximum,
                        induction,
                    } = count;
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
            };
            actions.push(action);
        }
        Ok(())
    }
}
