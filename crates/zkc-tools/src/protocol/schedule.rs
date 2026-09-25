use serde_json::Value;
use std::{collections::BTreeMap, sync::Arc};
use zkc_runtime::interactive::{Admitted, Origin, PathElement};

type Result<T> = std::result::Result<T, String>;
/// The cursor budget ran out. Like a role's iteration budget this is a
/// cumulative resource, so the driver reports it as an exhausted execution.
pub(crate) const WORK_LIMIT: &str = "source-schedule-work-limit";
fn array(value: &Value) -> Result<&[Value]> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or("source-array".into())
}
fn text(value: &Value) -> Result<&str> {
    value.as_str().ok_or("source-string".into())
}
fn at(value: &Value, i: usize) -> Result<&Value> {
    value.get(i).ok_or("source-record".into())
}
fn name(value: &Value, i: usize) -> Result<String> {
    Ok(text(at(value, i)?)?.to_owned())
}
fn pairs(value: &Value) -> Result<BTreeMap<String, String>> {
    array(value)?
        .iter()
        .map(|p| Ok((name(p, 0)?, name(p, 1)?)))
        .collect()
}

/// Observable cut selected by the actual common source, including its origin.
/// Calls and fixed public loops remain shared definitions and bounded cursors.
#[derive(Clone, Debug)]
pub enum ScheduledAction {
    Local {
        origin: Origin,
        site: String,
        role: String,
        function: String,
    },
    Message {
        origin: Origin,
        site: String,
        schema: String,
        sender: String,
        receiver: String,
    },
    Stop {
        origin: Origin,
        site: String,
        role: String,
        reason: String,
    },
}
struct Instance {
    protocol: String,
    parameters: BTreeMap<String, Value>,
    dependencies: BTreeMap<String, String>,
    roles: BTreeMap<String, String>,
}
struct Cursor {
    body: Arc<[Value]>,
    pc: usize,
    origin: Origin,
    // The final path element belongs to this loop and is advanced in place.
    repeat: u64,
}
type CallMappings = BTreeMap<(String, String, String), (String, String)>;
/// Source-cut policy available only for an artifact with checked source custody.
/// It does not implement protocol arithmetic or infer communication from readiness.
pub struct Schedule {
    protocols: BTreeMap<String, Value>,
    instances: BTreeMap<String, Instance>,
    root: Origin,
    cursors: Vec<Cursor>,
    remaining_work: u64,
    call_mappings: Option<CallMappings>,
}
impl Schedule {
    pub fn new(admitted: &Admitted, entry: &str, session: &str) -> Result<Self> {
        let bytes = admitted
            .checked_source()
            .ok_or("schedule-requires-checked-source")?;
        let source: Value = serde_json::from_slice(bytes).map_err(|_| "source-json")?;
        let source = if source.get(0).and_then(Value::as_str) == Some("zkc.library/1") {
            at(&source, 3)?
        } else {
            &source
        };
        let mut protocols = BTreeMap::new();
        for p in array(at(source, 3)?)? {
            protocols.insert(name(p, 1)?, p.clone());
        }
        let mut instances = BTreeMap::new();
        for i in array(at(source, 4)?)? {
            instances.insert(
                name(i, 1)?,
                Instance {
                    protocol: name(i, 2)?,
                    parameters: array(at(i, 3)?)?
                        .iter()
                        .map(|p| Ok((name(p, 0)?, at(p, 1)?.clone())))
                        .collect::<Result<_>>()?,
                    dependencies: pairs(at(i, 4)?)?,
                    roles: pairs(at(i, 5)?)?,
                },
            );
        }
        let selected = array(at(source, 5)?)?
            .iter()
            .find(|e| e.get(1).and_then(Value::as_str) == Some(entry))
            .ok_or("source-entry")?;
        let root = Origin {
            format: admitted.format(),
            session: session.to_owned(),
            entry: entry.to_owned(),
            instance: name(selected, 2)?,
            path: Vec::new(),
        };
        let mut result = Self {
            protocols,
            instances,
            root: root.clone(),
            cursors: Vec::new(),
            remaining_work: 1_000_000,
            call_mappings: admitted.source_map().map(|mapping| {
                mapping
                    .calls
                    .iter()
                    .map(|p| {
                        (
                            (p.instance.clone(), p.role.clone(), p.site.clone()),
                            (p.source_function.clone(), p.function.clone()),
                        )
                    })
                    .collect()
            }),
        };
        let body = result.body(&root.instance)?;
        result.cursors.push(Cursor {
            body,
            pc: 0,
            origin: root,
            repeat: 1,
        });
        Ok(result)
    }
    pub fn root(&self) -> &Origin {
        &self.root
    }
    pub fn format(&self) -> zkc_runtime::interactive::ArtifactFormat {
        self.root.format
    }
    /// Actual source port names, in each role's projected argument order.
    pub fn inputs(&self) -> Result<BTreeMap<String, Vec<(String, String)>>> {
        let instance = self.instance(&self.root.instance)?;
        let protocol = self
            .protocols
            .get(&instance.protocol)
            .ok_or("source-protocol")?;
        let mut result: BTreeMap<String, Vec<(String, String)>> = instance
            .roles
            .values()
            .map(|r| (r.clone(), Vec::new()))
            .collect();
        for p in array(at(protocol, 4)?)? {
            let role = self.role(&self.root.instance, text(at(p, 1)?)?)?;
            result
                .get_mut(&role)
                .ok_or("source-role")?
                .push((name(p, 0)?, name(p, 2)?));
        }
        Ok(result)
    }
    fn instance(&self, name: &str) -> Result<&Instance> {
        self.instances.get(name).ok_or("source-instance".into())
    }
    fn role(&self, instance: &str, role: &str) -> Result<String> {
        self.instance(instance)?
            .roles
            .get(role)
            .cloned()
            .ok_or("source-role".into())
    }
    fn body(&self, instance: &str) -> Result<Arc<[Value]>> {
        let p = self
            .protocols
            .get(&self.instance(instance)?.protocol)
            .ok_or("source-protocol")?;
        Ok(array(at(p, 7)?)?.to_vec().into())
    }
    /// The joint driver checks agreement after independent role ingress. This is
    /// an explicit driver precondition, not a communication/agreement theorem.
    pub fn bind_family(
        &mut self,
        selected: &BTreeMap<String, BTreeMap<String, u64>>,
    ) -> Result<()> {
        let instance = self
            .instances
            .get_mut(&self.root.instance)
            .ok_or("source-instance")?;
        for (name, binding) in &mut instance.parameters {
            if binding.is_array() {
                let mut count = None;
                for role in instance.roles.values() {
                    let actual = *selected
                        .get(role)
                        .and_then(|p| p.get(name))
                        .ok_or("interactive-family-unbound")?;
                    if count.is_some_and(|old| old != actual) {
                        return Err("interactive-family-disagreement".into());
                    }
                    count = Some(actual);
                }
                *binding = Value::String(count.ok_or("interactive-family-roles")?.to_string());
            }
        }
        Ok(())
    }

    pub fn next_action(&mut self) -> Result<Option<ScheduledAction>> {
        loop {
            if self.cursors.is_empty() {
                return Ok(None);
            }
            if self.remaining_work == 0 {
                return Err(WORK_LIMIT.into());
            }
            self.remaining_work -= 1;
            let current = self.cursors.last_mut().ok_or("source-cursor")?;
            if current.pc == current.body.len() {
                if current.repeat > 1 {
                    current.repeat -= 1;
                    current.pc = 0;
                    match current.origin.path.last_mut() {
                        Some(PathElement::Loop { iteration, .. }) => *iteration += 1,
                        _ => return Err("source-loop-cursor".into()),
                    }
                } else {
                    self.cursors.pop();
                }
                continue;
            }
            let instruction = current.body[current.pc].clone();
            current.pc += 1;
            let origin = current.origin.clone();
            match text(at(&instruction, 0)?)? {
                "local" => {
                    let role = self.role(&origin.instance, text(at(&instruction, 2)?)?)?;
                    let site = name(&instruction, 1)?;
                    let source_function = name(&instruction, 3)?;
                    let function = if let Some(mappings) = &self.call_mappings {
                        let (expected, target) = mappings
                            .get(&(origin.instance.clone(), role.clone(), site.clone()))
                            .ok_or("source-call-map")?;
                        if expected != &source_function {
                            return Err("source-call-map-origin".into());
                        }
                        target.clone()
                    } else {
                        source_function
                    };
                    return Ok(Some(ScheduledAction::Local {
                        role,
                        origin,
                        site,
                        function,
                    }));
                }
                "message" => {
                    return Ok(Some(ScheduledAction::Message {
                        sender: self.role(&origin.instance, text(at(&instruction, 3)?)?)?,
                        receiver: self.role(&origin.instance, text(at(&instruction, 4)?)?)?,
                        origin,
                        site: name(&instruction, 1)?,
                        schema: name(&instruction, 2)?,
                    }));
                }
                "stop" => {
                    self.cursors.clear();
                    return Ok(Some(ScheduledAction::Stop {
                        role: self.role(&origin.instance, text(at(&instruction, 2)?)?)?,
                        origin,
                        site: name(&instruction, 1)?,
                        reason: name(&instruction, 3)?,
                    }));
                }
                "call" => {
                    let site = name(&instruction, 1)?;
                    let child = self
                        .instance(&origin.instance)?
                        .dependencies
                        .get(text(at(&instruction, 2)?)?)
                        .cloned()
                        .ok_or("source-dependency")?;
                    let mut nested = origin;
                    nested.path.push(PathElement::Call {
                        site,
                        instance: child.clone(),
                    });
                    nested.instance = child.clone();
                    let body = self.body(&child)?;
                    self.cursors.push(Cursor {
                        body,
                        pc: 0,
                        origin: nested,
                        repeat: 1,
                    });
                }
                "loop" => {
                    let count = at(&instruction, 2)?;
                    let value = match text(at(count, 0)?)? {
                        "constant" => text(at(count, 1)?)?,
                        "parameter" => self
                            .instance(&origin.instance)?
                            .parameters
                            .get(text(at(count, 1)?)?)
                            .ok_or("source-parameter")?
                            .as_str()
                            .ok_or("interactive-family-unbound")?,
                        _ => return Err("source-loop-count".into()),
                    }
                    .parse::<u64>()
                    .map_err(|_| "source-natural")?;
                    if value > 0 {
                        let mut nested = origin;
                        nested.path.push(PathElement::Loop {
                            site: name(&instruction, 1)?,
                            iteration: 0,
                        });
                        self.cursors.push(Cursor {
                            body: array(at(&instruction, 5)?)?.to_vec().into(),
                            pc: 0,
                            origin: nested,
                            repeat: value,
                        });
                    }
                }
                "return" | "yield" => {
                    if let Some(current) = self.cursors.last_mut() {
                        current.pc = current.body.len();
                    }
                }
                _ => return Err("source-instruction".into()),
            }
            if self.cursors.len() > 64 {
                return Err("source-schedule-depth-limit".into());
            }
        }
    }
}
