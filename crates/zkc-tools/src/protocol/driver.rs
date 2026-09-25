use super::{Schedule, ScheduledAction, schedule::WORK_LIMIT};
use std::collections::BTreeMap;
use zkc_runtime::interactive::{
    Action, Backend, BackendError, Cut, CutKind, Packet, Receive, Runner, Stop, StopKind,
};

/// Installed public codecs. Decoding uses the receiver's own key/setup policy.
pub trait WireBackend: Backend {
    fn encode(&self, value: &Self::Value) -> Result<Vec<u8>, BackendError>;
    fn decode(
        &self,
        ty: zkc_runtime::interactive::PhysicalType,
        bytes: &[u8],
    ) -> Result<Self::Value, BackendError>;
}
/// Trusted receiving policy, separate from the possibly hostile transport.
/// The driver supplies the receiver's checked cut after matching both envelopes.
pub trait MessageDecoder<B: WireBackend> {
    fn decode(
        &self,
        backend: &B,
        receive: &Receive,
        bytes: &[u8],
    ) -> Result<B::Value, BackendError>;
}
pub struct BackendDecoder;
impl<B: WireBackend> MessageDecoder<B> for BackendDecoder {
    fn decode(
        &self,
        backend: &B,
        receive: &Receive,
        bytes: &[u8],
    ) -> Result<B::Value, BackendError> {
        backend.decode(receive.ty.clone(), bytes)
    }
}
#[derive(Debug)]
pub enum JointOutcome<V> {
    Returned(BTreeMap<String, Vec<V>>),
    Stopped(Stop),
    Failed(String),
}
#[derive(Clone, Copy, Debug, Default)]
pub struct WireUsage {
    pub cuts: u64,
    pub messages: u64,
    pub payload_bytes: usize,
    pub envelope_bytes: usize,
}
pub struct JointReport<V> {
    pub outcome: JointOutcome<V>,
    pub wire: WireUsage,
    /// Host cancellation is explicit and distinct from the role that stopped.
    pub cancelled: Vec<Stop>,
}
/// Hooks are host observations. They are not visible to either participant.
/// The default transfer faithfully roundtrips bytes; experiments may install a
/// hostile transport here without changing source or compiled role algorithms.
pub trait Transport<V> {
    fn transfer(&mut self, packet: &Packet<V>, bytes: Vec<u8>) -> Result<Vec<u8>, String>;
    fn delivered(&mut self, _packet: &Packet<V>) {}
}
pub struct LocalTransport;
impl<V> Transport<V> for LocalTransport {
    fn transfer(&mut self, _: &Packet<V>, bytes: Vec<u8>) -> Result<Vec<u8>, String> {
        Ok(bytes)
    }
}

/// Execute actual source cuts over separately owned role runners. On a local
/// stop, the host cancels other roles; no peer terminal message is invented.
/// Runners stay with the caller, retaining completed state even after failure.
pub fn drive<B: WireBackend, T: Transport<B::Value>>(
    schedule: &mut Schedule,
    runners: &mut BTreeMap<String, Runner<B>>,
    transport: &mut T,
) -> JointReport<B::Value> {
    drive_with_decoder(schedule, runners, transport, &BackendDecoder)
}

/// Run with an explicitly installed receiving policy, for example per-message
/// setup selection in a protocol containing several independent commitments.
pub fn drive_with_decoder<B: WireBackend, T: Transport<B::Value>, D: MessageDecoder<B>>(
    schedule: &mut Schedule,
    runners: &mut BTreeMap<String, Runner<B>>,
    transport: &mut T,
    decoder: &D,
) -> JointReport<B::Value> {
    let mut wire = WireUsage::default();
    let result = execute(schedule, runners, transport, decoder, &mut wire);
    let outcome = result.unwrap_or_else(JointOutcome::Failed);
    let mut cancelled = Vec::new();
    if !matches!(outcome, JointOutcome::Returned(_)) {
        for runner in runners.values_mut() {
            if !runner.is_terminal() {
                runner.cancel();
                if let Action::Stopped(stop) = runner.poll() {
                    cancelled.push(stop);
                }
            }
        }
    }
    JointReport {
        outcome,
        wire,
        cancelled,
    }
}
fn execute<B: WireBackend, T: Transport<B::Value>, D: MessageDecoder<B>>(
    schedule: &mut Schedule,
    runners: &mut BTreeMap<String, Runner<B>>,
    transport: &mut T,
    decoder: &D,
    wire: &mut WireUsage,
) -> Result<JointOutcome<B::Value>, String> {
    let roles = schedule.inputs()?;
    if !roles.keys().eq(runners.keys())
        || runners
            .iter()
            .any(|(role, runner)| runner.role() != role || runner.root_origin() != schedule.root())
    {
        return Err("driver-entry-binding".into());
    }
    // Construction already executes ingress. Inspect only terminal runners:
    // polling other roles here could start their member before family agreement.
    for runner in runners.values_mut() {
        if runner.is_terminal()
            && let Action::Stopped(stop) = runner.poll()
        {
            return Ok(JointOutcome::Stopped(stop));
        }
    }
    schedule.bind_family(
        &runners
            .iter()
            .map(|(role, runner)| (role.clone(), runner.selected_parameters().clone()))
            .collect(),
    )?;
    // Exhausting the scheduler's budget stops the whole execution, as
    // `exhausted` does in docs/spec/core/execution.md; it is not a host fault.
    // No role owns the stop, so it is attributed to the joint schedule.
    while let Some(action) = match schedule.next_action() {
        Err(error) if error == WORK_LIMIT => {
            return Ok(JointOutcome::Stopped(Stop {
                origin: schedule.root().clone(),
                role: "joint".into(),
                site: None,
                kind: StopKind::Limit,
                cleanup_errors: Vec::new(),
            }));
        }
        next => next?,
    } {
        wire.cuts += 1;
        match action {
            ScheduledAction::Local {
                origin,
                site,
                role,
                function,
            } => {
                let runner = runners.get_mut(&role).ok_or("driver-role")?;
                let expected = Cut {
                    origin,
                    role,
                    site,
                    kind: CutKind::Local,
                };
                match runner.poll() {
                    Action::Local(local) if local.cut == expected && local.function == function => {
                        runner.execute_local(&expected).map_err(|e| e.to_string())?;
                        if runner.is_terminal()
                            && let Action::Stopped(stop) = runner.poll()
                        {
                            return Ok(JointOutcome::Stopped(stop));
                        }
                    }
                    Action::Stopped(stop) => return Ok(JointOutcome::Stopped(stop)),
                    _ => return Err("driver-local-cut".into()),
                }
            }
            ScheduledAction::Message {
                origin,
                site,
                schema,
                sender,
                receiver,
            } => {
                let send_cut = Cut {
                    origin: origin.clone(),
                    role: sender.clone(),
                    site: site.clone(),
                    kind: CutKind::Send,
                };
                let source = runners.get_mut(&sender).ok_or("driver-sender")?;
                match source.poll() {
                    Action::Send(packet)
                        if packet.envelope.origin == origin
                            && packet.envelope.site == site
                            && packet.envelope.schema == schema
                            && packet.envelope.sender == sender
                            && packet.envelope.receiver == receiver => {}
                    Action::Stopped(stop) => return Ok(JointOutcome::Stopped(stop)),
                    _ => return Err("driver-send-cut".into()),
                }
                let packet = source.take_send(&send_cut).map_err(|e| e.to_string())?;
                let bytes = source
                    .backend()
                    .encode(&packet.payload)
                    .map_err(|e| e.to_string())?;
                let bytes = transport.transfer(&packet, bytes)?;
                wire.messages += 1;
                wire.payload_bytes = wire
                    .payload_bytes
                    .checked_add(bytes.len())
                    .ok_or("driver-byte-overflow")?;
                wire.envelope_bytes = wire
                    .envelope_bytes
                    .checked_add(packet.envelope.domain_bytes().len())
                    .ok_or("driver-byte-overflow")?;
                let destination = runners.get_mut(&receiver).ok_or("driver-receiver")?;
                let receive = match destination.poll() {
                    Action::Receive(receive)
                        if receive.envelope == packet.envelope && receive.ty == packet.ty =>
                    {
                        receive
                    }
                    Action::Stopped(stop) => return Ok(JointOutcome::Stopped(stop)),
                    _ => return Err("driver-receive-cut".into()),
                };
                let delivered = Packet {
                    envelope: packet.envelope,
                    ty: packet.ty,
                    payload: decoder
                        .decode(destination.backend(), &receive, &bytes)
                        .map_err(|e| e.to_string())?,
                };
                destination
                    .deliver(delivered.clone())
                    .map_err(|e| e.to_string())?;
                transport.delivered(&delivered);
            }
            ScheduledAction::Stop {
                origin,
                site,
                role,
                reason,
            } => {
                let runner = runners.get_mut(&role).ok_or("driver-stop-role")?;
                match runner.poll() {
                    Action::Stopped(stop)
                        if stop.origin == origin
                            && stop.site.as_ref() == Some(&site)
                            && stop.kind
                                == zkc_runtime::interactive::StopKind::Explicit(reason) =>
                    {
                        return Ok(JointOutcome::Stopped(stop));
                    }
                    Action::Stopped(stop) => return Ok(JointOutcome::Stopped(stop)),
                    _ => return Err("driver-stop-cut".into()),
                }
            }
        }
    }
    let mut values = BTreeMap::new();
    for (role, runner) in runners {
        match runner.poll() {
            Action::Returned(outputs) => {
                values.insert(role.clone(), outputs);
            }
            Action::Stopped(stop) => return Ok(JointOutcome::Stopped(stop)),
            _ => return Err("driver-unfinished-role".into()),
        }
    }
    Ok(JointOutcome::Returned(values))
}
