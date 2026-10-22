//! Ordered proof production and validation under application-supplied contracts.
use super::wire::{FormatError, ProofBackend, ProofFormat, ProofReader, ProofWriter, WireError};
use crate::interpreter::Runner;
use crate::vm::{Action, Backend, BackendError, RuntimeError, Stop, Value as RuntimeValue};

#[derive(Debug)]
pub enum ArtifactFailure {
    StartedRunner,
    Format(FormatError),
    Runtime(RuntimeError),
    Backend(BackendError),
    Wire(WireError),
    Stopped(Box<Stop>),
    UnexpectedCommunication,
    AcceptanceType,
    Rejected,
}
impl From<FormatError> for ArtifactFailure {
    fn from(error: FormatError) -> Self {
        Self::Format(error)
    }
}
impl From<RuntimeError> for ArtifactFailure {
    fn from(error: RuntimeError) -> Self {
        Self::Runtime(error)
    }
}
impl From<BackendError> for ArtifactFailure {
    fn from(error: BackendError) -> Self {
        Self::Backend(error)
    }
}

pub struct Produced<V> {
    pub proof: Vec<u8>,
    pub outputs: Vec<V>,
    retained: Vec<crate::vm::LiveReservation>,
}

pub struct ArtifactReport<T> {
    pub outcome: Result<T, ArtifactFailure>,
    pub messages: usize,
    pub bytes: usize,
    /// Host cancellation after a transport/format or entry-precondition error, with any cleanup
    /// errors. Completed backend transitions remain visible in the runner.
    pub cancelled: Option<Stop>,
}

impl<T> ArtifactReport<T> {
    /// Terminal execution diagnostics, or cleanup from a later host cancellation.
    pub fn stop(&self) -> Option<&Stop> {
        match &self.outcome {
            Err(ArtifactFailure::Stopped(stop)) => Some(stop),
            _ => self.cancelled.as_ref(),
        }
    }
}

// Preserve an already terminal stop before touching framing.
// It belongs to the retained runner, not to a newly consumed proof. A live runner
// that advanced past entry is cancelled on refusal, preserving its observations.
fn entry_report<B: Backend, T>(runner: &mut Runner<B>) -> Option<ArtifactReport<T>> {
    if let Some(stop) = runner.stop() {
        return Some(ArtifactReport {
            outcome: Err(ArtifactFailure::Stopped(Box::new(stop.clone()))),
            messages: 0,
            bytes: 0,
            cancelled: None,
        });
    }
    if !runner.is_at_entry() {
        return Some(ArtifactReport {
            outcome: Err(ArtifactFailure::StartedRunner),
            messages: 0,
            bytes: 0,
            cancelled: cancel_failure(runner, true),
        });
    }
    None
}

fn cancel_failure<B: Backend>(runner: &mut Runner<B>, failed: bool) -> Option<Stop> {
    if failed && !runner.is_terminal() {
        runner.cancel();
        if let Action::Stopped(stop) = runner.poll() {
            return Some(stop);
        }
    }
    None
}

/// How the admitted participant program exchanges its proof with the Host.
#[derive(Clone, Copy)]
pub enum Transport {
    Messages(ProofFormat),
    Record,
}
impl Transport {
    fn format(self) -> ProofFormat {
        match self {
            Self::Messages(format) => format,
            Self::Record => ProofFormat::RawBytes,
        }
    }
    fn record(self) -> bool {
        matches!(self, Self::Record)
    }
}

/// Execute a fresh producer after application admission. The Host owns binding,
/// transport and capacity selection. No deployment authority is derived here.
pub fn produce<B: ProofBackend>(
    runner: &mut Runner<B>,
    expected_binding: &[u8; 32],
    transport: Transport,
    limit: usize,
    ledger: Option<crate::vm::ExecutionLedger>,
) -> ArtifactReport<Produced<B::Value>> {
    let encoding_retained = std::cell::RefCell::new(None);
    produce_admitted_with_limit(
        runner,
        expected_binding,
        transport,
        limit,
        ledger.clone(),
        |backend, value| {
            let bound = if transport.format() == ProofFormat::RawBytes {
                value.retained_bytes()
            } else {
                backend
                    .encoding_bound(value)
                    .map_err(ArtifactFailure::Wire)?
            };
            // The allocation allowance includes retention/framing slack. The
            // writer checks actual frame bytes before any proof append.
            let live = crate::host::wire::reserve_allocation(ledger.as_ref(), bound)
                .map_err(|_| ArtifactFailure::Format(FormatError::Limit))?;
            encoding_retained.replace(live);
            transport
                .format()
                .encode(backend, value)
                .map_err(ArtifactFailure::Wire)
        },
    )
}

fn produce_admitted_with_limit<B: Backend>(
    runner: &mut Runner<B>,
    expected_binding: &[u8; 32],
    transport: Transport,
    limit: usize,
    ledger: Option<crate::vm::ExecutionLedger>,
    encode: impl for<'a> Fn(&B, &'a B::Value) -> Result<std::borrow::Cow<'a, [u8]>, ArtifactFailure>,
) -> ArtifactReport<Produced<B::Value>> {
    if let Some(report) = entry_report(runner) {
        return report;
    }
    let mut writer = match ProofWriter::with_shared_ledger(
        transport.format(),
        expected_binding,
        limit,
        ledger,
    ) {
        Ok(writer) => writer,
        Err(error) => {
            return ArtifactReport {
                outcome: Err(error.into()),
                messages: 0,
                bytes: 0,
                cancelled: cancel_failure(runner, true),
            };
        }
    };
    let outcome = (|| loop {
        while runner.advance_local_control()? {}
        let action = runner.poll();
        match action {
            Action::Query(query) => runner.execute_query(&query.cut)?,
            Action::Local(local) => runner.execute_local(&local.cut)?,
            Action::Send(_) if !transport.record() => {
                let cut = action
                    .cut()
                    .ok_or(ArtifactFailure::UnexpectedCommunication)?;
                let packet = runner.take_send(&cut)?;
                writer.message(&encode(runner.backend(), &packet.payload)?)?;
            }
            Action::Send(_) | Action::Receive(_) => {
                return Err(ArtifactFailure::UnexpectedCommunication);
            }
            Action::Stopped(stop) => return Err(ArtifactFailure::Stopped(Box::new(stop))),
            Action::Returned(outputs) => {
                if transport.record() {
                    let proof = outputs
                        .last()
                        .ok_or(ArtifactFailure::UnexpectedCommunication)?;
                    writer.message(&encode(runner.backend(), proof)?)?;
                }
                return Ok(outputs);
            }
        }
    })();
    let messages = writer.messages();
    let bytes = writer.bytes_written();
    let outcome = outcome.and_then(|outputs| {
        let (proof, retained) = writer.finish_retained()?;
        Ok(Produced {
            proof,
            outputs,
            retained,
        })
    });
    let cancelled = cancel_failure(runner, outcome.is_err());
    ArtifactReport {
        outcome,
        messages,
        bytes,
        cancelled,
    }
}

/// Validate an independent proof against a fresh admitted validator and the
/// application's explicit binding, transport and acceptance selector.
pub fn validate<B: ProofBackend>(
    runner: &mut Runner<B>,
    proof: &[u8],
    expected_binding: &[u8; 32],
    transport: Transport,
    acceptance: usize,
    ledger: Option<crate::vm::ExecutionLedger>,
) -> ArtifactReport<Vec<B::Value>> {
    validate_admitted(
        runner,
        proof,
        expected_binding,
        transport,
        acceptance,
        |backend, value| backend.acceptance(value),
        |runner, request, bytes| {
            let cut = Action::<B::Value>::Receive(request.clone())
                .cut()
                .ok_or(ArtifactFailure::UnexpectedCommunication)?;
            if let Some(ledger) = &ledger {
                ledger
                    .charge(
                        crate::vm::WorkBudget {
                            instructions: 0,
                            iterations: 0,
                            logical_bytes: bytes.len() as u64,
                        },
                        0,
                    )
                    .map_err(|_| ArtifactFailure::Format(FormatError::Limit))?;
            }
            let retained =
                match transport
                    .format()
                    .decoding_bound(runner.backend(), &request.ty, bytes)
                {
                    Ok(bound) => bound,
                    Err(WireError::Invalid(reason)) => {
                        // Measurement rejection is still an accepted Decode completion.
                        runner.complete_receive(&cut, Err(reason))?;
                        return Ok(());
                    }
                    Err(error) => return Err(ArtifactFailure::Wire(error)),
                };
            let _live = crate::host::wire::reserve_allocation(ledger.as_ref(), retained)
                .map_err(|_| ArtifactFailure::Format(FormatError::Limit))?;
            let decoded = match transport
                .format()
                .decode(runner.backend(), &request.ty, bytes)
            {
                Ok(value) => Ok(value),
                Err(WireError::Invalid(reason)) => Err(reason),
                Err(error) => return Err(ArtifactFailure::Wire(error)),
            };
            runner.complete_receive(&cut, decoded)?;
            Ok(())
        },
    )
}
fn validate_admitted<B: Backend>(
    runner: &mut Runner<B>,
    proof: &[u8],
    expected_binding: &[u8; 32],
    transport: Transport,
    acceptance_index: usize,
    boolean: impl Fn(&B, &B::Value) -> Option<bool>,
    receive: impl Fn(&mut Runner<B>, crate::vm::Receive, &[u8]) -> Result<(), ArtifactFailure>,
) -> ArtifactReport<Vec<B::Value>> {
    if let Some(report) = entry_report(runner) {
        return report;
    }
    let mut reader = match (!transport.record())
        .then(|| ProofReader::new(transport.format(), proof, expected_binding))
        .transpose()
    {
        Ok(reader) => reader,
        Err(error) => {
            let cancelled = cancel_failure(runner, true);
            return ArtifactReport {
                outcome: Err(error.into()),
                messages: 0,
                bytes: if matches!(error, FormatError::Header) {
                    40
                } else {
                    0
                },
                cancelled,
            };
        }
    };
    let outcome = (|| loop {
        while runner.advance_local_control()? {}
        match runner.poll() {
            Action::Query(query) => runner.execute_query(&query.cut)?,
            Action::Local(local) => runner.execute_local(&local.cut)?,
            Action::Receive(request) => {
                let bytes = reader
                    .as_mut()
                    .ok_or(ArtifactFailure::UnexpectedCommunication)?
                    .message()?;
                receive(runner, request, bytes)?;
            }
            Action::Send(_) => return Err(ArtifactFailure::UnexpectedCommunication),
            Action::Stopped(stop) => return Err(ArtifactFailure::Stopped(Box::new(stop))),
            Action::Returned(outputs) => {
                if let Some(reader) = &reader {
                    reader.finish()?;
                }
                return match outputs
                    .get(acceptance_index)
                    .and_then(|value| boolean(runner.backend(), value))
                {
                    Some(true) => Ok(outputs),
                    Some(false) => Err(ArtifactFailure::Rejected),
                    None => Err(ArtifactFailure::AcceptanceType),
                };
            }
        }
    })();
    ArtifactReport {
        cancelled: cancel_failure(runner, outcome.is_err()),
        outcome,
        messages: reader.as_ref().map_or(0, ProofReader::messages),
        bytes: reader.as_ref().map_or(proof.len(), ProofReader::bytes_read),
    }
}

impl<V> Produced<V> {
    /// Transfer the proof and outputs together with the proof buffer's live
    /// reservations. Keep these guards for as long as their bytes are retained.
    pub fn into_parts(self) -> (Vec<u8>, Vec<V>, Vec<crate::vm::LiveReservation>) {
        (self.proof, self.outputs, self.retained)
    }
}
