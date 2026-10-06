use super::{FormatError, ProofReader, ProofWriter};
use crate::protocol::{BackendDecoder, MessageDecoder, WireBackend};
use zkc_runtime::interactive::{Action, BackendError, Packet, Runner, RuntimeError, Stop};

#[derive(Debug)]
pub enum ArtifactFailure {
    StartedRunner,
    UnsupportedNativeProfile,
    Format(FormatError),
    Runtime(RuntimeError),
    Backend(BackendError),
    NativeWire(zkc_backends::NativeWireError),
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

// Preserve an already terminal stop (including ingress) before touching framing.
// It belongs to the retained runner, not to a newly consumed proof. A live runner
// that advanced past entry is cancelled on refusal, preserving its observations.
fn entry_report<B: WireBackend, T>(runner: &mut Runner<B>) -> Option<ArtifactReport<T>> {
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

fn cancel_failure<B: WireBackend>(runner: &mut Runner<B>, failed: bool) -> Option<Stop> {
    if failed && !runner.is_terminal() {
        runner.cancel();
        if let Action::Stopped(stop) = runner.poll() {
            return Some(stop);
        }
    }
    None
}

pub(super) fn refuse_native_profile<B: WireBackend, T>(
    runner: &mut Runner<B>,
) -> Option<ArtifactReport<T>> {
    runner.format().is_program().then(|| ArtifactReport {
        outcome: Err(ArtifactFailure::UnsupportedNativeProfile),
        messages: 0,
        bytes: 0,
        cancelled: cancel_failure(runner, true),
    })
}

/// The caller retains the runner, including resource/failure observations.
/// A failed production returns no candidate, even when a prefix was written.
/// The runner must still be at entry; use a fresh runner for each proof.
/// A pre-existing stop is returned unchanged. A live runner past entry is
/// cancelled; no proof bytes are consumed or produced in either case.
pub fn produce<B: WireBackend>(
    runner: &mut Runner<B>,
    expected_binding: &[u8; 32],
) -> ArtifactReport<Produced<B::Value>> {
    if let Some(report) = refuse_native_profile(runner) {
        return report;
    }
    produce_admitted(runner, expected_binding, false, |backend, value| {
        Ok(backend.encode(value)?)
    })
}
/// Called only by the host after native proof-entry admission.
pub(super) fn produce_admitted<B: WireBackend>(
    runner: &mut Runner<B>,
    expected_binding: &[u8; 32],
    native: bool,
    encode: impl Fn(&B, &B::Value) -> Result<Vec<u8>, ArtifactFailure>,
) -> ArtifactReport<Produced<B::Value>> {
    produce_admitted_with_limit(
        runner,
        expected_binding,
        native,
        super::MAX_PROOF_BYTES,
        encode,
    )
}

pub(super) fn produce_admitted_with_limit<B: WireBackend>(
    runner: &mut Runner<B>,
    expected_binding: &[u8; 32],
    native: bool,
    limit: usize,
    encode: impl Fn(&B, &B::Value) -> Result<Vec<u8>, ArtifactFailure>,
) -> ArtifactReport<Produced<B::Value>> {
    if let Some(report) = entry_report(runner) {
        return report;
    }
    let mut writer = match ProofWriter::with_limit(expected_binding, limit) {
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
        while native && runner.advance_local_control()? {}
        let action = runner.poll();
        match action {
            Action::Query(query) if native => runner.execute_query(&query.cut)?,
            Action::Query(_) => return Err(ArtifactFailure::UnsupportedNativeProfile),
            Action::Local(local) => runner.execute_local(&local.cut)?,
            Action::Send(_) => {
                let cut = action
                    .cut()
                    .ok_or(ArtifactFailure::UnexpectedCommunication)?;
                let packet = runner.take_send(&cut)?;
                writer.message(&encode(runner.backend(), &packet.payload)?)?;
            }
            Action::Receive(_) => return Err(ArtifactFailure::UnexpectedCommunication),
            Action::Stopped(stop) => return Err(ArtifactFailure::Stopped(Box::new(stop))),
            Action::Returned(outputs) => return Ok(outputs),
        }
    })();
    let messages = writer.messages();
    let bytes = writer.bytes_written();
    let cancelled = cancel_failure(runner, outcome.is_err());
    ArtifactReport {
        outcome: outcome.map(|outputs| Produced {
            proof: writer.finish(),
            outputs,
        }),
        messages,
        bytes,
        cancelled,
    }
}

/// Acceptance index is obtained from the checked construction result mapping.
/// The predicate only interprets the installed backend's Boolean value.
pub fn validate<B: WireBackend>(
    runner: &mut Runner<B>,
    proof: &[u8],
    expected_binding: &[u8; 32],
    acceptance_index: usize,
    boolean: impl Fn(&B::Value) -> Option<bool>,
) -> ArtifactReport<Vec<B::Value>> {
    validate_with_decoder(
        runner,
        proof,
        expected_binding,
        acceptance_index,
        boolean,
        &BackendDecoder,
    )
}

/// The application selects decoding policy from the receiving cut, independently
/// of candidate bytes. Legacy callers retain the backend's default decoder.
pub fn validate_with_decoder<B: WireBackend>(
    runner: &mut Runner<B>,
    proof: &[u8],
    expected_binding: &[u8; 32],
    acceptance_index: usize,
    boolean: impl Fn(&B::Value) -> Option<bool>,
    decoder: &impl MessageDecoder<B>,
) -> ArtifactReport<Vec<B::Value>> {
    if let Some(report) = refuse_native_profile(runner) {
        return report;
    }
    validate_admitted(
        runner,
        proof,
        expected_binding,
        acceptance_index,
        boolean,
        |runner, request, bytes| {
            let value = decoder.decode(runner.backend(), &request, bytes)?;
            runner.deliver(Packet {
                envelope: request.envelope,
                ty: request.ty,
                payload: value,
            })?;
            Ok(())
        },
    )
}
pub(super) fn validate_native(
    runner: &mut Runner<zkc_backends::NativeBackend>,
    proof: &[u8],
    expected_binding: &[u8; 32],
    acceptance: usize,
) -> ArtifactReport<Vec<zkc_backends::Value>> {
    validate_admitted(
        runner,
        proof,
        expected_binding,
        acceptance,
        |v| {
            if let zkc_backends::Value::Bool(b) = v {
                Some(*b)
            } else {
                None
            }
        },
        |runner, request, bytes| {
            let cut = Action::<zkc_backends::Value>::Receive(request.clone())
                .cut()
                .ok_or(ArtifactFailure::UnexpectedCommunication)?;
            let decoded = match runner.backend().decode_native_value(&request.ty, bytes) {
                Ok(value) => Ok(value),
                Err(zkc_backends::NativeWireError::Invalid(reason)) => Err(reason),
                Err(error) => return Err(ArtifactFailure::NativeWire(error)),
            };
            runner.complete_receive(&cut, decoded)?;
            Ok(())
        },
    )
}
fn validate_admitted<B: WireBackend>(
    runner: &mut Runner<B>,
    proof: &[u8],
    expected_binding: &[u8; 32],
    acceptance_index: usize,
    boolean: impl Fn(&B::Value) -> Option<bool>,
    receive: impl Fn(
        &mut Runner<B>,
        zkc_runtime::interactive::Receive,
        &[u8],
    ) -> Result<(), ArtifactFailure>,
) -> ArtifactReport<Vec<B::Value>> {
    if let Some(report) = entry_report(runner) {
        return report;
    }
    let mut reader = match ProofReader::new(proof, expected_binding) {
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
            Action::Query(_) => return Err(ArtifactFailure::UnsupportedNativeProfile),
            Action::Local(local) => runner.execute_local(&local.cut)?,
            Action::Receive(request) => {
                let bytes = reader.message()?;
                receive(runner, request, bytes)?;
            }
            Action::Send(_) => return Err(ArtifactFailure::UnexpectedCommunication),
            Action::Stopped(stop) => return Err(ArtifactFailure::Stopped(Box::new(stop))),
            Action::Returned(outputs) => {
                reader.finish()?;
                return match outputs.get(acceptance_index).and_then(&boolean) {
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
        messages: reader.messages(),
        bytes: reader.bytes_read(),
    }
}

#[cfg(test)]
mod tests;
