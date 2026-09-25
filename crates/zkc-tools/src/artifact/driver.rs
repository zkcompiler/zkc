use super::{FormatError, ProofReader, ProofWriter};
use crate::protocol::{BackendDecoder, MessageDecoder, WireBackend};
use zkc_runtime::interactive::{Action, BackendError, Packet, Runner, RuntimeError, Stop};

#[derive(Debug)]
pub enum ArtifactFailure {
    Format(FormatError),
    Runtime(RuntimeError),
    Backend(BackendError),
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
    /// Host cancellation after a transport/format error, with any cleanup
    /// errors. Completed backend transitions remain visible in the runner.
    pub cancelled: Option<Stop>,
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

/// The caller retains the runner, including resource/failure observations.
/// A failed production returns no candidate, even when a prefix was written.
pub fn produce<B: WireBackend>(
    runner: &mut Runner<B>,
    expected_binding: &[u8; 32],
) -> ArtifactReport<Produced<B::Value>> {
    let mut writer = ProofWriter::new(expected_binding);
    let outcome = (|| loop {
        let action = runner.poll();
        match action {
            Action::Local(local) => runner.execute_local(&local.cut)?,
            Action::Send(_) => {
                let cut = action
                    .cut()
                    .ok_or(ArtifactFailure::UnexpectedCommunication)?;
                let packet = runner.take_send(&cut)?;
                writer.message(&runner.backend().encode(&packet.payload)?)?;
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
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut)?,
            Action::Receive(request) => {
                let bytes = reader.message()?;
                let value = decoder.decode(runner.backend(), &request, bytes)?;
                runner.deliver(Packet {
                    envelope: request.envelope,
                    ty: request.ty,
                    payload: value,
                })?;
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
