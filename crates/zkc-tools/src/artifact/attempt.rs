//! Execute one stored participant body into a private, bounded message buffer.
//!
//! An external codec chooses container order after the body's returned retry
//! decision. Message order does not silently become transcript order. The caller
//! retains the actual runner/backend on every path and can place this driver
//! inside `zkc_runtime::attempt::Controller` without reconstructing provider state.

use super::{ArtifactFailure, ArtifactReport, FormatError};
use crate::protocol::WireBackend;
use zkc_runtime::{
    attempt::Decision,
    interactive::{Action, Envelope, PhysicalType, Runner, Value as RuntimeValue},
};

pub struct BufferedMessage<V> {
    pub envelope: Envelope,
    pub ty: PhysicalType,
    /// The typed payload. A proof codec selects its own field encoding without
    /// parsing or stripping a backend transport header.
    pub payload: V,
}

/// Produced bytes have no implicit header or binding prefix. Their external
/// codec and statement binding must be checked by the selected construction.
pub struct Ready<A> {
    pub value: A,
    pub bytes: Vec<u8>,
}

/// Classify returned data only. A runtime stop bypasses classification and
/// cannot be turned into a retry. The codec runs only for a completed attempt.
/// The codec is an installed adapter; its external effects are its own contract.
pub fn execute<B: WireBackend, R, A>(
    runner: &mut Runner<B>,
    limit: usize,
    classify: impl FnOnce(Vec<B::Value>) -> Result<Decision<R, A>, ArtifactFailure>,
    encode: impl FnOnce(&[BufferedMessage<B::Value>]) -> Result<Vec<u8>, ArtifactFailure>,
) -> ArtifactReport<Decision<R, Ready<A>>> {
    let mut messages = Vec::new();
    let mut bytes = 0usize;
    let mut retained = 0usize;
    let outcome = (|| {
        let outputs = loop {
            let action = runner.poll();
            match action {
                Action::Local(local) => runner.execute_local(&local.cut)?,
                Action::Send(_) => {
                    let cut = action
                        .cut()
                        .ok_or(ArtifactFailure::UnexpectedCommunication)?;
                    let packet = runner.take_send(&cut)?;
                    let encoded = runner.backend().encode(&packet.payload)?;
                    let next = bytes.checked_add(encoded.len()).ok_or(FormatError::Limit)?;
                    let retained_next = retained
                        .checked_add(packet.payload.retained_bytes())
                        .ok_or(FormatError::Limit)?;
                    if next > limit || retained_next > limit || messages.len() >= 32768 {
                        return Err(FormatError::Limit.into());
                    }
                    messages
                        .try_reserve(1)
                        .map_err(|_| FormatError::Allocation)?;
                    messages.push(BufferedMessage {
                        envelope: packet.envelope,
                        ty: packet.ty,
                        payload: packet.payload,
                    });
                    bytes = next;
                    retained = retained_next;
                }
                Action::Receive(_) => return Err(ArtifactFailure::UnexpectedCommunication),
                Action::Stopped(stop) => return Err(ArtifactFailure::Stopped(Box::new(stop))),
                Action::Returned(outputs) => break outputs,
            }
        };
        Ok(match classify(outputs)? {
            Decision::Retry(reason) => Decision::Retry(reason),
            Decision::Complete(value) => {
                let proof = encode(&messages)?;
                if proof.len() > limit {
                    return Err(FormatError::Limit.into());
                }
                Decision::Complete(Ready {
                    value,
                    bytes: proof,
                })
            }
        })
    })();
    let cancelled = if outcome.is_err() && !runner.is_terminal() {
        runner.cancel();
        match runner.poll() {
            Action::Stopped(stop) => Some(stop),
            _ => None,
        }
    } else {
        None
    };
    ArtifactReport {
        outcome,
        messages: messages.len(),
        bytes,
        cancelled,
    }
}
