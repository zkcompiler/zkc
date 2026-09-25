//! A controller primitive for Main's common-source traversal. The caller chooses
//! exactly one source cut; this module does not guess order from endpoint readiness.
use super::{Action, Backend, Cut, CutKind, Envelope, Runner, RuntimeError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DriverCut {
    Local(Cut),
    /// A single common message cut corresponds to its send and receive halves.
    Message {
        send: Cut,
        receive: Cut,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DriverEvent {
    Local { cut: Cut, stopped: bool },
    Delivered(Envelope),
}

/// Execute one source-selected local/message action. Both roles must belong to
/// the same admitted bindings, entry, session and root instance. Local execution
/// never polls the unrelated peer, including when that peer has already stopped.
/// The controller decides whether to continue after any local stop.
pub fn drive_cut<L, R>(
    left: &mut Runner<L>,
    right: &mut Runner<R>,
    cut: &DriverCut,
) -> Result<DriverEvent, RuntimeError>
where
    L: Backend,
    R: Backend<Value = L::Value>,
{
    if left.root_origin() != right.root_origin() || left.role() == right.role() {
        return Err(RuntimeError::Envelope);
    }
    match cut {
        DriverCut::Local(cut) => {
            if cut.kind != CutKind::Local {
                return Err(RuntimeError::WrongCut);
            }
            let stopped = if cut.role == left.role() {
                left.execute_local(cut)?;
                left.is_terminal()
            } else if cut.role == right.role() {
                right.execute_local(cut)?;
                right.is_terminal()
            } else {
                return Err(RuntimeError::Role);
            };
            Ok(DriverEvent::Local {
                cut: cut.clone(),
                stopped,
            })
        }
        DriverCut::Message { send, receive } => {
            if send.kind != CutKind::Send || receive.kind != CutKind::Receive {
                return Err(RuntimeError::WrongCut);
            }
            if send.role == left.role() && receive.role == right.role() {
                transfer(left, right, send, receive)
            } else if send.role == right.role() && receive.role == left.role() {
                transfer(right, left, send, receive)
            } else {
                Err(RuntimeError::Role)
            }
        }
    }
}
fn transfer<S, R>(
    sender: &mut Runner<S>,
    receiver: &mut Runner<R>,
    send: &Cut,
    receive: &Cut,
) -> Result<DriverEvent, RuntimeError>
where
    S: Backend,
    R: Backend<Value = S::Value>,
{
    let outgoing = sender.poll();
    if outgoing.cut().as_ref() != Some(send) {
        return Err(RuntimeError::WrongCut);
    }
    if receiver.poll().cut().as_ref() != Some(receive) {
        return Err(RuntimeError::WrongCut);
    }
    let Action::Send(packet) = outgoing else {
        return Err(RuntimeError::WrongAction);
    };
    receiver.check_delivery(&packet)?;
    let packet = sender.take_send(send)?;
    let envelope = packet.envelope.clone();
    receiver.deliver(packet)?;
    Ok(DriverEvent::Delivered(envelope))
}
