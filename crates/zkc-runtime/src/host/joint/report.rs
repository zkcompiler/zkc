use super::Step;
use crate::interpreter::Runner;
use crate::vm::{
    Backend, CutKind, DecodeReason, Origin, ProgramState, ReceiveCompletion, RuntimeError, Stop,
    StopKind, Usage,
};

/// UTF-8 prefix plus the number of omitted original bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Text {
    pub text: String,
    pub omitted_bytes: usize,
}
impl Text {
    pub(super) fn copy(value: &str) -> Self {
        let mut end = value.len().min(4096);
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        Self {
            text: value[..end].into(),
            omitted_bytes: value.len() - end,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StopCause {
    Decode(DecodeReason),
    Explicit(Text),
    Backend(Text),
    Limit,
    Cancelled,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StopSummary {
    pub origin: Origin,
    pub site: Option<String>,
    pub cause: StopCause,
    pub local: Option<Box<crate::vm::LocalContext>>,
    pub cleanup_errors: Vec<Text>,
    pub omitted_errors: usize,
}
impl StopSummary {
    pub(super) fn copy(stop: &Stop) -> Self {
        let cause = match &stop.kind {
            StopKind::Decode(r) => StopCause::Decode(*r),
            StopKind::Explicit(s) => StopCause::Explicit(Text::copy(s)),
            StopKind::Backend(e) => StopCause::Backend(Text::copy(&e.code)),
            StopKind::Limit => StopCause::Limit,
            StopKind::Cancelled => StopCause::Cancelled,
        };
        Self {
            origin: stop.origin.clone(),
            site: stop.site.clone(),
            cause,
            local: stop.local.clone(),
            cleanup_errors: stop
                .cleanup_errors
                .iter()
                .take(32)
                .map(|e| Text::copy(&e.code))
                .collect(),
            omitted_errors: stop.cleanup_errors.len().saturating_sub(32),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum State {
    NotStarted,
    Unpolled {
        kind: Option<CutKind>,
        site: Option<String>,
    },
    ReturnIf {
        site: String,
    },
    Pending {
        kind: CutKind,
        site: String,
    },
    Returned,
    Stopped(StopSummary),
}
impl State {
    pub(super) fn inspect<B: Backend>(runner: &Runner<B>) -> Self {
        match runner
            .inspect_program()
            .expect("joint session owns program runners")
        {
            ProgramState::Unpolled { kind, site } => Self::Unpolled {
                kind,
                site: site.map(str::to_owned),
            },
            // The report retains its existing coarse unpolled-state schema.
            ProgramState::Yield => Self::Unpolled {
                kind: None,
                site: None,
            },
            ProgramState::ReturnIf { site } => Self::ReturnIf { site: site.into() },
            ProgramState::Pending(cut) => Self::Pending {
                kind: cut.kind,
                site: cut.site.into(),
            },
            ProgramState::Returned => Self::Returned,
            ProgramState::Stopped(stop) => Self::Stopped(StopSummary::copy(stop)),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureKind {
    Setup,
    Limit,
    Contract,
    Codec,
    Hook,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    pub kind: FailureKind,
    pub detail: Text,
}
impl Failure {
    pub(super) fn new(kind: FailureKind, detail: &str) -> Self {
        Self {
            kind,
            detail: Text::copy(detail),
        }
    }
}
/// Preserve the typed category without formatting an unbounded backend message.
pub(super) fn runtime_failure(kind: FailureKind, error: &RuntimeError) -> Failure {
    let detail = match error {
        RuntimeError::Backend(e) => &e.code,
        RuntimeError::ExplicitStop(s) => s,
        RuntimeError::Admission(e) => &e.detail,
        RuntimeError::Entry => "Entry",
        RuntimeError::Role => "Role",
        RuntimeError::Session => "Session",
        RuntimeError::Inputs => "Inputs",
        RuntimeError::WrongAction => "WrongAction",
        RuntimeError::WrongCut => "WrongCut",
        RuntimeError::Envelope => "Envelope",
        RuntimeError::Payload => "Payload",
        RuntimeError::Limit => "Limit",
    };
    Failure::new(kind, detail)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Completed,
    ParticipantStopped {
        role: usize,
    },
    /// A live participant reached communication with a returned peer. Returned
    /// outputs are preserved; unfinished participants are cancelled by the host.
    ReturnedEarly {
        role: usize,
        blocked: usize,
    },
    DriverFailed(Failure),
    HostCancelled(Text),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Progress {
    Exposed,
    Completed,
    Stopped,
    Failed,
}
#[derive(Clone, Debug)]
pub struct Reached {
    pub step: Step,
    /// Outer-to-inner iteration numbers for this static instruction coordinate,
    /// shared by every reached step of the same dynamic region.
    pub iterations: std::sync::Arc<[u64]>,
    /// The validated local count; absent for other instructions or a bound stop.
    pub loop_count: Option<u64>,
    /// Exact reached participant branch arm; payload agreement is separate.
    pub branch_alternative: Option<usize>,
    pub branch_started: bool,
    /// Complete dynamic control path, including selected branch arms. Each
    /// distinct path is stored once and shared by the steps it contains.
    pub path: std::sync::Arc<[crate::vm::PathElement]>,
    /// Count agreement and this participant's loop start completed. For zero
    /// trips this means its initial carried results were bound, with no body.
    pub loop_started: bool,
    pub progress: Progress,
    pub sent_bytes: Option<usize>,
    pub replacement_bytes: Option<usize>,
    pub receive_completion: Option<ReceiveCompletion>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WireUsage {
    pub sends: usize,
    pub receives: usize,
    pub sent_bytes: usize,
    pub replacement_bytes: usize,
}
#[derive(Clone, Debug)]
pub struct PendingMessage {
    pub send_step: usize,
    pub receive_step: usize,
    pub original_bytes: usize,
    pub bytes: Vec<u8>,
}
#[derive(Clone, Debug, Default)]
pub struct Observation {
    pub value: Option<Text>,
    pub error: Option<Text>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    BeforeCancellation,
    AfterCancellation,
}
#[derive(Debug)]
pub struct RoleReport<V> {
    pub role: String,
    pub before: State,
    pub usage: Option<Usage>,
    pub execution_counts: crate::vm::ExecutionCounts,
    pub observation: Observation,
    pub cancelled: bool,
    pub after: State,
    pub after_observation: Observation,
    pub outputs: Vec<V>,
    pub return_at: Option<(Origin, String)>,
}
/// Owns backend custody after all snapshots and explicit host cleanup.
/// A false output is an ordinary Completed result; the host selects acceptance.
pub struct Report<B: Backend> {
    pub session: String,
    /// Effective limits selected by the host, independent of bundle bytes.
    pub limits: super::RunLimits,
    pub outcome: Outcome,
    pub reached: Vec<Reached>,
    /// Report storage charged against `limits.report_bytes`; the invocation
    /// root, when present, holds the same live bytes while the report exists.
    pub report_bytes: usize,
    pub wire: WireUsage,
    pub pending: Option<PendingMessage>,
    pub roles: Vec<RoleReport<B::Value>>,
    pub backends: Vec<(String, B)>,
    pub(super) retained: Vec<crate::vm::RetainedOutputs<B::Value>>,
    pub(super) wire_live: Option<crate::vm::LiveReservation>,
    /// Live allowance of each stored record and of the dynamic path it first
    /// references, held in the invocation root: `report_bytes` in total.
    pub(super) storage_live: Vec<crate::vm::LiveReservation>,
    pub(super) invocation: Option<crate::vm::ExecutionLedger>,
}
impl<B: Backend> Report<B> {
    /// The invocation root that charged this run's wire transport, received
    /// payload decoding and report storage, when the Host supplied one. The
    /// report keeps those live allowances until it is dropped.
    pub fn invocation_ledger(&self) -> Option<&crate::vm::ExecutionLedger> {
        self.invocation.as_ref()
    }
    /// Retained bytes of returned values whose runner shared no ledger. A
    /// Host that keeps this report reserves them in its own invocation root:
    /// custody passes to it without a new allocation. A runner that shared a
    /// ledger moved its values' reservation there with them.
    pub fn unreserved_output_bytes(&self) -> usize {
        use crate::vm::Value as _;
        self.retained
            .iter()
            .filter(|outputs| !outputs.is_reserved())
            .flat_map(|outputs| outputs.iter())
            .map(|value| value.retained_bytes())
            .fold(0, usize::saturating_add)
    }
    /// Drop every returned value this report retains, with its reservation.
    /// Cleanup observations taken before this call are unchanged.
    pub fn release_outputs(&mut self) {
        self.retained.clear();
        for role in &mut self.roles {
            role.outputs.clear();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::BackendError;
    #[test]
    fn diagnostic_copies_are_bounded_at_utf8_boundaries() {
        let huge = "한".repeat(3000);
        let stop = Stop {
            origin: Origin {
                session: "s".into(),
                entry: "main".into(),
                instance: "root".into(),
                path: vec![],
            },
            role: "Alice".into(),
            site: Some("site".into()),
            kind: StopKind::Backend(BackendError::new(huge.clone())),
            local: Some(Box::new(crate::vm::LocalContext {
                site: "call".into(),
                function: "fn".into(),
                instruction: Some("site".into()),
            })),
            cleanup_errors: (0..40).map(|_| BackendError::new(huge.clone())).collect(),
        };
        let summary = StopSummary::copy(&stop);
        assert_eq!(summary.local, stop.local);
        assert_eq!(summary.cleanup_errors.len(), 32);
        assert_eq!(summary.omitted_errors, 8);
        for error in &summary.cleanup_errors {
            assert_eq!(error.text.len(), 4095);
            assert_eq!(error.omitted_bytes, 4905);
        }
        let failure = runtime_failure(
            FailureKind::Setup,
            &RuntimeError::Backend(BackendError::new(huge)),
        );
        assert_eq!(failure.detail.text.len(), 4095);
        assert_eq!(failure.detail.omitted_bytes, 4905);
    }
}
