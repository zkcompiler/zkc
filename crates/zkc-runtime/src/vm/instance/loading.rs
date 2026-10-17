//! Complete invocation admission, before an evaluator executes instructions.
use super::*;
use crate::vm::code::Body;

pub(crate) struct Loaded<B: Backend> {
    pub instance: Instance<B>,
    pub frame: Frame,
    pub scope: Scope,
    pub body: Body,
    pub inputs: Vec<B::Value>,
}

impl<B: Backend> Instance<B> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        admitted: &Program,
        entry: &str,
        backend: B,
        role: &str,
        session: &str,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> std::result::Result<Self, LoadError<B>> {
        if work_budget.instructions > Limits::INSTRUCTIONS
            || work_budget.iterations > Limits::ITERATIONS
            || work_budget.logical_bytes > Limits::LOGICAL_BYTES
        {
            return Err(LoadError {
                error: RuntimeError::Limit,
                usage: Usage::default(),
                backend,
            });
        }
        if session.is_empty()
            || session.len() > 128
            || !session
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
        {
            return Err(LoadError {
                error: RuntimeError::Session,
                usage: Usage::default(),
                backend,
            });
        }
        let operations = match crate::vm::link::install(admitted, &backend) {
            Ok(operations) => operations,
            Err(error) => {
                return Err(LoadError {
                    error: RuntimeError::Admission(error),
                    usage: Usage::default(),
                    backend,
                });
            }
        };
        let participant = match admitted.participant(entry, role) {
            Ok(participant) => participant,
            Err(error) => {
                return Err(LoadError {
                    error,
                    usage: Usage::default(),
                    backend,
                });
            }
        };
        let calls = (0..admitted.executable.calls).map(|_| None).collect();
        Ok(Self {
            admitted: admitted.clone(),
            participant,
            counts: Counts::new(admitted.executable.bindings.len()),
            backend: BackendOwner(Some(backend)),
            operations,
            calls,
            arguments: Vec::new(),
            usage: Usage::default(),
            ledger: Ledger::default(),
            value_budget,
            work_budget,
            next_frame: 0,
            frames: Vec::new(),
            pending_frame: None,
            role: role.to_owned(),
            returned: Scope::new(),
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn load(
        admitted: &Program,
        entry: &str,
        role: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> std::result::Result<Loaded<B>, LoadError<B>> {
        let mut instance = Self::new(
            admitted,
            entry,
            backend,
            role,
            session,
            value_budget,
            work_budget,
        )?;
        let start = (|| {
            let participant = instance.participant.clone();
            let frame = instance.entry_frame(Origin {
                session: session.into(),
                entry: entry.into(),
                instance: participant.instance.clone(),
                path: vec![],
            });
            let scope = instance.enter_participant(&frame, &inputs, Retention::Input)?;
            Ok::<_, RuntimeError>((frame, scope, participant.body.clone()))
        })();
        match start {
            Ok((frame, scope, body)) => Ok(Loaded {
                instance,
                frame,
                scope,
                body,
                inputs,
            }),
            Err(error) => Err(LoadError {
                error,
                usage: instance.usage(),
                backend: instance.take_backend(),
            }),
        }
    }

    /// Participant arguments are retained before backend entry. A refused entry
    /// releases live charges while preserving cumulative input work.
    pub(crate) fn enter_participant(
        &mut self,
        frame: &Frame,
        values: &[B::Value],
        retention: Retention,
    ) -> Result<Scope> {
        self.check_frame_depth()?;
        if frame.inputs().len() != values.len() {
            return Err(RuntimeError::Inputs);
        }
        self.validate_values(values, frame.inputs().iter().map(|(_, ty)| ty))?;
        let scope = self.open_scope(values, retention)?;
        if let Err(error) = self.enter_frame(frame, values) {
            self.close_scope(scope, values.iter());
            return Err(error);
        }
        Ok(scope)
    }

    /// Local entry checks capacity before custody. The evaluator opens the
    /// value scope after the preparation checkpoint, so replay and execution
    /// account for the same body lifetime.
    pub(crate) fn enter_local(&mut self, frame: &Frame, values: &[B::Value]) -> Result<()> {
        self.check_frame_depth()?;
        self.can_retain(values, Retention::Transfer)?;
        self.enter_frame(frame, values)
    }
}
