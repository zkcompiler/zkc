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

pub(crate) struct LoadedLocal<B: Backend> {
    pub instance: Instance<B>,
    pub frame: Frame,
    pub scope: Scope,
    pub code: Arc<crate::vm::code::Function>,
    pub inputs: Vec<B::Value>,
}

pub(crate) enum Installation {
    FullProgram,
    SelectedRoot,
}

enum InitializationRoot<'a> {
    Participant {
        entry: &'a str,
        role: &'a str,
        installation: Installation,
    },
    Local(&'a str),
}

impl<B: Backend> Instance<B> {
    #[cfg(test)]
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
        Self::initialize(
            admitted,
            InitializationRoot::Participant {
                entry,
                role,
                installation: Installation::FullProgram,
            },
            session,
            backend,
            value_budget,
            work_budget,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn initialize(
        admitted: &Program,
        root: InitializationRoot<'_>,
        session: &str,
        backend: B,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
        shared: Option<ExecutionLedger>,
    ) -> std::result::Result<Self, LoadError<B>> {
        let start = (|| {
            if work_budget.instructions > Limits::INSTRUCTIONS
                || work_budget.iterations > Limits::ITERATIONS
                || work_budget.logical_bytes > Limits::LOGICAL_BYTES
            {
                return Err(RuntimeError::Limit);
            }
            if session.is_empty()
                || session.len() > 128
                || !session
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
            {
                return Err(RuntimeError::Session);
            }
            let operations = match &root {
                InitializationRoot::Local(function) => {
                    crate::vm::link::install_local(admitted, function, &backend)
                }
                InitializationRoot::Participant {
                    entry,
                    role,
                    installation,
                } => match installation {
                    Installation::SelectedRoot => {
                        crate::vm::link::install_role(admitted, entry, role, &backend)
                    }
                    Installation::FullProgram => crate::vm::link::install(admitted, &backend)
                        .map(|operations| operations.into_iter().map(Some).collect()),
                },
            }
            .map_err(RuntimeError::Admission)?;
            let participant = match &root {
                InitializationRoot::Participant { entry, role, .. } => {
                    Some(admitted.participant(entry, role)?)
                }
                InitializationRoot::Local(_) => None,
            };
            let live = shared
                .as_ref()
                .map(|ledger| ledger.reserve_live(value_budget.live_bytes))
                .transpose()?;
            Ok((operations, participant, live))
        })();
        let (operations, participant, live_reservation) = match start {
            Ok(loaded) => loaded,
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
            shared,
            live_reservation,
            arguments: Vec::new(),
            usage: Usage::default(),
            ledger: Ledger::default(),
            value_budget,
            work_budget,
            next_frame: 0,
            frames: Vec::new(),
            pending_frame: None,
            role: match root {
                InitializationRoot::Participant { role, .. } => role,
                InitializationRoot::Local(_) => "",
            }
            .to_owned(),
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
        Self::load_role(
            admitted,
            entry,
            role,
            session,
            backend,
            inputs,
            value_budget,
            work_budget,
            Installation::FullProgram,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn load_role(
        admitted: &Program,
        entry: &str,
        role: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
        installation: Installation,
        shared: Option<ExecutionLedger>,
    ) -> std::result::Result<Loaded<B>, LoadError<B>> {
        let mut instance = Self::initialize(
            admitted,
            InitializationRoot::Participant {
                entry,
                role,
                installation,
            },
            session,
            backend,
            value_budget,
            work_budget,
            shared,
        )?;
        let start = (|| {
            let participant = instance
                .participant
                .as_ref()
                .expect("participant root")
                .clone();
            let frame = instance.entry_frame(Origin {
                session: session.into(),
                entry: entry.into(),
                instance: participant.instance.clone(),
                path: vec![],
            });
            let scope = instance.enter_root(&frame, &inputs, Retention::Input)?;
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
            Err(error) => {
                // The consumed inputs may be their payloads' final owners.
                // Backend recovery releases the live allowance only afterward.
                drop(inputs);
                Err(LoadError {
                    error,
                    usage: instance.usage(),
                    backend: instance.take_backend(),
                })
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn load_local(
        admitted: &Program,
        function: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
        shared: Option<ExecutionLedger>,
    ) -> std::result::Result<LoadedLocal<B>, LoadError<B>> {
        let mut instance = Self::initialize(
            admitted,
            InitializationRoot::Local(function),
            session,
            backend,
            value_budget,
            work_budget,
            shared,
        )?;
        let code = admitted.function(function);
        let start = (|| {
            let frame = instance.function_entry_frame(
                Origin {
                    session: session.into(),
                    entry: function.into(),
                    instance: function.into(),
                    path: vec![],
                },
                code.body.inputs.clone(),
            );
            let scope = instance.enter_root(&frame, &inputs, Retention::Input)?;
            Ok((frame, scope))
        })();
        match start {
            Ok((frame, scope)) => Ok(LoadedLocal {
                instance,
                frame,
                scope,
                code,
                inputs,
            }),
            Err(error) => {
                drop(inputs);
                Err(LoadError {
                    error,
                    usage: instance.usage(),
                    backend: instance.take_backend(),
                })
            }
        }
    }

    /// Root and participant-region arguments are retained before backend entry. A refused entry
    /// releases live charges while preserving cumulative input work.
    pub(crate) fn enter_root(
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
    pub(crate) fn enter_local(
        &mut self,
        frame: &Frame,
        values: &[B::Value],
    ) -> Result<Option<crate::vm::execution_ledger::AllocationReservation>> {
        self.check_frame_depth()?;
        let charge = self.can_retain(values, Retention::Transfer)?;
        let reservation = self
            .shared
            .as_ref()
            .map(|ledger| ledger.reserve_output(charge.fresh, false));
        let reservation = match reservation {
            Some(reservation) if reservation.bytes() < charge.fresh => {
                reservation.settle(0, 0)?;
                return Err(RuntimeError::Limit);
            }
            reservation => reservation,
        };
        self.enter_frame(frame, values)?;
        Ok(reservation)
    }
}
