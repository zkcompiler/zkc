//! A role-free execution root for the maintained numerical Local evaluator.
use super::*;

/// One admitted Local function and one owned backend. There are no synthetic
/// participants, service ports, messages or protocols. Loading validates
/// inputs; `execute` performs the body once and preserves a stable terminal cut.
pub struct LocalRunner<B: Backend> {
    runner: Runner<B>,
    initial: Option<LocalInvocation<B::Value>>,
}
struct LocalInvocation<V> {
    frame: Frame,
    scope: Scope,
    code: Arc<crate::vm::code::Function>,
    inputs: Vec<V>,
}
impl<B: Backend> LocalRunner<B> {
    pub fn new(
        program: &Program,
        function: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
    ) -> std::result::Result<Self, LoadError<B>> {
        Self::new_with_budgets(
            program,
            function,
            session,
            backend,
            inputs,
            ValueBudget::default(),
            WorkBudget::default(),
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_budgets(
        program: &Program,
        function: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        values: ValueBudget,
        work: WorkBudget,
    ) -> std::result::Result<Self, LoadError<B>> {
        Self::new_with_ledger(
            program, function, session, backend, inputs, values, work, None,
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_ledger(
        program: &Program,
        function: &str,
        session: &str,
        backend: B,
        inputs: Vec<B::Value>,
        values: ValueBudget,
        work: WorkBudget,
        ledger: Option<ExecutionLedger>,
    ) -> std::result::Result<Self, LoadError<B>> {
        let loaded = Instance::load_local(
            program, function, session, backend, inputs, values, work, ledger,
        )?;
        Ok(Self {
            runner: Runner {
                root: loaded.frame.origin().clone(),
                instance: loaded.instance,
                preparation: None,
                stack: vec![],
                pending: None,
                local_failure: None,
                local_cleanup_errors: vec![],
                early_return: None,
            },
            initial: Some(LocalInvocation {
                frame: loaded.frame,
                scope: loaded.scope,
                code: loaded.code,
                inputs: loaded.inputs,
            }),
        })
    }
    /// Synchronous local evaluation; repeated inspection performs no more work.
    pub fn execute(&mut self) -> &Action<B::Value> {
        if let Some(LocalInvocation {
            frame,
            scope,
            code,
            inputs,
        }) = self.initial.take()
        {
            let local = self.runner.instance.local_frame(
                frame.origin().clone(),
                Arc::new(FrameKind::Local {
                    site: frame.origin().entry.clone(),
                    function: frame.origin().entry.clone(),
                }),
                code.body.inputs.clone(),
            );
            let result = self.runner.run_local_frame(
                &local,
                &code.origin,
                &code.body,
                inputs.clone(),
                1,
                None,
            );
            let result = match result {
                Ok(values) => match self.runner.instance.return_root(&frame, &values) {
                    Ok(()) => Ok(values),
                    Err(failure) => {
                        self.runner
                            .local_cleanup_errors
                            .extend(failure.cleanup_errors);
                        self.runner.instance.release_return(values);
                        Err(failure.error)
                    }
                },
                Err(error) => {
                    if let Err(cleanup) =
                        self.runner
                            .instance
                            .leave_frame(&frame, FrameExit::Stopped, &[])
                    {
                        self.runner.local_cleanup_errors.push(cleanup);
                    }
                    Err(error)
                }
            };
            self.runner.instance.close_scope(scope, inputs.iter());
            drop(inputs);
            match result {
                Ok(values) => {
                    let values = self.runner.instance.release_return(values);
                    self.runner.pending = Some(Action::Returned(values));
                }
                Err(error) => {
                    let (site, origin) = self
                        .runner
                        .local_failure
                        .take()
                        .unwrap_or_else(|| (String::new(), frame.origin().clone()));
                    self.runner
                        .failed(error, Some(frame.origin().entry.clone()), Some(origin));
                    if let Some(Action::Stopped(stop)) = self.runner.pending.as_mut() {
                        stop.local = Some(Box::new(LocalContext {
                            site: frame.origin().entry.clone(),
                            function: frame.origin().entry.clone(),
                            instruction: (!site.is_empty()).then_some(site),
                        }));
                        stop.cleanup_errors
                            .splice(0..0, self.runner.local_cleanup_errors.drain(..));
                    }
                }
            }
        }
        self.runner.pending.as_ref().expect("local terminal action")
    }
    pub fn usage(&self) -> Usage {
        self.runner.usage()
    }
    pub fn execution_counts(&self) -> ExecutionCounts {
        self.runner.execution_counts()
    }
    pub fn backend(&self) -> &B {
        self.runner.backend()
    }
    pub fn root_origin(&self) -> &Origin {
        self.runner.root_origin()
    }
    pub fn stop(&self) -> Option<&Stop> {
        self.runner.stop()
    }
    pub fn returned_values(&self) -> Option<&[B::Value]> {
        self.runner.returned_values()
    }
    pub fn is_terminal(&self) -> bool {
        self.runner.is_terminal()
    }
    pub fn cancel(&mut self) {
        if let Some(LocalInvocation { scope, inputs, .. }) = self.initial.take() {
            // The root input scope is owned here, outside Runner's stack.
            // Keep its allowance through both unwind and payload destruction.
            let reservation = self.runner.instance.take_live_reservation();
            self.runner.cancel();
            self.runner.instance.close_scope(scope, inputs.iter());
            drop(inputs);
            drop(reservation);
        } else {
            self.runner.cancel();
        }
    }
    pub fn into_backend(mut self) -> B {
        self.cancel();
        self.runner.discard_returned();
        self.runner.instance.take_backend()
    }
    /// Move successful values and their live allowance to the parent Host.
    /// An unexecuted function is cancelled; callers execute explicitly first.
    pub fn into_retained_outputs(mut self) -> (B, Option<RetainedOutputs<B::Value>>) {
        self.cancel();
        let outputs = match self.runner.pending.take() {
            Some(Action::Returned(values)) => {
                self.runner.instance.release_returned(&values);
                Some(RetainedOutputs {
                    values,
                    reservation: self.runner.instance.take_live_reservation(),
                })
            }
            terminal => {
                self.runner.pending = terminal;
                None
            }
        };
        if outputs.is_some() {
            self.runner.pending = Some(Action::Returned(vec![]));
        }
        (self.runner.instance.take_backend(), outputs)
    }
}
impl<B: Backend> Drop for LocalRunner<B> {
    fn drop(&mut self) {
        self.cancel();
    }
}
