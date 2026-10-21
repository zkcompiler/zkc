//! Semantic frame custody and ordered cleanup.
use super::*;

pub(crate) struct RootFailure {
    pub error: RuntimeError,
    pub cleanup_errors: Vec<BackendError>,
}

impl<B: Backend> Instance<B> {
    /// Reserve terminal values before successful entry-frame exit. On failure,
    /// release that reservation and preserve the primary cause and cleanup order.
    /// The caller holds the return transfer across this operation.
    pub(crate) fn return_root(
        &mut self,
        frame: &Frame,
        values: &Transfer<B::Value>,
    ) -> std::result::Result<(), RootFailure> {
        debug_assert!(matches!(frame.kind(), FrameKind::Entry));
        if let Err(error) = self.retain_returned(values) {
            let cleanup = self.leave_frame(frame, FrameExit::Stopped, &[]);
            return Err(RootFailure {
                error,
                cleanup_errors: cleanup.err().into_iter().collect(),
            });
        }
        if let Err(error) = self.leave_frame_retained(frame, FrameExit::Returned, values) {
            self.release_returned(values);
            return Err(RootFailure {
                error: error.into(),
                cleanup_errors: vec![],
            });
        }
        Ok(())
    }
    /// A generic execution root with exact function ports and no participant
    /// services. Native backends retain their existing Entry custody contract.
    pub(crate) fn function_entry_frame(&mut self, origin: Origin, inputs: FrameInputs) -> Frame {
        let data = self.frame_data(origin, Arc::new(FrameKind::Entry), inputs);
        self.propose_frame(data)
    }
    pub(crate) fn entry_frame(&mut self, origin: Origin) -> Frame {
        let mut data = self.frame_data(
            origin,
            Arc::new(FrameKind::Entry),
            self.participant
                .as_ref()
                .expect("participant root")
                .inputs
                .clone()
                .into(),
        );
        data.services = self
            .participant
            .as_ref()
            .expect("participant root")
            .services
            .clone();
        self.propose_frame(data)
    }
    pub(crate) fn local_frame(
        &mut self,
        origin: Origin,
        kind: Arc<FrameKind>,
        inputs: FrameInputs,
    ) -> Frame {
        debug_assert!(matches!(kind.as_ref(), FrameKind::Local { .. }));
        let data = self.frame_data(origin, kind, inputs);
        self.propose_frame(data)
    }
    pub(crate) fn loop_frame(&mut self, origin: Origin, site: &str, iteration: u64) -> Frame {
        let inputs = self
            .admitted
            .loop_inputs(
                &self.participant.as_ref().expect("participant root").symbol,
                site,
            )
            .clone();
        let mut data = self.frame_data(
            origin,
            Arc::new(FrameKind::Loop {
                site: site.into(),
                iteration,
            }),
            inputs,
        );
        data.services = self.frames.last().expect("loop parent").services().to_vec();
        self.propose_frame(data)
    }
    fn propose_frame(&mut self, data: FrameData) -> Frame {
        let frame: Frame = data.into();
        self.pending_frame = Some(frame.clone());
        frame
    }
    fn frame_data(
        &mut self,
        origin: Origin,
        kind: Arc<FrameKind>,
        inputs: FrameInputs,
    ) -> FrameData {
        let parent = self.frames.last();
        self.counts.event(Event::Frame);
        self.next_frame += 1; // bounded by instruction/iteration/call ceilings
        FrameData {
            id: FrameId(self.next_frame),
            parent: parent.map(Frame::id),
            role: self.role.clone(),
            origin,
            kind,
            inputs,
            services: vec![],
        }
    }
    pub(crate) fn check_frame_depth(&self) -> Result<()> {
        if self.frames.len() >= Limits::STACK_DEPTH {
            Err(RuntimeError::Limit)
        } else {
            Ok(())
        }
    }
    pub(crate) fn enter_frame(&mut self, frame: &Frame, values: &[B::Value]) -> Result<()> {
        self.check_frame_depth()?;
        if frame.parent() != self.frames.last().map(Frame::id) {
            return Err(BackendError::new("vm-frame-parent").into());
        }
        if self
            .pending_frame
            .as_ref()
            .is_none_or(|pending| !pending.identical(frame))
        {
            return Err(BackendError::new("vm-frame-entry").into());
        }
        // A proposal authorizes one attempt. Backend refusal cannot make it
        // reusable, and equal instance-local IDs from another VM grant nothing.
        self.pending_frame = None;
        self.counts.event(Event::Enter);
        self.backend
            .enter_frame_retained(frame, values, self.ledger.view())?;
        self.frames.push(frame.clone());
        Ok(())
    }
    fn check_exit(&self, frame: &Frame) -> std::result::Result<(), BackendError> {
        if self.frames.last().is_none_or(|top| !top.identical(frame)) {
            return Err(BackendError::new("vm-frame-order"));
        }
        Ok(())
    }
    pub(crate) fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[B::Value],
    ) -> std::result::Result<(), BackendError> {
        self.check_exit(frame)?;
        self.counts.event(Event::Leave);
        let result = self.backend.leave_frame(frame, exit, values);
        self.frames.pop();
        result
    }
    pub(crate) fn leave_frame_retained(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[B::Value],
    ) -> std::result::Result<(), BackendError> {
        self.check_exit(frame)?;
        self.counts.event(Event::Leave);
        let result = self
            .backend
            .leave_frame_retained(frame, exit, values, self.ledger.view());
        self.frames.pop();
        result
    }
    /// Close actual entered views in order, then let the evaluator release each
    /// corresponding environment. Recovery and destruction use this same walk.
    pub(crate) fn unwind(
        &mut self,
        exit: FrameExit,
        mut release: impl FnMut(&mut Self, &Frame),
    ) -> Vec<BackendError> {
        let mut errors = Vec::new();
        while let Some(frame) = self.frames.last().cloned() {
            if let Err(error) = self.leave_frame(&frame, exit, &[]) {
                errors.push(error);
            }
            release(self, &frame);
        }
        errors
    }
}
