//! Local VM code evaluation. Calls and accounting go through the instance.
use super::*;

impl<B: Backend> Runner<B> {
    /// Execute one accepted local frame, preserving the original failure and
    /// recording cleanup failures in actual inner-to-outer leave order.
    pub(super) fn run_local_frame(
        &mut self,
        frame: &Frame,
        logical_origin: &LogicalOrigin,
        body: &LocalCode,
        args: Vec<B::Value>,
        depth: usize,
        key: Option<crate::vm::preparation::Key>,
    ) -> Result<Transfer<B::Value>> {
        let reservation = self.instance.enter_local(frame, &args)?;
        let reused = key.as_ref().and_then(|key| self.reuse_computation(key));
        let (result, record) = if let Some(values) = reused {
            (Ok(values), None)
        } else {
            let checkpoint = key.and_then(|key| self.begin_computation(key));
            let result = self.run_local_body(frame, logical_origin, body, args, depth, reservation);
            let record = match (checkpoint, &result) {
                (Some(recording), Ok(values)) => {
                    self.instance.record_computation(recording, values)
                }
                _ => None,
            };
            (result, record)
        };
        let (exit, returned) = match &result {
            Ok(values) => (FrameExit::Returned, values.as_slice()),
            Err(_) => (FrameExit::Stopped, &[][..]),
        };
        let leave = self.instance.leave_frame_retained(frame, exit, returned);
        match result {
            Ok(values) => {
                if let Err(error) = leave {
                    self.instance.release_return(values);
                    return Err(error.into());
                }
                self.publish_computation(record);
                Ok(values)
            }
            Err(error) => {
                if let Err(cleanup) = leave {
                    self.local_cleanup_errors.push(cleanup);
                }
                Err(error)
            }
        }
    }
    fn run_local_body(
        &mut self,
        frame: &Frame,
        logical_origin: &LogicalOrigin,
        body: &LocalCode,
        args: Vec<B::Value>,
        depth: usize,
        reservation: Option<crate::vm::execution_ledger::AllocationReservation>,
    ) -> Result<Transfer<B::Value>> {
        let mut scope =
            self.instance
                .open_reserved_scope(&args, Retention::Transfer, reservation)?;
        let mut env = Values::new(args);
        let mut current_site = None;
        let mut current_has_own_site = false;
        let result = (|| {
            for instruction in &body.instructions {
                current_has_own_site = matches!(
                    instruction,
                    Operation::BoolConstant { .. }
                        | Operation::Conditional { .. }
                        | Operation::For { .. }
                        | Operation::Match { .. }
                        | Operation::Stop { .. }
                );
                current_site = match instruction {
                    Operation::BoolConstant { site, .. }
                    | Operation::Variant { site, .. }
                    | Operation::Match { site, .. }
                    | Operation::Stop { site, .. }
                    | Operation::Conditional { site, .. }
                    | Operation::For { site, .. } => Some(site.as_str()),
                    Operation::Op { call, .. } => Some(call.site.as_str()),
                    _ => None,
                };
                if let Operation::Release(names) = instruction {
                    self.instance.counts().instruction(instruction);
                    for name in names {
                        // Admission independently excludes resources and future reads.
                        // Removing ordinary immutable storage has no backend effect.
                        let value = env.remove(name).expect("admitted storage release");
                        // The binding's storage stays charged until frame cleanup.
                        // Its ledger entries go now, so a later allocation that
                        // reuses a freed address is charged as fresh storage.
                        self.instance.release_storage(&mut scope, &value);
                    }
                    continue;
                }
                self.instance.tick()?;
                self.instance.counts().instruction(instruction);
                match instruction {
                    Operation::BoolConstant { output, value, .. } => {
                        let value = self.instance.boolean(&mut scope, *value)?;
                        env.insert(*output, value);
                    }
                    Operation::Stop { reason, .. } => {
                        return Err(RuntimeError::ExplicitStop(reason.clone()));
                    }
                    Operation::Variant {
                        ty,
                        alternative,
                        payload,
                        output,
                        ..
                    } => {
                        let value = self.instance.variant(
                            &mut scope,
                            ty,
                            *alternative,
                            payload.iter().map(|n| &env[n]),
                        )?;
                        env.insert(*output, value);
                    }
                    Operation::Match {
                        site,
                        input,
                        captures,
                        arms,
                        outputs,
                    } => {
                        let (arm, mut args) = self.instance.match_variant(&env[input], arms)?;
                        args.extend(captures.iter().map(|n| env[n].clone()));
                        let values = self.run_local_region(
                            frame,
                            logical_origin,
                            &arm.body,
                            args,
                            PathElement::Match {
                                site: site.clone(),
                                alternative: arm.alternative.clone(),
                            },
                            depth,
                        )?;
                        let values =
                            self.instance
                                .bind_return(&mut scope, outputs.len(), values)?;
                        env.extend(outputs, values.into_iter());
                    }
                    Operation::Op {
                        call,
                        inputs,
                        outputs,
                    } => {
                        let values = self.instance.invoke(
                            &mut scope,
                            logical_origin,
                            call,
                            inputs.iter().map(|n| env[n].clone()),
                        )?;
                        env.extend(outputs, values.into_iter());
                    }
                    Operation::Conditional {
                        site,
                        condition,
                        captures,
                        then_body,
                        else_body,
                        outputs,
                    } => {
                        let taken = env[condition].control_bool()?;
                        let args = captures.iter().map(|n| env[n].clone()).collect::<Vec<_>>();
                        let values = self.run_local_region(
                            frame,
                            logical_origin,
                            if taken { then_body } else { else_body },
                            args,
                            PathElement::Conditional {
                                site: site.clone(),
                                taken,
                            },
                            depth,
                        )?;
                        let values =
                            self.instance
                                .bind_return(&mut scope, outputs.len(), values)?;
                        env.extend(outputs, values.into_iter());
                    }
                    Operation::For {
                        conditional,
                        site,
                        lower,
                        upper,
                        carried,
                        captures,
                        body,
                        outputs,
                    } => {
                        let range = Instance::<B>::local_range(&env[lower], &env[upper])?;
                        let mut initial =
                            carried.iter().map(|n| env[n].clone()).collect::<Vec<_>>();
                        let mut carried: Option<Transfer<B::Value>> = None;
                        let result = (|| {
                            for index in range {
                                if let Err(error) = self.instance.iteration() {
                                    let mut origin = frame.origin().clone();
                                    origin.path.push(PathElement::For {
                                        site: site.clone(),
                                        index,
                                    });
                                    self.local_failure = Some((site.clone(), origin));
                                    return Err(error);
                                }
                                let mut args = vec![self.instance.index_value(index)?];
                                let values = carried
                                    .as_ref()
                                    .map_or(initial.as_slice(), Transfer::as_slice);
                                args.extend(values.iter().cloned());
                                args.extend(captures.iter().map(|n| env[n].clone()));
                                let returned = self.run_local_region(
                                    frame,
                                    logical_origin,
                                    body,
                                    args,
                                    PathElement::For {
                                        site: site.clone(),
                                        index,
                                    },
                                    depth,
                                )?;
                                if let Some(previous) = carried.replace(returned) {
                                    self.instance.release_return(previous);
                                } else {
                                    initial = Vec::new();
                                }
                                if *conditional
                                    && !self
                                        .instance
                                        .take_condition(carried.as_mut().expect("returned carry"))?
                                {
                                    break;
                                }
                            }
                            let values = if let Some(values) = carried.take() {
                                self.instance
                                    .bind_return(&mut scope, outputs.len(), values)?
                            } else {
                                Self::matches_outputs(outputs, &initial)?;
                                self.instance.retain_in(
                                    &mut scope,
                                    &initial,
                                    Retention::Transfer,
                                )?;
                                initial
                            };
                            env.extend(outputs, values.into_iter());
                            Ok::<(), RuntimeError>(())
                        })();
                        if let Some(values) = carried {
                            self.instance.release_return(values);
                        }
                        result?;
                    }
                    Operation::Release(_) => unreachable!("handled without a tick"),
                    Operation::Return(names) | Operation::Yield(names) => {
                        return Ok(names.iter().map(|n| env[n].clone()).collect::<Vec<_>>());
                    }
                }
            }
            unreachable!("admitted local terminator")
        })();
        if result.is_err() && self.local_failure.is_none() && (depth > 1 || current_has_own_site) {
            let site = current_site.map(str::to_owned).unwrap_or_else(|| {
                match frame.origin().path.last() {
                    Some(
                        PathElement::Conditional { site, .. }
                        | PathElement::For { site, .. }
                        | PathElement::Match { site, .. },
                    ) => site.clone(),
                    _ => String::new(),
                }
            });
            self.local_failure = Some((site, frame.origin().clone()));
        }
        // Keep the owned return tuple and its backing obligation together while
        // closing this environment. The receiver consumes the transfer once.
        let result = result.map(|values| self.instance.hold_return(values));
        // Deferred storage charges survive physical release, including on every early error.
        self.instance.close_scope(scope, env.values());
        result
    }
    #[allow(clippy::too_many_arguments)]
    fn run_local_region(
        &mut self,
        parent: &Frame,
        logical_origin: &LogicalOrigin,
        body: &LocalCode,
        args: Vec<B::Value>,
        path: PathElement,
        depth: usize,
    ) -> Result<Transfer<B::Value>> {
        let mut origin = parent.origin().clone();
        origin.path.push(path);
        let frame = self.local_frame(origin, parent.shared_kind(), body.inputs.clone());
        let result = (|| {
            self.instance.check_frame_depth()?;
            self.instance
                .validate_values(&args, frame.inputs().iter().map(|(_, ty)| ty))?;
            self.run_local_frame(&frame, logical_origin, body, args, depth + 1, None)
        })();
        if result.is_err() && self.local_failure.is_none() {
            let site = match frame.origin().path.last() {
                Some(
                    PathElement::Conditional { site, .. }
                    | PathElement::For { site, .. }
                    | PathElement::Match { site, .. },
                ) => site.clone(),
                _ => String::new(),
            };
            self.local_failure = Some((site, frame.origin().clone()));
        }
        result
    }
}
