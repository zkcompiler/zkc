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
    ) -> Result<Vec<B::Value>> {
        self.instance.check_frame_depth()?;
        self.instance.can_retain(&args, Retention::Transfer)?;
        self.instance.enter_frame(frame, &args)?;
        let reused = key.as_ref().and_then(|key| self.reuse_computation(key));
        let (result, record) = if let Some(values) = reused {
            (Ok(values), None)
        } else {
            let checkpoint = key.as_ref().and_then(|key| self.begin_computation(key));
            let result = self.run_local_body(frame, logical_origin, body, args, depth);
            let record = match (key, checkpoint, &result) {
                (Some(key), Some((available, usage, frames, before)), Ok(values)) => self
                    .instance
                    .record_computation(key, available, usage, frames, before, values),
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
                    self.instance.unpin_return(&values);
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
    ) -> Result<Vec<B::Value>> {
        let mut scope = self.instance.open_scope(&args, Retention::Transfer)?;
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
                        let value = B::Value::from_control_bool(*value)?;
                        let value = self.instance.accept(value, &crate::vm::code::BOOL_TYPE)?;
                        self.instance.retain_in(
                            &mut scope,
                            std::slice::from_ref(&value),
                            Retention::Input,
                        )?;
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
                        let descriptor = ty
                            .logical()
                            .variant_descriptor()
                            .expect("admitted variant")
                            .clone();
                        let index = *alternative;
                        let payload = payload.iter().map(|n| env[n].clone()).collect();
                        let value = B::Value::pack_variant(descriptor, index, payload)?;
                        let value = self.instance.accept(value, ty)?;
                        self.instance.retain_in(
                            &mut scope,
                            std::slice::from_ref(&value),
                            Retention::Input,
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
                        let value = &env[input];
                        self.instance.validate_backend(value)?;
                        let (descriptor, alternative, mut args) = value.unpack_variant()?;
                        if value.physical_type().logical().variant_descriptor() != Some(&descriptor)
                        {
                            return Err(BackendError::new("variant-descriptor").into());
                        }
                        let arm = arms
                            .get(alternative)
                            .ok_or_else(|| BackendError::new("variant-alternative"))?;
                        let declared = descriptor
                            .alternatives()
                            .get(alternative)
                            .ok_or_else(|| BackendError::new("variant-alternative"))?;
                        if arm.alternative != declared.label()
                            || args.len() != declared.payload().len()
                        {
                            return Err(BackendError::new("variant-payload").into());
                        }
                        for (v, (_, ty)) in args.iter().zip(arm.body.inputs.iter()) {
                            self.instance.validate(v, ty, false)?;
                        }
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
                        self.accept_return(values, |runner, values| {
                            Self::matches_outputs(outputs, values)?;
                            runner
                                .instance
                                .retain_in(&mut scope, values, Retention::Transfer)?;
                            env.extend(outputs, values.iter().cloned());
                            Ok(())
                        })?;
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
                        self.accept_return(values, |runner, values| {
                            Self::matches_outputs(outputs, values)?;
                            runner
                                .instance
                                .retain_in(&mut scope, values, Retention::Transfer)?;
                            env.extend(outputs, values.iter().cloned());
                            Ok(())
                        })?;
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
                        let lower = env[lower].control_index()?;
                        let upper = env[upper].control_index()?;
                        if lower > Limits::PARAMETER
                            || upper > Limits::PARAMETER
                            || upper.saturating_sub(lower) > Limits::LOOP_COUNT
                        {
                            return Err(BackendError::new("exhausted:local-bound-limit").into());
                        }
                        let mut values = carried.iter().map(|n| env[n].clone()).collect::<Vec<_>>();
                        let mut pinned = false;
                        let result = (|| {
                            for index in lower..upper {
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
                                if pinned {
                                    self.instance.unpin_return(&values);
                                }
                                values = returned;
                                pinned = true;
                                if *conditional {
                                    let condition = values.remove(0);
                                    let continue_loop = condition.control_bool();
                                    self.instance.unpin_return(std::slice::from_ref(&condition));
                                    if !continue_loop? {
                                        break;
                                    }
                                }
                            }
                            Self::matches_outputs(outputs, &values)?;
                            self.instance
                                .retain_in(&mut scope, &values, Retention::Transfer)?;
                            env.extend(outputs, values.iter().cloned());
                            Ok::<(), RuntimeError>(())
                        })();
                        if pinned {
                            self.instance.unpin_return(&values);
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
        if let Ok(values) = &result {
            // Each value is already held by this region and validated by this
            // backend. Keep its shared subtree live while dropping the region's
            // bindings; the caller releases this reference on every exit path.
            self.instance.pin_return(values);
        }
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
    ) -> Result<Vec<B::Value>> {
        let mut origin = parent.origin().clone();
        origin.path.push(path);
        let frame = self.frame(origin, parent.shared_kind(), body.inputs.clone());
        let result = (|| {
            self.instance.check_frame_depth()?;
            let args = self
                .instance
                .accept_values(args, frame.inputs().iter().map(|(_, ty)| ty))?;
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
