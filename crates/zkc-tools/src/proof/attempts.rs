//! Repeated entry retains actual backend/provider state; only transcript and
//! tentative proof bytes belong to an individual attempt.
use super::*;
use zkc_runtime::{
    Outcome, Stop,
    attempt::{Controller, Decision, Limits as AttemptLimits},
    interactive::{Limits, Usage, ValueBudget, WorkBudget},
};

/// Application policy, independent of the candidate and its proof. Ports refer
/// to the original common-program signature, as in native invocation inputs.
#[derive(Clone, Debug)]
pub struct AttemptPolicy {
    /// Producer Boolean output: true completes; false requests another attempt.
    pub completion: usize,
    /// Every RNG input and its returned successor output, exactly once.
    pub rng: Vec<(usize, usize)>,
    pub limits: AttemptLimits,
    /// Cumulative interpreter work across all attempts.
    pub work: WorkBudget,
    /// Live payload limit per attempt; cumulative allocation charge per session.
    pub values: ValueBudget,
}

#[derive(Debug)]
pub struct AttemptRecord {
    pub attempt: u64,
    /// Returned decision or fatal execution/cleanup failure, never private outputs.
    pub decision: Result<bool>,
    pub usage: Usage,
    pub messages: usize,
    pub bytes: usize,
    /// Primitive work consumed by this attempt, including discarded trials and
    /// work completed before a fatal stop. Sum equals the invocation report.
    pub external_work: u64,
    pub transcript: Option<Json>,
    /// Successful entry-return coordinate; absent for the ordinary final return.
    pub return_at: Option<(zkc_runtime::interactive::Origin, String)>,
    pub stop: Option<zkc_runtime::interactive::Stop>,
}

pub(super) struct Plan {
    completion: usize,
    rng: Vec<(usize, usize)>,
    pub(super) policy: AttemptPolicy,
}
impl AttemptPolicy {
    /// Maximum completed or discarded trials in one invocation.
    pub const MAX_ATTEMPTS: u64 = 1024;
    /// Bounded array/string invocation format; parsing grants no deployment authority.
    pub fn parse(bytes: &[u8]) -> Result<Self> {
        let value = super::parse(bytes, 64 * 1024)?;
        let row = array(&value, 6)?;
        if text(&row[0])? != "zkc.native-attempt-policy/2" {
            return Err("native-attempt-policy".into());
        }
        let limits = array(&row[3], 2)?;
        let work = array(&row[4], 2)?;
        let values = array(&row[5], 2)?;
        let size = |v: &Json| {
            usize::try_from(natural(v)?).map_err(|_| String::from("native-attempt-limits"))
        };
        let pairs = list(&row[2])?;
        if pairs.len() > Limits::PORTS {
            return Err("native-attempt-rng-map".into());
        }
        Ok(Self {
            completion: index(&row[1])?,
            rng: pairs
                .iter()
                .map(|p| {
                    let p = array(p, 2)?;
                    Ok((index(&p[0])?, index(&p[1])?))
                })
                .collect::<Result<_>>()?,
            limits: AttemptLimits {
                attempts: natural(&limits[0])?,
                proof_bytes: size(&limits[1])?,
            },
            work: WorkBudget {
                instructions: natural(&work[0])?,
                iterations: natural(&work[1])?,
            },
            values: ValueBudget {
                live_bytes: size(&values[0])?,
                total_bytes: size(&values[1])?,
            },
        })
    }
    pub(super) fn identity(&self) -> String {
        let pairs: Vec<_> = self
            .rng
            .iter()
            .map(|(i, o)| json!([i.to_string(), o.to_string()]))
            .collect();
        let record = json!([
            "zkc.native-attempt-policy/2",
            self.completion.to_string(),
            pairs,
            [
                self.limits.attempts.to_string(),
                self.limits.proof_bytes.to_string()
            ],
            [
                self.work.instructions.to_string(),
                self.work.iterations.to_string()
            ],
            [
                self.values.live_bytes.to_string(),
                self.values.total_bytes.to_string()
            ]
        ]);
        hash(&serde_json::to_vec(&record).expect("array/string policy encodes"))
    }
    pub(super) fn check(&self, deployment: &NativeDeployment) -> Result<Plan> {
        if self.limits.attempts == 0
            || self.limits.attempts > Self::MAX_ATTEMPTS
            || self.limits.proof_bytes > super::MAX_PROOF_BYTES
            || self.work.instructions > deployment.capacity.work.instructions
            || self.work.iterations > deployment.capacity.work.iterations
            || self.values.live_bytes > deployment.capacity.values.live_bytes
            || self.values.total_bytes > deployment.capacity.values.total_bytes
        {
            return Err("native-attempt-limits".into());
        }
        let role = deployment.entry.producer();
        let map = &deployment.maps[&role.role];
        let completion = map
            .outputs
            .iter()
            .position(|p| p.original == self.completion)
            .filter(|&i| role.outputs[i].kind() == Type::Bool)
            .ok_or("native-attempt-completion")?;
        if role.inputs.iter().any(|(_, ty)| ty.kind() == Type::Nonce) {
            return Err("native-attempt-one-shot-input".into());
        }
        for (_, ty) in role.inputs.iter().take(map.data.len()) {
            if !matches!(
                input_kind(ty)?,
                "wire" | "verifier_key" | "prover_key_file" | "rng"
            ) {
                return Err("native-attempt-input-kind".into());
            }
        }
        if role
            .outputs
            .iter()
            .any(|ty| ty.is_affine() && !matches!(ty.kind(), Type::Rng | Type::Transcript))
        {
            return Err("native-attempt-output-kind".into());
        }
        let mut rng = Vec::new();
        for &(input, output) in &self.rng {
            let input = map
                .data
                .iter()
                .position(|p| p.original == input)
                .ok_or("native-attempt-rng-map")?;
            let output = map
                .outputs
                .iter()
                .position(|p| p.original == output)
                .ok_or("native-attempt-rng-map")?;
            if role.inputs[input].1.kind() != Type::Rng
                || role.inputs[input].1 != role.outputs[output]
                || rng.iter().any(|&(i, o)| i == input || o == output)
            {
                return Err("native-attempt-rng-map".into());
            }
            rng.push((input, output));
        }
        if role
            .inputs
            .iter()
            .filter(|(_, ty)| ty.kind() == Type::Rng)
            .count()
            != rng.len()
            || role
                .outputs
                .iter()
                .filter(|ty| ty.kind() == Type::Rng)
                .count()
                != rng.len()
        {
            return Err("native-attempt-rng-map".into());
        }
        Ok(Plan {
            completion,
            rng,
            policy: self.clone(),
        })
    }
}
struct State {
    // Taken only while Runner owns custody; restored on every outcome.
    backend: Option<NativeBackend>,
    inputs: Vec<Value>,
    usage: Usage,
    records: Vec<AttemptRecord>,
    cleanup: Vec<String>,
    cancelled: bool,
}
fn accumulate(total: &mut Usage, used: Usage) {
    total.instructions += used.instructions;
    total.iterations += used.iterations;
    total.total_value_bytes += used.total_value_bytes;
    total.live_values = used.live_values;
    total.live_value_bytes = used.live_value_bytes;
}

struct Session<'a> {
    deployment: &'a NativeDeployment,
    root: &'a [u8],
    binding: &'a [u8; 32],
    domain: Domain,
    transcript_budget: u64,
    registry: &'a ServiceRegistry,
    services: &'a [ServiceReference],
    plan: &'a Plan,
}
struct Executed {
    backend: NativeBackend,
    record: AttemptRecord,
    result: Result<(bool, driver::Produced<Value>)>,
    cleanup: Vec<String>,
    cancelled: bool,
}
impl Session<'_> {
    /// Returning backend custody is part of the result type on every path.
    fn run(
        &self,
        mut backend: NativeBackend,
        inputs: &mut [Value],
        used: Usage,
        attempt: u64,
    ) -> Executed {
        let mut cleanup = Vec::new();
        let external_work_before = backend.external_work_spent();
        let mut cancelled = false;
        let mut invocation_inputs = inputs.to_vec();
        let mut transcript = None;
        let mut record = AttemptRecord {
            attempt,
            decision: Ok(false),
            usage: Usage::default(),
            messages: 0,
            bytes: 0,
            external_work: 0,
            transcript: None,
            return_at: None,
            stop: None,
        };
        let issued = if let Some(ty) = self.deployment.entry.transcript() {
            backend
                .issue_transcript_for(
                    ty.logical().identity(),
                    self.domain.clone(),
                    self.transcript_budget,
                    self.root,
                )
                .map(|value| {
                    if let Value::Transcript(token) = &value {
                        transcript = Some(token.clone());
                    }
                    invocation_inputs.push(value);
                })
                .map_err(|e| e.to_string())
        } else {
            Ok(())
        };
        let issued = issued.and_then(|()| {
            if !self.services.is_empty() {
                let ports = self
                    .deployment
                    .entry
                    .producer()
                    .services
                    .iter()
                    .zip(self.services)
                    .map(|(port, reference)| (port.name.clone(), reference.clone()))
                    .collect();
                backend
                    .install_services(self.registry.clone(), ports)
                    .map_err(|e| e.to_string())?;
            }
            Ok(())
        });
        let mut result = match issued {
            Err(error) => Err(error),
            Ok(()) => {
                let work = WorkBudget {
                    instructions: self
                        .plan
                        .policy
                        .work
                        .instructions
                        .saturating_sub(used.instructions),
                    iterations: self
                        .plan
                        .policy
                        .work
                        .iterations
                        .saturating_sub(used.iterations),
                };
                let values = ValueBudget {
                    live_bytes: self.plan.policy.values.live_bytes,
                    total_bytes: self
                        .plan
                        .policy
                        .values
                        .total_bytes
                        .saturating_sub(used.total_value_bytes),
                };
                match Runner::new_with_budgets(
                    self.deployment.entry.admitted(),
                    self.deployment.entry.entry(),
                    &self.deployment.entry.producer().role,
                    "native-proof",
                    backend,
                    invocation_inputs,
                    values,
                    work,
                ) {
                    Err(failed) => {
                        record.usage = failed.usage;
                        backend = failed.backend;
                        Err(failed.error.to_string())
                    }
                    Ok(mut runner) => {
                        let produced = driver::produce_admitted_with_limit(
                            &mut runner,
                            self.binding,
                            self.plan.policy.limits.proof_bytes,
                            |backend, value| {
                                backend
                                    .encode_native_value(value)
                                    .map_err(driver::ArtifactFailure::NativeWire)
                            },
                        );
                        record.stop = produced.stop().cloned();
                        if let Some(stop) = &record.stop {
                            cleanup.extend(stop.cleanup_errors.iter().map(|e| e.to_string()));
                        }
                        record.return_at =
                            runner.early_return().map(|(o, s)| (o.clone(), s.into()));
                        record.usage = runner.usage();
                        record.messages = produced.messages;
                        record.bytes = produced.bytes;
                        cancelled |= produced.cancelled.is_some();
                        backend = runner.into_backend();
                        produced
                            .outcome
                            .map_err(|e| driver::failure(&e))
                            .and_then(|produced| {
                                for &(input, output) in &self.plan.rng {
                                    let (Value::Rng(before), Some(Value::Rng(after))) =
                                        (&inputs[input], produced.outputs.get(output))
                                    else {
                                        return Err("native-attempt-rng-successor".into());
                                    };
                                    backend
                                        .verify_successor(before, after)
                                        .map_err(|e| e.to_string())?;
                                }
                                let Some(Value::Bool(complete)) =
                                    produced.outputs.get(self.plan.completion)
                                else {
                                    return Err("native-attempt-completion".into());
                                };
                                for &(input, output) in &self.plan.rng {
                                    inputs[input] = produced.outputs[output].clone();
                                }
                                Ok((*complete, produced))
                            })
                    }
                }
            }
        };
        // Retire even after an exhausted scalar transition left no successor.
        if let Some(token) = transcript {
            match backend.retire(&token) {
                Ok(o) => {
                    record.transcript = Some(json!({"generation":o.generation,
            "transitions":o.draw_count,"budget":o.budget,"stage":o.stage}))
                }
                Err(e) => cleanup.push(e.to_string()),
            }
        }
        if backend.active_frames() != 0 {
            cleanup.push("native-proof-active-frames".into());
        }
        for reference in self.services {
            match self.registry.observe(reference) {
                Ok(o) if !o.leased && o.state.is_some() => {
                    if o.poisoned && result.is_ok() {
                        result = Err("native-attempt-service-poisoned".into());
                    }
                }
                Ok(_) => cleanup.push("native-attempt-service-state".into()),
                Err(e) => cleanup.push(e.to_string()),
            }
        }
        let result = result.and_then(|value| {
            if cleanup.is_empty() {
                Ok(value)
            } else {
                Err("native-proof-cleanup".into())
            }
        });
        record.external_work = backend.external_work_spent() - external_work_before;
        record.decision = result
            .as_ref()
            .map(|(complete, _)| *complete)
            .map_err(Clone::clone);
        Executed {
            backend,
            record,
            result,
            cleanup,
            cancelled,
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute(
    deployment: &NativeDeployment,
    backend: NativeBackend,
    inputs: Vec<Value>,
    root: &[u8],
    binding: &[u8; 32],
    domain: Domain,
    transcript_budget: u64,
    registry: &ServiceRegistry,
    services: &[ServiceReference],
    plan: &Plan,
    report: &mut NativeProofReport,
) -> NativeBackend {
    let session = Session {
        deployment,
        root,
        binding,
        domain,
        transcript_budget,
        registry,
        services,
        plan,
    };
    let state = State {
        backend: Some(backend),
        inputs,
        usage: Usage::default(),
        records: Vec::new(),
        cleanup: Vec::new(),
        cancelled: false,
    };
    let execution = Controller::<_, (), BTreeMap<usize, Value>>::new(state, plan.policy.limits)
        .advance(
            plan.policy.limits.attempts as usize + 1,
            |attempt, context| {
                let state = context.state_mut();
                let executed = session.run(
                    state.backend.take().expect("attempt owns backend"),
                    &mut state.inputs,
                    state.usage,
                    attempt,
                );
                state.backend = Some(executed.backend);
                accumulate(&mut state.usage, executed.record.usage);
                state.records.push(executed.record);
                state.cleanup.extend(executed.cleanup);
                state.cancelled |= executed.cancelled;
                match executed.result {
                    Err(_) => Err(Stop::Abort),
                    Ok((false, _)) => Ok(Decision::Retry(())),
                    Ok((true, produced)) => {
                        if let Err(reason) = context.append(&produced.proof) {
                            let state = context.state_mut();
                            let error = "native-attempt-buffer-limit".to_owned();
                            state
                                .records
                                .last_mut()
                                .expect("completed attempt")
                                .decision = Err(error);
                            return Err(reason);
                        }
                        Ok(Decision::Complete(deployment.original_outputs(
                            deployment.entry.producer(),
                            produced.outputs,
                        )))
                    }
                }
            },
        )
        .close();
    let mut state = execution.state;
    report.outcome = match execution.outcome {
        Outcome::Returned(proof) => {
            report.outputs = Some(proof.value);
            Ok(proof.bytes)
        }
        // Body and buffer failures are recorded before stopping. Reaching the
        // attempt bound instead leaves a normal retry as the last decision.
        Outcome::Stopped(_) => Err(state
            .records
            .last()
            .and_then(|record| record.decision.as_ref().err())
            .cloned()
            .unwrap_or_else(|| "native-attempt-limit".into())),
    };
    report.messages = state.records.iter().map(|r| r.messages).sum();
    report.bytes = state.records.iter().map(|r| r.bytes).sum();
    report.usage = state.usage;
    report.attempts = state.records;
    report.cleanup_errors = state.cleanup;
    report.cancelled = state.cancelled;
    state
        .backend
        .take()
        .expect("attempt returns backend custody")
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn attempt_policy_ingress_is_bounded_and_canonical() {
        let valid = br#"["zkc.native-attempt-policy/2","1",[["2","2"]],["4","1024"],["100","10"],["4096","8192"]]"#;
        let p = AttemptPolicy::parse(valid).unwrap();
        assert_eq!(p.rng, [(2, 2)]);
        assert_eq!(p.identity(), hash(valid));
        for bad in [b"{}".as_slice(), b"[]", &[b'['; 70], &vec![b' '; 65537]] {
            assert!(AttemptPolicy::parse(bad).is_err());
        }
        assert!(
            AttemptPolicy::parse(
                &String::from_utf8(valid.to_vec())
                    .unwrap()
                    .replace("\"4\"", "\"04\"")
                    .into_bytes()
            )
            .is_err()
        );
        let old = String::from_utf8(valid.to_vec())
            .unwrap()
            .replace("zkc.native-attempt-policy/2", "zkc.native-attempt-policy/1");
        assert_eq!(
            AttemptPolicy::parse(old.as_bytes()).unwrap_err(),
            "native-attempt-policy"
        );
        let triple = String::from_utf8(valid.to_vec())
            .unwrap()
            .replace("[\"100\",\"10\"]", "[\"100\",\"0\",\"10\"]");
        assert!(AttemptPolicy::parse(triple.as_bytes()).is_err());
        let mut changed = p.clone();
        changed.completion = 2;
        assert_ne!(p.identity(), changed.identity());
    }
}
