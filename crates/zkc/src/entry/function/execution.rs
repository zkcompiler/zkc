use super::{
    carrier::{Block, Operation},
    *,
};
use serde_json::{Value as Json, json};
use zkc_runtime::interpreter::LocalRunner;
use zkc_runtime::vm::{ExecutionLedger, ExecutionLedgerUsage, Value as RuntimeValue, WorkBudget};

#[derive(Clone, Debug)]
pub struct CallReceipt {
    pub target: String,
    pub operation: String,
    pub path: Vec<String>,
    pub completed: bool,
    pub native: Json,
}
#[derive(Clone, Debug)]
pub struct FunctionFailure {
    pub code: String,
    pub path: Vec<String>,
    pub native: Option<Json>,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct FunctionUsage {
    pub execution: ExecutionLedgerUsage,
    pub dispatches: usize,
    pub wire_bytes: usize,
    pub proof_bytes: usize,
    pub external_work: u64,
    pub ring_work: u64,
    pub sequence_work: u64,
    pub service_draws: u64,
    pub service_allowances: u64,
}
#[must_use = "inspect failure and the stopped prefix before using the source result"]
pub struct FunctionReport {
    pub value: Option<TypedValue>,
    pub failure: Option<FunctionFailure>,
    pub usage: FunctionUsage,
    pub calls: Vec<CallReceipt>,
    pub journal_truncated: bool,
    /// Optional native observations merged across reached children only.
    pub execution_counts: zkc_runtime::vm::ExecutionCounts,
    _journal_live: Vec<zkc_runtime::vm::LiveReservation>,
}
impl FunctionReport {
    pub fn is_success(&self) -> bool {
        self.failure.is_none() && self.value.is_some()
    }
    pub fn into_result(self) -> std::result::Result<Self, Box<Self>> {
        if self.is_success() {
            Ok(self)
        } else {
            Err(Box::new(self))
        }
    }
    pub fn diagnostics(&self) -> Json {
        json!({"format":"zkc.entry-function-result/0","completed":self.is_success(),
            "failure":self.failure.as_ref().map(|f|json!({"code":f.code,"path":f.path,"native":f.native})),
            "usage":{"instructions":self.usage.execution.instructions,"iterations":self.usage.execution.iterations,
                "logical_bytes":self.usage.execution.logical_bytes,"fresh_bytes":self.usage.execution.total_value_bytes,
                "live_reserved_bytes":self.usage.execution.live_reserved_bytes,"dispatches":self.usage.dispatches,
                "wire_bytes":self.usage.wire_bytes,"proof_bytes":self.usage.proof_bytes,"external_work":self.usage.external_work,
                "ring_work":self.usage.ring_work,"sequence_work":self.usage.sequence_work,"service_draws":self.usage.service_draws,"service_allowances":self.usage.service_allowances},
            "calls":self.calls.iter().map(|c|json!({"target":c.target,"operation":c.operation,"path":c.path,"completed":c.completed,"native":c.native})).collect::<Vec<_>>(),
            "journal_truncated":self.journal_truncated})
    }
}
pub struct PreparedFunction<'a> {
    host: &'a EntryHost,
    arguments: Vec<TypedValue>,
    context: InvocationContext,
    pub(super) ledger: ExecutionLedger,
    context_live: Option<zkc_runtime::vm::LiveReservation>,
}
impl EntryHost {
    pub fn prepare(&self, mut request: FunctionRequest) -> Result<PreparedFunction<'_>> {
        require(
            request.arguments.len() == self.signature().parameters.len(),
            "entry-host-argument-names",
        )?;
        let ledger = ExecutionLedger::new(
            self.options.limits.capacity.values,
            self.options.limits.capacity.work,
        );
        let context_live = zkc_runtime::host::wire::reserve_allocation(
            Some(&ledger),
            deployment::context_bytes(&request.context),
        )
        .map_err(|e| EntryError::new(EntryPhase::Preparation, e))?;
        deployment::context_check(self, &request.context, &ledger)?;
        let arguments = self
            .signature()
            .parameters
            .iter()
            .map(|p| {
                self.interface.check_input(&p.schema)?;
                let value = request
                    .arguments
                    .remove(&p.name)
                    .ok_or_else(|| error("entry-host-argument-names"))?;
                data::import(self, &p.schema, value, &ledger)
                    .map_err(|e| EntryError::new(EntryPhase::Preparation, e))
            })
            .collect::<Result<_>>()?;
        Ok(PreparedFunction {
            host: self,
            arguments,
            context: request.context,
            ledger,
            context_live,
        })
    }
}
impl PreparedFunction<'_> {
    pub fn execute(self) -> FunctionReport {
        let mut execution = Execution {
            host: self.host,
            context: self.context,
            ledger: self.ledger,
            path: vec![],
            usage: FunctionUsage::default(),
            calls: vec![],
            truncated: false,
            last_native: None,
            _context_live: self.context_live,
            journal_live: vec![],
            execution_counts: Default::default(),
        };
        // Reserve bounded native observation scratch even when the retained
        // journal is disabled or full. A final failure still carries its stop.
        let returned = match zkc_runtime::host::wire::reserve_allocation(
            Some(&execution.ledger),
            crate::host::diagnostics::SCRATCH_BYTES,
        ) {
            Ok(live) => {
                execution.journal_live.extend(live);
                execution.function(&self.host.entry, self.arguments)
            }
            Err(error) => Err(execution.fail(error)),
        };
        let (value, failure) = match returned {
            Ok(v) => (Some(v), None),
            Err(e) => (None, Some(e)),
        };
        execution.usage.execution = execution.ledger.snapshot();
        FunctionReport {
            value,
            failure,
            usage: execution.usage,
            calls: execution.calls,
            journal_truncated: execution.truncated,
            _journal_live: execution.journal_live,
            execution_counts: execution.execution_counts,
        }
    }
}
struct Execution<'a> {
    host: &'a EntryHost,
    context: InvocationContext,
    ledger: ExecutionLedger,
    path: Vec<String>,
    usage: FunctionUsage,
    calls: Vec<CallReceipt>,
    truncated: bool,
    last_native: Option<Json>,
    _context_live: Option<zkc_runtime::vm::LiveReservation>,
    journal_live: Vec<zkc_runtime::vm::LiveReservation>,
    execution_counts: zkc_runtime::vm::ExecutionCounts,
}
type ExecResult<T> = std::result::Result<T, FunctionFailure>;
impl Execution<'_> {
    fn fail(&self, code: impl ToString) -> FunctionFailure {
        FunctionFailure {
            code: code.to_string(),
            path: self.path.clone(),
            native: self.last_native.clone(),
        }
    }
    fn charge(&self, instructions: u64, iterations: u64) -> ExecResult<()> {
        self.ledger
            .charge(
                WorkBudget {
                    instructions,
                    iterations,
                    logical_bytes: 0,
                },
                0,
            )
            .map_err(|e| self.fail(e))
    }
    fn function(&mut self, symbol: &str, arguments: Vec<TypedValue>) -> ExecResult<TypedValue> {
        let _frame = zkc_runtime::host::wire::reserve_allocation(
            Some(&self.ledger),
            symbol
                .len()
                .saturating_add(arguments.len() * 512)
                .saturating_add(512),
        )
        .map_err(|e| self.fail(e))?;
        self.path.push(symbol.into());
        self.charge(1, 0)?;
        let f = self
            .host
            .functions
            .iter()
            .find(|f| f.signature.symbol == symbol)
            .expect("admitted static function");
        let result = self.block(&f.body, arguments).map(|mut v| v.remove(0));
        self.path.pop();
        result
    }
    fn block(&mut self, b: &Block, arguments: Vec<TypedValue>) -> ExecResult<Vec<TypedValue>> {
        let slots = b.arguments.len()
            + b.operations
                .iter()
                .map(|op| op.results().len())
                .sum::<usize>();
        let _environment =
            zkc_runtime::host::wire::reserve_allocation(Some(&self.ledger), slots * 512 + 512)
                .map_err(|e| self.fail(e))?;
        let mut env: BTreeMap<_, _> = b.arguments.iter().map(|a| a.id).zip(arguments).collect();
        for (index, op) in b.operations.iter().enumerate() {
            self.path.push(format!("operation:{index}"));
            self.last_native = None;
            self.charge(1, 0)?;
            let _operands = zkc_runtime::host::wire::reserve_allocation(
                Some(&self.ledger),
                (op.operands().len() + op.results().len()) * 512 + 512,
            )
            .map_err(|e| self.fail(e))?;
            let values = op
                .operands()
                .iter()
                .map(|i| env[i].clone())
                .collect::<Vec<_>>();
            let results = match op {
                Operation::Construct {
                    alternative,
                    results,
                    ..
                } => vec![
                    data::pack(
                        self.host,
                        &results[0].schema,
                        alternative,
                        values,
                        &self.ledger,
                    )
                    .map_err(|e| self.fail(e))?,
                ],
                Operation::Project { path, .. } => {
                    let mut v = values[0].clone();
                    for i in path {
                        v = v.fields()[*i as usize].clone();
                    }
                    vec![v]
                }
                Operation::Unpack { .. } => values[0].fields().to_vec(),
                Operation::Call { callee, .. } => {
                    let receipt = self.begin(callee, "entry")?;
                    self.dispatch().map_err(|f| self.failed_call(f))?;
                    let result = self.function(callee, values);
                    self.end(receipt, result.is_ok(), json!({}));
                    vec![result?]
                }
                Operation::Numeric { calculation, .. } => self
                    .numeric(calculation, values)
                    .map_err(|f| self.failed_call(f))?,
                Operation::Invoke { deployment, .. } => vec![
                    self.invoke(deployment, &values)
                        .map_err(|f| self.failed_call(f))?,
                ],
                Operation::If { regions, .. } => self.block(
                    &regions[usize::from(!values[0].boolean())],
                    values[1..].to_vec(),
                )?,
                Operation::Match {
                    alternatives,
                    regions,
                    ..
                } => {
                    let data::Payload::Alternative {
                        alternative,
                        fields,
                        ..
                    } = values[0].payload.as_ref()
                    else {
                        unreachable!("admitted match")
                    };
                    let index = alternatives
                        .iter()
                        .position(|a| a == alternative)
                        .expect("complete coverage");
                    let mut arguments = fields.clone();
                    arguments.extend_from_slice(&values[1..]);
                    self.block(&regions[index], arguments)?
                }
                Operation::For {
                    carried, regions, ..
                } => {
                    let count = *carried as usize;
                    let mut carried = values[2..2 + count].to_vec();
                    for i in values[0].index()..values[1].index() {
                        self.charge(0, 1)?;
                        self.path.push(format!("iteration:{i}"));
                        let induction = data::index(
                            self.host,
                            &regions[0].arguments[0].schema,
                            i,
                            &self.ledger,
                        )
                        .map_err(|e| self.fail(e))?;
                        let mut arguments = vec![induction];
                        arguments.append(&mut carried);
                        arguments.extend_from_slice(&values[2 + count..]);
                        carried = self.block(&regions[0], arguments)?;
                        self.path.pop();
                    }
                    carried
                }
                Operation::Require { .. } => {
                    if !values[0].boolean() {
                        return Err(self.fail("entry-host-require"));
                    }
                    vec![]
                }
                Operation::Drop { operands, .. } => {
                    env.remove(&operands[0]);
                    vec![]
                }
                Operation::Stop { reason, .. } => {
                    return Err(self.fail(format!("entry-host-stop: {reason}")));
                }
            };
            for (definition, value) in op.results().iter().zip(results) {
                env.insert(definition.id, value);
            }
            self.path.pop();
        }
        Ok(b.returns.iter().map(|i| env[i].clone()).collect())
    }
    fn begin(&mut self, target: &str, operation: &str) -> ExecResult<Option<usize>> {
        if self.calls.len() == self.host.options.journal_events {
            self.truncated = true;
            return Ok(None);
        }
        let bytes = 64 * 1024
            + target.len()
            + operation.len()
            + self.path.iter().map(|s| s.len() + 512).sum::<usize>();
        let live = zkc_runtime::host::wire::reserve_allocation(Some(&self.ledger), bytes)
            .map_err(|e| self.fail(e))?;
        self.journal_live.extend(live);
        let index = self.calls.len();
        self.calls.push(CallReceipt {
            target: target.into(),
            operation: operation.into(),
            path: self.path.clone(),
            completed: false,
            native: json!({}),
        });
        Ok(Some(index))
    }
    fn end(&mut self, index: Option<usize>, completed: bool, native: Json) {
        self.last_native = Some(native.clone());
        if let Some(i) = index {
            self.calls[i].completed = completed;
            self.calls[i].native = native;
        }
    }
    fn failed_call(&mut self, mut failure: FunctionFailure) -> FunctionFailure {
        let native = failure
            .native
            .clone()
            .unwrap_or_else(|| json!({"failure":failure.code,"phase":"preparation"}));
        if let Some(call) = self.calls.last_mut().filter(|c| c.path == self.path) {
            call.completed = false;
            call.native = native.clone();
        }
        failure.native = Some(native);
        failure
    }
    fn reserve_services(&mut self, mut budgets: impl Iterator<Item = u64>) -> ExecResult<()> {
        let amount = budgets
            .try_fold(0u64, |n, b| n.checked_add(b))
            .ok_or_else(|| self.fail("entry-host-service-limit"))?;
        let total = self
            .usage
            .service_allowances
            .checked_add(amount)
            .filter(|n| *n <= self.host.options.service_draws)
            .ok_or_else(|| self.fail("entry-host-service-limit"))?;
        self.usage.service_allowances = total;
        Ok(())
    }
    fn dispatch(&mut self) -> ExecResult<()> {
        if self.usage.dispatches >= self.host.options.limits.steps {
            return Err(self.fail("entry-host-dispatch-limit"));
        }
        self.usage.dispatches += 1;
        Ok(())
    }
    /// Partition the remaining aggregate allowance once per native invocation.
    /// Keep transport/result space beside the runners' full live reservations.
    fn child_capacity(&self, runners: usize) -> crate::execution::Capacity {
        let mut capacity = self.host.options.limits.capacity;
        capacity.values.live_bytes = capacity
            .values
            .live_bytes
            .saturating_sub(self.ledger.snapshot().live_reserved_bytes)
            / 2
            / runners.max(1);
        capacity
    }
    fn numeric(&mut self, id: &str, values: Vec<TypedValue>) -> ExecResult<Vec<TypedValue>> {
        let index = self.begin(id, "numeric")?;
        self.dispatch()?;
        let c = &self.host.calculations[id];
        let _input_vector = zkc_runtime::host::wire::reserve_allocation(
            Some(&self.ledger),
            values.iter().map(|v| v.schema().leaves.len() * 512).sum(),
        )
        .map_err(|e| self.fail(e))?;
        let capacity = self.child_capacity(1);
        let mut inputs = Vec::new();
        for v in values {
            v.flatten(&mut inputs).map_err(|e| self.fail(e))?;
        }
        let backend = data::numerical_backend(self.host, capacity, &c.function)
            .map_err(|e| self.fail(e))?
            .with_ring_assets(self.host.assets.registry().clone())
            .map_err(|e| self.fail(e))?
            .with_relation_assets(self.host.assets.relation_registry().clone())
            .map_err(|e| self.fail(e))?
            .with_external_work_limit(
                self.host
                    .options
                    .limits
                    .external_work
                    .saturating_sub(self.usage.external_work),
            )
            .with_ring_work_limit(
                zkc_cpu::ring::DEFAULT_WORK_LIMIT.saturating_sub(self.usage.ring_work),
            )
            .with_sequence_work_limit(16_777_216u64.saturating_sub(self.usage.sequence_work));
        let result = LocalRunner::new_with_ledger(
            &c.program,
            &c.function,
            "entry-host",
            backend,
            inputs,
            capacity.values,
            capacity.work,
            Some(self.ledger.clone()),
        );
        let mut runner = match result {
            Ok(r) => r,
            Err(f) => {
                self.end(index, false, json!({"error":f.error.to_string()}));
                return Err(self.fail(f.error));
            }
        };
        runner.execute();
        self.execution_counts.merge(&runner.execution_counts());
        self.usage.external_work += runner.backend().external_work_spent();
        self.usage.ring_work += runner.backend().ring_work_spent();
        self.usage.sequence_work += runner.backend().sequence_work_spent();
        let diagnostic = json!({"stop":runner.stop().map(crate::host::diagnostics::stop)});
        let failed = runner.stop().is_some();
        self.end(index, !failed, diagnostic);
        let values = runner
            .returned_values()
            .ok_or_else(|| self.fail("entry-host-numeric-stopped"))?;
        let metadata = c.results.iter().map(data::metadata).sum::<usize>();
        self.ledger
            .charge(
                WorkBudget {
                    instructions: 0,
                    iterations: 0,
                    logical_bytes: 0,
                },
                metadata,
            )
            .map_err(|e| self.fail(e))?;
        let bytes = values
            .iter()
            .map(RuntimeValue::retained_bytes)
            .sum::<usize>()
            .saturating_add(metadata);
        // Reserve the parent's exact retained result while the child still owns
        // its full live allowance. No gap exposes unreserved native backings.
        let live = std::sync::Arc::new(self.ledger.reserve_live(bytes).map_err(|e| self.fail(e))?);
        let outputs = values.to_vec();
        drop(runner.into_backend());
        let mut outputs = outputs.into_iter();
        c.results
            .iter()
            .map(|s| {
                data::collect(self.host, s, &mut outputs, live.clone()).map_err(|e| self.fail(e))
            })
            .collect()
    }
    fn invoke(&mut self, id: &str, values: &[TypedValue]) -> ExecResult<TypedValue> {
        let deployment = &self.host.deployments[id];
        let index = self.begin(id, deployment.operation())?;
        self.dispatch()?;
        let binding = &self.context.deployments[id];
        // Source values retain their original backing guards. Withhold the
        // additional request products and copied application setup bytes before
        // converting the checked values to the owning native request format.
        let context_copy = match binding {
            InvocationBinding::Run(v) => {
                v.setups.values().map(Vec::len).sum::<usize>()
                    + v.roles
                        .values()
                        .flat_map(|r| r.inputs.values())
                        .map(data::description_bytes)
                        .sum::<usize>()
            }
            InvocationBinding::Proof(v) => {
                v.setups.values().map(Vec::len).sum::<usize>()
                    + v.context.len()
                    + v.private
                        .inputs
                        .values()
                        .map(data::description_bytes)
                        .sum::<usize>()
            }
        };
        let descriptors = values
            .iter()
            .map(|v| data::metadata(v.schema()))
            .sum::<usize>();
        let _request_live = zkc_runtime::host::wire::reserve_allocation(
            Some(&self.ledger),
            context_copy.saturating_add(descriptors),
        )
        .map_err(|e| self.fail(e))?;
        match (&deployment.kind, binding) {
            (DeploymentKind::Run(entry), InvocationBinding::Run(context)) => {
                let request = deployment::run_request(entry, &values[0], context)
                    .map_err(|e| self.fail(e))?;
                let service_budgets = entry
                    .interface()
                    .roles()
                    .iter()
                    .flat_map(|r| {
                        entry.interface().services(r).map(|s| {
                            request.roles[&r.name]
                                .services
                                .get(&s.name)
                                .copied()
                                .unwrap_or(crate::entry::DEFAULT_DRAW_BUDGET)
                        })
                    })
                    .collect::<Vec<_>>();
                self.reserve_services(service_budgets.into_iter())?;
                let mut limits = self.host.options.limits.clone();
                limits.capacity = self.child_capacity(entry.interface().roles().len());
                limits.steps = limits.steps.saturating_sub(self.usage.dispatches);
                limits.total_wire_bytes = limits
                    .total_wire_bytes
                    .saturating_sub(self.usage.wire_bytes);
                limits.external_work = limits
                    .external_work
                    .saturating_sub(self.usage.external_work)
                    / entry.interface().roles().len() as u64;
                let ring = zkc_cpu::ring::DEFAULT_WORK_LIMIT.saturating_sub(self.usage.ring_work)
                    / entry.interface().roles().len() as u64;
                let sequence = 16_777_216u64.saturating_sub(self.usage.sequence_work)
                    / entry.interface().roles().len() as u64;
                let report = entry
                    .execute_shared(request, limits, ring, sequence, self.ledger.clone())
                    .map_err(|e| self.fail(e))?;
                if let Some(execution) = &report.native.execution {
                    for role in &execution.roles {
                        self.execution_counts.merge(&role.execution_counts);
                    }
                    self.usage.dispatches += execution.reached.len();
                    self.usage.wire_bytes +=
                        execution.wire.sent_bytes + execution.wire.replacement_bytes;
                    for (_, backend) in &execution.backends {
                        self.usage.external_work += backend.external_work_spent();
                        self.usage.ring_work += backend.ring_work_spent();
                        self.usage.sequence_work += backend.sequence_work_spent();
                    }
                }
                let completed = report.is_success();
                self.usage.service_draws += report.native.service_draws;
                let diagnostics = bounded_native(report.native.diagnostics_summary());
                self.end(index, completed, diagnostics);
                let output = report.outputs.filter(|_| completed).ok_or_else(|| {
                    self.fail(
                        report
                            .output_error
                            .unwrap_or_else(|| "entry-host-run-failed".into()),
                    )
                })?;
                let raw = deployment::run_value(&deployment.result, output);
                data::from_output(self.host, &deployment.result, raw, &self.ledger)
                    .map_err(|e| self.fail(e))
            }
            (DeploymentKind::Proof { entry, operation }, InvocationBinding::Proof(context)) => {
                let producer = *operation == super::super::ProofOperation::Prove;
                let request = deployment::proof_request(entry, producer, values, context)
                    .map_err(|e| self.fail(e))?;
                let p = entry.interface().proof().expect("proof");
                let role = &entry.interface().roles()[if producer { p.prover } else { p.verifier }];
                let service_budgets = entry
                    .interface()
                    .services(role)
                    .map(|s| {
                        request
                            .private
                            .services
                            .get(&s.name)
                            .copied()
                            .unwrap_or(crate::entry::DEFAULT_DRAW_BUDGET)
                    })
                    .collect::<Vec<_>>();
                self.reserve_services(service_budgets.into_iter())?;
                let proof = if producer {
                    None
                } else {
                    Some(deployment::proof_bytes(&values[1]).map_err(|e| self.fail(e))?)
                };
                let proof_limit = zkc_runtime::host::wire::MAX_PROOF_BYTES
                    .saturating_sub(self.usage.proof_bytes)
                    .min(
                        self.host
                            .options
                            .limits
                            .total_wire_bytes
                            .saturating_sub(self.usage.wire_bytes),
                    );
                let report = entry
                    .execute_shared(
                        request,
                        proof,
                        self.child_capacity(1),
                        self.host
                            .options
                            .limits
                            .external_work
                            .saturating_sub(self.usage.external_work),
                        zkc_cpu::ring::DEFAULT_WORK_LIMIT.saturating_sub(self.usage.ring_work),
                        16_777_216u64.saturating_sub(self.usage.sequence_work),
                        proof_limit,
                        self.ledger.clone(),
                    )
                    .map_err(|e| self.fail(e))?;
                self.usage.external_work += report.native.external_work;
                self.usage.ring_work += report.native.ring_work;
                self.usage.sequence_work += report.native.sequence_work;
                self.execution_counts.merge(&report.native.execution_counts);
                self.usage.proof_bytes += report.native.bytes;
                self.usage.wire_bytes += report.native.bytes;
                let decision = report.verification_result();
                let completed = report.is_success() || decision == Some(false);
                self.usage.service_draws += report.native.service_draws;
                let diagnostics = bounded_native(report.native.diagnostics_summary());
                self.end(index, completed, diagnostics);
                if !completed {
                    return Err(self.fail(
                        report
                            .output_error
                            .or_else(|| report.native.outcome.err())
                            .unwrap_or_else(|| "entry-host-proof-failed".into()),
                    ));
                }
                // Preserve native output reservations until the parent has its
                // own checked typed result. Vec-to-Arc proof conversion also
                // reserves the second allocation before copying exact bytes.
                let _proof_copy = if producer {
                    zkc_runtime::host::wire::reserve_allocation(
                        Some(&self.ledger),
                        report.native.bytes.saturating_add(512),
                    )
                    .map_err(|e| self.fail(e))?
                } else {
                    None
                };
                let raw = if producer {
                    deployment::prove_value(
                        report.outputs.expect("successful producer outputs"),
                        report.native.outcome.expect("successful proof"),
                    )
                } else {
                    deployment::verify_value(if decision == Some(true) {
                        report.outputs
                    } else {
                        None
                    })
                };
                data::from_output(self.host, &deployment.result, raw, &self.ledger)
                    .map_err(|e| self.fail(e))
            }
            _ => unreachable!("checked invocation binding"),
        }
    }
}
// Retain bounded control diagnostics; large native reports/backends are dropped.
fn bounded_native(mut value: Json) -> Json {
    // These summaries are already bounded by their native owners. Keep the
    // primary failure even when observational prefixes exhaust the trim budget.
    let object = value.as_object_mut().expect("native diagnostic object");
    let primary = ["failure_role", "stop"].map(|key| (key, object.remove(key)));
    let mut summary = crate::host::diagnostics::trim(&value, &mut 256, &mut 4096, 0);
    for (key, value) in primary {
        if let Some(value) = value {
            summary[key] = value;
        }
    }
    summary
}

impl std::fmt::Debug for FunctionReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionReport")
            .field("value", &self.value)
            .field("failure", &self.failure)
            .field("usage", &self.usage)
            .field("calls", &self.calls)
            .field("journal_truncated", &self.journal_truncated)
            .finish()
    }
}
