use crate::{
    CheckFailure, CheckRequest, Checker, Error, Library, Outcome, PhaseEvidence, Realization, Sort,
    format,
    plan::{self, Context, Program},
};
use num_traits::ToPrimitive;
use serde_json::{Value, json};
use std::sync::Arc;

/// A definition reference is a name and a revision.
fn reference_shape(value: &Value) -> Result<(), Error> {
    let r = format::array(value, 2)?;
    format::string(&r[0])?;
    format::string(&r[1])?;
    Ok(())
}

pub struct AdmissionFailure {
    pub source: Vec<u8>,
    pub candidate: Vec<u8>,
    pub phase: Option<PhaseEvidence>,
    pub reason: Error,
    pub checking: Option<CheckFailure>,
}
pub struct AdmittedProgram<O> {
    source: Vec<u8>,
    candidate: Vec<u8>,
    phase: Option<PhaseEvidence>,
    realization: Realization,
    context: Context,
    body: Program<O>,
}
impl<O: Clone> AdmittedProgram<O> {
    pub fn admit<L: Library<Operation = O>>(
        source: Vec<u8>,
        candidate: Vec<u8>,
        phase: Option<PhaseEvidence>,
        library: &L,
        checker: &impl Checker,
    ) -> Result<Arc<Self>, Box<AdmissionFailure>> {
        Self::admit_interpreted(
            source,
            candidate,
            phase,
            Realization::DirectLogicalPlan,
            library,
            library,
            checker,
        )
    }

    pub(crate) fn admit_interpreted<L: Library<Operation = O>, S: Library>(
        source: Vec<u8>,
        candidate: Vec<u8>,
        phase: Option<PhaseEvidence>,
        realization: Realization,
        source_library: &S,
        library: &L,
        checker: &impl Checker,
    ) -> Result<Arc<Self>, Box<AdmissionFailure>> {
        let mut checking = None;
        let mut decode = || -> Result<(Context, Program<O>), Error> {
            if let Some(evidence) = &phase {
                if evidence.profile.is_empty()
                    || evidence.profile.len() > 128
                    || !evidence.profile.is_ascii()
                    || evidence.profile.contains('\0')
                {
                    return Err(Error("invalid-phase-profile"));
                }
                // Bound untrusted certificate syntax before invoking a tool.
                format::parse(&evidence.certificate)?;
                if let Some(entry) = &evidence.entry {
                    if entry.role.is_empty() {
                        return Err(Error("invalid-entry-role"));
                    }
                    format::parse(entry.json().to_string().as_bytes())?;
                }
            }
            let s = format::parse(&source)?;
            let p = format::parse(&candidate)?;
            // Request decoding (docs/spec/profiles/compiler/direct-plan.md):
            // its version and semantics are read before their supported values
            // are tested, and an unsupported one is a shape error.
            let s = format::array(&s, 6)?;
            if s[0] != "zkc-request" {
                return Err(Error("invalid-shape"));
            }
            let version = format::natural(&s[1])?;
            let semantics = format::string(&s[2])?;
            if version != 1u8.into() {
                return Err(Error("invalid-shape"));
            }
            let source_format = plan::SourceFormat::decode(semantics)?;
            let source_ctx = plan::context(source_library, &s[3])?;
            let permitted = format::list(&s[4])?;
            for reference in permitted {
                reference_shape(reference)?;
            }
            let installed = |library: &dyn Fn() -> Value| {
                if s[3][3] != library() {
                    return Err(Error("unresolved-dependency"));
                }
                Ok(())
            };
            let (ctx, target_body, target_format) = match realization {
                Realization::DirectLogicalPlan => {
                    let p = format::array(&p, 10)?;
                    if p[0] != "zkc-plan" {
                        return Err(Error("invalid-shape"));
                    }
                    let version = format::natural(&p[1])?;
                    let candidate_semantics = format::string(&p[2])?;
                    let capabilities = format::list(&p[3])?;
                    for capability in capabilities {
                        format::string(capability)?;
                    }
                    let realization = format::string(&p[4])?;
                    let rule = format::string(&p[5])?;
                    for part in format::array(&p[6], 3)? {
                        format::string(part)?;
                    }
                    let ctx = plan::context(library, &p[7])?;
                    let requirements = format::list(&p[8])?;
                    for reference in requirements {
                        reference_shape(reference)?;
                    }
                    installed(&|| source_library.dependencies())?;
                    installed(&|| library.dependencies())?;
                    // The metadata tests, in order; the first that fails names
                    // the refusal.
                    let unsupported = if version != 1u8.into() {
                        Some("unsupported-format-version")
                    } else if candidate_semantics != semantics {
                        Some("unsupported-semantics-version")
                    } else if !capabilities.is_empty() {
                        Some("unsupported-capability")
                    } else if realization != "direct-logical-plan" {
                        Some("unsupported-realization")
                    } else if rule != "direct-lowering" {
                        Some("unsupported-rule")
                    } else if p[6]
                        != json!([
                            "equality",
                            "logical-outcome-state-events",
                            "all-inputs-and-handlers"
                        ])
                    {
                        Some("unsupported-claim")
                    } else if p[7] != s[3] {
                        Some("context-mismatch")
                    } else if !plan::valid_context(&s[3]) {
                        Some("invalid-context")
                    } else if requirements.iter().any(|r| !permitted.contains(r)) {
                        Some("unapproved-requirement")
                    } else if !requirements.is_empty() {
                        Some("unsupported-requirement")
                    } else {
                        None
                    };
                    if let Some(code) = unsupported {
                        return Err(Error(code));
                    }
                    (ctx, &p[9], source_format)
                }
                Realization::TablePhysicalPlan => {
                    let p = format::array(&p, 4)?;
                    if p[0] != "zkc-table-physical-plan" || format::natural(&p[1])? != 1u8.into() {
                        return Err(Error("invalid-shape"));
                    }
                    let ctx = plan::context(library, &p[2])?;
                    installed(&|| source_library.dependencies())?;
                    installed(&|| library.dependencies())?;
                    if p[2] != s[3] {
                        return Err(Error("context-mismatch"));
                    }
                    if !plan::valid_context(&s[3]) {
                        return Err(Error("invalid-context"));
                    }
                    (ctx, &p[3], plan::SourceFormat::Region)
                }
            };
            if phase
                .as_ref()
                .and_then(|p| p.entry.as_ref())
                .is_some_and(|e| e.role != ctx.role)
            {
                return Err(Error("endpoint-role-mismatch"));
            }
            let sorts = ctx
                .inputs
                .iter()
                .map(|i| i.sort.clone())
                .collect::<Vec<_>>();
            let source_sorts = source_ctx
                .inputs
                .iter()
                .map(|i| i.sort.clone())
                .collect::<Vec<_>>();
            plan::decode(
                source_library,
                &s[5],
                &source_sorts,
                &source_ctx.result,
                256,
                source_format,
            )?;
            let body = plan::decode(
                library,
                target_body,
                &sorts,
                &ctx.result,
                256,
                target_format,
            )?;
            checker
                .check(CheckRequest {
                    source: &source,
                    candidate: &candidate,
                    phase: phase.as_ref(),
                    realization,
                })
                .map_err(|failure| {
                    let reason = failure.reason();
                    checking = Some(failure);
                    reason
                })?;
            Ok((ctx, body))
        };
        match decode() {
            Ok((context, body)) => Ok(Arc::new(Self {
                source,
                candidate,
                phase,
                realization,
                context,
                body,
            })),
            Err(reason) => Err(Box::new(AdmissionFailure {
                source,
                candidate,
                phase,
                reason,
                checking,
            })),
        }
    }
    pub fn retained_bytes(&self) -> (&[u8], &[u8]) {
        (&self.source, &self.candidate)
    }
    pub fn phase_evidence(&self) -> Option<&PhaseEvidence> {
        self.phase.as_ref()
    }
    pub fn realization(&self) -> Realization {
        self.realization
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Budget {
    pub steps: u64,
    pub bytes: usize,
    pub values: usize,
    pub events: usize,
    pub natural_bits: usize,
}
impl Default for Budget {
    fn default() -> Self {
        Self {
            steps: 100_000,
            bytes: 32 * 1024 * 1024,
            values: 100_000,
            events: 100_000,
            natural_bits: 65_536,
        }
    }
}
#[derive(Clone, Copy, Debug, Default)]
pub struct Resources {
    pub steps: u64,
    pub bytes: usize,
    pub values: usize,
    pub scratch: usize,
    pub events: usize,
    pub slots: usize,
    pub arguments: usize,
}
impl Resources {
    fn sequence(self, other: Self) -> Result<Self, Error> {
        let e = Error("capacity-overflow");
        Ok(Self {
            steps: self.steps.checked_add(other.steps).ok_or(e)?,
            bytes: self.bytes.checked_add(other.bytes).ok_or(e)?,
            values: self.values.checked_add(other.values).ok_or(e)?,
            scratch: self.scratch.max(other.scratch),
            events: self.events.checked_add(other.events).ok_or(e)?,
            slots: self.slots.max(other.slots),
            arguments: self.arguments.max(other.arguments),
        })
    }
    fn join(self, other: Self) -> Self {
        Self {
            steps: self.steps.max(other.steps),
            bytes: self.bytes.max(other.bytes),
            values: self.values.max(other.values),
            scratch: self.scratch.max(other.scratch),
            events: self.events.max(other.events),
            slots: self.slots.max(other.slots),
            arguments: self.arguments.max(other.arguments),
        }
    }
    fn check(self, b: &Budget) -> Result<Self, Error> {
        if self.steps > b.steps
            || self
                .bytes
                .checked_add(self.scratch)
                .ok_or(Error("capacity-overflow"))?
                > b.bytes
            || self.values > b.values
            || self.events > b.events
        {
            return Err(Error("capacity-limit"));
        }
        Ok(self)
    }
}
pub trait Bindings: Library {
    type Value: Clone;
    type Bound: Clone;
    /// Check the retained entry against the actual actor and persistent state.
    /// Must be pure; called before input loading and again before execution.
    /// Stateful adapters must require their policy even if evidence is omitted.
    /// Default bindings support no stateful endpoint contract.
    fn validate_entry(&self, _role: &str, evidence: Option<&PhaseEvidence>) -> Result<(), Error> {
        if evidence.and_then(|p| p.entry.as_ref()).is_some() {
            Err(Error("unsupported-endpoint-binding"))
        } else {
            Ok(())
        }
    }
    fn input(&mut self, sort: &Sort, value: &Value) -> Result<Self::Value, Error>;
    fn validate(&self, sort: &Sort, value: &Self::Value) -> Result<(), Error>;
    /// Adapters may use types resolved during admission instead of reconstructing
    /// allocating signature descriptors at each operation boundary.
    fn validate_output(&self, op: &Self::Operation, value: &Self::Value) -> Result<(), Error> {
        self.validate(&self.signature(op).1, value)
    }
    /// Check argument-dependent constraints on an operation's final result,
    /// after static sort validation and before the source continuation runs.
    /// This is not an interface-reply hook: invoke may interpret the operation
    /// using zero or several provider calls. The adapter must check each call's
    /// reply before using it, including intermediate replies hidden here.
    /// Failure is a host contract violation; Completed retains actual post-state.
    /// This check must be pure and does not prove the full transition contract.
    /// With mutable carriers, retain any pre-call data needed for the check;
    /// cloning a handle alone does not snapshot its logical value.
    fn validate_result(
        &self,
        operation: &Self::Operation,
        arguments: &[Self::Value],
        reply: &Self::Value,
    ) -> Result<(), Error>;
    fn condition(&self, value: &Self::Value) -> Result<bool, Error>;
    fn bound(&self, value: &Self::Value) -> Result<Self::Bound, Error>;
    fn top(&self, sort: &Sort, budget: &Budget) -> Result<Self::Bound, Error>;
    fn join(&self, a: &Self::Bound, b: &Self::Bound) -> Self::Bound;
    fn estimate(
        &self,
        op: &Self::Operation,
        args: &[Self::Bound],
        budget: &Budget,
    ) -> Result<(Self::Bound, Resources), Error>;
    /// Account for reading/exporting a returned value in its completion owner.
    fn output_resources(&self, _value: &Self::Bound) -> Result<Resources, Error> {
        Ok(Resources::default())
    }
    fn reserve(&mut self, resources: Resources, budget: &Budget) -> Result<(), Error>;
    /// Start an invocation after successful reservation. Reset invocation-local
    /// observations, preserving persistent state, storage and provider custody.
    /// This hook must not draw challenges or perform protocol effects.
    fn begin_execution(&mut self);
    /// A source operation can make several interface calls. A stateful adapter
    /// must track phase and validate replies at each call, before any internal
    /// continuation; a later stop retains the entry phase of that call. Host
    /// failure within a call leaves its phase unknown. Between completed calls,
    /// a host failure retains the last known phase. Exclusive provider state and
    /// truthful logical outcomes are adapter obligations, not enforced by Rust
    /// ownership alone (e.g. an adapter can contain externally shared handles).
    fn invoke(
        &mut self,
        op: &Self::Operation,
        args: &[Self::Value],
    ) -> Result<Outcome<Self::Value>, Error>;
}
pub struct BindingFailure<B: Bindings> {
    pub program: Arc<AdmittedProgram<B::Operation>>,
    pub inputs: Value,
    pub bindings: B,
    pub reason: Error,
}
pub struct AdmittedJob<B: Bindings> {
    program: Arc<AdmittedProgram<B::Operation>>,
    inputs: Value,
    bindings: B,
    env: Vec<B::Value>,
}
pub struct StartFailure<B: Bindings> {
    pub job: AdmittedJob<B>,
    pub reason: Error,
}
pub struct Session<B: Bindings> {
    program: Arc<AdmittedProgram<B::Operation>>,
    bindings: B,
    env: Vec<B::Value>,
    resources: Resources,
    arguments: Vec<B::Value>,
}
pub struct Completed<B: Bindings> {
    started: bool,
    outcome: Result<Outcome<B::Value>, Error>,
    bindings: B,
}
impl<B: Bindings> Completed<B> {
    /// False if the final entry check failed before begin_execution. Bindings
    /// and prior observations are still returned; no invocation was started.
    pub fn started(&self) -> bool {
        self.started
    }
    pub fn outcome(&self) -> &Result<Outcome<B::Value>, Error> {
        &self.outcome
    }
    pub fn bindings(&self) -> &B {
        &self.bindings
    }
    pub fn into_parts(self) -> (Result<Outcome<B::Value>, Error>, B) {
        (self.outcome, self.bindings)
    }
}
fn slot<T>(env: &[T], index: usize) -> Result<&T, Error> {
    env.get(
        env.len()
            .checked_sub(index + 1)
            .ok_or(Error("invalid-runtime-operand"))?,
    )
    .ok_or(Error("invalid-runtime-operand"))
}
// The value bound describes returning executions only. None is the empty set
// of returns, not a maximal value. Resource bounds still cover stopped paths
// and the native policy's checks of dormant children.
fn estimate<B: Bindings>(
    bindings: &B,
    program: &Program<B::Operation>,
    env: &mut Vec<B::Bound>,
    _result: &Sort,
    budget: &Budget,
    remaining: &mut u64,
) -> Result<(Option<B::Bound>, Resources), Error> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or(Error("preflight-work-limit"))?;
    let mut base = Resources {
        steps: 1,
        slots: env.len() + 1,
        ..Resources::default()
    };
    let length = env.len();
    let result = match program {
        Program::Return(i) => (Some(slot(env, *i)?.clone()), base),
        Program::Stop(_) => (None, base),
        Program::Apply(op, args, next) => {
            base.arguments = args.len();
            let args = args
                .iter()
                .map(|i| slot(env, *i).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            let (bound, cost) = bindings.estimate(op, &args, budget)?;
            env.push(bound);
            let (bound, tail) = estimate(bindings, next, env, _result, budget, remaining)?;
            (bound, base.sequence(cost)?.sequence(tail)?)
        }
        Program::Choose(_, yes, no) => {
            let (a, ca) = estimate(bindings, yes, env, _result, budget, remaining)?;
            let (b, cb) = estimate(bindings, no, env, _result, budget, remaining)?;
            let returned = match (a, b) {
                (Some(a), Some(b)) => Some(bindings.join(&a, &b)),
                (a, b) => a.or(b),
            };
            (returned, base.sequence(ca.join(cb))?)
        }
        Program::Bind(ty, body, next) => {
            let (bound, cost) = estimate(bindings, body, env, ty, budget, remaining)?;
            let returns = bound.is_some();
            // Dormant children still satisfy the native capacity policy, but
            // they cannot invent a return value for an always-stopped body.
            env.push(match bound {
                Some(bound) => bound,
                None => bindings.top(ty, budget)?,
            });
            let (bound, tail) = estimate(bindings, next, env, _result, budget, remaining)?;
            (
                if returns { bound } else { None },
                base.sequence(cost)?.sequence(tail)?,
            )
        }
        Program::Repeat(count, ty, initial, body, next) => {
            let count = count
                .to_u64()
                .filter(|n| *n <= budget.steps)
                .ok_or(Error("capacity-limit"))?;
            let mut bound = slot(env, *initial)?.clone();
            let mut returns = true;
            let mut cost = base;
            // Even a dormant body is checked against the native capacity policy.
            for iteration in 0..count.max(1) {
                env.push(bound.clone());
                let (next_bound, step) = estimate(bindings, body, env, ty, budget, remaining)?;
                env.truncate(length);
                if iteration < count {
                    match next_bound {
                        Some(next_bound) => bound = next_bound,
                        None => returns = false,
                    }
                    cost = cost.sequence(step)?.check(budget)?;
                }
            }
            env.push(bound);
            let (bound, tail) = estimate(bindings, next, env, _result, budget, remaining)?;
            (if returns { bound } else { None }, cost.sequence(tail)?)
        }
    };
    env.truncate(length);
    Ok((result.0, result.1.check(budget)?))
}
impl<B: Bindings> AdmittedJob<B> {
    pub fn bind(
        program: Arc<AdmittedProgram<B::Operation>>,
        inputs: Value,
        mut bindings: B,
    ) -> Result<Self, BindingFailure<B>> {
        let mut bind = || -> Result<Vec<B::Value>, Error> {
            if bindings.dependencies() != program.context.dependencies
                || bindings.condition_sort() != program.context.condition
            {
                return Err(Error("library-mismatch"));
            }
            bindings.validate_entry(&program.context.role, program.phase.as_ref())?;
            let supplied = format::list(&inputs)?;
            if supplied.len() != program.context.inputs.len() {
                return Err(Error("input-count"));
            }
            let mut env = Vec::new();
            env.try_reserve_exact(supplied.len())
                .map_err(|_| Error("reservation-failed"))?;
            for (value, declaration) in supplied.iter().zip(&program.context.inputs) {
                let value = format::array(value, 3)?;
                if format::string(&value[0])? != declaration.name {
                    return Err(Error("wrong-input-name"));
                }
                if bindings.sort(&value[1])? != declaration.sort {
                    return Err(Error("wrong-input-type"));
                }
                let decoded = bindings.input(&declaration.sort, &value[2])?;
                bindings.validate(&declaration.sort, &decoded)?;
                env.push(decoded);
            }
            env.reverse();
            Ok(env)
        };
        match bind() {
            Ok(env) => Ok(Self {
                program,
                inputs,
                bindings,
                env,
            }),
            Err(reason) => Err(BindingFailure {
                program,
                inputs,
                bindings,
                reason,
            }),
        }
    }
    pub fn bindings(&self) -> &B {
        &self.bindings
    }
    pub fn into_parts(self) -> (Arc<AdmittedProgram<B::Operation>>, Value, B) {
        (self.program, self.inputs, self.bindings)
    }
    pub fn reserve(mut self, budget: Budget) -> Result<Session<B>, StartFailure<B>> {
        let mut arguments = Vec::new();
        let mut reserve = || -> Result<Resources, Error> {
            self.bindings
                .validate_entry(&self.program.context.role, self.program.phase.as_ref())?;
            let mut bounds = self
                .env
                .iter()
                .map(|v| self.bindings.bound(v))
                .collect::<Result<Vec<_>, _>>()?;
            let mut remaining = budget.steps;
            let (output, resources) = estimate(
                &self.bindings,
                &self.program.body,
                &mut bounds,
                &self.program.context.result,
                &budget,
                &mut remaining,
            )?;
            let output_resources = match output {
                Some(output) => self.bindings.output_resources(&output)?,
                None => Resources::default(),
            };
            let resources = resources.sequence(output_resources)?.check(&budget)?;
            self.env
                .try_reserve_exact(resources.slots.saturating_sub(self.env.len()))
                .map_err(|_| Error("reservation-failed"))?;
            arguments
                .try_reserve_exact(resources.arguments)
                .map_err(|_| Error("reservation-failed"))?;
            let slot_bytes = self
                .env
                .capacity()
                .checked_add(arguments.capacity())
                .ok_or(Error("capacity-overflow"))?
                .checked_mul(std::mem::size_of::<B::Value>())
                .ok_or(Error("capacity-overflow"))?;
            let mut provider_budget = budget;
            provider_budget.bytes = budget
                .bytes
                .checked_sub(slot_bytes)
                .ok_or(Error("capacity-limit"))?;
            self.bindings.reserve(resources, &provider_budget)?;
            Ok(resources)
        };
        match reserve() {
            Ok(resources) => Ok(Session {
                program: self.program,
                bindings: self.bindings,
                env: self.env,
                resources,
                arguments,
            }),
            Err(reason) => Err(StartFailure { job: self, reason }),
        }
    }
}
impl<B: Bindings> Session<B> {
    pub fn execute(mut self) -> Completed<B> {
        let mut remaining = self.resources.steps;
        let mut started = false;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.bindings
                .validate_entry(&self.program.context.role, self.program.phase.as_ref())?;
            started = true;
            self.bindings.begin_execution();
            execute(
                &mut self.bindings,
                &self.program.body,
                &mut self.env,
                &mut remaining,
                &mut self.arguments,
            )
        }))
        .unwrap_or(Err(Error("backend-panic")));
        Completed {
            started,
            outcome,
            bindings: self.bindings,
        }
    }
}
fn execute<B: Bindings>(
    bindings: &mut B,
    program: &Program<B::Operation>,
    env: &mut Vec<B::Value>,
    remaining: &mut u64,
    arguments: &mut Vec<B::Value>,
) -> Result<Outcome<B::Value>, Error> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or(Error("execution-bound-violation"))?;
    let length = env.len();
    let outcome = match program {
        Program::Return(i) => Ok(Outcome::Returned(slot(env, *i)?.clone())),
        Program::Stop(reason) => Ok(Outcome::Stopped(*reason)),
        Program::Apply(op, args, next) => {
            arguments.clear();
            if args.len() > arguments.capacity() {
                return Err(Error("argument-bound-violation"));
            }
            for i in args {
                arguments.push(slot(env, *i)?.clone());
            }
            match bindings.invoke(op, arguments)? {
                Outcome::Stopped(reason) => Ok(Outcome::Stopped(reason)),
                Outcome::Returned(value) => {
                    bindings.validate_output(op, &value)?;
                    bindings.validate_result(op, arguments, &value)?;
                    arguments.clear();
                    env.push(value);
                    execute(bindings, next, env, remaining, arguments)
                }
            }
        }
        Program::Choose(condition, yes, no) => execute(
            bindings,
            if bindings.condition(slot(env, *condition)?)? {
                yes
            } else {
                no
            },
            env,
            remaining,
            arguments,
        ),
        Program::Repeat(count, _, initial, body, next) => {
            let count = count.to_u64().ok_or(Error("execution-bound-violation"))?;
            let mut value = slot(env, *initial)?.clone();
            for _ in 0..count {
                env.push(value);
                match execute(bindings, body, env, remaining, arguments)? {
                    Outcome::Stopped(reason) => {
                        env.truncate(length);
                        return Ok(Outcome::Stopped(reason));
                    }
                    Outcome::Returned(result) => value = result,
                }
                env.truncate(length);
            }
            env.push(value);
            execute(bindings, next, env, remaining, arguments)
        }
        Program::Bind(_, body, next) => match execute(bindings, body, env, remaining, arguments)? {
            Outcome::Stopped(reason) => Ok(Outcome::Stopped(reason)),
            Outcome::Returned(value) => {
                env.push(value);
                execute(bindings, next, env, remaining, arguments)
            }
        },
    };
    env.truncate(length);
    outcome
}
