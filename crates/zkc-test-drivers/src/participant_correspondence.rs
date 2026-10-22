//! Observe real endpoints against structured source replay requests.
//! Test-only sampled generator-multiple relation, never discrete-log extraction.
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs};
use zkc_native::services::{ServiceReference, ServiceRegistry};
use zkc_native::{Domain, EntryPolicy, GroupPoint, NativeBackend, NativeWireError, Policy, Value};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Action, Backend, BackendError, BoundSignature, CallContext, Cut, Frame, FrameExit, Invocation,
    OperationBinding, PhysicalType, Program, ReceiveCompletion, RuntimeError, ServiceContract,
    ServiceInvocation, ServiceSupport, StopKind, Value as RuntimeValue,
};

type Result<T> = std::result::Result<T, Failure>;
#[derive(Debug)]
struct Failure(&'static str, String);
fn harness(e: impl std::fmt::Debug) -> Failure {
    Failure("HarnessFailure", format!("{e:?}"))
}
fn require(ok: bool, message: &str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(Failure("Mismatch", message.into()))
    }
}
fn unsupported(message: &str) -> Failure {
    Failure("Unsupported", message.into())
}
fn string(v: &Json) -> Result<&str> {
    v.as_str().ok_or_else(|| harness("expected string"))
}
fn array(v: &Json) -> Result<&Vec<Json>> {
    v.as_array().ok_or_else(|| harness("expected array"))
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Binding {
    entry: String,
    role: String,
    participant: String,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
    service_inputs: Vec<usize>,
    input_types: Vec<Json>,
    output_types: Vec<Json>,
    queries: BTreeMap<String, usize>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Provider {
    handle: String,
    budget: u64,
    tape: Vec<String>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Fault {
    action: usize,
    mode: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    format: String,
    binding: Binding,
    request: Json,
    expected: Json,
    providers: Vec<Provider>,
    fault: Option<Fault>,
    session: String,
}

/// Delegation preserves all native operations and service custody. The single
/// injection point deliberately damages a reply AFTER the real provider call.
struct ObservedBackend {
    native: NativeBackend,
    draws: Vec<Value>,
    malformed_site: Option<String>,
    faults_applied: usize,
}
impl Backend for ObservedBackend {
    type Value = Value;
    type Operation = zkc_native::NativeOperation;
    type Call = zkc_native::NativeCall;
    type Checkpoint = zkc_native::ComputationCheckpoint;

    fn computation_checkpoint(&self) -> Option<Self::Checkpoint> {
        self.native.computation_checkpoint()
    }
    fn replay_computation(&mut self, before: Self::Checkpoint, after: Self::Checkpoint) -> bool {
        self.native.replay_computation(before, after)
    }

    fn prepare_binding(&self, binding: &OperationBinding) -> Option<Self::Operation> {
        self.native.prepare_binding(binding)
    }
    fn supports_boolean_literals(&self) -> bool {
        self.native.supports_boolean_literals()
    }
    fn service_support(&self, c: ServiceContract, m: &str) -> Option<ServiceSupport> {
        self.native.service_support(c, m)
    }
    fn query(
        &mut self,
        i: &ServiceInvocation<'_>,
        args: &[Value],
    ) -> std::result::Result<Vec<Value>, BackendError> {
        let values = self.native.query(i, args)?;
        self.draws.extend(values.iter().cloned());
        if self.malformed_site.as_deref() == Some(i.site) {
            self.faults_applied += 1;
            Ok(vec![Value::Bool(true)])
        } else {
            Ok(values)
        }
    }
    fn reject_service_reply(&mut self, i: &ServiceInvocation<'_>) {
        self.native.reject_service_reply(i);
    }
    fn binding_signature(&self, b: &OperationBinding) -> Option<BoundSignature> {
        self.native.binding_signature(b)
    }
    fn validate_value(&self, v: &Value) -> std::result::Result<(), BackendError> {
        self.native.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, v: &[Value]) -> std::result::Result<(), BackendError> {
        self.native.enter_frame(f, v)
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        e: FrameExit,
        v: &[Value],
    ) -> std::result::Result<(), BackendError> {
        self.native.leave_frame(f, e, v)
    }
    fn validate_value_retained(
        &self,
        v: &Value,
        retained: zkc_runtime::vm::Retained<'_>,
    ) -> std::result::Result<(), BackendError> {
        self.native.validate_value_retained(v, retained)
    }
    fn enter_frame_retained(
        &mut self,
        f: &Frame,
        v: &[Value],
        retained: zkc_runtime::vm::Retained<'_>,
    ) -> std::result::Result<(), BackendError> {
        self.native.enter_frame_retained(f, v, retained)
    }
    fn leave_frame_retained(
        &mut self,
        f: &Frame,
        e: FrameExit,
        v: &[Value],
        retained: zkc_runtime::vm::Retained<'_>,
    ) -> std::result::Result<(), BackendError> {
        self.native.leave_frame_retained(f, e, v, retained)
    }
    fn operand_work(
        &self,
        operation: &Self::Operation,
        i: &CallContext<'_>,
        v: &[Value],
    ) -> Option<u64> {
        self.native.operand_work(operation, i, v)
    }
    fn apply_prepared(
        &mut self,
        operation: &Self::Operation,
        call: &mut Option<Self::Call>,
        i: &Invocation<'_>,
        v: &[Value],
    ) -> std::result::Result<Vec<Value>, BackendError> {
        self.native.apply_prepared(operation, call, i, v)
    }
    fn apply(
        &mut self,
        operation: &Self::Operation,
        i: &Invocation<'_>,
        v: &[Value],
    ) -> std::result::Result<Vec<Value>, BackendError> {
        self.native.apply(operation, i, v)
    }
}
fn value(ty: &Json, v: &Json) -> Result<Value> {
    if *ty == json!(["bool"]) {
        return Ok(Value::Bool(v.as_bool().ok_or_else(|| harness("bool"))?));
    }
    if *ty == json!(["field", "bls12-381.fr"]) {
        return Ok(Value::Field(
            zkc_kernels::parse_decimal(string(v)?).map_err(harness)?,
        ));
    }
    if *ty == json!(["group", "bls12-381.g1"]) {
        return Ok(Value::Curve(
            GroupPoint::generator().scale(zkc_kernels::parse_decimal(string(v)?).map_err(harness)?),
        ));
    }
    Err(unsupported(
        "value relation supports bool, BLS12-381 Fr and G1 labels",
    ))
}
fn logical(ty: &PhysicalType) -> Result<Json> {
    for (t, v) in [
        (json!(["bool"]), json!(false)),
        (json!(["field", "bls12-381.fr"]), json!("0")),
        (json!(["group", "bls12-381.g1"]), json!("0")),
    ] {
        if value(&t, &v)?.physical_type() == *ty {
            return Ok(t);
        }
    }
    Err(unsupported("native physical type outside sampled relation"))
}
fn same_value(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Field(a), Value::Field(b)) => a == b,
        (Value::Curve(a), Value::Curve(b)) => a == b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        _ => false,
    }
}
fn same_action(a: &Action<Value>, b: &Action<Value>) -> bool {
    match (a, b) {
        (Action::Query(a), Action::Query(b)) => {
            a.cut == b.cut
                && a.port == b.port
                && a.method == b.method
                && a.results == b.results
                && a.arguments.len() == b.arguments.len()
                && a.arguments
                    .iter()
                    .zip(&b.arguments)
                    .all(|(x, y)| same_value(x, y))
        }
        (Action::Receive(a), Action::Receive(b)) => a == b,
        (Action::Send(a), Action::Send(b)) => {
            a.envelope == b.envelope && a.ty == b.ty && same_value(&a.payload, &b.payload)
        }
        _ => false,
    }
}
fn related(
    native: &NativeBackend,
    v: &Value,
    expected: &Json,
    wires: &mut Vec<Json>,
) -> Result<Json> {
    let ty = logical(&v.physical_type())?;
    let mapped = value(&ty, expected)?;
    let actual = native.encode_native_value(v).map_err(harness)?;
    let encoded = native.encode_native_value(&mapped).map_err(harness)?;
    let decoded = native
        .decode_native_value(&v.physical_type(), &actual)
        .map_err(harness)?;
    require(same_value(&decoded, v), "native codec round trip")?;
    wires.push(json!({"type":ty,"label":expected,"actual":hex(&actual),"mapped":hex(&encoded)}));
    if !same_value(v, &mapped) || actual != encoded {
        return Err(Failure("ValueMismatch", wires.last().unwrap().to_string()));
    }
    Ok(expected.clone())
}
fn scalar(v: &Value) -> Result<Json> {
    match v {
        Value::Field(f) => Ok(json!(f.to_string())),
        _ => Err(harness("provider did not return field")),
    }
}
fn roots(
    registry: &ServiceRegistry,
    references: &BTreeMap<String, ServiceReference>,
) -> Result<Json> {
    let mut result = serde_json::Map::new();
    for (handle, r) in references {
        let o = registry.observe(r).map_err(harness)?;
        let state = o.state.map(|s| json!({"generation":s.generation,"draws":s.draw_count,"budget":s.budget,"stage":s.stage}));
        result.insert(handle.clone(), json!({"issued":r.issued_id(),"owner":o.owner,
            "leased":o.leased,"poisoned":o.poisoned,"completion_known":state.is_some(),"state":state}));
    }
    Ok(Json::Object(result))
}
fn state(
    r: &Runner<ObservedBackend>,
    registry: &ServiceRegistry,
    references: &BTreeMap<String, ServiceReference>,
) -> Result<Json> {
    let u = r.usage();
    Ok(
        json!({"providers":roots(registry,references)?,"active_frames":r.backend().native.active_frames(),
        "live_resource_units":r.backend().native.live_resource_units(),
        "usage":{"instructions":u.instructions,"iterations":u.iterations,"live_values":u.live_values,
        "live_bytes":u.live_value_bytes,"total_bytes":u.total_value_bytes,"logical_bytes":u.logical_bytes}}),
    )
}
fn coordinate(cut: &Cut) -> Json {
    json!({"origin":cut.origin.json(),"role":cut.role,"site":cut.site,"kind":format!("{:?}",cut.kind)})
}
fn next(r: &mut Runner<ObservedBackend>) -> Result<Action<Value>> {
    for _ in 0..4096 {
        match r.poll() {
            Action::Local(a) => r.execute_local(&a.cut).map_err(harness)?,
            a => return Ok(a),
        }
    }
    Err(unsupported("native observation local-action capacity"))
}
fn refuse(
    r: &mut Runner<ObservedBackend>,
    cut: &Cut,
    kind: &Action<Value>,
) -> std::result::Result<(), RuntimeError> {
    match kind {
        Action::Query(_) => r.execute_query(cut),
        Action::Send(_) => r.take_send(cut).map(|_| ()),
        Action::Receive(_) => r.complete_receive(cut, Ok(Value::Bool(true))).map(|_| ()),
        _ => Err(RuntimeError::WrongAction),
    }
}
fn stop_json(s: &zkc_runtime::vm::Stop) -> Json {
    let cause = match &s.kind {
        StopKind::Decode(r) => json!(["decode", r.as_str()]),
        StopKind::Explicit(r) => json!(["explicit", r]),
        StopKind::Backend(e) => json!(["backend", e.code]),
        StopKind::Limit => json!(["limit"]),
        StopKind::Cancelled => json!(["cancelled"]),
    };
    json!({"origin":s.origin.json(),"role":s.role,"site":s.site,"cause":cause,
        "cleanup_errors":s.cleanup_errors.iter().map(|e| &e.code).collect::<Vec<_>>()})
}

fn check_stop(
    stop: Option<&zkc_runtime::vm::Stop>,
    kind: &StopKind,
    site: Option<&str>,
    cut: &Cut,
    role: &str,
) -> Result<()> {
    require(
        stop.is_some_and(|s| {
            &s.kind == kind && s.site.as_deref() == site && s.origin == cut.origin && s.role == role
        }),
        "terminal cause, site, origin or role differs from adapter",
    )
}

fn shape(ok: bool, message: &str) -> Result<()> {
    if ok { Ok(()) } else { Err(harness(message)) }
}
fn type_shape(ty: &Json) -> Result<()> {
    let row = array(ty)?;
    shape(
        (row.len() == 1 && matches!(row[0].as_str(), Some("bool" | "index")))
            || (row.len() == 2
                && matches!(
                    row[0].as_str(),
                    Some("field" | "group" | "service" | "vector")
                )
                && row[1].is_string()),
        "binding type shape",
    )
}
fn action_shape(action: &Json) -> Result<()> {
    let a = array(action)?;
    let Some(kind) = a.first().and_then(Json::as_str) else {
        return Err(harness("action kind"));
    };
    let length = match kind {
        "send" => 6,
        "receive" => 5,
        "draw" => 6,
        _ => return Err(unsupported("source action vocabulary")),
    };
    shape(a.len() == length, "action arity")?;
    shape(a[1..4].iter().all(Json::is_string), "action coordinates")?;
    if kind == "draw" {
        shape(a[4..].iter().all(Json::is_string), "draw identity")
    } else {
        type_shape(&a[4])
    }
}
fn validate_request(req: &Request) -> Result<()> {
    shape(
        req.format == "zkc.participant-probe/0",
        "probe envelope format",
    )?;
    let b = &req.binding;
    for ty in b.input_types.iter().chain(&b.output_types) {
        type_shape(ty)?;
    }
    for (indices, limit) in [
        (&b.inputs, b.input_types.len()),
        (&b.service_inputs, b.input_types.len()),
        (&b.outputs, b.output_types.len()),
    ] {
        shape(
            indices.iter().all(|&i| i < limit) && indices.windows(2).all(|p| p[0] < p[1]),
            "binding indices must be ordered, distinct and in range",
        )?;
    }
    shape(
        b.inputs
            .iter()
            .all(|i| !b.service_inputs.contains(i) && b.input_types[*i][0] != "service")
            && b.service_inputs
                .iter()
                .all(|i| b.input_types[*i][0] == "service"),
        "binding data/service partition",
    )?;
    shape(
        b.queries.values().all(|i| b.service_inputs.contains(i)),
        "binding query root outside owned service inputs",
    )?;
    let script = array(&req.request)?;
    shape(
        script.len() == 5
            && script[0] == "zkc.structured-open-request/0"
            && script[1] == b.role
            && script[4].as_u64().is_some_and(|n| n > 0),
        "source request shape",
    )?;
    shape(
        array(&script[2])?.len() == b.input_types.len(),
        "source input arity",
    )?;
    let replies = array(&script[3])?;
    for row in replies {
        let row = array(row)?;
        shape(row.len() == 3 && row[0] == "reply", "reply shape")?;
        action_shape(&row[1])?;
        let response = array(&row[2])?;
        shape(
            (response.len() == 1 && response[0] == "unit")
                || (response.len() == 2 && matches!(response[0].as_str(), Some("value" | "stop"))),
            "response shape",
        )?;
    }
    let expected = array(&req.expected)?;
    shape(
        expected.len() == 4
            && expected[0] == "zkc.structured-open-result/0"
            && expected[3].as_u64().is_some(),
        "expected result shape",
    )?;
    let outcome = array(&expected[1])?;
    match outcome.first().and_then(Json::as_str) {
        Some("returned") => {
            shape(outcome.len() == 2, "expected return shape")?;
            shape(
                array(&outcome[1])?.len() == b.output_types.len(),
                "expected source output arity",
            )?;
        }
        Some("stopped") => shape(
            outcome.len() == 3 && outcome[1].is_string() && outcome[2].is_string(),
            "expected stop shape",
        )?,
        _ => return Err(harness("expected outcome")),
    }
    for event in array(&expected[2])? {
        let event = array(event)?;
        shape(!event.is_empty(), "expected event")?;
        match event[0].as_str() {
            Some("request") => {
                shape(event.len() == 3, "request event shape")?;
                action_shape(&event[2])?;
            }
            Some("reply") => shape(event.len() == 3, "reply event shape")?,
            Some("stop") => shape(event.len() == 4, "stop event shape")?,
            _ => return Err(harness("event kind")),
        }
    }
    if let Some(fault) = &req.fault {
        shape(fault.action < replies.len(), "fault action index")?;
        let action = &replies[fault.action][1];
        let response = &replies[fault.action][2];
        let mode = fault.mode.strip_prefix("complete-").unwrap_or(&fault.mode);
        let valid = match fault.mode.as_str() {
            "malformed-reply" => action[0] == "draw" && *response == json!(["stop", "refused"]),
            _ => {
                action[0] == "receive"
                    && match mode {
                        "length" | "noncanonical" => {
                            matches!(action[4][0].as_str(), Some("field" | "group"))
                        }
                        "modulus" => action[4] == json!(["field", "bls12-381.fr"]),
                        "noncanonical-identity" => action[4] == json!(["group", "bls12-381.g1"]),
                        _ => false,
                    }
                    && if fault.mode.starts_with("complete-") {
                        *response == json!(["stop", "refused"])
                    } else {
                        response[0] == "value"
                    }
            }
        };
        shape(valid, "fault mode/action/type/response combination")?;
    }
    Ok(())
}

fn run(bytes: &[u8], req: Request, progress: &mut Json) -> Result<Json> {
    validate_request(&req)?;
    require(req.format == "zkc.participant-probe/0", "probe format")?;
    let script = array(&req.request)?;
    require(
        script.len() == 5
            && script[0] == "zkc.structured-open-request/0"
            && script[1] == req.binding.role,
        "source request shape/role",
    )?;
    let inputs = array(&script[2])?;
    let replies = array(&script[3])?;
    require(
        inputs.len() == req.binding.input_types.len(),
        "source input count",
    )?;
    let b = &req.binding;
    let native = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(&b.role, &req.session, &b.entry, None), None),
        Default::default(),
    )
    .map_err(harness)?;
    let admitted = Program::decode(bytes).map_err(harness)?;
    admitted.check_installation(&native).map_err(harness)?;
    require(admitted.bytes() == bytes, "admitted byte custody")?;
    let endpoint = admitted
        .entry(&b.entry)
        .ok_or_else(|| harness("entry"))?
        .into_iter()
        .find(|e| e.role == b.role)
        .ok_or_else(|| harness("role"))?;
    require(
        endpoint.participant == b.participant && endpoint.instance == b.entry,
        "projection participant/instance binding",
    )?;
    require(
        endpoint.inputs.len() == b.inputs.len()
            && endpoint.outputs.len() == b.outputs.len()
            && endpoint.services.len() == b.service_inputs.len(),
        "projection interface arity",
    )?;
    let mut native_inputs = Vec::new();
    for ((_, ty), &i) in endpoint.inputs.iter().zip(&b.inputs) {
        let v = value(&b.input_types[i], &inputs[i])?;
        require(v.physical_type() == *ty, "projection input type")?;
        native_inputs.push(v);
    }
    for (ty, &i) in endpoint.outputs.iter().zip(&b.outputs) {
        require(logical(ty)? == b.output_types[i], "projection output type")?;
    }
    let registry = ServiceRegistry::new(Policy::default());
    let mut references = BTreeMap::new();
    for p in &req.providers {
        require(
            !references.contains_key(&p.handle),
            "duplicate provider handle",
        )?;
        let tape = p
            .tape
            .iter()
            .map(|v| zkc_kernels::parse_decimal(v).map_err(harness))
            .collect::<Result<Vec<_>>>()?;
        references.insert(
            p.handle.clone(),
            registry
                .issue_test_tape(&b.role, p.budget, tape)
                .map_err(harness)?,
        );
    }
    let mut ingress = b
        .inputs
        .iter()
        .chain(&b.service_inputs)
        .copied()
        .collect::<Vec<_>>();
    ingress.sort_unstable();
    let mut ports = BTreeMap::new();
    let mut handles = BTreeMap::new();
    let mut bindings = Vec::new();
    for port in &endpoint.services {
        let i = *ingress
            .get(port.input_index)
            .ok_or_else(|| harness("local service index"))?;
        require(
            b.service_inputs.contains(&i)
                && b.input_types[i] == json!(["service", port.contract.name()]),
            "projection service root/type",
        )?;
        let handle = string(&inputs[i])?;
        let root = references
            .get(handle)
            .ok_or_else(|| harness("unbound provider"))?;
        ports.insert(port.name.clone(), root.clone());
        handles.insert(port.name.clone(), handle.to_owned());
        bindings.push(json!({"port":port.name,"local_index":port.input_index,"source_index":i,"handle":handle,"issued":root.issued_id()}));
    }
    let aliases = bindings
        .iter()
        .map(|a| {
            bindings
                .iter()
                .map(|b| {
                    references[string(&a["handle"]).unwrap()]
                        .same_root(&references[string(&b["handle"]).unwrap()])
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let native = native
        .with_services(registry.clone(), ports)
        .map_err(harness)?;
    let observed = ObservedBackend {
        native,
        draws: Vec::new(),
        faults_applied: 0,
        malformed_site: req
            .fault
            .as_ref()
            .filter(|f| f.mode == "malformed-reply")
            .map(|f| {
                string(
                    &replies
                        .get(f.action)
                        .ok_or_else(|| harness("fault action index"))?[1][1],
                )
                .map(str::to_owned)
            })
            .transpose()?,
    };
    let mut runner = Runner::new(
        &admitted,
        &b.entry,
        &b.role,
        &req.session,
        observed,
        native_inputs,
    )
    .map_err(|f| harness(f.error))?;
    let initial = state(&runner, &registry, &references)?;
    let mut events = Vec::new();
    let mut checkpoints = Vec::new();
    let mut wires = Vec::new();
    let mut probes = Vec::new();
    let mut wire_faults_applied = 0;
    let mut position = 0;
    let mut mapped_stop: Option<(String, String)> = None;
    let outcome;
    loop {
        *progress = json!({"events":events,"checkpoints":checkpoints,"wires":wires,
            "state":state(&runner,&registry,&references)?});
        let action = next(&mut runner)?;
        match &action {
            Action::Returned(values) => {
                require(
                    values.len() == b.outputs.len(),
                    "native returned output arity",
                )?;
                let expected = &req.expected[1][1];
                let mut outputs = vec![Json::Null; b.output_types.len()];
                for (v, &i) in values.iter().zip(&b.outputs) {
                    outputs[i] = related(&runner.backend().native, v, &expected[i], &mut wires)?;
                }
                outcome = json!(["returned", outputs]);
                break;
            }
            Action::Stopped(stop) => {
                let (reason, site) = if let Some(pair) = &mapped_stop {
                    pair.clone()
                } else if let StopKind::Explicit(reason) = &stop.kind {
                    (reason.clone(), stop.site.clone().unwrap_or_default())
                } else {
                    return Err(Failure(
                        "Mismatch",
                        format!("unmapped native stop: {:?}", stop.kind),
                    ));
                };
                events.push(json!(["stop", reason, site, position]));
                outcome = json!(["stopped", reason, site]);
                break;
            }
            _ => {}
        }
        let cut = action.cut().ok_or_else(|| harness("action cut"))?;
        if !cut.origin.path.is_empty() {
            return Err(unsupported("nested protocol occurrence source replay"));
        }
        let row = replies.get(position);
        let anticipated = row.map(|r| &r[1]).unwrap_or(&Json::Null);
        let request = match &action {
            Action::Query(q) => {
                let source_index = *ingress
                    .get(q.port.input_index)
                    .ok_or_else(|| harness("query source index"))?;
                require(
                    b.queries.get(&cut.site) == Some(&source_index),
                    "query original root binding",
                )?;
                require(
                    q.method == "draw" && q.arguments.is_empty() && q.results.len() == 1,
                    "draw signature",
                )?;
                let handle = handles
                    .get(&q.port.name)
                    .ok_or_else(|| harness("query port"))?;
                json!([
                    "draw",
                    cut.site,
                    b.role,
                    q.port.contract.name(),
                    handle,
                    "bls12-381.fr"
                ])
            }
            Action::Receive(r) => json!([
                "receive",
                cut.site,
                r.envelope.sender,
                r.envelope.receiver,
                logical(&r.ty)?
            ]),
            Action::Send(p) => {
                // Pending send still carries a value. Its expected source request
                // is supplied independently by the source observer in expected.
                let expected = if row.is_some() {
                    &anticipated[5]
                } else {
                    &req.expected[2][events.len()][2][5]
                };
                let label = related(&runner.backend().native, &p.payload, expected, &mut wires)?;
                json!([
                    "send",
                    cut.site,
                    p.envelope.sender,
                    p.envelope.receiver,
                    logical(&p.ty)?,
                    label
                ])
            }
            _ => return Err(harness("observable action")),
        };
        let before = state(&runner, &registry, &references)?;
        for _ in 0..3 {
            require(
                same_action(&runner.poll(), &action),
                "pending poll action changed",
            )?;
            require(
                state(&runner, &registry, &references)? == before,
                "pending poll state changed",
            )?;
        }
        let mut wrong = cut.clone();
        wrong.origin.session.push_str("-wrong");
        require(
            refuse(&mut runner, &wrong, &action) == Err(RuntimeError::WrongCut),
            "wrong cut was not refused",
        )?;
        require(
            state(&runner, &registry, &references)? == before
                && same_action(&runner.poll(), &action),
            "wrong cut advanced",
        )?;
        checkpoints.push(json!({"position":position,"request":request,"cut":coordinate(&cut),"state":before,"polls":3,"wrong_cut_refused":true}));
        events.push(json!(["request", position, request]));
        let Some(row) = row else {
            outcome = json!(["pending", cut.site]);
            break;
        };
        require(
            array(row)?.len() == 3 && row[0] == "reply" && row[1] == request,
            "native action differs from source request",
        )?;
        let response = &row[2];
        let fault = req.fault.as_ref().filter(|f| f.action == position);
        if response == &json!(["stop", "abort"]) {
            runner.cancel();
            // Runner cancellation deliberately has no instruction site. The
            // source abort site belongs to this adapter's accepted pending cut.
            check_stop(runner.stop(), &StopKind::Cancelled, None, &cut, &b.role)?;
            mapped_stop = Some(("abort".into(), cut.site.clone()));
        } else {
            match &action {
                Action::Query(_) => {
                    let prior = runner.backend().draws.len();
                    runner.execute_query(&cut).map_err(harness)?;
                    if let Some(stop) = runner.stop() {
                        check_stop(Some(stop), &stop.kind, Some(&cut.site), &cut, &b.role)?;
                        let reason = match &stop.kind {
                            StopKind::Backend(e)
                                if e.code == "exhausted:resource-budget"
                                    || e.code == "exhausted:test-tape" =>
                            {
                                "exhausted"
                            }
                            StopKind::Backend(e)
                                if fault.is_some_and(|f| f.mode == "malformed-reply")
                                    && e.code == "runtime-contract:Payload" =>
                            {
                                "refused"
                            }
                            _ => {
                                return Err(Failure(
                                    "Mismatch",
                                    format!("unmapped query stop {:?}", stop.kind),
                                ));
                            }
                        };
                        require(*response == json!(["stop", reason]), "query stop adapter")?;
                        mapped_stop = Some((reason.into(), cut.site.clone()));
                    } else {
                        require(
                            runner.backend().draws.len() == prior + 1,
                            "native query result count",
                        )?;
                        let actual = &runner.backend().draws[prior];
                        require(
                            *response == json!(["value", scalar(actual)?]),
                            "native draw differs from replay",
                        )?;
                        related(&runner.backend().native, actual, &response[1], &mut wires)?;
                    }
                }
                Action::Send(_) => {
                    require(*response == json!(["unit"]), "send response")?;
                    runner.take_send(&cut).map_err(harness)?;
                }
                Action::Receive(r) => {
                    let input = if response[0] == "value" {
                        value(&logical(&r.ty)?, &response[1])?
                    } else {
                        value(&logical(&r.ty)?, &json!("0"))?
                    };
                    let wire = runner
                        .backend()
                        .native
                        .encode_native_value(&input)
                        .map_err(harness)?;
                    if let Some(f) = fault {
                        wire_faults_applied += 1;
                        let mut bad = wire.clone();
                        match f.mode.as_str() {
                            "length" | "complete-length" => {
                                bad.pop();
                            }
                            "noncanonical" | "complete-noncanonical" => bad[6..].fill(255),
                            "noncanonical-identity" | "complete-noncanonical-identity" => {
                                bad[6..].fill(0);
                                bad[6] = 1;
                                let end = bad.len() - 1;
                                bad[end] = 64;
                            }
                            "modulus" | "complete-modulus" => {
                                let n = num_bigint::BigUint::parse_bytes(
                                    zkc_kernels::SCALAR_MODULUS_DECIMAL.as_bytes(),
                                    10,
                                )
                                .unwrap();
                                shape(bad.len() == 38, "modulus fault requires scalar wire")?;
                                bad[6..].copy_from_slice(&n.to_bytes_le());
                            }
                            _ => return Err(unsupported("wire fault")),
                        }
                        let before = state(&runner, &registry, &references)?;
                        let decoded = runner.backend().native.decode_native_value(&r.ty, &bad);
                        let Err(NativeWireError::Invalid(reason)) = decoded else {
                            return Err(Failure(
                                "Mismatch",
                                "malformed wire was not Invalid".into(),
                            ));
                        };
                        require(
                            state(&runner, &registry, &references)? == before
                                && same_action(&runner.poll(), &action),
                            "codec preflight advanced receive",
                        )?;
                        let api = runner.complete_receive(&cut, Ok(Value::Bool(true)));
                        require(
                            api == Err(RuntimeError::Payload)
                                && state(&runner, &registry, &references)? == before
                                && same_action(&runner.poll(), &action),
                            "wrong typed API payload advanced",
                        )?;
                        let completed = f.mode.starts_with("complete-");
                        if completed {
                            require(
                                runner
                                    .complete_receive(&cut, Err(reason))
                                    .map_err(harness)?
                                    == ReceiveCompletion::Stopped,
                                "decode attempt completion",
                            )?;
                            check_stop(
                                runner.stop(),
                                &StopKind::Decode(reason),
                                Some(&cut.site),
                                &cut,
                                &b.role,
                            )?;
                            require(
                                *response == json!(["stop", "refused"]),
                                "decode adapter reply",
                            )?;
                            mapped_stop = Some(("refused".into(), cut.site.clone()));
                        }
                        probes.push(json!({"position":position,"bytes":hex(&bad),"decode_reason":reason.as_str(),"api_payload_refused":true,"completed":completed,"adapter_payload_retention_obligation":!completed}));
                    }
                    if runner.stop().is_none() {
                        require(response[0] == "value", "typed receive reply")?;
                        let decoded = runner
                            .backend()
                            .native
                            .decode_native_value(&r.ty, &wire)
                            .map_err(harness)?;
                        related(&runner.backend().native, &decoded, &response[1], &mut wires)?;
                        require(
                            runner
                                .complete_receive(&cut, Ok(decoded))
                                .map_err(harness)?
                                == ReceiveCompletion::Delivered,
                            "receive delivered",
                        )?;
                    }
                }
                _ => return Err(harness("dispatch")),
            }
        }
        let after = state(&runner, &registry, &references)?;
        require(
            refuse(&mut runner, &cut, &action).is_err(),
            "stale cut accepted",
        )?;
        require(
            state(&runner, &registry, &references)? == after,
            "stale cut advanced",
        )?;
        checkpoints.last_mut().unwrap()["stale_cut_refused"] = json!(true);
        events.push(json!(["reply", position, response]));
        position += 1;
    }
    let before_cleanup = state(&runner, &registry, &references)?;
    let faults_applied = wire_faults_applied + runner.backend().faults_applied;
    shape(
        faults_applied == usize::from(req.fault.is_some()),
        "requested fault was not applied exactly once",
    )?;
    let native_stop = runner.stop().map(stop_json);
    runner.cancel();
    if outcome[0] == "pending" {
        require(
            runner.stop().is_some_and(|s| {
                s.kind == StopKind::Cancelled && s.site.is_none() && s.role == b.role
            }),
            "pending cleanup must cancel",
        )?;
    }
    let after_cleanup = state(&runner, &registry, &references)?;
    let cleanup_stop = runner.stop().map(stop_json);
    require(
        runner.stop().is_none_or(|s| s.cleanup_errors.is_empty()),
        "native cleanup errors",
    )?;
    *progress = json!({"events":events,"checkpoints":checkpoints,"wires":wires,
        "before_cleanup":before_cleanup,"after_cleanup":after_cleanup,"native_stop":native_stop});
    require(
        after_cleanup["active_frames"] == 0
            && after_cleanup["live_resource_units"] == 0
            && after_cleanup["usage"]["live_values"]
                == runner.returned_values().map_or(0, |v| v.len()),
        "terminal cleanup",
    )?;
    let retained_output_bytes: usize = runner
        .returned_values()
        .unwrap_or(&[])
        .iter()
        .map(RuntimeValue::retained_bytes)
        .sum();
    require(
        after_cleanup["usage"]["live_bytes"] == retained_output_bytes,
        "retained output byte accounting",
    )?;
    // Reacquisition exercises poison/lease state, without resetting any root.
    let retry_session = format!("{}-reuse", req.session);
    let retry_backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(&b.role, &retry_session, &b.entry, None), None),
        Default::default(),
    )
    .map_err(harness)?;
    let ports = bindings
        .iter()
        .map(|p| {
            Ok((
                string(&p["port"])?.to_owned(),
                references[string(&p["handle"])?].clone(),
            ))
        })
        .collect::<Result<BTreeMap<_, _>>>()?;
    let retry_backend = retry_backend
        .with_services(registry.clone(), ports)
        .map_err(harness)?;
    let retry_inputs = b
        .inputs
        .iter()
        .map(|&i| value(&b.input_types[i], &inputs[i]))
        .collect::<Result<Vec<_>>>()?;
    let retry = Runner::new(
        &admitted,
        &b.entry,
        &b.role,
        &retry_session,
        retry_backend,
        retry_inputs,
    );
    let reacquired = retry.is_ok();
    let reacquisition_error = retry
        .as_ref()
        .err()
        .map(|failure| format!("{:?}", failure.error));
    let poisoned = references
        .values()
        .any(|r| registry.observe(r).is_ok_and(|o| o.poisoned));
    if poisoned {
        require(
            matches!(&retry, Err(failure) if matches!(&failure.error, RuntimeError::Backend(e) if e.code == "refused:service-poisoned")),
            "poisoned root refusal cause",
        )?;
    } else {
        require(reacquired, "unpoisoned root reacquisition")?;
    }
    drop(retry);
    require(
        roots(&registry, &references)? == after_cleanup["providers"],
        "reacquisition changed provider state",
    )?;
    Ok(
        json!({"format":"zkc.participant-observation/0","status":"Pass","outcome":outcome,"events":events,"consumed":position,
        "checkpoints":checkpoints,"wires":wires,"wire_probes":probes,"bindings":bindings,"aliases":aliases,
        "initial":initial,"before_cleanup":before_cleanup,"after_cleanup":after_cleanup,"native_stop":native_stop,"cleanup_stop":cleanup_stop,"reacquired":reacquired,"reacquisition_error":reacquisition_error,"faults_applied":faults_applied,
        "provider_values":runner.backend().draws.iter().map(scalar).collect::<Result<Vec<_>>>()?,
        "native_defaults":{"policy":format!("{:?}",Policy::default()),"work_budget":format!("{:?}",zkc_runtime::vm::WorkBudget::default()),"value_budget":format!("{:?}",zkc_runtime::vm::ValueBudget::default())}}),
    )
}
fn main() {
    let mut progress = json!({});
    let result = (|| -> Result<Json> {
        let args = std::env::args().collect::<Vec<_>>();
        if args.len() != 3 {
            return Err(harness(
                "usage: participant_correspondence CANDIDATE REQUEST",
            ));
        }
        let req = serde_json::from_slice(&fs::read(&args[2]).map_err(harness)?).map_err(harness)?;
        run(&fs::read(&args[1]).map_err(harness)?, req, &mut progress)
    })();
    let (report, code) = match result {
        Ok(r) => (r, 0),
        Err(Failure(s, m)) => (
            json!({"format":"zkc.participant-observation/0","status":if s == "ValueMismatch" {"Mismatch"} else {s},"detail":m,"reason":if s == "ValueMismatch" {Some("value-relation")} else {None},"partial":progress}),
            1,
        ),
    };
    println!("{}", serde_json::to_string(&report).unwrap());
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc_runtime::vm::{CutKind, DecodeReason, Origin, Stop};

    fn request_with_draw() -> Json {
        let draw = json!([
            "draw",
            "first",
            "P",
            "random.bls12-381.fr/0",
            "17",
            "bls12-381.fr"
        ]);
        json!({"format":"zkc.participant-probe/0", "session":"validator",
            "binding":{"entry":"main","role":"P","participant":"endpoint",
                "inputs":[],"service_inputs":[0],"outputs":[],
                "input_types":[["service","random.bls12-381.fr/0"]],"output_types":[],"queries":{"first":0}},
            "request":["zkc.structured-open-request/0","P",["17"],[["reply",draw,["value","3"]]],100],
            "expected":["zkc.structured-open-result/0",["returned",[]],[["request",0,draw],["reply",0,["value","3"]]],1],
            "providers":[],"fault":null})
    }

    #[test]
    fn six_field_draw_validates_in_replies_and_expected_events() {
        validate_request(&serde_json::from_value(request_with_draw()).unwrap()).unwrap();
        let mut pending = request_with_draw();
        pending["request"][3] = json!([]);
        pending["expected"] = json!([
            "zkc.structured-open-result/0",
            ["stopped", "incomplete", "first"],
            [
                pending["expected"][2][0].clone(),
                ["stop", "incomplete", "first", 0]
            ],
            0
        ]);
        validate_request(&serde_json::from_value(pending).unwrap()).unwrap();
        for pointer in ["/request/3/0/1", "/expected/2/0/2"] {
            for long in [false, true] {
                let mut malformed = request_with_draw();
                let action = malformed
                    .pointer_mut(pointer)
                    .unwrap()
                    .as_array_mut()
                    .unwrap();
                if long {
                    action.push(json!("extra"));
                } else {
                    action.pop();
                }
                let failure =
                    validate_request(&serde_json::from_value(malformed).unwrap()).unwrap_err();
                assert_eq!(failure.0, "HarnessFailure");
            }
        }
    }

    #[test]
    fn terminal_adapter_rejects_limits_wrong_reason_and_wrong_site() {
        let cut = Cut {
            origin: Origin {
                session: "s".into(),
                entry: "main".into(),
                instance: "i".into(),
                path: vec![],
            },
            role: "V".into(),
            site: "receive".into(),
            kind: CutKind::Receive,
        };
        let decode = StopKind::Decode(DecodeReason::Scalar);
        let mut stop = Stop {
            origin: cut.origin.clone(),
            role: "V".into(),
            site: Some(cut.site.clone()),
            kind: decode.clone(),
            cleanup_errors: vec![],
            local: None,
        };
        check_stop(Some(&stop), &decode, Some(&cut.site), &cut, "V").unwrap();
        for kind in [
            StopKind::Limit,
            StopKind::Decode(DecodeReason::Group),
            StopKind::Cancelled,
        ] {
            stop.kind = kind;
            assert!(check_stop(Some(&stop), &decode, Some(&cut.site), &cut, "V").is_err());
        }
        stop.kind = decode.clone();
        stop.site = Some("wrong".into());
        assert!(check_stop(Some(&stop), &decode, Some(&cut.site), &cut, "V").is_err());
        stop.kind = StopKind::Cancelled;
        stop.site = None;
        check_stop(Some(&stop), &StopKind::Cancelled, None, &cut, "V").unwrap();
        stop.kind = StopKind::Limit;
        assert!(check_stop(Some(&stop), &StopKind::Cancelled, None, &cut, "V").is_err());
    }
}
