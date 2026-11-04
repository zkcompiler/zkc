//! Test-only deployment of exact compiler output with passive primitive tracing.
use revm::{
    Context, InspectCommitEvm, Inspector, MainBuilder, MainContext,
    context::{CfgEnv, TxEnv},
    context_interface::{Cfg, ContextTr, result::ExecutionResult},
    database::CacheDB,
    database_interface::{Database, EmptyDB},
    interpreter::{
        CallInputs, CallOutcome, Interpreter,
        interpreter_types::{Jumps, MemoryTr},
    },
    primitives::{Address, Bytes, TxKind, U256, hardfork::SpecId},
    state::AccountInfo,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    io::{self, Read},
    str::FromStr,
    sync::LazyLock,
};

const MAX_JSON: u64 = 4 * 1024 * 1024;
const MAX_TRACE_BYTES: usize = 32 * 1024 * 1024;
const MAX_EVENTS: usize = 16384;
const MAX_REPEAT: u64 = 8;

/// The installed EVM target declaration, `zkc.evm-target/0`. The runner reads
/// its forks, validation gas and validation gas maximum, and checks each fork's
/// consensus facts against the pinned engine.
const DECLARATION: &str = include_str!("../../../targets/evm.json");
const DECLARATION_FORMAT: &str = "zkc.evm-target/0";

// Every declared field is required, so a missing or unknown one refuses; the
// runner reads only the fork facts, the validation gas and its maximum.
#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Declaration {
    format: String,
    abi: Value,
    solc: Value,
    default_fork: String,
    forks: Vec<ForkRow>,
    validation_gas: u64,
    validation_gas_maximum: u64,
    limits: Value,
    reverts: Value,
}

#[allow(dead_code)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ForkRow {
    name: String,
    solc: String,
    hardfork: String,
    transaction_gas_cap: Option<u64>,
    runtime_code_bytes: u64,
    initcode_bytes: u64,
    rules: Vec<String>,
}

/// One declared fork, the engine specification its hardfork names, and the
/// gas each validation transaction requests by default.
struct Fork {
    name: String,
    spec: SpecId,
    budget: u64,
}

/// The declared facts the runner uses: the forks, and the most gas any
/// validation transaction may request, which is also every run's block gas
/// limit.
struct Target {
    forks: Vec<Fork>,
    gas_maximum: u64,
}

/// Parses the declaration and checks the facts the runner uses: unique
/// lowercase fork names, a declared default, validation gas within the
/// declared maximum, and for each fork an engine hardfork whose transaction
/// gas cap and code size limits equal the declared ones. A fork's budget is
/// its consensus cap, or the validation gas when it declares none.
fn check_declaration(text: &str) -> Result<Target, String> {
    let declaration: Declaration =
        serde_json::from_str(text).map_err(|e| format!("target-declaration: {e}"))?;
    if declaration.format != DECLARATION_FORMAT {
        return Err("target-declaration: format".into());
    }
    let gas_maximum = declaration.validation_gas_maximum;
    if !(1..=gas_maximum).contains(&declaration.validation_gas) {
        return Err("target-declaration: validation gas".into());
    }
    let mut forks: Vec<Fork> = Vec::new();
    for row in declaration.forks {
        if row.name.is_empty()
            || !row.name.bytes().all(|b| b.is_ascii_lowercase())
            || forks.iter().any(|fork| fork.name == row.name)
        {
            return Err(format!("target-declaration: fork name {}", row.name));
        }
        let spec = SpecId::from_str(&row.hardfork)
            .map_err(|_| format!("target-declaration: hardfork {}", row.hardfork))?;
        let engine = CfgEnv::new_with_spec(spec);
        if engine.tx_gas_limit_cap() != row.transaction_gas_cap.unwrap_or(u64::MAX)
            || u64::try_from(engine.max_code_size()) != Ok(row.runtime_code_bytes)
            || u64::try_from(engine.max_initcode_size()) != Ok(row.initcode_bytes)
        {
            return Err(format!(
                "target-declaration: fork {} differs from the engine's {}",
                row.name, row.hardfork
            ));
        }
        let budget = row
            .transaction_gas_cap
            .unwrap_or(declaration.validation_gas);
        if budget > gas_maximum {
            return Err(format!(
                "target-declaration: fork {} budget exceeds the validation gas maximum",
                row.name
            ));
        }
        forks.push(Fork {
            name: row.name,
            spec,
            budget,
        });
    }
    if !forks
        .iter()
        .any(|fork| fork.name == declaration.default_fork)
    {
        return Err("target-declaration: default fork".into());
    }
    Ok(Target { forks, gas_maximum })
}

static TARGET: LazyLock<Result<Target, String>> = LazyLock::new(|| check_declaration(DECLARATION));

fn target() -> &'static Target {
    TARGET.as_ref().expect("checked declaration")
}

/// A request's fork: an index into the declared forks, spelled by its name.
#[derive(Clone, Copy)]
struct EvmFork(usize);
impl EvmFork {
    fn declared(self) -> &'static Fork {
        &target().forks[self.0]
    }
    fn spec(self) -> SpecId {
        self.declared().spec
    }
    fn budget(self) -> u64 {
        self.declared().budget
    }
}
impl Serialize for EvmFork {
    fn serialize<S: serde::Serializer>(&self, encoder: S) -> Result<S::Ok, S::Error> {
        encoder.serialize_str(&self.declared().name)
    }
}
impl<'de> Deserialize<'de> for EvmFork {
    fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        let name = String::deserialize(decoder)?;
        let target = TARGET.as_ref().map_err(serde::de::Error::custom)?;
        target
            .forks
            .iter()
            .position(|fork| fork.name == name)
            .map(Self)
            .ok_or_else(|| serde::de::Error::custom("unsupported-fork"))
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    creation_bytecode: String,
    calldata: String,
    #[serde(default)]
    gas_limit: Option<u64>,
    fork: EvmFork,
    #[serde(default)]
    deployment_gas_limit: Option<u64>,
    #[serde(default)]
    expected_runtime_bytecode: Option<String>,
    #[serde(default)]
    repeat_count: Option<u64>,
}

#[derive(Serialize)]
struct Primitive {
    kind: &'static str,
    input: String,
    output: String,
    status: &'static str,
    pc: Option<usize>,
}

struct PendingKeccak {
    offset: Option<usize>,
    length: Option<usize>,
    pc: usize,
}

#[derive(Default)]
struct Trace {
    events: Vec<Primitive>,
    bytes: usize,
    error: Option<&'static str>,
    pending: Option<PendingKeccak>,
    sha_calls: Vec<usize>,
    memory_high_water: usize,
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn unhex(value: &str) -> Result<Vec<u8>, String> {
    let value = value.strip_prefix("0x").unwrap_or(value);
    if !value.len().is_multiple_of(2) || !value.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err("invalid-hex".into());
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).map_err(|e| e.to_string())
        })
        .collect()
}

impl Trace {
    fn room(&mut self, bytes: usize) -> bool {
        if self.error.is_some() {
            return false;
        }
        if self.events.len() >= MAX_EVENTS || bytes > MAX_TRACE_BYTES.saturating_sub(self.bytes) {
            self.error = Some("trace-capacity");
            return false;
        }
        self.bytes += bytes;
        true
    }
}

impl<CTX: ContextTr> Inspector<CTX> for Trace {
    fn step(&mut self, interp: &mut Interpreter, _context: &mut CTX) {
        if interp.bytecode.opcode() != 0x20 {
            return;
        }
        let stack = interp.stack.data();
        // Underflow/OOG never creates a completed primitive event.
        if stack.len() >= 2 {
            self.pending = Some(PendingKeccak {
                offset: usize::try_from(stack[stack.len() - 1]).ok(),
                length: usize::try_from(stack[stack.len() - 2]).ok(),
                pc: interp.bytecode.pc(),
            });
        }
    }

    fn step_end(&mut self, interp: &mut Interpreter, _context: &mut CTX) {
        self.memory_high_water = self.memory_high_water.max(interp.memory.size());
        let Some(pending) = self.pending.take() else {
            return;
        };
        // Successful KECCAK leaves no control action. On exceptional execution
        // no hash was computed, even if an earlier opcode expanded memory.
        if interp.bytecode.action.is_some() {
            return;
        }
        let Some(length) = pending.length else {
            self.error = Some("trace-length-overflow");
            return;
        };
        if !self.room(length) {
            return;
        }
        // A zero-length memory operation ignores even an overflowing offset.
        let input = if length == 0 {
            String::new()
        } else if let Some(offset) = pending.offset.filter(|offset| {
            offset
                .checked_add(length)
                .is_some_and(|end| end <= interp.memory.size())
        }) {
            hex(&interp.memory.slice(offset..offset + length))
        } else {
            self.error = Some("trace-memory-range");
            return;
        };
        let Some(output) = interp.stack.data().last() else {
            self.error = Some("trace-missing-result");
            return;
        };
        self.events.push(Primitive {
            kind: "keccak256",
            input,
            output: hex(&output.to_be_bytes::<32>()),
            status: "return",
            pc: Some(pending.pc),
        });
    }

    fn call(&mut self, context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        if inputs.bytecode_address == Address::with_last_byte(2) {
            // Copy here: revm's shared call-input range may be reused on return.
            if self.room(inputs.input.len()) {
                let index = self.events.len();
                self.events.push(Primitive {
                    kind: "sha256",
                    input: hex(&inputs.input.bytes(context)),
                    output: String::new(),
                    status: "pending",
                    pc: None,
                });
                self.sha_calls.push(index);
            }
        }
        None
    }

    fn call_end(&mut self, _context: &mut CTX, inputs: &CallInputs, outcome: &mut CallOutcome) {
        if inputs.bytecode_address == Address::with_last_byte(2)
            && let Some(index) = self.sha_calls.pop()
        {
            let event = &mut self.events[index];
            event.output = hex(outcome.output());
            event.status = if outcome.instruction_result().is_ok() {
                "return"
            } else {
                "halt"
            };
        }
    }
}

fn result_json(result: &ExecutionResult) -> Value {
    let (status, reason) = match result {
        ExecutionResult::Success { reason, .. } => ("return", format!("{reason:?}")),
        ExecutionResult::Revert { .. } => ("revert", "Revert".into()),
        ExecutionResult::Halt { reason, .. } => ("halt", format!("{reason:?}")),
    };
    json!({"status": status, "reason": reason,
        "output": result.output().map(|bytes| hex(bytes)).unwrap_or_default(),
        "gas_used": result.tx_gas_used()})
}

fn run(request: Request) -> Result<Value, String> {
    let repeat = request.repeat_count.unwrap_or(1);
    if !(1..=MAX_REPEAT).contains(&repeat) {
        return Err("runner-repeat-cap".into());
    }
    // Without explicit limits, deployment and calls request the fork's budget.
    let gas_limit = request.gas_limit.unwrap_or(request.fork.budget());
    let deploy_gas = request
        .deployment_gas_limit
        .unwrap_or(request.fork.budget());
    let gas_maximum = target().gas_maximum;
    if gas_limit > gas_maximum || deploy_gas > gas_maximum {
        return Err("runner-gas-cap".into());
    }
    let creation = unhex(&request.creation_bytecode)?;
    let calldata = unhex(&request.calldata)?;
    let expected = request
        .expected_runtime_bytecode
        .as_deref()
        .map(unhex)
        .transpose()?;
    let caller = Address::with_last_byte(0x42);
    let mut db = CacheDB::<EmptyDB>::default();
    db.insert_account_info(
        caller,
        AccountInfo {
            balance: U256::MAX,
            ..Default::default()
        },
    );
    let context = Context::mainnet()
        .with_db(db)
        .modify_cfg_chained(|cfg| cfg.set_spec_and_mainnet_gas_params(request.fork.spec()))
        .modify_block_chained(|block| {
            block.gas_limit = gas_maximum;
            block.basefee = 0;
        });
    let mut evm = context.build_mainnet_with_inspector(Trace::default());
    let deployment = evm
        .inspect_tx_commit(TxEnv {
            caller,
            kind: TxKind::Create,
            data: Bytes::from(creation),
            gas_limit: deploy_gas,
            gas_price: 0,
            nonce: 0,
            ..Default::default()
        })
        .map_err(|e| format!("deployment-transaction: {e:?}"))?;
    let deployment_trace = std::mem::take(&mut evm.inspector);
    if let Some(error) = deployment_trace.error {
        return Err(error.into());
    }
    let Some(address) = deployment.created_address() else {
        return Ok(
            json!({"engine":"revm/43.0.3", "fork":request.fork, "phase":"deployment",
            "status":result_json(&deployment)["status"], "deployment":result_json(&deployment),
            "output":result_json(&deployment)["output"], "deployment_gas":deployment.tx_gas_used(),
            "runtime_gas":null, "code_size":0, "trace":[], "deployment_trace":deployment_trace.events}),
        );
    };
    // Read committed installed code, not a bytecode section supplied by a caller.
    let account = evm
        .ctx
        .journaled_state
        .database
        .basic(address)
        .map_err(|e| format!("installed-account: {e:?}"))?
        .ok_or("missing-installed-account")?;
    let code = evm
        .ctx
        .journaled_state
        .database
        .code_by_hash(account.code_hash)
        .map_err(|e| format!("installed-code: {e:?}"))?
        .original_bytes();
    if expected
        .as_ref()
        .is_some_and(|expected| expected.as_slice() != code.as_ref())
    {
        return Err("installed-runtime-mismatch".into());
    }
    let mut calls = Vec::new();
    for nonce in 1..=repeat {
        let execution = evm
            .inspect_tx_commit(TxEnv {
                caller,
                kind: TxKind::Call(address),
                data: Bytes::copy_from_slice(&calldata),
                gas_limit,
                gas_price: 0,
                nonce,
                ..Default::default()
            })
            .map_err(|e| format!("runtime-transaction: {e:?}"))?;
        // Each transaction commits into this same database. Taking the inspector
        // resets passive trace limits and memory accounting without resetting state.
        let trace = std::mem::take(&mut evm.inspector);
        if let Some(error) = trace.error {
            return Err(error.into());
        }
        let installed = evm
            .ctx
            .journaled_state
            .database
            .basic(address)
            .map_err(|e| format!("installed-account: {e:?}"))?
            .ok_or("missing-installed-account")?;
        let installed_code = evm
            .ctx
            .journaled_state
            .database
            .code_by_hash(installed.code_hash)
            .map_err(|e| format!("installed-code: {e:?}"))?
            .original_bytes();
        if installed_code != code {
            return Err("installed-runtime-changed".into());
        }
        let mut call = result_json(&execution);
        call["nonce"] = json!(nonce);
        call["address"] = json!(address.to_string());
        call["memory_high_water"] = json!(trace.memory_high_water);
        call["trace"] = json!(trace.events);
        calls.push(call);
    }
    let execution_json = &calls[0];
    Ok(
        json!({"engine":"revm/43.0.3", "fork":request.fork, "phase":"runtime",
        "status":execution_json["status"], "reason":execution_json["reason"],
        "output":execution_json["output"], "deployment":result_json(&deployment),
        "deployment_gas":deployment.tx_gas_used(), "runtime_gas":execution_json["gas_used"],
        "code_size":code.len(), "runtime_bytecode":hex(&code), "address":address.to_string(),
        "memory_high_water":execution_json["memory_high_water"],
        "trace":execution_json["trace"], "calls":calls,
        "deployment_trace":deployment_trace.events}),
    )
}

fn main() {
    let result = (|| {
        // A declaration the engine contradicts refuses every request.
        TARGET.as_ref().map_err(Clone::clone)?;
        let mut bytes = Vec::new();
        io::stdin()
            .take(MAX_JSON + 1)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        if bytes.len() > MAX_JSON as usize {
            return Err("runner-input-limit".into());
        }
        run(serde_json::from_slice(&bytes).map_err(|e| format!("request-json: {e}"))?)
    })();
    match result {
        Ok(value) => println!("{value}"),
        Err(error) => {
            println!("{}", json!({"error":error}));
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declared_forks_match_the_engine() {
        let target = check_declaration(DECLARATION).unwrap();
        let forks = target.forks;
        let declaration: Value = serde_json::from_str(DECLARATION).unwrap();
        assert_eq!(
            target.gas_maximum,
            declaration["validation_gas_maximum"].as_u64().unwrap()
        );
        let rows = declaration["forks"].as_array().unwrap();
        assert_eq!(forks.len(), rows.len());
        for (fork, row) in forks.iter().zip(rows) {
            assert_eq!(fork.name, row["name"]);
            assert_eq!(fork.spec.to_string(), row["hardfork"]);
            // The consensus cap, or the declared validation gas without one.
            let budget = row["transaction_gas_cap"]
                .as_u64()
                .unwrap_or(declaration["validation_gas"].as_u64().unwrap());
            assert_eq!(fork.budget, budget);
        }
    }

    #[test]
    fn osaka_transaction_cap_applies_to_deployment_and_calls() {
        let fork = target()
            .forks
            .iter()
            .position(|fork| fork.name == "osaka")
            .unwrap();
        let cap = EvmFork(fork).budget();
        let request = |call, deployment| Request {
            // Deploy one STOP byte as the exact runtime.
            creation_bytecode: "6001600c60003960016000f300".into(),
            calldata: String::new(),
            gas_limit: Some(call),
            fork: EvmFork(fork),
            deployment_gas_limit: Some(deployment),
            expected_runtime_bytecode: Some("00".into()),
            repeat_count: Some(1),
        };
        let accepted = run(request(cap, cap)).unwrap();
        assert_eq!(accepted["status"], "return");
        assert!(
            run(request(cap + 1, cap))
                .unwrap_err()
                .starts_with("runtime-transaction:")
        );
        assert!(
            run(request(cap, cap + 1))
                .unwrap_err()
                .starts_with("deployment-transaction:")
        );
    }

    #[test]
    fn requested_gas_above_the_declared_maximum_refuses() {
        let request = |gas_limit, deployment_gas_limit| Request {
            creation_bytecode: String::new(),
            calldata: String::new(),
            gas_limit: Some(gas_limit),
            fork: EvmFork(0),
            deployment_gas_limit: Some(deployment_gas_limit),
            expected_runtime_bytecode: None,
            repeat_count: None,
        };
        let maximum = target().gas_maximum;
        for (call, deployment) in [(maximum + 1, maximum), (maximum, maximum + 1)] {
            assert_eq!(
                run(request(call, deployment)).err().as_deref(),
                Some("runner-gas-cap")
            );
        }
    }

    #[test]
    fn engine_disagreements_and_unknown_fields_refuse() {
        let declaration: Value = serde_json::from_str(DECLARATION).unwrap();
        let maximum = declaration["validation_gas_maximum"].as_u64().unwrap();
        let edits: [(&str, Value); 12] = [
            ("/validation_gas", json!(0)),
            ("/validation_gas", json!(maximum + 1)),
            ("/validation_gas_maximum", json!(0)),
            ("/validation_gas_maximum", Value::Null),
            ("/forks/0/runtime_code_bytes", json!(24577)),
            ("/forks/0/initcode_bytes", json!(49153)),
            ("/forks/0/transaction_gas_cap", json!(16777216)),
            ("/forks/0/hardfork", json!("Latest")),
            ("/forks/0/name", json!("Cancun")),
            ("/default_fork", json!("shanghai")),
            ("/format", json!("zkc.evm-target/1")),
            ("/forks/0/extra", json!(true)),
        ];
        for (path, value) in edits {
            let mut changed = declaration.clone();
            match changed.pointer_mut(path) {
                Some(slot) => *slot = value,
                None => {
                    let (parent, key) = path.rsplit_once('/').unwrap();
                    changed.pointer_mut(parent).unwrap()[key] = value;
                }
            }
            let refused = check_declaration(&changed.to_string()).err();
            assert!(
                refused.is_some_and(|e| e.starts_with("target-declaration")),
                "{path}"
            );
        }
        let mut repeated = declaration;
        let first = repeated["forks"][0].clone();
        repeated["forks"].as_array_mut().unwrap().push(first);
        assert!(check_declaration(&repeated.to_string()).is_err());
    }
}
