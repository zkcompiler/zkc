//! Test-only deployment of exact compiler output with passive primitive tracing.
use revm::{
    Context, InspectCommitEvm, Inspector, MainBuilder, MainContext,
    context::TxEnv,
    context_interface::{ContextTr, result::ExecutionResult},
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
use std::io::{self, Read};

const MAX_JSON: u64 = 4 * 1024 * 1024;
const MAX_TRACE_BYTES: usize = 32 * 1024 * 1024;
const MAX_EVENTS: usize = 16384;
const MAX_GAS: u64 = 100_000_000;
const MAX_REPEAT: u64 = 8;

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "lowercase")]
enum EvmFork {
    Cancun,
    Prague,
}
impl<'de> Deserialize<'de> for EvmFork {
    fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self, D::Error> {
        match String::deserialize(decoder)?.as_str() {
            "cancun" => Ok(Self::Cancun),
            "prague" => Ok(Self::Prague),
            _ => Err(serde::de::Error::custom("unsupported-fork")),
        }
    }
}
impl EvmFork {
    fn spec(self) -> SpecId {
        match self {
            Self::Cancun => SpecId::CANCUN,
            Self::Prague => SpecId::PRAGUE,
        }
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    creation_bytecode: String,
    calldata: String,
    gas_limit: u64,
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
    let deploy_gas = request.deployment_gas_limit.unwrap_or(request.gas_limit);
    if request.gas_limit > MAX_GAS || deploy_gas > MAX_GAS {
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
            block.gas_limit = MAX_GAS;
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
                gas_limit: request.gas_limit,
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
