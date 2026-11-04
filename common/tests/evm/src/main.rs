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

/// Physical call diagnostics, deliberately separate from the exact hash oracle.
#[derive(Serialize)]
struct PrecompileCall {
    kind: &'static str,
    address: String,
    input: String,
    output: String,
    status: &'static str,
    reason: String,
    precompile_called: bool,
    /// Number of hash events already entered when this call was reached.
    hash_event_frontier: usize,
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
    precompile_events: Vec<PrecompileCall>,
    precompile_bytes: usize,
    // One slot for every call hook, including unobserved calls and refused
    // captures. A nested return must never consume its parent's event slot.
    precompile_calls: Vec<Option<usize>>,
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

    fn precompile_room(&mut self, bytes: usize, new_event: bool) -> bool {
        if self.error.is_some() {
            return false;
        }
        if (new_event && self.precompile_events.len() >= MAX_EVENTS)
            || bytes > MAX_TRACE_BYTES.saturating_sub(self.precompile_bytes)
        {
            self.error = Some("precompile-trace-capacity");
            return false;
        }
        self.precompile_bytes += bytes;
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
        let kind = match inputs.bytecode_address {
            address if address == Address::with_last_byte(0x05) => Some("modexp"),
            address if address == Address::with_last_byte(0x0b) => Some("bls12_g1add"),
            address if address == Address::with_last_byte(0x0c) => Some("bls12_g1msm"),
            _ => None,
        };
        let mut index = None;
        if let Some(kind) = kind
            && self.precompile_room(inputs.input.len(), true)
        {
            index = Some(self.precompile_events.len());
            self.precompile_events.push(PrecompileCall {
                kind,
                address: inputs.bytecode_address.to_string(),
                // Capture before nested execution or a shared-memory return.
                input: hex(&inputs.input.as_bytes(context)),
                output: String::new(),
                status: "pending",
                reason: String::new(),
                precompile_called: false,
                hash_event_frontier: self.events.len(),
            });
        }
        self.precompile_calls.push(index);
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
        if let Some(Some(index)) = self.precompile_calls.pop()
            && self.precompile_room(outcome.output().len(), false)
        {
            let event = &mut self.precompile_events[index];
            event.output = hex(outcome.output());
            event.status = if outcome.instruction_result().is_ok() {
                "return"
            } else if outcome.instruction_result().is_revert() {
                "revert"
            } else {
                "halt"
            };
            event.reason = format!("{:?}", outcome.instruction_result());
            event.precompile_called = outcome.was_precompile_called;
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
            "runtime_gas":null, "code_size":0, "trace":[], "precompile_trace":[],
            "deployment_trace":deployment_trace.events,
            "deployment_precompile_trace":deployment_trace.precompile_events}),
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
        call["precompile_trace"] = json!(trace.precompile_events);
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
        "trace":execution_json["trace"], "precompile_trace":execution_json["precompile_trace"],
        "calls":calls, "deployment_trace":deployment_trace.events,
        "deployment_precompile_trace":deployment_trace.precompile_events}),
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
    use revm::{
        ExecuteCommitEvm,
        bytecode::Bytecode,
        interpreter::{CallInput, Gas, InstructionResult, InterpreterResult},
    };

    fn fork_named(name: &str) -> EvmFork {
        EvmFork(
            target()
                .forks
                .iter()
                .position(|fork| fork.name == name)
                .unwrap(),
        )
    }

    fn creation_for(runtime: &[u8]) -> Vec<u8> {
        let length = u16::try_from(runtime.len()).unwrap().to_be_bytes();
        let mut creation = vec![0x61, length[0], length[1], 0x61, 0, 13, 0x5f, 0x39, 0x61];
        creation.extend(length);
        creation.extend([0x5f, 0xf3]);
        creation.extend(runtime);
        creation
    }

    fn runtime_request(runtime: &[u8], calldata: &[u8], fork: &str, repeat: u64) -> Request {
        Request {
            creation_bytecode: hex(&creation_for(runtime)),
            calldata: hex(calldata),
            gas_limit: Some(2_000_000),
            fork: fork_named(fork),
            deployment_gas_limit: None,
            expected_runtime_bytecode: Some(hex(runtime)),
            repeat_count: Some(repeat),
        }
    }

    fn push(program: &mut Vec<u8>, value: usize) {
        program.push(0x61);
        program.extend(u16::try_from(value).unwrap().to_be_bytes());
    }

    fn staticcall(
        program: &mut Vec<u8>,
        address: u8,
        input: (usize, usize),
        output: (usize, usize),
        gas: bool,
    ) {
        for value in [output.1, output.0, input.1, input.0, usize::from(address)] {
            push(program, value);
        }
        program.push(if gas { 0x5a } else { 0x5f });
        program.push(0xfa);
    }

    fn modexp_input() -> Vec<u8> {
        let mut input = vec![0; 96];
        for index in [31, 63, 95] {
            input[index] = 1;
        }
        // 2^5 mod 13 = 6. Trailing bytes must be observed verbatim.
        input.extend([2, 5, 13, 0xde, 0xad]);
        input
    }

    fn g1_generator() -> Vec<u8> {
        // Uncompressed affine BLS12-381 generator with EIP-2537 padding.
        unhex(concat!(
            "00000000000000000000000000000000",
            "17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
            "00000000000000000000000000000000",
            "08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1"
        )).unwrap()
    }

    fn physical_event(
        address: u8,
        input: &[u8],
        output: &[u8],
        frontier: usize,
        reason: &str,
        called: bool,
    ) -> Value {
        let kind = match address {
            5 => "modexp",
            11 => "bls12_g1add",
            12 => "bls12_g1msm",
            _ => unreachable!(),
        };
        json!({"kind":kind, "address":Address::with_last_byte(address).to_string(),
            "input":hex(input), "output":hex(output), "status":"return", "reason":reason,
            "precompile_called":called, "hash_event_frontier":frontier})
    }

    /// Compare passive inspection with ordinary engine execution, including gas.
    fn observe_runtime(
        runtime: &[u8],
        calldata: &[u8],
        spec: SpecId,
        accounts: &[(Address, Vec<u8>)],
    ) -> (ExecutionResult, Trace) {
        let caller = Address::with_last_byte(0x42);
        let address = Address::with_last_byte(0x99);
        let mut db = CacheDB::<EmptyDB>::default();
        db.insert_account_info(
            caller,
            AccountInfo {
                balance: U256::MAX,
                ..Default::default()
            },
        );
        for (address, code) in
            std::iter::once((address, runtime.to_vec())).chain(accounts.iter().cloned())
        {
            db.insert_account_info(
                address,
                AccountInfo::default().with_code(Bytecode::new_raw(Bytes::from(code))),
            );
        }
        let context = Context::mainnet()
            .with_db(db)
            .modify_cfg_chained(|cfg| cfg.set_spec_and_mainnet_gas_params(spec))
            .modify_block_chained(|block| {
                block.gas_limit = target().gas_maximum;
                block.basefee = 0;
            });
        let tx = TxEnv {
            caller,
            kind: TxKind::Call(address),
            data: Bytes::copy_from_slice(calldata),
            gas_limit: 2_000_000,
            gas_price: 0,
            ..Default::default()
        };
        let mut ordinary = context.clone().build_mainnet();
        let expected = ordinary.transact_commit(tx.clone()).unwrap();
        let mut observed = context.build_mainnet_with_inspector(Trace::default());
        let actual = observed.inspect_tx_commit(tx).unwrap();
        assert_eq!(actual, expected, "inspection changed execution or gas");
        assert!(observed.inspector.precompile_calls.is_empty());
        (actual, observed.inspector)
    }

    #[test]
    fn exact_physical_precompile_bytes_order_and_repeated_fields() {
        let modexp = modexp_input();
        let generator = g1_generator();
        let mut add = generator.clone();
        add.extend([0; 128]); // G + infinity = G.
        let mut msm = generator.clone();
        msm.extend([0; 31]);
        msm.push(1); // 1 * G = G.
        let calldata = [modexp.clone(), add.clone(), msm.clone()].concat();
        let mut runtime = unhex("365f5f37").unwrap(); // CALLDATACOPY.
        let first_pc = runtime.len() + 2;
        runtime.extend([0x5f, 0x5f, 0x20, 0x50]);
        staticcall(&mut runtime, 5, (0, modexp.len()), (2048, 1), true);
        runtime.push(0x50);
        staticcall(&mut runtime, 2, (0, 0), (2080, 32), true);
        runtime.push(0x50);
        staticcall(
            &mut runtime,
            11,
            (modexp.len(), add.len()),
            (2112, 128),
            true,
        );
        runtime.push(0x50);
        let last_pc = runtime.len() + 2;
        runtime.extend([0x5f, 0x5f, 0x20, 0x50]);
        staticcall(
            &mut runtime,
            12,
            (modexp.len() + add.len(), msm.len()),
            (2240, 128),
            true,
        );
        runtime.push(0x50);
        push(&mut runtime, 128);
        push(&mut runtime, 2240);
        runtime.push(0xf3);
        let empty_keccak = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470";
        let expected_hashes = json!([
            {"kind":"keccak256", "input":"", "output":empty_keccak, "status":"return", "pc":first_pc},
            {"kind":"sha256", "input":"", "output":"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "status":"return", "pc":null},
            {"kind":"keccak256", "input":"", "output":empty_keccak, "status":"return", "pc":last_pc}
        ]);
        let expected_physical = json!([
            physical_event(5, &modexp, &[6], 1, "Return", true),
            physical_event(11, &add, &generator, 2, "Return", true),
            physical_event(12, &msm, &generator, 3, "Return", true)
        ]);
        for fork in ["prague", "osaka"] {
            let result = run(runtime_request(&runtime, &calldata, fork, 3)).unwrap();
            assert_eq!(result["runtime_bytecode"], hex(&runtime));
            assert_eq!(result["precompile_trace"], expected_physical);
            assert_eq!(result["trace"], expected_hashes);
            assert_eq!(result["deployment_precompile_trace"], json!([]));
            for call in result["calls"].as_array().unwrap() {
                assert_eq!(call["output"], hex(&generator));
                assert_eq!(call["status"], "return");
                assert_eq!(call["precompile_trace"], expected_physical);
                assert_eq!(call["trace"], expected_hashes);
            }
            let (execution, trace) =
                observe_runtime(&runtime, &calldata, fork_named(fork).spec(), &[]);
            assert_eq!(result_json(&execution)["output"], hex(&generator));
            assert_eq!(
                serde_json::to_value(trace.precompile_events).unwrap(),
                expected_physical
            );
        }
    }

    #[test]
    fn physical_output_is_not_the_callers_truncated_memory_copy() {
        let generator = g1_generator();
        let mut add = generator.clone();
        add.extend([0; 128]);
        for (address, input, output) in [(5, modexp_input(), vec![6]), (11, add, generator)] {
            for output_length in [0, 1, 32, 192] {
                let mut runtime = unhex("365f5f37").unwrap();
                staticcall(
                    &mut runtime,
                    address,
                    (0, input.len()),
                    (0, output_length),
                    true,
                );
                runtime.extend([0x50, 0x00]);
                let (_, trace) = observe_runtime(&runtime, &input, SpecId::OSAKA, &[]);
                assert_eq!(
                    serde_json::to_value(trace.precompile_events).unwrap(),
                    json!([physical_event(address, &input, &output, 0, "Return", true)])
                );
            }
        }
    }

    #[test]
    fn reached_failures_and_inactive_addresses_keep_actual_empty_outputs() {
        for (address, input) in [(5, modexp_input()), (11, vec![0xff]), (12, vec![0xff])] {
            for gas in [false, true] {
                if address == 5 && gas {
                    continue;
                }
                let mut runtime = unhex("365f5f37").unwrap();
                staticcall(&mut runtime, address, (0, input.len()), (256, 128), gas);
                runtime.extend(unhex("5f5260205ff3").unwrap()); // Return the actual CALL success flag.
                let (execution, trace) = observe_runtime(&runtime, &input, SpecId::OSAKA, &[]);
                assert_eq!(result_json(&execution)["output"], hex(&[0; 32]));
                let events = serde_json::to_value(trace.precompile_events).unwrap();
                assert_eq!(events[0]["input"], hex(&input));
                assert_eq!(events[0]["output"], "");
                assert_eq!(events[0]["status"], "halt");
                assert_eq!(events[0]["precompile_called"], true);
                assert_eq!(
                    events[0]["reason"],
                    if gas || address == 12 {
                        "PrecompileError"
                    } else {
                        "PrecompileOOG"
                    }
                );
                assert!(trace.events.is_empty());
            }
        }
        for address in [11, 12] {
            let input = [0xaa, 0xbb];
            let mut runtime = unhex("365f5f37").unwrap();
            staticcall(&mut runtime, address, (0, 2), (0, 2), true);
            runtime.extend(unhex("5060025ff3").unwrap());
            let (execution, trace) = observe_runtime(&runtime, &input, SpecId::CANCUN, &[]);
            assert_eq!(result_json(&execution)["output"], "aabb"); // Untouched output memory is not return data.
            assert_eq!(
                serde_json::to_value(trace.precompile_events).unwrap(),
                json!([physical_event(address, &input, &[], 0, "Stop", false)])
            );
        }
    }

    #[test]
    fn nested_observed_and_unobserved_calls_preserve_slots_and_entry_bytes() {
        // Cancun permits code at the inactive G1ADD address. Its child G1MSM
        // address has no account; ordinary and SHA calls must also nest safely.
        let mut child = unhex("365f5f37365f2050").unwrap();
        staticcall(&mut child, 12, (0, 3), (0, 3), true);
        child.push(0x50);
        staticcall(&mut child, 0x44, (0, 0), (0, 0), true);
        child.push(0x50);
        staticcall(&mut child, 2, (0, 3), (0, 32), true);
        child.extend(unhex("5060ff5f5360015ff3").unwrap());
        let mut runtime = unhex("365f5f37").unwrap();
        staticcall(&mut runtime, 11, (0, 3), (0, 1), true);
        runtime.extend(unhex("5060015ff3").unwrap());
        for (opcode, status, reason) in [(0xf3, "return", "Return"), (0xfd, "revert", "Revert")] {
            *child.last_mut().unwrap() = opcode;
            let (execution, trace) = observe_runtime(
                &runtime,
                b"abc",
                SpecId::CANCUN,
                &[(Address::with_last_byte(11), child.clone())],
            );
            assert_eq!(result_json(&execution)["output"], "ff");
            let mut parent_event = physical_event(11, b"abc", &[0xff], 0, reason, false);
            parent_event["status"] = json!(status);
            assert_eq!(
                serde_json::to_value(trace.precompile_events).unwrap(),
                json!([
                    parent_event,
                    physical_event(12, b"abc", &[], 1, "Stop", false)
                ])
            );
            assert_eq!(trace.events.len(), 2);
            assert_eq!(trace.events[1].input, "616263");
            assert_eq!(
                trace.events[1].output,
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
            );
        }
    }

    #[test]
    fn physical_events_survive_later_revert_and_unreached_calls_are_absent() {
        let input = modexp_input();
        let mut runtime = unhex("365f5f37").unwrap();
        staticcall(&mut runtime, 5, (0, input.len()), (0, 1), true);
        runtime.extend(unhex("505f5ffd").unwrap());
        staticcall(&mut runtime, 11, (0, 0), (0, 0), true);
        let result = run(runtime_request(&runtime, &input, "osaka", 2)).unwrap();
        for call in result["calls"].as_array().unwrap() {
            assert_eq!(call["status"], "revert");
            assert_eq!(call["trace"], json!([]));
            assert_eq!(
                call["precompile_trace"],
                json!([physical_event(5, &input, &[6], 0, "Return", true)])
            );
        }
    }

    #[test]
    fn deployment_physical_events_are_separate_even_on_failure() {
        let input = modexp_input();
        let mut constructor = Vec::new();
        // Put an exact ModExp request in memory without using calldata.
        for (index, chunk) in input.chunks(32).enumerate() {
            let mut word = [0; 32];
            word[..chunk.len()].copy_from_slice(chunk);
            constructor.push(0x7f);
            constructor.extend(word);
            push(&mut constructor, index * 32);
            constructor.push(0x52);
        }
        staticcall(&mut constructor, 5, (0, input.len()), (256, 1), true);
        constructor.push(0x50);
        for ending in ["60015ff3", "5f5ffd"] {
            let mut creation = constructor.clone();
            creation.extend(unhex(ending).unwrap()); // Deploy STOP or revert.
            // Clear memory[0] so successful deployment installs STOP.
            let suffix_length = unhex(ending).unwrap().len();
            let insertion = creation.len() - suffix_length;
            creation.splice(insertion..insertion, [0x5f, 0x5f, 0x53]);
            let mut request = runtime_request(&[0], &[], "osaka", 1);
            request.creation_bytecode = hex(&creation);
            let result = run(request).unwrap();
            assert_eq!(
                result["phase"],
                if ending == "5f5ffd" {
                    "deployment"
                } else {
                    "runtime"
                }
            );
            assert_eq!(result["precompile_trace"], json!([]));
            assert_eq!(result["trace"], json!([]));
            assert_eq!(
                result["deployment_precompile_trace"],
                json!([physical_event(5, &input, &[6], 0, "Return", true)])
            );
        }
    }

    fn hook_inputs(address: u8, input: Vec<u8>) -> CallInputs {
        CallInputs {
            bytecode_address: Address::with_last_byte(address),
            input: CallInput::Bytes(Bytes::from(input)),
            return_memory_offset: 0..0,
            gas_limit: 1_000_000,
            reservoir: 0,
            known_bytecode: Default::default(),
            target_address: Address::with_last_byte(address),
            caller: Address::with_last_byte(0x42),
            value: Default::default(),
            scheme: revm::interpreter::CallScheme::StaticCall,
            is_static: true,
            charged_new_account_state_gas: false,
        }
    }

    fn hook_outcome(output: Vec<u8>) -> CallOutcome {
        CallOutcome::new(
            InterpreterResult {
                result: InstructionResult::Return,
                output: Bytes::from(output),
                gas: Gas::new(1_000_000),
            },
            0..0,
        )
    }

    #[test]
    fn physical_capacity_counts_both_directions_and_keeps_hash_budget_separate() {
        let mut trace = Trace {
            precompile_bytes: MAX_TRACE_BYTES - 3,
            ..Default::default()
        };
        let mut context = Context::mainnet();
        let mut inputs = hook_inputs(5, vec![0xaa]);
        assert!(trace.call(&mut context, &mut inputs).is_none());
        let mut outcome = hook_outcome(vec![0xbb, 0xcc]);
        let original = outcome.clone();
        trace.call_end(&mut context, &inputs, &mut outcome);
        assert_eq!(outcome, original);
        assert_eq!(trace.precompile_bytes, MAX_TRACE_BYTES);
        assert!(trace.error.is_none());
        assert_eq!(trace.precompile_events[0].output, "bbcc");
        assert_eq!(trace.bytes, 0);
        assert!(trace.room(1)); // Hash capacity is unchanged.
        assert!(!trace.precompile_room(1, true));
        assert_eq!(trace.error, Some("precompile-trace-capacity"));

        let mut trace = Trace {
            precompile_bytes: MAX_TRACE_BYTES - 1,
            ..Default::default()
        };
        let mut inputs = hook_inputs(5, vec![0xaa]);
        trace.call(&mut context, &mut inputs);
        trace.call_end(&mut context, &inputs, &mut outcome);
        assert_eq!(trace.error, Some("precompile-trace-capacity"));
        assert_eq!(trace.precompile_events[0].status, "pending"); // The result will be refused, never forged.
        assert!(trace.precompile_events[0].output.is_empty());
        assert!(trace.precompile_calls.is_empty());

        let mut trace = Trace::default();
        let mut oversized = hook_inputs(5, vec![]);
        oversized.input = CallInput::SharedBuffer(0..MAX_TRACE_BYTES + 1);
        assert!(trace.call(&mut context, &mut oversized).is_none()); // Refuse before touching/copying the range.
        trace.call_end(&mut context, &oversized, &mut outcome);
        assert_eq!(trace.error, Some("precompile-trace-capacity"));
        assert!(trace.precompile_events.is_empty());
        assert!(trace.precompile_calls.is_empty());
    }

    #[test]
    fn physical_event_limit_refuses_without_losing_nested_call_alignment() {
        let mut context = Context::mainnet();
        let mut trace = Trace::default();
        let mut inputs = hook_inputs(5, vec![]);
        let mut outcome = hook_outcome(vec![]);
        for _ in 0..MAX_EVENTS {
            assert!(trace.call(&mut context, &mut inputs).is_none());
            trace.call_end(&mut context, &inputs, &mut outcome);
        }
        assert!(trace.error.is_none());
        assert_eq!(trace.precompile_events.len(), MAX_EVENTS);
        assert!(trace.call(&mut context, &mut inputs).is_none());
        let mut unobserved = hook_inputs(0x44, vec![]);
        trace.call(&mut context, &mut unobserved);
        trace.call_end(&mut context, &unobserved, &mut outcome);
        trace.call_end(&mut context, &inputs, &mut outcome);
        assert_eq!(trace.error, Some("precompile-trace-capacity"));
        assert_eq!(trace.precompile_events.len(), MAX_EVENTS);
        assert!(trace.precompile_calls.is_empty());
        assert!(trace.events.is_empty());
    }

    #[test]
    fn deployed_physical_event_overflow_refuses_the_result() {
        let mut runtime = Vec::new();
        push(&mut runtime, MAX_EVENTS + 1);
        let loop_pc = runtime.len();
        runtime.push(0x5b); // JUMPDEST.
        staticcall(&mut runtime, 5, (0, 0), (0, 0), true);
        // Discard the call flag, decrement the counter and loop while nonzero.
        runtime.extend(unhex("506001900380").unwrap());
        push(&mut runtime, loop_pc);
        runtime.extend([0x57, 0x50, 0x00]);
        let mut request = runtime_request(&runtime, &[], "osaka", 1);
        request.gas_limit = None; // The existing fork budget, with no limit changes.
        assert_eq!(run(request).unwrap_err(), "precompile-trace-capacity");
    }

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
