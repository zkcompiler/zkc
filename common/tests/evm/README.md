# Deployed EVM verifier validation

This is an optional test workspace. It does not add an EVM engine to the SDK,
decode a native program in EVM, or implement a replacement Sumcheck prover.
The runner uses revm **43.0.3**, whose MSRV is Rust 1.91, with Rust 1.99 in the
development environment. Its own `Cargo.lock` freezes transitive dependencies.
The selected Cancun or Prague fork is explicit; standard precompiles, gas,
initcode and runtime size limits remain enabled. Each request deploys the supplied
creation bytes once into fresh state, reads the installed code, then invokes that
same deployment one to eight times. Calls
commit storage and advance the caller nonce; passive traces reset for each call.

From the repository root:

```sh
CARGO_BUILD_JOBS=2 \
 CARGO_TARGET_DIR=build/experiments/evm-implementation/evm-target \
 cargo build --locked --manifest-path common/tests/evm/Cargo.toml
ZKC_EVM_RUNNER="$PWD/build/experiments/evm-implementation/evm-target/debug/zkc-evm-test-runner" \
 python3 -m unittest discover -s common/tests/evm -v
```

The Python helpers use only the standard library and the existing independent
Keccak/logical-tree reference. Without `ZKC_EVM_RUNNER`, deployed controls are
explicitly skipped. Do not count those skips as deployed validation.

## Runner protocol

One JSON object on stdin, one on stdout, with hex strings optionally prefixed
by `0x`:

```json
{
  "creation_bytecode": "...",
  "expected_runtime_bytecode": "...",
  "calldata": "...",
  "gas_limit": 20000000,
  "deployment_gas_limit": 5000000,
  "fork": "cancun",
  "repeat_count": 2
}
```

Always supply `expected_runtime_bytecode` for artifact integration. It must come
from the independently authenticated SDK artifact. The runner compares it with
the code read from committed deployed state. The optional field is omitted only
for deployment experiments without an advertised runtime. Bytecode mutations
are passed exactly as supplied, without rewriting or instrumentation.

Results contain `status` (`return`, `revert`, `halt`), `reason`, `output`,
`deployment_gas`, `runtime_gas`, `code_size`, exact `runtime_bytecode`,
`memory_high_water`, ordered runtime `trace` and separate `deployment_trace`.
`calls` contains each invocation's nonce, address, gas, output, memory and trace;
the top-level runtime result describes the first call. `repeat_count` defaults
to one and must be between one and eight. Installed code is checked after every
call. `test_engine.py` uses a storage counter to prove state persists and traces
do not accumulate.
`fork` is exactly `cancun` or `prague`; results repeat that selection. Gas includes
transaction intrinsic gas and the selected fork's normal charges. Deployment
failure sets `phase=deployment` and `runtime_gas=null`. Transaction admission,
JSON, runtime pin and trace-capacity errors use `error` and nonzero process exit;
they are not EVM false/revert/halt. Limits are 4 MiB JSON, 100 million gas per
transaction, 16,384 primitive events and 32 MiB captured preimages. Exceeding a
trace limit refuses the result, so no truncated trace can pass the oracle.

Keccak events capture memory after a successful opcode and the actual resulting
stack word. SHA-256 events capture address-2 call input before revm reuses shared
memory and its actual precompile return. Hooks return no override and modify no
EVM state. Events are preserved across later transaction reverts, allowing
stopped-prefix comparison. A failed Keccak opcode has no completed hash event;
a reached failed SHA-256 call has a failing trace event.

## ABI and execution oracles

`abi.py` encodes standard `verify(bytes[],bytes,bytes)` calls. The strict decoder
implements the accepted canonical target profile: no holes, overlap, alternative
tail order, nonzero padding or trailing bytes. `malformed_cases` supplies actual
mutated calldata to deployed integration tests, independent of backend code.
The argument and wire order is `publicInputs, context, proof`; the identical
`bytes` types in the selector do not distinguish an accidental swap.

`oracle.py` compares all primitive preimages, digests, status and order, including
exact count. It also independently recomputes hashes. A matching prefix never
passes for a completed run. Source stops require an independently expected
prefix through the stop, excluding later frame decoding and later transitions.

`test_engine.py` validates the adapter with small machine-code controls. Its
deleted-final-Keccak mutant returns the same ABI true while failing the oracle.
These controls establish adapter behavior, not compilation of a real protocol.

## solc effect probe

```sh
python3 common/tests/evm/probe.py \
 --solc build/experiments/evm-implementation/tools/solc \
 --runner build/experiments/evm-implementation/evm-target/debug/zkc-evm-test-runner \
 --output build/experiments/evm-implementation/EVM-EXECUTION-PROBE.json
```

The script verifies the pinned solc 0.8.38 executable SHA-256, compiles standard
JSON for Cancun, and deploys every exact resulting artifact. It compares disabled,
enabled and explicit `:` optimizer profiles. A missing runner records compilation
only with `dynamic=false`; it does not establish hash preservation.

Observed with the pinned tool: all three profiles delete an unused final Keccak;
a GAS threshold also loses it. Both an identity-precompile anchor and the
smaller `verbatim_1i_0o(hex"50", finalState)` POP sink retain the required hash
dynamically. The POP sink consumes the computed digest without an additional ABI
result or external call. Each release must pass the exact trace and mutation gates.

Unused deterministic computations are not a construction-effect contract in
Yul. Solidity documents both removal of unused computations and the extra
optimizer stages, including pruning when ordinary optimization is disabled.
`verbatim` is opaque to its optimizer, but may still move, duplicate, combine or
remove unreachable blocks. Use a stack-correct POP sink and keep the pinned
release execution gate; an optimizer setting alone is insufficient. See the
[optimizer documentation](https://docs.soliditylang.org/en/v0.8.38/internals/optimizer.html)
and [verbatim restrictions](https://docs.soliditylang.org/en/v0.8.38/yul.html#verbatim).

## Native SDK fixture adapter

The `evm_native` binary in `zkc-test-drivers` uses the SDK `evm`
feature alongside normal native proof support. Build it from the root workspace:

```sh
CARGO_BUILD_JOBS=2 cargo build --locked -p zkc-test-drivers --bin evm_native
```

The driver uses normal `Project`,
`Compiler`, `PreparedData`, and separate `ProofEntry::prove`/`verify` admissions;
these are the actual current SDK proof APIs. It exports canonical public frames
in the fixture's declared `values, claim, rounds` order, context, full descriptor,
ten-slot root bytes/tree, binding hash, proof and native reports/outputs. The
exported root must equal the independently executed native binding. It never
implements protocol arithmetic beyond preparing the public table and its claim.

```sh
evm_native --compiler "$ZKC_COMPILER_BIN" \
 --project examples/projects/sumcheck-keccak/zkc.toml \
 --entry example::Proof --rounds 4 --context 65766d --budget 64
```

Repeat with rounds 10 for 1,024 values and rounds 0 for the zero-round boundary.
The maintained example imports the Sumcheck library with Max=10 and the accepted
Keccak construction. `--proof FILE` independently verifies supplied proof bytes;
`--values FILE`, `--claim INTEGER`, `--rounds`, `--budget` and `--context HEX`
support malformed/altered-input, stopped-prefix and logical budget controls.

Generate the complete native/reference matrix with:

```sh
python3 common/tests/evm/native_fixtures.py \
 --driver /path/to/evm_native --compiler "$ZKC_COMPILER_BIN" \
 --output build/experiments/evm-implementation/EVM-EXECUTION-FIXTURES
```

`reference.py` independently reconstructs the ten-slot root, lazy scalar frame
decoding, descriptor-derived dynamic origins, challenge reduction, terminal
public-table evaluation and exact hash calls. It consumes SDK proof messages;
it does not implement a replacement producer. The native verifier's actual
primitive calls are not intercepted. Native acceptance, proof messages, binding,
source stops and budget frontiers are checked against the reference instead.
Generated expected traces include the invocation SHA-256 precompile and every
construction Keccak, including the otherwise-unused final delivery hashes.

The matrix includes terminal false after valid round checks, zero-round terminal
false, source rejection before a malformed later frame, reached scalar/length
failures, trailing bytes after both true and false, and logical budget stops.
The `transitions` count in the reference counts completed transitions; native
retirement diagnostics may also count the attempted failing debit.

## Actual artifact comparison

Build the artifact through the normal EVM SDK or CLI and retain its manifest
pin. Optional paired `evm_native --evm-artifact DIR --evm-sha256 PIN` calls
`Artifact::capture` and `Artifact::calldata` on the native input tuple. It checks
source and descriptor agreement and exports calldata, authenticated hashes and
the exact captured bytecode under `evm` in the fixture. `validate.py` compares
that calldata against the independent Python codec and requires supplied
bytecode and the selected execution fork to equal the SDK export. Pass
`--evm-version=prague` to validation and capacity commands for a Prague artifact;
a mismatch refuses before execution. `native_fixtures.py` accepts the same paired
options for the complete matrix.

Pass the unmodified **binary** creation/runtime files to the execution helper; `--bytecode-format hex` is available for explicit hex files.

```sh
python3 common/tests/evm/validate.py \
 --runner /path/to/zkc-evm-test-runner \
 --creation /authenticated/artifact/creation.bin \
 --runtime /authenticated/artifact/runtime.bin \
 --fixture /fixtures/honest-16.json \
 --final-hash-mutant /receipts/final-observation-16.json \
 --output /receipts/deployed-16.json
```

The default oracle reconstructs the maintained Sumcheck fixture. An independently
prepared `--expected-trace` list or reference record is also accepted. Stops use
`--expected-status revert --expected-revert-class source --expected-revert-code 6
--no-controls` (with the exact class and code appropriate to that stop). Every
malformed ABI/proof control requires its exact structured class/code and an
independently expected complete trace frontier. Validation defaults to two calls
to the same deployment, checking the full expected trace on each call. Normal
false returns the canonical 32-byte Boolean zero and still requires the complete trace and proof consumption.

For a unique final hash PC, the helper mutates that opcode to POP in a copy of
the supplied creation/runtime bytes. Real loop observations often share one PC.
For that case, generate the separate negative control with:

```sh
python3 common/tests/evm/mutant.py \
 --solc /pinned/solc --solc-input /authenticated/artifact/solc-input.json \
 --runner /path/to/zkc-evm-test-runner --fixture /fixtures/honest-16.json \
 --creation /authenticated/artifact/creation.bin \
 --runtime /authenticated/artifact/runtime.bin \
 --output /receipts/final-observation-16.json
```

This first recompiles the original input to require exact release byte equality,
deploys the unmodified artifact and checks its full native/reference trace. Its
clearly separate invalid artifact omits only the final delivery value hash at
the fixture's completed generation. It must retain the same Boolean output and
all preceding primitive events while failing the complete oracle. Both versions
use passive revm inspection; no trace outputs or engine overrides are added.
This mutation is a test control and never a publishable verifier artifact.

Repeat for `honest-1024` and its matching generation. `capacity.py` supplies
one-over calldata/context/proof/public-byte/element controls, proof-at-cap final
consumption, authored round-bound and EVM gas-halt controls. Supply a real SDK
fixture with 4,096 context bytes through `--maximum-context-fixture` for the
positive context ceiling. Immutable lower transcript budgets require separate
compiler deployments with matching `EvmOptions`, not a calldata budget field.

The aggregate public-byte check needs a separate compiler deployment whose
`EvmOptions.limits.publicBytes` is one less than the sum of the fixture's public
frames. Supply `--aggregate-creation`, `--aggregate-runtime` and
`--aggregate-public-bytes` together. Each frame is individually bounded, earlier
frames decode successfully, and the final frame crosses the aggregate ceiling;
the required refusal is resource code 11 with no primitive events. A separate
public-frame control requires resource code 5. The default Sumcheck deployment's
type/element bounds prevent reaching its larger aggregate byte ceiling.

Immutable lower budgets and aggregate capacity must come from real compiler
options, with separate artifact identities and matching fixtures. No calldata
field changes a deployment limit. Exact captured release traces, including a
separate omitted-final-hash mutant, are required after source or tool changes.

## Common layout and arithmetic controls

The same adapter tests the shared target layouts without protocol-specific
execution. Build `evm_fixture` in `zkc-test-drivers` and the compiler's
`zkc-evm_wire-test` consumer, then run:

```sh
CARGO_BUILD_JOBS=2 cargo build --locked -p zkc-test-drivers --bin evm_fixture
python3 common/tests/evm/foundation_controls.py \
 --compiler build/compiler/zkc-compile --native-driver target/debug/evm_fixture \
 --solc /pinned/solc --runner /path/to/zkc-evm-test-runner \
 --output build/experiments/evm-foundation
python3 common/tests/evm/wire_controls.py \
 --consumer build/compiler/test/zkc-evm_wire-test --compiler build/compiler/zkc-compile \
 --solc /pinned/solc --runner /path/to/zkc-evm-test-runner \
 --output build/experiments/evm-wire
```

The foundation controls use real native producers, independent prime/binomial
arithmetic, and complete invocation/transcript hash oracles. They cover
structured observations, non-first acceptance, extension-vector strides, nested
and filtered finite callbacks, empty admission, source stops and later malformed
frames. The wire consumer emits the production expected-type helpers; separate
raw-value views check coefficient order independently of their encoder. Its
controls cover whole-value node/element/memory budgets, inactive/empty type
refusals, fixed arrays, and opaque root/path envelopes. Envelope transport does
not establish cryptographic authentication. These are bounded differential
controls, not a general EVM refinement proof.
