# Deployed EVM verifier validation

This is an optional test workspace. It does not add an EVM engine to the SDK,
decode a native program in EVM, or implement a replacement Sumcheck prover.
The runner uses revm **43.0.3**, whose MSRV is Rust 1.91, with Rust 1.99 in the
development environment. Its own `Cargo.lock` freezes transitive dependencies.
The selected fork is explicit and is one of the forks of the
[target declaration](../../../docs/spec/targets/evm.md#target-declaration);
standard precompiles, gas, initcode and runtime size limits remain enabled. The
runner and the Python helpers (`target.py`) read the declaration itself: its
forks, solc release and optimizer settings, ABI selector, deployment ceilings and
revert classes. The runner refuses every request if a declared fork's engine
hardfork has a different transaction gas cap or code size limits. Each request deploys the supplied
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
  "gas_limit": 16777216,
  "deployment_gas_limit": 16777216,
  "fork": "osaka",
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
`fork` is exactly a declared fork name; results repeat that selection. Gas includes
transaction intrinsic gas and the selected fork's normal charges. `gas_limit`
and `deployment_gas_limit` are optional: each defaults to the fork's transaction
budget, its declared consensus transaction gas cap or, for a fork without one,
the declaration's `validation_gas`. The Python helpers request the same budget
for calls and deployment alike, so a runtime at the fork's code size ceiling
always deploys. Deployment
failure sets `phase=deployment` and `runtime_gas=null`. Transaction admission,
JSON, runtime pin and trace-capacity errors use `error` and nonzero process exit;
they are not EVM false/revert/halt. A request above the declaration's
`validation_gas_maximum` refuses with `runner-gas-cap`; that maximum is also the
block gas limit of every run. Other limits are 4 MiB JSON, 16,384 primitive
events and 32 MiB captured preimages. Exceeding a
trace limit refuses the result, so no truncated trace can pass the oracle.

Keccak events capture memory after a successful opcode and the actual resulting
stack word. SHA-256 events capture address-2 call input before revm reuses shared
memory and its actual precompile return. Hooks return no override and modify no
EVM state. Events are preserved across later transaction reverts, allowing
stopped-prefix comparison. A failed Keccak opcode has no completed hash event;
a reached failed SHA-256 call has a failing trace event.

Physical ModExp (`0x05`), EIP-2537 G1ADD (`0x0b`) and G1MSM (`0x0c`)
calls are captured separately in `precompile_trace`. Every entry has `kind`
(`modexp`, `bls12_g1add`, `bls12_g1msm`), the full `address`, exact hex `input`
and `output`, `status` (`return`, `revert`, `halt`), the engine's instruction
`reason`, `precompile_called` and `hash_event_frontier`. The frontier counts
hash events already entered in `trace` at call entry; array order is call-entry
order, including nested calls. The existing hash array and its byte semantics
remain unchanged. Each member of `calls` and the first call's top-level result
use the same physical fields. `deployment_precompile_trace` holds constructor
observations separately, including on failed deployment.

Input is copied at entry before shared memory can be reused, and output comes
from the actual call outcome, including bytes omitted by a short or zero-length
caller output window. A halted call keeps its actual output and reason. An
inactive BLS address with no account returns empty output with reason `Stop`
and `precompile_called=false`; untouched caller memory is not return data.
Reaching an address alone does not establish that a precompile ran. Records
survive later reverts, and unreached calls produce no record. These hooks
observe engine execution without executing calls or overriding outcomes.

The physical array has its own existing-size ceiling of 16,384 events and
32 MiB total raw input **plus output** bytes per transaction. Both directions
are checked before copying or hex encoding. It resets between calls along with
the hash trace; it does not consume the existing hash budget. Overflow refuses
the request with `precompile-trace-capacity` and a nonzero process exit instead
of returning a truncated result. Engine gas, account, fork and resource rules
remain unchanged. Focused Rust tests exercise exact physical bytes, passive
execution and gas agreement, nested callback lifetimes, failures and bounds:

```sh
CARGO_TARGET_DIR=build/typed-evm/runner-target \
 cargo test --locked --manifest-path common/tests/evm/Cargo.toml -j 2
```

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

The script verifies the pinned solc executable SHA-256 and the declared solc
release, compiles standard JSON for the selected declared fork (the declared
default unless `--evm-version` selects another), and deploys every exact
resulting artifact. It compares disabled, enabled and the declared release
optimizer profiles. A missing runner records compilation
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
evm_native --compiler "$ZKC_COMPILER_BIN/zkc-compile" \
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
 --driver /path/to/evm_native --compiler "$ZKC_COMPILER_BIN/zkc-compile" \
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
bytecode and the selected execution fork to equal the SDK export. Pass the
artifact's fork as `--evm-version` to validation and capacity commands when it is
not the declared default; a mismatch refuses before execution. `native_fixtures.py` accepts the same paired
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
frames. Participant-loop controls retain distinct Copy formals bound to the
same parent value, including empty loops and altered messages. Success requires
the exact 32-byte ABI Boolean; refusals require the exact class, code and hash
frontier. The wire consumer emits the production expected-type helpers; separate
raw-value views check coefficient order independently of their encoder. Its
controls cover whole-value node/element/memory budgets, inactive/empty type
refusals, fixed arrays, and opaque root/path envelopes, including the path
ceiling at the declared default and lowered below a path's length. Envelope transport does
not establish cryptographic authentication. These are bounded differential
controls, not a general EVM refinement proof.

The wire controls also deploy `zkc-evm_wire-test --emit-tree-hex`, which calls
the production `evm_tree_hex` runtime helper. They check the complete logical
string header, lowercase hexadecimal payload and returned end offset against
the independent logical-tree encoder. Cases include empty input, 15/16/17 and
31/32/33-byte boundaries, every tail length, multiple bulk chunks, all byte
values, and aligned/unaligned source and destination addresses. Nonzero input
padding and output sentinels expose accidental dependence on trailing loaded
bytes or writes beyond the exact output; full allocation snapshots also check
that input, guards and allocation padding remain untouched. Input and output
are disjoint, as in production: invocation rows and context are ABI-tail
allocations separate from the bounded root buffer. Arbitrary overlapping
buffers are outside this helper's caller invariant.

## Managed Keccak transcript controls

With the same prepared compiler, native fixture driver, wire consumer, pinned
solc and revm runner, run:

```sh
python3 common/tests/evm/transcript_controls.py \
 --compiler build/compiler/zkc-compile --native-driver target/debug/evm_fixture \
 --solc /pinned/solc --runner /path/to/zkc-evm-test-runner \
 --sampler-consumer build/compiler/test/zkc-evm_wire-test \
 --gate-witness-code 5 --gate-rejection-code 0 --sampler-exhaustion-code 15 \
 --output build/experiments/evm-transcript
```

The explicit refusal codes are expectations from the target contract. They are
never inferred from generated Yul, an engine result or a failed run. The default
matrix covers quartic and octic challenges, scalar indices, ordered index blocks, gated
CHECK and repeated occurrences, with real native producers and independently
constructed complete hash traces. Every execution case requires two calls on
the same deployment. The block matrix includes Q=128/129 with bound 256: all
ordered samples are compared with a native echo after subsequent observations
and proof-frame decoding, while the source retains both sampled and echoed
outputs through the final message. Their varied values discriminate overlapping
result compaction from all-zero controls.

`--suite challenge`, `index`, `block`, `gate` or `repeated` selects compiled
cases and may be repeated. With `--sampler-consumer`, separate helper controls
also run. Use `--suite helpers` with the arguments above to run only those
controls; compiler/native-driver paths must still exist for tool fingerprinting,
but neither executable is invoked in that selection. Omit the consumer and
exhaustion-code arguments together to select only compiled cases.

The helper consumer renames the original production request function and wraps
it: every real request expansion and successor executes before caller-provided
synthetic bytes overwrite the answer. Sampler cases cover masking/rejection,
partial acceptance across answers, an empty first answer, success on answer
sixteen, total exhaustion and partial exhaustion. Each compares all reached
request preimages, digests and successors, including all sixteen requests on
exhaustion. Successful helper returns additionally check the final digest,
coordinates, generation, draw count and remaining budget. No synthetic-answer
hash markers are added.

Block helper cases reach the declared target element maximum and maximum+1
(currently 1,024/1,025); the latter requires resource code 2 and an empty hash
frontier. At the maximum, every ordered result is checked against real request
bytes. Other helper cases check b=64 with a synthetic zero gate passing and a
gate of 2^63 failing despite its low 63 bits being zero, with complete production
request hashing even on failure. The b=0 equation uses the same explicit initial
digest and origin as the ungated reference. Both lower to identical runtime
arguments, so this does not test source gate selection or distinct proof roots.

`summary.json` separates `compiled_cases`, `sampler_helpers`, `block_helpers`
and Python-only `reference_only` probes. Per-case expected and revm reports,
native reports for compiled cases, source products and solc requests/artifacts
remain under the output directory. Helper deployments have no compiled native
proof, authenticated SDK artifact or natural sampler-exhaustion evidence.
The maximum-count helper does not test compiled output compaction or lifetime.
Refusal precedence, internal preflight atomicity and an honest passing b=64
compiled proof remain outside these added controls. No native
b=64 witness search is attempted.

## Authenticated rows, polynomials and FRI closure

Build the compiler, `evm_fixture` native driver and runner separately through
the normal development workflow.

```sh
python3 common/tests/evm/authentication_controls.py \
 --compiler /path/to/zkc-compile --native-driver /path/to/evm_fixture \
 --solc /path/to/pinned/solc --runner /path/to/zkc-evm-test-runner \
 --output build/evm-research/authentication-controls
```

Use `--suite authentication`, `--suite polynomial` or `--suite require` to
select affected checks. The harness reuses `Subjects`, the native proof driver,
canonical ABI helpers and complete-trace oracle. Each case deploys once and calls
twice, retaining compiler products, native requests, expected hashes and receipts.

Raw row controls cover installed base/quartic/octic Keccak commitments, width
and height one, both orientations, non-power-of-two height with zero-digest
padding, wrong roots/rows/siblings, short and extra rows/paths, shape/product/
coordinate precedence, canonical decode failures, and a tiny opening of a
`2^16`-row shape within the native default table allowance. Independent integer
Keccak derives every preimage; repeated authentication executes again.
Polynomial controls cover empty, zero, trailing-zero and extension coefficients,
installed roots, Horner evaluation, dynamic index selection and domain failures.
Backend `require` controls distinguish its source stop from Boolean false and
check that a later malformed message is not reached after the stop. Malformed
ODS controls prevent vector operations from forging normalized polynomials.

`fri_keccak.zkc` and `fri_keccak_block.zkc` use the ordinary shared FRI library,
Direct quartic challenges and the quartic Keccak transcript at the explicit
structural tuple `(LogSize, TerminalLog, Rounds, Queries) = (5,0,3,8)`. Neither
fixture is a production security profile. `fri_closure.py --queries 2` selects a
separately labelled diagnostic, preserving the default eight-query subject.
The default physical realization uses individual natural leaves and atomic
blocks; grouping, order, authentication and scalar/block sampling are explicit.

`fri_reference.py` independently replays supported descriptors, complete proof
frames, actual origin coordinates, transcript requests, row authentication,
folds and terminal equality. It refuses unrecognized profiles. It reads no target
trace or native outcome to derive an expectation; `--check-native` compares its
already derived result afterward. `--expectation FILE --fork osaka` emits a
proof-pinned complete primitive trace for `fri_closure.py --expected FILE`.
An invocation SHA-256 and every construction/authentication Keccak must match
in count, order and bytes; a Merkle-only prefix cannot pass.

The original eight-query scalar native subject uses 122 transcript transitions,
above the unchanged EVM ceiling of 64. Its independent budget-64 replay records
the exact `resource/8` frontier. Actual EVM source lowering also exposes solc
stack pressure in wide helper signatures; native or reference success alone is
not successful deployed FRI. Smaller diagnostics, target resource stops and
primitive tests establish their stated boundaries only. Full STARK deployment,
fixed-strength feasibility and formal/security correspondence remain separate.
