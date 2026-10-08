# zkc-tools

Run `zkc --help` to list commands, `zkc COMMAND --help` for argument details,
and `zkc --version` for the package version. These requests do not open inputs
or start checkers. The [walkthrough](../../docs/getting-started.md) runs a complete
maintained example; the commands below describe lower-level host interfaces.

The binaries are command-line adapters over these host APIs:

| Surface | Home |
|---|---|
| Named source Entries, CLI files and optional Rust data bindings | `entry/`; [guide](../../docs/language/entries.md) |
| Artifact construction, preparation and execution | `artifact/`, `noninteractive.rs` |
| Interactive participants and transport | `protocol/` |
| Finite closed-source table execution | `table.rs` |
| Exact closed-source checker response | `checker.rs`, exported as `LeanChecker` |
| Shared bounded I/O and direct-child lifecycle | internal `host/` |
| Groth16 application and snarkjs formats | `groth16/`, `snarkjs/` |

`zkc`, `artifact-primitive`, `groth16-artifact` and `snarkjs-import` retain their
command names. Each consumer retains response interpretation, byte limits and
error classification. Shared process mechanics own the direct child and captured
files through response reading; they do not supervise descendants.

The current protocol artifact path is described in the
[artifact guide](../../docs/compiler/artifact-execution.md). For the opt-in
[normalized identity](../../docs/runtime/artifact-identity.md),
`zkc inspect-artifact-identity SOURCE DESCRIPTOR [CONFIGURATION]` reports resolved
source/selectors and the normalized protocol. It explicitly reports
`admission: "not-checked"`: structural inspection does not replace construction
recomputation, participant admission or proof validation.

## Interactive protocols

`zkc run-protocol SOURCE PARTICIPANTS INPUTS CHECKER` checks compiled participants
against explicit common source, then executes their role-local programs. Compile
`.pir` with `protocol-source` and `protocol-compile`; supply the
[run-input contract](../../docs/runtime/inputs.md#input-format).
The [interactive example](../../examples/protocols/README.md#compile-and-run-an-interactive-source)
owns the complete command sequence. Successful execution alone does not certify
protocol acceptance: inspect the returned outcomes and declared acceptance result.

## Native proof execution

`zkc produce-native-proof DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF` and
`zkc validate-native-proof DEPLOYMENT EXPECTED_SHA256 INPUTS PROOF` independently
execute roles in a native deployment. Obtain the expected exact-file digest
from trusted compilation or deployment configuration. Each invocation creates
fresh transcript/service state, checks public bindings and retires resources.
Setup-bearing deployments require application-supplied `--key-id=EXPECTED_KEY_ID`
for one setup or `--setups=AUTHORITY` for several under policy `/4`.
`--attempts=POLICY` selects bounded retries; `--capacity=LIMITS` sets host capacity.
The [native proof guide](../../docs/compiler/native-proofs.md#command-line-use)
describes compilation, authority, formats and supported scope.

## Finite table execution

The commands below describe the finite table client; their input and
checker profiles are distinct from the protocol artifact path.

`zkc run SOURCE PLAN INPUTS CHECKER` owns the external checking boundary and
invokes the generic runtime with the finite table interpretation. `CHECKER` is
selected by the consumer, not read from a candidate artifact. `LeanChecker`
copies retained bytes into a private directory, invokes the installed tool and
accepts only its canonical complete response for the consumer-selected realization.

`zkc run-physical SOURCE PLAN INPUTS CHECKER [--storage packed|segmented]`
executes a checked native physical table plan. Use the Lean
`table-physical-reference` executable as `CHECKER`; its native candidate response
must name `table-physical-plan`. The Lean-only `zkc-table-physical-reference` candidate
profile is rejected. Physical runs accept the same `--phase PROFILE CERTIFICATE`
and `--endpoint PROFILE CERTIFICATE` options as `run`, before trailing `--storage`.
The checker must acknowledge the original `complete-logical-execution` claim,
the selected `table-physical-plan` realization, exact phase profile and optional
entry. A checker that omits any requested acknowledgment cannot admit the run.

Successful physical reports contain `execution` (status, outcome, state, events),
`table-evaluations` and `scalar-cells`, matching the Lean physical reference.
Preparation choices are per site in the checked plan, independent of the selected
buffer layout. Returned lazy references are decoded in their retained completion
owner and that read is included in the evaluation count. Physical reservation
failure reports `execution.status: "start-failed"`; execution or output-read host
failure reports `"interrupted"`, preserving the completed prefix. Admission and
input errors are explicit refusals.

`interrupted` describes failure to finish the native invocation, including its
result decoding. It does not assert that the logical body failed to return;
state and events remain available, but no successfully decoded result is claimed.
Declared-input rank/size limits are part of the native input profile and produce
`refused` (`input-rank-limit` or `input-capacity`). A capacity limit discovered
while reserving the admitted program, including in a dormant body, produces
`start-failed`. Neither result is a logical protocol stop.

An optional trailing `--storage packed|segmented` selects the finite table
buffer layout (default: packed). It also works after `--phase` or `--endpoint`
arguments. Both layouts use the same source checker, dispatcher and kernels;
this is backend installation, not compiler selection of a physical plan.

`--phase PROFILE CERTIFICATE` additionally requests the installed phase check.
The installed profile is `table-round/1`: role `trace`, balanced send/draw ordering
from `ready` back to `ready`. The checker must return both preservation and the
exact selected profile; a preservation-only response cannot satisfy that request.
The runtime retains the profile and certificate bytes with the admitted program.
Trace bindings have no runtime phase guard: this mode relies on the checked
source and native correspondence. Stateful endpoint bindings additionally
guard each actual call against their retained phase.

`--endpoint table-endpoint/1 CERTIFICATE` selects stateful `prover` admission.
Its invocation state is `[actor, phase, logicalState]`, including the actual
`ready` or `sent` entry; reports retain that envelope inside `execution.state`
for physical runs. Trace admission retains the ordinary logical state. Endpoint
bindings require matching evidence at binding, reservation and execution;
failed host calls leave an unknown phase that cannot be reused for admission.
Preparations and final scalar reads retain the same owner without changing phase.

The adapter has a configurable timeout (30 seconds by default) and a 4-KiB
response limit. It reaps the child on failure and preserves distinct timeout,
I/O/process, malformed-response, unsupported-policy and inconclusive outcomes.
These are checker outcomes, not new logical protocol stops or refutations.
Cleanup kills and reaps the direct child, not descendants spawned by a wrapper.
The child inherits the host environment. Output is polled against the limit;
this is not a hard filesystem quota. Executable provenance, subprocess isolation
and host allocation are consumer assumptions. The CLI exposes logical completion, failed start and host
interruption as different reports. It is a development client, not a deployed
artifact loader.

[Build and run](../../compiler/README.md) and
[execution scope](../../docs/compiler/table-execution.md).

## Compiled attempt bodies

`artifact::attempt::execute` drives an admitted stored participant using its
actual retained backend. It buffers typed send actions, classifies returned
data, and invokes an installed external container codec only for a completed
attempt. A runtime stop cannot be reclassified as retry. `BufferedMessage<V>` keeps
the full envelope, physical type and typed payload. The external codec never
needs to parse a transport header. Transport length and retained payload size
are independently bounded by the supplied limit; only typed payloads are kept.
Buffer/container limits refuse before
returning `Ready`; `Ready` itself is still unpublished. Codecs are explicit
adapter callbacks, not proved pure functions. Receiving actions require a
separate driver and are refused here.

`tests/attempts.rs` compiles `examples/protocols/attempt-control.pir` and places
this driver inside `zkc_runtime::attempt::Controller`. It checks consumed RNG
state across retries, stale capabilities, terminal exhaustion, and output/codec
failures. The fixture tests the construction boundary, not a BP+ proof algorithm.

`tests/zero_challenge.rs` injects zero only at the test primitive boundary after
an actual native Monero update succeeds. The compiled body computes the zero
guard; discarded attempts preserve real RNG/work consumption. This is fault
oracle evidence, not a discovered Keccak preimage or a complete BP+ protocol.
`tests/grinding.rs` separates clone-search work from one compiled live witness
check, including rejected and zero-difficulty checks.

## Joint execution

`protocol::run::Bundle::admit` checks `zkc.run/1` bundles containing
`zkc.program/1`, using Runtime's own action layout. Flat bodies, compact iteration,
and structured or variable-size messages share the same format, bounded codecs
and schedule checks. Superseded native bundle and program tags are refused.
`protocol::run::run` takes
exact named `RoleInput`s, a host session ID, `RunLimits` and optional `Hooks`. It
returns outcomes, all role outputs, reached cuts, pending bytes, observations
and backend custody after explicit cleanup. Select verifier acceptance by an
explicit role and result index; `Completed` may contain false results.

The `native_joint` example consumes freshly generated bundles from
`compiler/test/native_joint.py`. The cross test in
`tests/protocol/test_native_mathematical.py` compiles and executes them together.
The [joint execution contract](../../docs/spec/profiles/compiler/run.md)
defines the synchronous handoff, read-only observer obligations and supplied
admission boundary.


## Mathematical bundles

`zkc run-bundle BUNDLE EXPECTED_SHA256 INPUTS` runs an authenticated mathematical
bundle through the general joint driver. Its positional data/service inputs,
setup authority, capacity and failure reports are documented in the
[bundle walkthrough](../../docs/runtime/bundles.md) and
[bundle contract](../../docs/spec/profiles/compiler/run.md#installed-host-and-authority).
The library exports `RunHost`, single-use `PreparedRun` and `HostReport` under
`protocol::run`. Byte requests use `prepare`; in-process callers use
`prepare_typed(&RunInputs)` with ordered `RoleInputs` and `InputValue` operands.
`InputValue::from(value)` passes supported immutable native data without a wire
roundtrip. Both forms check input types, setup associations, capacity and entry
constraints before execution. The prepared call owns its loaded inputs.
Custom joint-driver callers pass `RunLimits` and receive effective limits in `Report`. Retained source-driver callers pass `DriverLimits` to `drive`
or `drive_with_decoder`; `Schedule::new_with_work_limit` selects source traversal
capacity. These schedules and byte counters retain distinct contracts.


## Named source Entries

`entry::RunEntry` binds an authenticated `entry::Package` to its source interface
and the native run Host. `RunRequest` supplies role names, named inputs and named
service budgets. `entry::Value` represents logical records, tuples, arrays,
variants, associated values and unit; scalar/native leaves use `Value::from` or
`InputValue::Wire`. Empty products remain required input values. Source constructor
permissions apply to native and encoded inputs alike.

```rust,ignore
use zkc_tools::entry::{Package, RunEntry};
use zkc_tools::protocol::run::{HostLimits, SetupAuthority};

let package = Package::capture(&bytes, &authorized_digest, Package::MAX_BYTES)?;
let entry = RunEntry::admit(package, HostLimits::default(), SetupAuthority::default())?;
let report = entry.prepare(named_request)?.execute();
// Complete named results exist only after successful execution and cleanup.
let results = report.outputs;
```

The [source contract](../../docs/spec/profiles/source/mathematical-language.md#named-run-calls)
defines result delivery and constructor/custody refusals. The native report retains
stops, failures, usage and cleanup; it does not interpret a returned Boolean as
proof acceptance. Affine result export requires a custody API and currently refuses
at Entry admission. Named proof calls, source setup associations, package CLI and
thin generated bindings remain separate work in this frontend package.
