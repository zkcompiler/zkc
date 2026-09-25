# zkc-tools

Run `zkc --help` to list commands, `zkc COMMAND --help` for argument details,
and `zkc --version` for the package version. These requests do not open inputs
or start checkers. The [walkthrough](../../docs/getting-started.md) runs a complete
maintained example; the commands below describe lower-level host interfaces.

The binaries are command-line adapters over these host APIs:

| Surface | Home |
|---|---|
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

## Finite table execution

The commands below describe the earlier finite table client; their input and
checker profiles are distinct from the protocol artifact path.

`zkc run SOURCE PLAN INPUTS CHECKER` owns the external checking boundary and
invokes the generic runtime with the finite table interpretation. `CHECKER` is
selected by the consumer, not read from a candidate artifact. `LeanChecker`
copies retained bytes into a private directory, invokes the installed tool and
accepts only its canonical complete response for the consumer-selected realization.

`zkc run-physical SOURCE PLAN INPUTS CHECKER [--storage packed|segmented]`
executes a checked native physical table plan. Install the updated Lean
`table-physical-reference` executable as `CHECKER`; its native candidate response
must name `table-physical-plan`. The old `zkc-table-physical-reference` candidate
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
The first profile is `table-round/1`: role `trace`, balanced send/draw ordering
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
