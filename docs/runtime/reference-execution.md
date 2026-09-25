# Native checked-plan execution

This guide describes the maintained finite logical/physical plan runtime in
[`zkc-runtime`](../../crates/zkc-runtime/README.md). The
[interactive participant runtime](../../crates/zkc-runtime/src/interactive/README.md)
is a separate execution surface. The enclosing experiment controller in the
[runtime design](design.md) is a broader design, not the lifecycle implemented
by one finite `Session`.

Owned execution of source-checked plans. `Library` defines sorts and
signatures; `Bindings` supplies input values, resource bounds and operation
execution; `Checker` supplies consumer-selected source-relative admission.
Its `CheckRequest` also carries the selected realization and optional phase evidence. Success must establish
every requested check. `CheckFailure` preserves the kind and available detail
of an unsuccessful check; the runtime itself launches no subprocess.
The library owns its condition sort as well as operation signatures. Binding
rechecks the admitted dependency identities and condition sort before loading
inputs. Those identities select a contract; they do not prove that a backend
implements it.

## Admission and execution ownership

The ownership path is `AdmittedProgram → AdmittedJob → Session → Completed`.
Failed admission retains the source, candidate, optional policy/certificate and
typed checker failure. An admitted program owns the same checked bytes;
`phase_evidence()` exposes them immutably. Failed binding retains inputs and
bindings. Failed reservation returns the job before any challenge draw.
Completion retains the storage needed to interpret returned handles.
`Bindings::begin_execution` resets invocation-local observations only after a
successful reservation. Reusing completed bindings preserves state, storage and
the remaining provider, while the next result contains only its own events.
Binding or reservation failure does not clear the preceding trace.

## Physical table plans

`AdmittedProgram::admit_physical` independently decodes the logical table source
and the native `zkc-table-physical-plan` region using their installed operation
interpretations. It retains both byte streams and requires the checker's exact
`table-physical-plan` claim. Both source grammars retain their logical input ABI;
the target always uses the existing region grammar. The older physical-reference
wire is refused. Optional phase/endpoint evidence uses the same selected policy
and exact acknowledgment requirements as direct admission, with the physical
realization retained.

`PhysicalTableBindings` wraps the same `TableBindings` owner, kernels and provider.
It can retain an endpoint-enabled owner: entry validation delegates to that owner
at binding, reservation and execution, and `endpoint_entry()` exposes its actual
entry for readmission. Preparation and deferred scalar reads do not advance phase;
invocations use the existing actual call boundaries. A failed deferred read keeps
the known phase, while a host failure during a provider call leaves it unknown.
Each preparation checks its shape immediately and publishes a fresh immutable
scalar cell. Lazy cells retain residual/point handles; materialized cells publish
one owned scalar buffer. Ordinary invocations decode physical operands and call
the shared native operations. Eager evaluation and independently chosen modes
can coexist. Returned scalar references must be read through the completion's
bindings; `value_json` counts that read in `table_evaluations()`. `scalar_cells()`
counts live prepared cells, including cells retained across owned invocations.

## Resource accounting and failures

Preflight joins value bounds only from returning paths; stopped paths retain
their resource costs but supply no result value. It propagates possible lazy
ranks through joins and bounded loops, and
reserves output-read scratch, arena/buffer capacity, dispatcher and decoded
operand scratch, event records and sent-message capacity before execution.
Storage reservation failure returns a start failure with provider custody; it
does not produce a PIR stop. Events accumulate as finite records; JSON encoding
occurs when the host requests a report. Arbitrary-precision digest arithmetic,
external backend progress and host decoding/report allocation retain their
existing implementation assumptions. This is no allocator/extraction proof or
performance theorem. The physical controls use explicit fixture authorization;
live checking is covered by the integration harness and by tools tests with
`ZKC_LEAN_BIN` set to the directory containing the installed Lean checkers.

## Adapter results and storage

`Bindings::validate_result` is required: after static sort validation it checks
argument-dependent constraints before exposing an operation result to the source
continuation. It does not see intermediate interface replies. An operation may
make several provider calls; its adapter must validate each reply before using
it. A malformed reply or result interrupts execution and retains actual post-state
and events in `Completed`. These checks do not prove the provider's transition
law. The [independent service consumer](../../crates/zkc-tools/examples/vector-service/main.rs)
exercises both boundaries, including a two-call operation and bad intermediate
replies. See the [library guide](../compiler/libraries.md).

`table` supplies the first concrete finite interpretation, with distinct field
kernel, challenge-provider and buffer-store contracts, immutable original tables and ordered residual
views. `arena` rejects foreign/stale handles. The dispatcher preserves complete
outcomes, state and events through branches and public loops.

`buffer::BufferStore<T>` owns immutable buffers independently of logical table
metadata. `PackedBuffers<T>` uses checked offsets into one payload vector;
`SegmentedBuffers<T>` retains reservation segments. Both reserve payload and
descriptor capacity before publication and preserve old aliases. The default
table constructor uses packed storage; `TableBindings::with_storage` installs
another typed store. `buffer_usage()` reports retained payload/descriptor
capacity, excluding allocator bookkeeping. Reservation estimates are minima;
the table adapter also checks actual capacity before execution.

[Architecture, capacity limits and evidence](../compiler/table-execution.md)
state the implemented scope. `cargo test -p zkc-runtime` checks custody, failure
prefixes, adapter substitution and arena validity. The cross-language harness
uses the actual Lean checker, independently of the unit-test checker fixture.

## Stateful admission

Stateful `PhaseEvidence.entry` is consumer-selected and retained with the check.
`Bindings::validate_entry` checks it before inputs, reservation and execution;
an adapter that supports stateful admission must require its policy even if
omitted by a caller. `Completed::started()` distinguishes final entry rejection
from an interrupted invocation. Both retain bindings and observations.

`TableBindings::with_endpoint` installs the local `prover` actor and a recorded
phase once. The host supplies initial phase/data consistency. Writes, sends and
challenge receives track their own completion; stopped calls preserve entry
phase, while an error or unwind during a call leaves `Unknown`. A later source
must be admitted from the retained known phase. Provider exclusivity and crash
recovery are host obligations; serialized state is not authenticated recovery.
See [stateful admission](../compiler/phase-admission.md#stateful-table-admission).
