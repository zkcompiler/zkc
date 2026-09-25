# Direct table compilation and execution

The `compiler/` and Rust workspace compile the
adopted [table source](table-storage/source.md) through registered MLIR, export
its actual direct plan, check it against retained source in Lean and execute it
in Rust. This is a finite table instance of the selected
[representation](representation.md), not the whole native obligation.
See the [build instructions](../../compiler/README.md) for running this path.

## Representation and lowering

| Carrier | Retained meaning |
|---|---|
| `pir.program`, `pir.choose`, `pir.repeat`, `pir.bind`, `pir.return`, `pir.stop` | Typed source, isolated regions, explicit captures, public natural iteration and stopped execution |
| `algebra` | Field sorts and arithmetic/equality operations; F₂ and F₇ remain different domains |
| `poly` | Immutable original tables, residual views, ordered restriction, points and evaluation |
| `pir` interaction operations | Sending, drawing, writes and toy ordered-digest operations |
| `plan` control | Direct executable control around the same logical domain operations |

The current target is a direct logical plan interpreted by the Rust dispatcher,
with native field/table kernels. It does not yet generate machine code for the
whole protocol.
These dialects separate operation families; they are not four implemented
abstraction levels. Contract/construction admission and physical kernel/storage
selection are separate checking steps. The direct conversion
largely replaces control operation names while retaining their structure.

A table type retains its original natural rank. Restriction changes its ordered
prefix, not that type. Well-typed evaluation with the wrong point length returns
the logical `refused` stop at execution. It does not become a source type error.
Field values and natural counts have distinct carriers; large naturals are
canonical decimal attributes, without truncation to a native index width.

The conversion pass selects direct control and retains algebra/polynomial
operations. It does not lower tables into scalar instruction lists or buffers.
`SourceOpInterface` reconstructs operation descriptors from actual types,
attributes and operands. Export walks the final regions and reconstructs ordered
references; it cannot return a saved input body after an IR change.
Explicit region captures can be selected, reordered or aliased. Export maps
their actual SSA operands to semantic binding positions; it does not require
the original capture list to survive CSE. A terminal `choose` remains terminal within its region.
The [compact region profile](regions.md) adds `bind` around a result-producing
region and retains one shared suffix; both native import/export and execution
use it directly. The original finite profile keeps its tree grammar. Capture
pruning and general shared analyses remain separate work. The
[interpolation checker](targets.md#checked-logical-folding) admits its specific
changed-candidate rule; the direct checker alone requires the unchanged body.

Calls that can stop or mutate state thread a flow value and have conservative
MLIR effects. Logical pure operations advertise purity. Program verification runs
after child verification and rejects malformed types, captures, flow and extra
control attributes. Structural verification does not prove protocol phase laws.
Generic optimizer changes that alter the direct body require an applicable
checker rule; unsupported changes are rejected even when types remain valid.

This uses [ODS](https://mlir.llvm.org/docs/DefiningDialects/Operations/) for typed
operations and verification and
[dialect conversion](https://mlir.llvm.org/docs/DialectConversion/) for selective
legality. Physical table selection supports lazy and materialized scalar plans
through `zkc-table-pipeline` and checked physical admission. General region
dataflow and bufferization remain separate work. The table vocabulary uses the shared
[closed-library resolver](libraries.md), also exercised by an independently
registered service family. Open-template binding remains separate work.

## Checking and ownership

The command sequence is:

```text
retained finite source
  → typed MLIR source admission
  → direct control conversion
  → export of actual plan
  → installed Lean preservation check and any requested phase admission
  → named input binding
  → capacity estimation and reservation
  → Rust execution with owned state and storage
```

Rust's `AdmittedProgram` owns immutable source/candidate bytes, any supplied phase
evidence and the decoded plan. The tools crate invokes the consumer-installed
checker on private copies of those exact bytes. A strict complete success
response admits the plan; source
and candidate cannot choose a checker executable. This adapter and executable
selection remain consumer trust boundaries.

The optional [table phase profile](phase-admission.md#native-table-admission)
checks send/draw order for one invocation starting at `ready`. Normal returns
must be at `ready`; a stop can retain an unfinished round. Persistent provider
state is preserved, but is not checked against that abstract entry phase.
Admitting another invocation therefore does not establish session composition.
Without `--phase`, the CLI requests preservation only.

`AdmittedJob` binds every declared input, including dormant captures. A failed
library identity or condition-sort comparison refuses binding before input
loading. The library identities select semantic contracts, with backend
conformance still an explicit assumption. A failed
reservation returns the job with the provider unconsumed, so the owner can retry
or recover its parts. `Session` owns execution. `Completed` offers read-only
outcome/storage access or explicit ownership transfer. No unchecked admitted
constructor or mutable decoded-plan accessor is exposed.
Reusing completed bindings starts a new invocation-local event trace at execution,
preserving persistent state and remaining provider resources. Failed binding or
reservation preserves the preceding trace.

Tables use immutable roots and monotone, session-owned storage. Views retain the
original root and ordered coordinates. Handles check issuing session, slot and
generation. No slots are reused in this implementation. Origin labels are
logical data, not object identities: different tables may share a label.
Returning a view keeps its root alive through the completed owner.

The generic runtime separates `Library`, `Bindings` and `Checker`. The concrete
table bindings separate `FieldKernel`, `ChallengeProvider` and `BufferStore<u8>`;
tests substitute all three. Immutable cell buffers use either packed or retained
segmented storage through the same table adapter, dispatcher and kernels. Logical
root/residual metadata stays in a separate monotone arena. C++ owns IR and conversion; Rust receives a complete checked plan and
does not feed analysis decisions back into MLIR.

## Execution, limits and evidence

The Lean client imports the maintained generic source, direct-plan checker and
execution laws. Reusable all-ring table definitions live in
[`Zkc.Polynomial.Table`](../../formal/Zkc/Polynomial/Table.lean); the finite
language, codecs and reference handler live in
[`Examples/TableProtocol`](../../formal/Examples/TableProtocol/README.md).
The checker establishes exact direct lowering for the decoded source and plan.
Differential tests cover the native representation and execution connection;
there is no theorem that the C++ or Rust code implements Lean's evaluator.

Execution preserves returned false, all five logical stops, actual writes,
ordered events and residual challenge tape. Failed writes are not rolled back.
Stopped loops skip remaining iterations and their suffix. Native start failure
and backend interruption remain separate from logical refusal.

The current native profile admits rank at most 12, source depth 256 and input
files at most 1 MiB. Numeric tokens have at most 1,024 digits. Public resource
analysis propagates accumulator bounds through each iteration, checks dormant
bodies, and reserves arena/cell/scratch/event arrays before execution. Its byte
policy includes those backing arrays and interpreter slots. It excludes decoded
JSON, allocator metadata and temporary backend allocations; successful admission
is not a total-memory or allocation-free execution theorem. Kernel progress and
host allocation remain explicit runtime assumptions.
Buffer estimates count retained backing capacity, including unused earlier
segments and descriptor arrays. Admission rechecks actual managed capacity after
reservation, before execution; failure preserves old values and provider state,
although private capacity may have grown. Scratch is reused across invocations.
This is not an RSS bound: allocator bookkeeping, decoded JSON, natural-number
temporaries and provider-internal resources remain outside this accounting.
The adapter still reserves its conservative per-operation byte estimate as cell
capacity even for scalar operations. More precise physical allocation accounting
remains part of the physical-plan implementation.

The default native budget is 100,000 work units, 32 MiB of accounted storage,
100,000 produced values/events and 65,536 natural bits. Input naturals get a
uniform 4,096-bit bound. Conservative bounds can refuse a logically valid run;
that refusal is recorded separately from Lean execution. These are profile
limits, not limits in the generic PIR semantics.

The reproduced suite compares Rust and Lean on tables, prefix growth, mixed
domains, nested control, failure effects, natural arithmetic, a one-variable
Sumcheck trace and toy ordered Merkle paths. An independent Boolean-basis
calculation checks table values. Mutating an actual MLIR Merkle direction yields
an exported candidate refused against the unchanged source.

The Sumcheck client is a closed shared-table trace with a deterministic tape,
not separate prover/verifier endpoints or a Fiat–Shamir construction. Merkle
uses exact natural pairing, not a cryptographic hash. No speedup is claimed.

## Scope relative to the interactive path

This finite path supplies closed library installation, dependent-reply checks,
table trace and stateful endpoint certificates, and checked lazy/materialized
physical plans. Its storage tests include a second layout and failing/corrupt
stores. The publication proof is a logical reference model; native layout
correspondence remains tested.

The [interpolation pass](targets.md#checked-logical-folding) checks a changed
candidate against retained source through physical execution. General endpoint
admission, open slot environments and broader preparation transformations need
additional contracts and checking rules.

Complete committed Sumcheck endpoints, statement binding, challenge construction
and PCS terminals are implemented on the separate
[interactive protocol route](interactive-execution.md), not supplied by the
finite shared-table trace. See [status](../status.md) for supported paths and
[remaining work](../roadmap.md) for project priorities.
