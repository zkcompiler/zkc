# Storage ownership and execution API

This design implements the [source instance](source.md) under the existing
[runtime resource policy](../../runtime/design.md#4-randomness-cancellation-and-resource-failure)
and [heterogeneous representation relation](../../spec/realization/representations.md).
The records and function names below describe the selected API contract;
the [direct implementation](../table-execution.md) instantiates a finite part of
it. They are not a serialized physical plan.

## Logical values and native ownership

Use one session-owned arena of immutable roots, residual descriptors and
published values. Captures are transferred into exclusive ownership or actually
snapshotted during binding. A borrowed pointer into externally mutable memory is
not an immutable capture. Cloning a value copies a handle or a small scalar,
not every original table.

A root record contains its resolved domain, original dimension, fixed row order,
fresh allocation identity and exact canonical field cells. A residual contains a
root handle and the ordered prefix. The first implementation may copy a prefix
into a reserved array of at most `N` scalars. It need not copy or materialize the
root on restriction. Point values are immutable ordered arrays. Mutable module
cells are separate from these allocations.

An internal handle contains `(session, slot, generation, kind)`. The arena checks
its session and generation and checks the slot's kind, domain and shape against
the resolved expected sort. Handles are privately constructed, never accepted
from producer bytes as evidence of a value. A generation is a lifetime check,
not a cryptographic capability. Mathematical identity comes from the resolved
record and its immutable payload.

Initially persistent slots are allocated monotonically and never recycled during
an invocation. Older residuals and aliases keep their roots valid. Scratch is
separate, exclusively borrowed and reused after a synchronous kernel completes.
Retirement occurs only when the last owning completion/session is dropped.
Session identities cannot wrap into a live or externally retained identity;
counter exhaustion is a start failure. Generation checks leave a clear boundary
for later recycling but do not authorize it in the native implementation.

The completion object owns the arena even if its result is a table or residual.
Its value accessor returns a borrow tied to that owner; an exported copy requires
actual serialization or explicit ownership transfer. Dropping local interpreter
slots must not destroy the storage behind the returned value. A stopped
completion also owns its residual state and events.

## Value and state correspondence

Let `H` be native storage and module state. `V_H(t,v,h)` means:

| Logical sort | Required native correspondence |
|---|---|
| Scalar | The selected domain's canonical decoded value equals `v` |
| Table | Checked live handle resolves to the same domain, original rank, origin binding, row order and all actual cells |
| Residual | Checked live handle resolves to a related immutable root and exactly the ordered logical prefix; its length is at most the original rank |
| Point | Same domain and exactly the ordered list of elements |
| Boolean/digest/summary | Exact Boolean, mathematical natural, or componentwise ordered tuple; no machine wraparound |

`R(W,H)` additionally relates both mutable field cells and the natural write
counter, requires the arena invariant, and preserves the mapping of **every
still-live** source value/capture. Native bookkeeping may change; logical roots
and old residual values do not. Selected event decoding maps the native ordered
write records to exactly the logical `Event` list.

On successful shape-checked restriction, publish a new descriptor related to
`(T,p++[r])` and preserve every old mapping. On failed restriction or evaluation,
produce logical `refused` with no own module mutation/event. On either write
outcome, update the selected cell and counter and append the event before
returning or propagating the stop. An unchanged heap is not the state relation:
the arena may contain additional immutable values while representing the same
logical state.

[Storage.lean](Storage.lean) proves generic lookup, foreign/stale refusal and the
surviving-slot frame. It deliberately models payloads abstractly. It does not
prove Rust pointer validity, uniqueness of a native issuer, scalar decoding,
the complete `V_H` relation, or preservation by a native allocator. These are
obligations of the actual implementation and its differential evidence.

The native adapter separates logical metadata from `BufferStore<u8>`. Packed
and segmented implementations publish owned copies and lend contiguous slices
to the same synchronous kernels. A segmented buffer never crosses segments;
unused earlier capacity remains charged. Each store owns its private reference
arena, so a reference from another store is refused. Captures, points and ordered
prefixes use this boundary; scratch remains separate.

[`Examples.BufferStorage`](../../../formal/Examples/BufferStorage.lean) proves
that packed offsets represent independently stored complete buffers after any
sequence of publications, with equality of **all** reads and the next reference.
The old-buffer frame requires bounds on each existing span. This pure list
model forgets reservation segments, capacities and native issuer identity;
it supplies a reference law, not a verification of either Rust allocator.

## Evaluation kernel and materialization

The initial direct kernel can copy the original `2^N` cells into exclusively
borrowed scratch, then fold one coordinate at a time over `p++q`. At each stage
with `2m` live cells, write
`scratch[j]=(1-r)*scratch[j]+r*scratch[m+j]` for `0≤j<m`, then continue with
the first `m` cells. Reading the two halves implements the first-coordinate
most-significant-bit convention. Inputs and published roots are never scratch.
Check the logical point-length guard before calling this kernel.

One full-root scratch allocation suffices for this sequential algorithm.
At most `N+3(2^N-1)` field additions/subtractions/multiplications are needed if
`1-r` is formed once per level. This is an arithmetic work estimate for the
selected kernel, not a native timing result or a new proved implementation law.
The native implementation must test it against `atPoint` and prove or explicitly trust the field
primitive adapter under its normal correspondence policy.

Later materialization of a residual may store folded cells of length
`2^(N-length(p))`. Its required law is equality with original-root evaluation
for **every** admitted suffix, with the same old-value frame and failure policy.
No dense coefficient expansion is required. No materialization instruction is
added to the version-1 exported logical plan by this design.

## Capacity and admission

Capacity is a conditional native progress domain. Compute and reserve a
conservative public bound before modeled execution. The source's own shape
guards remain at their original execution points. Admitting capacity does not
turn those guards into successful preconditions or change dormant capture binding.

The plan includes immutable input cells, input points, persistent descriptors
and prefix storage, interpreter slots, temporary scratch, output values, module
counter space, retained event records, and backend/internal allocation assumptions.
The implemented buffer boundary distinguishes requested minimum capacity from
actual retained capacity. Check both before allowing execution. Reservation may
grow private capacity even on a failed start, while preserving old buffers and
provider state. Retained scratch/event/message and metadata arrays count toward
the finite adapter policy. This policy does not bound all process memory or
prove that arbitrary stores report their resources truthfully.

Parsing/checking has its own byte, depth, natural-size and work budgets before
this reservation; computing an enormous `2^N` is not a permissible unchecked
preflight step.

For each operation and admitted public operand-shape bound, resolve a finite
resource tuple: persistent bytes/slots `P`, scratch peak `S`, event count/bytes
`E` and work bound `K`. For nonnegative component bounds:

```text
sequence:    P = P₁+P₂;  S = max(S₁,S₂); E = E₁+E₂; K = K₁+K₂
branch:      componentwise maximum of the two fully formed arms
repeat c:    P = c*Pbody; S = Sbody; E = c*Ebody; K = c*Kbody
```

Add the actual control/slot overhead, initial inputs and post-loop continuation;
do not count a lexical loop body as a single execution. Monotone persistent
allocation makes the sum safe even when values become unreachable. A stopped
prefix uses at most this bound. Nested scratch lifetimes would require an
additive simultaneous-live bound; the native kernels are synchronous and unnested.

The repetition equation requires a **uniform** body bound for every reachable
accumulator in every iteration. A bound calculated only from the initial
accumulator is insufficient. The first estimator propagates conservative public
size/range bounds through operations, joins branches by maxima, and performs
bounded abstract iteration for each public loop count, charging that iteration
to the preflight work budget. Sum per-iteration persistent/event/work bounds and
take the maximum scratch requirement; the displayed multiplication is shorthand
only when one established bound covers them all. A closed-form bound or checked
inductive invariant may replace this calculation later. Refuse start when no
bound is established within budget; never assume size stability from a stable
source sort. The residual prefix bound `N` is stable; digest bit length need
not be.

For `view` reserve one descriptor; for `restrict(d,N)` reserve one descriptor
and up to `N` field elements; for `evaluate(d,N)` reserve a scalar output and
`2^N` scratch field elements. A stateful call has one event on every outcome.
Failed guards need no new published value, but their upper bound may include
one. An implementation may choose a tighter verified estimator without changing the API.

The [protocol trace extension](protocols.md) adds a two-field-element stored
message and one event per `send`, and at most one event per `draw`. Reserve
message storage as well as the event log. The tape is an owned immutable array
with a consumed-position counter; drawing requires no new tape allocation.
An exhausted draw retains its prior state and emits nothing.
Literal endpoint points and singleton challenge points each require a descriptor
and one field element, covered by the same persistent-value reservation.

Natural-valued digests require numeric bounds too. If both ordered-pair inputs
are at most `B`, `(2B+1)^2` is a conservative result bound. Propagate this through
control using public input bit-length limits, and reserve sufficient natural
storage, including temporary arithmetic. Repeated pairing can grow rapidly;
report capacity refusal when the resulting bound exceeds policy. Field arithmetic
and `writes + callBound` likewise need explicit representation/overflow checks.
Neither silently wrapping `Nat.pair` into a machine word nor reducing a natural
counter modulo the field is a permitted implementation.

All size exponentiation, products, sums and conversions to machine integers
are checked against finite policy limits as they are computed. Budget refusal
precedes allocator requests that exceed those limits. Private-dependent paths
can run within the reserved public worst case; the initial estimator does not
inspect private field elements to choose its capacity promise.

## API transitions and failure categories

The selected ownership transitions are:

```text
admit(retained_request, candidate, supplied_values, registry)
  -> AdmittedJob | AdmissionError with caller custody preserved

reserve(AdmittedJob, Providers, Budget)
  -> Session | StartFailure { job, unchanged providers, reason }

execute(Session)
  -> Completed { logical_outcome, arena, residual_providers, events }
   | HostInterrupted { reason, recoverable_custody, available_prefix }

Completed.value(&self) -> borrowed logical/native result view
Completed.into_owned_parts(self) -> owned result storage, providers, events
```

`AdmittedJob` owns the independently retained source, public specialization
connection, checked candidate, resolved interpretations and frozen inputs.
It does not expose a way to replace the plan after checking. Provider admission
and reservation do not invoke a source operation, consume a tape or mutate
provider state. If either fails, custody remains with the caller; temporary
private allocations may be released. `Session` has exclusive execution custody.

The backend borrows immutable operands through checked positions, resolves
handles against its arena, borrows reserved scratch, and publishes an immutable
result only after completing it. The dispatcher keeps the current flow/world
and event sink through both call outcomes. It invokes each operation exactly
where the direct plan prescribes. New signature APIs use program-owned resolved
`SortId` values or owned structured sorts, not leaked `&'static str` values.

| Boundary | Result and meaning |
|---|---|
| Malformed type/value/shape, missing binding, unresolved operation, unchecked candidate | Admission error before execution |
| Budget limit, representational size overflow or failed reservation | Host start failure; return the admitted job and unchanged providers |
| Source shape guard, explicit stop, stopped registered call | Completed logical stop, with actual residual state and ordered events |
| Returned `false` from `record` | Ordinary completed reply; continue through the selected source branch |
| Foreign/stale internal handle, broken event bound, backend contract failure | Host interruption/contract violation; never fabricate a new logical stop |
| Process/device/allocator interruption outside promised progress | No unconditional completion claim; report only state/custody actually recoverable |

`HostInterrupted` is not a general rollback promise. A process failure may
prevent returning even that object. Completed execution correspondence is
conditional on the admitted representation/progress domain and lawful adapters.
All concrete diagnostic strings and first-error ordering are frozen with the native
decoder and tests; the categories above already constrain those choices.

## Preparation identity

Before introducing caching, retain the resolved operation and algorithm revision,
field/domain interpretation, original dimension and row order, immutable input
occurrences and actual payload mapping, ordered prefix, and all other actual
dependencies. A session-local root identity is sufficient only under the
immutable issuer invariant. Distinct origin labels may denote equal cells;
deduplicating them requires a separately justified full-value relation.

A hash may index a complete key; equality must compare that key unless an
explicit collision assumption is part of the claim. Cross-session reuse needs
its own persistent identity and lifetime design. A failed mutable write can
invalidate readiness while leaving frozen table preparation mathematically
valid. This package introduces no cache and does not remove any readiness guard.
