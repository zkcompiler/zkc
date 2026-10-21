# Runtime capacity

This native contract defines operational ceilings. Sufficient but different
ceilings preserve successful proof bytes; they do not guarantee completion.

## Application capacity

`NativeDeployment::with_capacity` and CLI `--capacity=PATH` select operational
ceilings independently of the authenticated deployment, inputs and proof.
Successful proof bytes are unchanged when different ceilings are sufficient.
The CLI reports the effective record, including defaults:

```text
["zkc.native-capacity/0", "elements", "groups", "wire_bytes", "value_bytes",
 ["instructions", "iterations", "logical_bytes"], ["live_bytes", "total_bytes"]]
```

All entries are canonical decimal strings. The file is at most 4 KiB and has
exact arity; unknown fields or tags refuse. Defaults are 65,536 elements,
4,096 collection/aggregate group points, 16 MiB wire, 64 MiB per value/live
values, 256 MiB cumulative fresh allocation, one million instructions,
100,000 iterations and 4 GiB of logical work. Element/group counts may rise to
1,048,576/32,768. Other ceilings may only be lowered. Numeric elements and group
points are counted across a complete nested message, not separately for each
child collection. For
the QAP matrix sequence, the nonzeros across A, B and C share the element ceiling:
three matrices with 25,000 entries each exceed the default 65,536 aggregate
limit even though each matrix fits individually. A zero group collection ceiling does not
forbid an independently decoded fixed scalar group value. Count ceilings do not
promise that many values fit: wire size, retained backing, decode scratch and
live/cumulative budgets all apply. For example, a 32-byte scalar vector reaches
the 64 MiB decoding peak bound before 1,048,576 elements. The 16 MiB invocation
JSON envelope also counts hexadecimal text and duplicated public/data rows.

Entry function output conversion preserves owner validation for standalone
native leaves, including leaves in source products. Constructing a native
variant checks its complete active arm's element/group totals and retained
construction peak. Opaque opening-state collections count handles, not elements
of their backing tables; singular key/state handles add no backing-element
collection count. Retained-byte and owner validation limits still apply.
Before each native payload measurement, the Host charges its conservative
retained-byte bound to the invocation-wide logical work allowance, including
repeated uses of shared data. Immutable sequences and variants retain this
bound, so computing their charge does not traverse their payloads. Standalone
output leaves need no such scan.

The selected policy reaches native data loading, backend kernels, setup import,
service registry and runner budgets. Attempts cannot exceed these invocation
ceilings. Signature-only deployment admission uses a dummy default backend;
it loads no invocation payload and grants no capacity. Existing setup/provider
limits and the separately configured external-work ledger retain their owners.
Input admission and runtime execution use separate accounting ledgers: the same
`total_bytes` setting bounds loading work and cumulative runtime fresh allocation
independently. Canonical public values needed by the selected role are admitted
once and reused after checking exact data-row bytes and physical layout. Other
public values are checked and discarded. These ledgers do not bound total process
memory or combined work across both phases. Byte
preflight for native wire inputs precedes decoding; the loading ledger admits
the decoded value afterward, so a reduced loading ceiling alone does not prevent
a single decode allocation permitted by the backend value ceiling.

The [joint Host](../../runtime/bundles.md) uses the same capacity record. The group
quota covers one collection or complete nested message. It is not
a cumulative per-proof subgroup-work bound: many standalone G2/GT messages remain
bounded by proof size and execution limits. Neither this count nor the instruction
budget measures CPU time.

## Retained values and logical work

Each runner keeps three ledgers. Each value has a conservative retained
charge, which the per-value ceiling bounds. The installed value adapter
partitions that charge into storage owned by one binding, such as an inline
scalar, and the immutable allocations it shares. A shared allocation's charge
includes the inline storage it holds, such as a collection's element slots.

- **Live bytes** count each shared allocation once while any live binding, view
  or container retains it, plus the owned storage of every live binding. A view
  or collection that retains a parent allocation keeps the parent's whole charge
  live until its last reference ends.
- **Total bytes** count each shared allocation once, when a kernel, service,
  entry input, received payload, literal or variant construction produces it,
  plus owned storage at every binding. Captures, arguments, carried values and
  results that cross frames allocate nothing. Release never refunds this ledger.
- **Logical bytes** count work at every kernel and service invocation: the
  operand bytes read and the result bytes newly allocated. Operands are charged
  at their full retained charge at every use, however their storage is shared.
  An installed kernel may declare a smaller read extent; it bounds every operand
  byte the kernel body reads and never exceeds the full charge. Native operand
  admission can additionally walk nested values; its sequence-work ledger
  bounds those walks separately. The native
  row opening declares its row and authentication path; element and handle
  accessors and length queries declare one handle and index.

Allocation identity is the address of a live immutable allocation, recorded
only while a runner binding holds it, so a freed address that is reused counts
as a new allocation. Equal contents never establish identity: separately
created equal allocations are charged separately. Identities never appear in
reports, proofs or semantic observations. An adapter that reports no sharing
is charged in full at every binding. A kernel's output allowance is the
minimum of the per-value ceiling and the remaining live, total and logical
budgets; it bounds storage the kernel newly allocates, not storage its result
shares with its operands.

A capability-free immutable value bound under the same physical type reuses its
successful backend validation for aliases. A borrowed runtime-owned `Retained`
view also lets the backend reuse validation of intrinsically typed immutable
sequence subtrees. Only allocations still held by this Runner are present;
entries disappear with their final reference. Numeric storage whose validity
depends on its physical type does not use subtree reuse. Capabilities are always
checked against current custody. Backend
policy, setup authorization, frame custody and capability checks remain required.
External calls and codecs receive no retained-validation evidence.

Local and participant return/yield handoffs keep shared backing in the ledger between region
exit and caller binding. These internal references add no value binding or
inline charge. They are released after transfer and on every failed transfer,
loop step or frame leave. This preserves storage accounting while avoiding a
repeated walk of a carried immutable subtree.

For example, a prover that commits 65,536 extension-field rows once and opens
64 rows from a repeated phase capturing the opening state retains the vector
and the 6.29 MB state once; each opening allocates and reads only its row and
path. This completes under the default record.

## Shared invocation execution policy

`ExecutionLedger::new(ValueBudget, WorkBudget)` adds optional policy across
independent runners and Host scopes. Its cloneable handle shares atomic
instruction, iteration, logical-byte and cumulative fresh-byte allowances. Each
runner keeps its own limits and backend-local retention/validation ledger.
Every participant of a joint invocation, every proof attempt and every numerical
child must receive a clone of the same handle from the Host. Creating a child
never replenishes shared capacity. Native sequence, external and ring work,
wire/proof transport, loading and scratch retain their existing owners; Hosts
must apply cumulative policy to those counters separately.

Before loading inputs, each shared runner reserves its entire selected live-byte
allowance. Simultaneously live parent and child runners therefore count together,
even while the parent is suspended. This is conservative: separate runners count
shared aliases independently, and unused capacity stays reserved. Within one
instance, the existing backing identities still avoid duplicate shared-storage
charges. This policy is neither actual allocator accounting nor peak RSS.
`reserve_live(bytes)` gives Host-owned storage the same explicit live guard;
`charge(work, fresh_bytes)` debits known Host work/storage before its effect.

Instruction and iteration charges precede their steps. Operand logical work
precedes backend application. An allocating kernel withholds shared fresh and
logical output capacity before application and receives the clipped output
allowance. Capacity withheld by an in-flight call is unavailable to concurrent
calls and reported separately by `snapshot()`. Successful calls settle their
provisional allowance to actual admitted output charges. Unused provisional
capacity was never committed work. A failing call conservatively commits its
entire withheld allowance because partial allocation cannot be observed. Service
queries reserve their complete installed reply bound before their effect.
Committed instructions, iterations, logical work and fresh allocation are never
refunded on release or unwind.

For shared execution, trusted Value adapters advertise constructor allocation
bounds before scalar/variant construction. The scalar default is 512 bytes; the
variant default covers its descriptor, conservative payload slots and full
payload charges. Larger adapters must override these bounds. Insufficient
capacity refuses before the constructor runs, even if the actual value might
have been smaller. Induction temporaries have an additional conservative fresh
charge before their later frame binding. Local frame inputs reserve their known
transfer charge before backend entry. The per-value, structural, scratch and
backend-specific preallocation contracts still apply independently.

Cleanup refunds only live allowance, once all stopped scopes and outstanding
handoffs have released their storage. Successful terminal values keep the
runner's reservation. `into_retained_outputs()` transfers backend custody and an
optional `RetainedOutputs` guard containing the successful values and that live
reservation; an unfinished runner is cancelled. A Host retaining values across a
child call must keep the guard, or separately reserve their storage. Dropping
the guard releases live allowance after dropping its values and never refunds
cumulative work. Borrowing or cloning a value grants no new live allowance.

Shared accounting carries no `Retained` backend-validation evidence. Another
backend must independently validate every incoming value, setup and capability;
allocation identity cannot transfer authority. Ordinary constructors without a
shared ledger retain their existing installation and resource behavior.

## Byte construction

Native `bytes.repeat` and `bytes.join` check byte limits and reserve `256 + 2*n`
output bytes for a result of length `n`, including temporary and immutable
storage. Operand-read and result-retention charges also apply. `join` uses the
sequence validation work ledger: a retained input needs only its root check,
while the full operand-read charge accounts for reading its fragments.

## Host allowances

[Numerical calls](numerical.md#managed-construction) additionally bound managed
scratch, result-construction overlap and numerical work in their migrated native
handlers. These per-call backend policy ceilings are separate from the CLI
capacity record and the VM's retained-value ledgers.

[Joint dispatch](joint.md#joint-dispatch-and-handoff) owns dispatch, message
and cumulative wire limits; the [joint Host](joint.md#installed-host-and-authority)
owns its external-work allowance. [Proof transport](../formats/proof.md) owns
proof framing limits, and [attempts](attempts.md) own retry counts and cumulative
budgets. Loading, setup and backend scratch retain their own limits. These
units do not establish one global peak-memory or elapsed-time bound.

## Loading and capacity

Public declarations count toward invocation loading even when used only in the
binding root. Matching role operands reuse decoded values after exact agreement;
each operand counts toward loading. Entry retention charges their shared storage
once and inline values per operand. Per-value decode preflight
precedes payload decoding. Cumulative loading admission has its own ledger and
can occur after that decoding; it is not a whole-process memory bound.
Key files use bounded regular-file reads and pinned material. Data, entry and
transcript-root capacities are checked before execution entropy.

Nonce/RNG operands and the selected transcript reserve their capability retention
charges before issuance. Sequential attempts reserve one live transcript slot
while retaining cumulative execution work and allocation accounting. JSON,
logical counts, retained values, wire bytes and primitive work have distinct
ceilings; raising one does not raise the others.
