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

A capability-free immutable value that is bound under the same physical type
reuses its successful backend validation for aliases. Values carrying
capabilities and newly allocated values, including received payloads, are
validated in full. Backends still perform their own frame-entry and operand
checks.

For example, a prover that commits 65,536 extension-field rows once and opens
64 rows from a repeated phase capturing the opening state retains the vector
and the 6.29 MB state once; each opening allocates and reads only its row and
path. This completes under the default record.

## Host allowances

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
