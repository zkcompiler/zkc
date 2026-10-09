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
 ["instructions", "iterations"], ["live_bytes", "total_bytes"]]
```

All entries are canonical decimal strings. The file is at most 4 KiB and has
exact arity; unknown fields or tags refuse. Defaults are 65,536 elements,
4,096 collection/aggregate group points, 16 MiB wire, 64 MiB per value/live
values, a 256 MiB cumulative runtime value charge, one million instructions and
100,000 iterations. Element/group counts may rise to 1,048,576/32,768. Other
ceilings may only be lowered. Numeric elements and group points are counted
across a complete nested message, not separately for each child collection. For
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
`total_bytes` setting bounds loading work and the cumulative runtime value charge
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
each operand still counts toward entry retention. Per-value decode preflight
precedes payload decoding. Cumulative loading admission has its own ledger and
can occur after that decoding; it is not a whole-process memory bound.
Key files use bounded regular-file reads and pinned material. Data, entry and
transcript-root capacities are checked before execution entropy.

Nonce/RNG operands and the selected transcript reserve their capability retention
charges before issuance. Sequential attempts reserve one live transcript slot
while retaining cumulative execution work and allocation accounting. JSON,
logical counts, retained values, wire bytes and primitive work have distinct
ceilings; raising one does not raise the others.
