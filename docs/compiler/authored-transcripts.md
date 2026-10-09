# Authored transcript boundaries

Native `/5` deployments execute the existing external hash-chain and duplex
operations through ordinary mathematical IR, local functions and the general
interpreter. The [external construction specification](../spec/realization/external-constructions.md)
owns their semantics. No new dialect, state type, host constructor or proof
version is needed for these selected clients.

## Structure and authority

```text
public seed/context or snapshot
    → authored initialization and ordered primitive calls
    → explicit state values, trial copies and samples
    → ordinary proof messages
    → verifier calls over its actual received values
    → authored acceptance predicate
```

External state is an immutable `indices` envelope. Its metadata is checked but
never hashed. Copying permits a trial computation; the backend still charges
every executed primitive. Existing affine RNG and derived-transcript resources
retain their separate custody rules. A nominal external-state type could improve
static diagnostics, but would not give a copyable snapshot authority or prove its
history. Revisit it when a required analysis or wire schema needs that static
distinction. Initialization stays visible as an IR call.

The deployment digest authorizes the program. Public inputs come from the
application. The host binds their exact encoded bytes into the container header.
Authored code decides what enters the external cryptographic state; adding the
zkc header to the upstream hash/permutation would change its algorithm.
`binding_scope = "header"` therefore remains accurate for this host guarantee.
These component clients check transcript consistency. They are not BP+ range
proofs, OpenVM execution proofs or automatic Fiat–Shamir constructions.

## Clients and evidence

| Client | Composition checked |
|---|---|
| [Hash chain](../../compiler/test/fixtures/mathematical/authored-monero.mlir) | Public initial word/context, a runtime sequence of differently sized word batches, compact interaction rounds, actual receives, ordered updates and final challenge comparison. |
| [Duplex search](../../compiler/test/fixtures/mathematical/authored-openvm.mlir) | Public context, candidate trials from the same live state, live witness checking, extension coefficients, masked samples, a following scalar sample and verifier comparisons. |
| [Retained prefix](../../compiler/test/fixtures/mathematical/authored-prefix.mlir) | Persistent RNG across retries, an executed hash prefix, a conditional RNG/hash suffix, returned successors and a later send. The retry predicate is synthetic; it does not force a real zero hash. |

The [compiler checks](../../compiler/test/native_authored_transcripts.py) cover
ordinary, unsimplified and released storage, imported snapshots, unused repeated
trials and source-relative operand mutations. The [native client](../../crates/zkc-tools/examples/native_authored_transcripts/main.rs)
compares payloads and work against separately authored schedules, Keccak plus
scalar reduction outside the adapter, the pinned Plonky3 challenger,
and archived upstream Monero/OpenVM checkpoints. The reference schedules share
primitive libraries with the adapters. Work comparisons use adapter metrics;
fixed prefix costs separately pin 65/130 units. Literal validator totals also
pin the empty and eight-round/observation clients. These are bounded execution
and adapter checks, not primitive-correctness proofs.

Round/observation counts include 0, 1, 7, 8, 9, 16 and 64. The OpenVM client
places a noncanonical candidate after success: no later trial touches it.
Duplicate unused trials still consume work. State validation covers all 72
in-range duplex cursor pairs, without attesting reachability. The independently
selected CLI roles receive only their inputs and the final proof. The existing
Lean reader refuses the native carrier; native Lean interpretation remains
separate work.

The retained-prefix client uses deterministic test entropy `[0, 0, 3, 7]`.
Its attempts consume external work `[65, 65, 130]`, advance one RNG by four draws
and execute one send each. Only the final proof is retained. A cap of 129 stops
the second attempt after its RNG draw and before its first hash; the first
65 units remain consumed. Reports include per-attempt work and the actual
invocation limit. The application API can lower the default 16,777,216 units;
CLI execution uses that default.

Byte words currently use eight bytes per index in the native payload, plus
framing. This preserves exact values but is not the upstream wire format.
General original-byte adapters and a compact byte leaf retain separate scope.

## Control decision and remaining work

Keep existing structured control for bounded trial search and conditional local
work. Do not represent retry as a fatal stop: attempts recover actual RNG
successors on normal return, and failures must stay fatal.

[Entry completion](entry-completion.md) supplies that control boundary.
`protocol.finish_if` skips the participant suffix and enclosing rounds while
returning its actual successor tuple. The Monero prefix client abandons before
its send and preserves 65 primitive-work units and its consumed RNG draw.
The OpenVM search uses `local.condition` to stop its bounded loop after a
successful trial; unused iterations are not entered. Both use the same
interpreter and attempt policy as ordinary entries.

Authored admission does not require every received message to be observed and
does not establish imported-state reachability, soundness, entropy, safe state
disclosure or upstream proof compatibility. Preserve those distinctions when
adding protocol libraries or future observation analyses.
