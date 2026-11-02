# Proof attempts

This native contract defines repeated producer execution under an
application-authorized policy. [Proof execution](proofs.md) owns a single run.

## Native attempt policy

The native host accepts this application-owned record alongside a pinned native
deployment. It is not supplied by a candidate proof or inferred from its header:

```text
["zkc.native-attempt-policy/0", completion_original_result,
 [[rng_original_input, rng_original_result], ...],
 [attempt_limit, proof_byte_limit],
 [instruction_limit, iteration_limit]]
```

Every number is a canonical unsigned decimal string, and every field is
required. Parsing is bounded to 64 KiB and the existing logical JSON tree
limits. Port indices are below 1024; attempts are 1 through 1024. Proof bytes
cannot exceed 16 MiB; instruction and iteration limits cannot exceed the
interpreter hard ceilings or the selected [capacity](capacity.md). Zero
instruction, iteration or proof budgets are deliberate execution refusals, not
unbounded values. The proof cap includes the framing header. The policy selects
no byte allowance: the call's
[invocation root](capacity.md#invocation-ledgers) bounds the logical work,
fresh bytes and live bytes of every attempt.

The completion port must name a producer Boolean result. True completes; false
requests retry. RNG pairs are a bijection over producer RNG input/result ports,
with equal physical types. Port maps resolve original indices, excluding the
internal transcript ports. Every returned RNG, on retry and completion alike,
must authenticate as the current generation of the mapped original root.
Wrong roots, stale/foreign handles and other affine output types refuse.
One-shot nonce inputs refuse; only installed wire/key constructors and persistent
RNG inputs are admitted by this adapter. Services retain their issued references
and actual provider state across entry leases.

Each attempt issues a fresh selected-suite transcript with the same invocation
root, then retires it after runner cleanup. The host does not reset RNG/service
state or external primitive-work charge. The remaining instruction and
iteration fuel is passed into each runner; initialization failure retains
reached charges. Each attempt's runner charges its entry inputs again, even when
their storage is shared with a previous attempt. Transcript-transition limits
are per attempt. Every attempt's runner charges its bytes to the call's
[invocation root](capacity.md#invocation-ledgers) as it executes and keeps no
byte allowance of its own; a discarded attempt keeps its committed charges, so
later attempts run on what the root has left. Transcript initialization reabsorbs the bounded invocation root
once per attempt, outside interpreter and external-work charges. The proof
writer enforces the per-attempt byte cap before extending its buffer. Terminal
execution and cleanup failures prevent retry and publication. Cleanup diagnostics
do not replace a prior execution failure.

Only normal completion followed by successful session cleanup returns proof bytes
to the publisher. Failed/retried bytes and producer outputs never enter CLI
proof diagnostics. The typed SDK returns copyable original outputs only from the
selected successful final attempt. Per-attempt decisions, stop coordinates, counters and a policy digest are
private host diagnostics. The digest is SHA-256 of compact UTF-8 JSON for the
record above, with no whitespace and the supplied pair order. It is not inserted
into the transcript or proof. The application must authorize the policy itself;
verifier acceptance does not certify which retry policy the producer used. A
retry attempt may itself contain an accepting proof; discarding its bytes is a
host publication property, not an additional verifier predicate.

The native host supports the registered native transcript suites
and deployments with authored copyable external state. This policy does not expand the
constructor's rejection of authored transcript inputs, hidden selected draws or
unsupported message types.

## Design and ownership

| Component | Responsibility |
|---|---|
| Authored protocol | Compute the retryable result, including guards around partial operations, and return actual affine successors. |
| Compiler | Preserve that mathematics, output mapping, control, effects and transcript chain through the ordinary native pipeline. |
| Application | Authorize the deployment, retry result and RNG mapping, public context and resource/work limits. |
| Native host | Issue persistent roots once, reinstall the same service references for each entry, create/retire an attempt transcript, and recover backend custody on every outcome. |
| Controller | Discard retry bytes, preserve successor state and stop at the attempt limit. |
| Interpreter | Enforce the remaining instruction and iteration fuel and the root's byte allowances inside execution, including local bodies and initialization. |
| Publisher | Publish only a completed result after session cleanup succeeds. |

The host resolves original common-program port indices through the deployment's
retained input/output maps. Every RNG input and output has exactly one mapping.
On every normal return, including completion, the backend authenticates both
handles and checks the current successor belongs to the original root. Counters
and numeric IDs never construct a capability.

The backend is moved into each runner and recovered after success or failure.
A separate attempt function returns backend custody as part of its result type.
The runner removes its frame views at exit; reentry cannot inherit an old view.
Services release their leases and clear entry bindings on exit. Consequently the
host reinstalls the same references at reentry, rather than issuing replacement
providers. Transcript retirement releases its slot without reusing issuance IDs.

Only currently admitted copyable wire/key inputs and explicit RNG inputs enter
this repeated-entry adapter. It refuses one-shot nonce inputs. Copyable inputs
are retained unchanged, and their entry bindings are charged again on every
attempt. This does not grant copying permission to future resource types.

## Retry and transcript semantics

Each attempt starts the selected transcript suite with the same authorized
invocation root. The protocol's changing entropy influences messages and hence
challenges. Repeating identical inputs under the same root produces no new
challenges. Diagnostic attempt indices add no cryptographic bytes; any
additional construction bytes require an explicit suite rule. A terminal
stop, zero-inverse backend failure, exhausted provider or malformed successor
never becomes a retry. A protocol that wants recovery checks its condition and
returns false through ordinary control instead of executing a fatal operation.

No-progress retries deterministically consume the bounded attempt allowance.
The host does not invent a freshness or progress test. The application must
choose an appropriate retry rule; bounded execution proves no randomness law or
cryptographic retry probability.

| Budget | Scope |
|---|---|
| Attempt count | Whole host invocation; default 1, maximum 1024. |
| Proof bytes | Each tentative proof, including framing, enforced by the writer during production; default and maximum 16 MiB. |
| Instructions and iterations | Runner fuel, cumulative across the attempts of one call, bounded by the selected capacity; by default one million instructions and 100,000 iterations, at most 2^32 of each. |
| Logical work, fresh and live bytes | The call's [invocation root](capacity.md#invocation-ledgers), with no policy field: every attempt's runner bytes and proof buffer, and the completed proof's retained copy, are charged there before they grow, and a discarded attempt keeps its cumulative charge. These count retained payload bindings, not process RSS. |
| RNG and service draws | One persistent root budget; failed scalar consumes can increment generation/debit before refusal. |
| Transcript transitions | Per freshly issued attempt transcript; observations remain in the attempt record. |
| Transcript initialization | Reabsorbs the bounded invocation root once per attempt, outside interpreter and external-work charges; bounded by root size times attempt count. |
| External primitive work | Charges persist across attempts with the backend; each report includes its consumed work. The application may lower the invocation cap, reported separately from the attempt-policy identity. This counter does not include every PCS or polynomial kernel; their kernel/allocation limits apply independently. |

Only a completing attempt copies its writer bytes into the controller's bounded
private buffer. A retry discards its writer buffer directly.
The two buffers together hold at most twice the per-attempt cap in proof bytes;
allocator capacity, message encoding and other host storage are separate. The
host retains only the selected final proof. Cumulative written bytes are bounded
by attempt count times proof cap. A write-limit failure is fatal even if the
body would eventually have returned retry.

## Reports

`NativeDeployment::execute(&inputs, Invocation::Attempts(&policy))` shares input
admission and session cleanup with single-shot execution. It returns
`NativeProofReport`.
Its `outputs` field returns copyable original results from the successful final
attempt, keyed by original output index; failures and cleanup errors leave it
absent. Private state successors remain with the lifecycle. CLI diagnostics do
not serialize application outputs. The attempt report includes a canonical policy digest, per-attempt decisions,
interpreter usage, transcript observations and terminal stop coordinates.
Persistent-root observations describe actual final state, including failures.
Their `transitions` field reports the backend `draw_count`: bulk sampling charges
per-element units, while `generation` counts consuming transitions. Load-time
refusals occur before an entry frame exists, so they have no execution stop
coordinates; an in-body stop retains its origin and site.
CLI `messages` and `bytes` count all attempts. Producer-only `proof_bytes` gives
the size of the completed candidate, or zero on failure. Structural policy
refusals precede report construction; an admitted policy retains its digest even
if resource setup fails.
One-shot reports retain `stop` with the origin, role, site, kind, cleanup errors
and optional local call/function/instruction context. Attempt records retain their
own stops. The diagnostic local namespace changes no protocol/transcript bytes.
Primary execution failure and cleanup errors remain separate. The shared proof
driver preserves a stop reached during entry initialization before opening a
proof reader or writer, including its ordered cleanup diagnostics. Session cleanup
also refuses residual logical resource units; this proof host does not export
them to a caller. These are private host diagnostics, not fields in the published
proof.
