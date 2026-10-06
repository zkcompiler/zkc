# Native proof attempts

Native proof production can repeat one admitted participant entry while retaining
its actual RNG and service state. An application selects a producer Boolean
result: false requests retry; true completes. The existing controller and native
proof driver implement this policy. There is no retry dialect or protocol-specific
execution loop.

The [native proof specification](../spec/profiles/compiler/native-proofs.md#native-attempt-policy)
owns the policy format and lifecycle. [Status](../status.md#foundation-capability-map)
records coverage; the [roadmap](../roadmap.md) orders the remaining consumer migration.

## Design and ownership

| Component | Responsibility |
|---|---|
| Authored protocol | Compute the retryable result, including guards around partial operations, and return actual affine successors. |
| Compiler | Preserve that mathematics, output mapping, control, effects and transcript chain through the ordinary native pipeline. |
| Application | Authorize the deployment, retry result and RNG mapping, public context and resource/work limits. |
| Native host | Issue persistent roots once, reinstall the same service references for each entry, create/retire an attempt transcript, and recover backend custody on every outcome. |
| Controller | Discard retry bytes, preserve successor state and stop at the attempt limit. |
| Interpreter | Enforce the remaining instruction/call/iteration and payload budgets inside execution, including local bodies and initialization. |
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
challenges. Diagnostic attempt indices add no cryptographic bytes. A terminal
stop, zero-inverse backend failure, exhausted provider or malformed successor
never becomes a retry. A protocol that wants recovery checks its condition and
returns false through ordinary control instead of executing a fatal operation.

The concrete model is consistent with the restart boundary in the pinned
[Monero BP+ prover](https://github.com/monero-project/monero/blob/4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5/src/ringct/bulletproofs_plus.cc#L532):
it restarts transcript construction on a zero challenge and draws new prover
randomness. This is a lifecycle reference, not an interoperability claim. The
implemented clients use the installed BLS Merlin and Spongefish contracts.

No-progress retries deterministically consume the bounded attempt allowance.
The host does not invent a freshness or progress test. The application must
choose an appropriate retry rule; bounded execution proves no randomness law or
cryptographic retry probability.

| Budget | Scope |
|---|---|
| Attempt count | Whole host invocation; 1 through 1024. |
| Proof bytes | Each tentative proof, including framing, enforced by the writer during production. |
| Instructions, participant calls, iterations | Cumulative across all runners in the invocation, bounded by interpreter hard ceilings. |
| Retained payload charge | Live limit per runner and cumulative total charge across attempts; counts bindings, not process RSS. |
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

## API and commands

`NativeDeployment::execute_attempts(inputs, policy)` shares input admission and
session cleanup with ordinary `execute`. Both return `NativeProofReport`. The
attempt report includes a canonical policy digest, per-attempt decisions,
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

Run from the repository root after the [native build](../development/README.md),
with `target/release` on `PATH` and an authenticated deployment and invocation
configuration.

```sh
zkc produce-native-proof deployment.json TRUSTED_SHA256 producer.json proof.bin --attempts=attempts.json
zkc validate-native-proof deployment.json TRUSTED_SHA256 validator.json proof.bin
```

The application authenticates `attempts.json` alongside its deployment
configuration. Any local key-file paths in inputs are also host configuration,
not untrusted request-selected paths. The recorded policy digest supports
auditing; it does not bind a retry policy into the proof or prove that a producer
used it. Ordinary single-shot production remains a separate application choice.
The validator receives its public context and final proof, without prover state
or failed attempts.

## Evidence and scope

The [source generator](../../compiler/test/native_attempts.py) and
[runtime client](../../crates/zkc-tools/examples/native_attempts.rs) exercise:

- A two-round scalar fold with an affine RNG, a returned zero-condition decision,
  partial inversion under `local.if`, and constructed transcript successors
  through `protocol.repeat`.
- Service-backed Schnorr with the same host, without RNG ports, and a fold
  carrying both an affine RNG and a service provider.
- A transcript-free, header-only client with no resources, including 1,024
  deterministic retries, normal first-attempt completion and a completion output
  after another producer result.
- Both installed transcript suites, ordinary/unsimplified/released storage,
  forced retry through the fourth attempt, shorter completed proofs after longer
  discarded prefixes, first-attempt completion and fatal stops.
- Exact equality with a single attempt supplied the advanced random value;
  independent validation, canonical changed messages and reordered observations.
- Cumulative work/payload limits, proof and transcript limits, exact scalar draw
  debit on provider exhaustion, final retirement failure suppressing completed
  bytes, wrong same-typed RNG result maps on both retry and completion, malformed
  policies and one-shot input refusal. A partial setup failure retires the
  already-issued RNG and retains its policy digest.
- [Committed-profile attempts](../../crates/zkc-tools/examples/native_committed_proof/main.rs)
  reuse an actual prover key for PCS commit/open execution, accept a completed
  proof independently, and charge entry payloads again on retry even when key
  storage is shared. Exact canonical policy-digest bytes are checked separately.
- [Separate CLI processes](../../tests/protocol/test_native_mathematical.py),
  including failed production preserving an existing proof and creating no
  partial output file. Deterministic provider tapes exercise forced retries;
  separate CLI processes exercise production entropy and first-attempt completion.
- Guaranteed false completion results force three production-entropy attempts for
  BLS affine RNGs and services under both suites. The
  [typed domain client](../../crates/zkc-tools/examples/native_domains.rs) also
  exercises Ristretto and ext8 service retries. Final root transition counts,
  cumulative work/bytes and clean retirement are checked independently of sampled
  values. This establishes the reached lifecycle, not an entropy distribution.

Resource-origin tests cover ambiguous-root refusals and composed RNG/transcript
local control. [Authored transcripts](authored-transcripts.md) cover
copyable external states, exact primitive inputs and retained work in this same
host. [Composed state](composed-state.md) and [nested data](nested-data.md) cover
their selected message/container extensions. [Entry completion](entry-completion.md)
adds conditional participant return and retained prefix coordinates. Arbitrary
affine transcript inputs, full BP+, new distribution/security analysis
and native Lean correspondence retain separate contracts.
