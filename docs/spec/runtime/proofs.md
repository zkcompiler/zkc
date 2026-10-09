# Proof execution

This native contract defines proof execution, completion and failure.
[Transport](../formats/proof.md) owns bytes; [attempts](attempts.md) own retries.

## Completion and failure

Validation accepts only after the selected Boolean result is true, the role has
returned normally, and the proof reader is exhausted. A true result with
trailing bytes is not acceptance. Stop reasons retain their distinctions; host
failures are not coerced into an ordinary false result. A partial proof is never
a completed producer result. Successful completion permits [per-file publication](publication.md), with
its own staging and failure rules. A runner already stopped during entry initialization retains that
stop and its cleanup diagnostics; the driver does not open a proof reader or
writer after that stop. Every proof operation otherwise requires a runner still
at entry. Successful ingress is part of loading; polling that merely exposes the
first action is allowed. A completed or partly consumed runner refuses with
`artifact-runner-started`, before consuming proof bytes. A live partly consumed
runner is cancelled and retains its cleanup observations. A pre-existing terminal
stop is returned unchanged, even on a subsequent call; it is not a new proof
failure. The host always constructs a fresh runner for each proof or attempt.

One-shot reports retain the actual stop, including local call/function/instruction
coordinates, independently of their short failure code. Attempt reports retain
per-attempt stops. Ingress keeps its `ingress.<parameter>` outer site and stores
the inner instruction separately. These are diagnostics and do not alter origins,
transcript history or proof framing.

Session cleanup requires no active frames or residual logical resource units.
The proof host does not export returned logical units to a caller. Deployment
admission refuses affine entry outputs other than RNG, nonce or transcript
successors with `native-proof-output-kind`, before invocation loading or issuance.
The attempt policy further restricts successors to its persistent RNG and
transcript kinds. Internal units remain legal when consumed or retired at frame
exit. Unreturned units retire on return, stop or cancellation. The final residual
unit check is a defense against a broken backend or host custody contract:
`native-proof-live-resource-units` prevents publication, including for single-shot
execution. Admitted completed executions do not normally reach this refusal.

Completed draws, transcript transitions, consumed bytes and work remain consumed
on rejection, stop, cancellation and failed attempts. Decoding finishes before
the receive is accepted and before its subsequent transcript observation. A
length consumed before truncation remains consumed in the reported prefix.

The constructor preserves a finite attempt body; the native Host repeats it
only under the explicit [attempt policy](attempts.md).

Independent loop execution uses the role's actual count under declared bounds.
Any required shared count is derived from bound public context or an admitted
proof value and checked by the validator; a joint driver's agreement check is
unavailable in independent proof execution. Zero trips execute no body draws or
absorptions. Program and metadata size remain independent of runtime trip count.

### Typed invocation inputs

`NativeDeployment::execute_typed(&ProofInputs, proof)` and
`execute_attempts_typed(&ProofInputs, policy)` share preparation, issuance,
execution and cleanup with positional invocation records. The adapter checks
explicit original port selectors before constructing the typed request. Typed
vectors follow the admitted public, role-input and service order exactly.
Context is a byte vector of at most 4096 bytes; provider/transcript budgets retain
the one-million-transition ceiling. Attempt policy admission precedes request
parsing, material loading and entropy issuance.

Public values are independently authorized by the caller. Ordinary public and
private data use shared `InputValue::Native`, `Wire` or `Variant` constructors.
Native values retain upstream library invariants and undergo the same complete
physical type, installed profile, setup and entry checks as decoded data.
Public verifier keys require canonical wire bytes and independently installed
pins. A role's unit `VerifierKey` declaration selects its admitted public key;
a prover key uses its separate authenticated material constructor. Foreign
capabilities or key handles cannot enter through ordinary native data.

`ProverMaterial::from_bytes` imports immutable proving material against a complete
material fingerprint and the supplied verifier key. Import alone grants no
invocation authority: each call selects its own independently pinned setup.
`from_file` captures
one bounded regular file and delegates to the same import. The handle has private
storage and supports shared ownership; requests use `InputValue::ProverKey`.
Each invocation rechecks the actual selected setup, complete physical type and
current backend limits before loading files or issuing resources. Retained data,
loading work and every runtime/retry operand remain charged. Reuse avoids file
reads and key parsing; it shares no live capability or mutable session. Import
checks per-object wire/retention limits; execution budgets belong to each call.
A material fingerprint authenticates identity, not the honesty of setup bases.

Constructor shapes, complete native types, wire lengths and the statically known
binding-root size are checked before importing verifier keys. The whole
invocation reserves loading capacity before data decoding, key-file
reads or entropy issuance. Public verifier-key import scans consume cumulative
work and registry material consumes retention, including receive-only keys.
Immutable values are validated before loading other wire/file inputs. Public
native values are canonically encoded for the binding; private native values
need no serialization unless they also occupy a public port. Every shared role
operand must have the same canonical bytes as its independently supplied public
value. Mismatch returns `native-proof-shared-public-input` before execution.
Wire requests retain exact-byte agreement and reuse the matching admitted public
value. Additional native encoding work is reserved before loading, and binding
hex expansion is bounded before allocating its strings. Invocation loading
capacity and per-attempt execution budgets are distinct: a valid request may
load successfully and then report an execution limit at its first attempt.

### Typed participant results

`NativeProofReport::outputs` contains successful copyable results keyed by their
original common-program output indices. Producer and validator results use their
own role maps. It is `None` on rejection, body failure, attempt exhaustion or
cleanup failure, and `Some` with an empty map when success has no copyable
original results. Generated transcript results and private RNG/nonce successors
remain lifecycle state and are retired; they are not exported as data. Result
selection follows the admitted output map and physical duplicability.

A bounded attempt run retains results only from the final successful attempt.
Earlier attempts retain their existing decision/usage/stop records. The Host
uses the same controller and actual provider state across attempts. Adding SDK
result access neither serializes those values into CLI diagnostics nor places
them in proof bytes; proof framing and binding remain unchanged.

## Terminal composition

The protocol author is responsible for naming the original commitment, actual
verifier point, claimed value, opening proof and authorized verifier key, and for
making the `pcs.check` result necessary for acceptance. An ordered guard is one
way to do this. A final Sumcheck residual by itself does not verify a committed
polynomial evaluation. The committed Sumcheck examples open each factor at the
verifier's accumulated point and combine those checked evaluations with the
final claim.

The compiler preserves the authored operands, guards and result flow; it does
not prove that these choices establish the intended relation. Omitting an
opening guard in the source can therefore produce a well-formed deployment
with an unsound acceptance predicate. Source-relative checking rejects changing
or removing a guard or its operand relative to the captured source. These are
distinct checks: preserving a protocol does not prove its soundness.

`pcs.commit` retains an immutable original table in its local opening state.
Sumcheck restrictions produce separate scratch tables. Opening the original
state through aliases, including repeated openings, cannot replace its backing
with a restricted table. The installed PCS requires positive arity; a
zero-variable committed invocation refuses instead of silently padding. Public
zero-variable Sumcheck remains available without this PCS terminal.

These contracts establish representation and execution boundaries. They do not
establish PCS or Fiat–Shamir security, hiding, a zero-knowledge protocol or native
Lean correspondence. For authored proofs, unrelated application context remains
only header-bound unless the authored algorithm binds it cryptographically.
