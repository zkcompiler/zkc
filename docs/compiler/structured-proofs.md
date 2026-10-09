# Structured proof boundaries

Native proof policy `/5` permits one typed message to contain records,
alternatives and variable-length numeric data. It reuses nominal variants,
dynamic field/group tensors and the ordinary interpreter. The exact contract is
[structured native proof messages](../spec/profiles/compiler/structured-proof-messages.md).

## Shape and execution

The maintained batch client has this structure:

```text
Batch = None | Plain(vector<Fr>) | Scaled(vector<Fr>, Fr)
Announcement = { commitment: G1, batch: Batch }

producer:
  k = nonce.draw()
  send Announcement(g * k, private_batch)
  c = derived_challenge()
  send k + c * witness

validator:
  announcement = receive Announcement
  (count, value, tag) = inspect(announcement.batch)
  guard count == public_count
  guard value == public_value
  guard tag == public_tag
  c = derived_challenge()
  z = receive Fr
  return g * z == announcement.commitment + public_key * c
```

The alternatives, vector lengths and scalar leaves contribute distinct
canonical bytes to the challenge. The validator observes its decoded message.
A changed producer batch with a freshly recomputed transcript still fails the
authored public-configuration guards. This is an execution test, not a
zero-knowledge claim for the batch or a new protocol theorem.

The second client sends `None | Some(value: Fr, proof: KZGOpening)` and checks
the present arm against an authorized key, original commitment and actual
point. It opens the same immutable backing twice through composed local calls.
The absent arm cannot satisfy acceptance. This authored client has no inserted
transcript. It exercises the same interpreter and proof-host codec as the batch
client, with ordinary PCS kernels.

## Responsibility boundaries

| Owner | Responsibility |
|---|---|
| `data` / existing variants | Total common data operations and nominal aggregate identity |
| `local` | Checked construction and elimination, including copyable non-total PCS payloads |
| `protocol` | Roles, messages, guards, source origins and selected construction |
| `crypto` | Typed transcript observation and PCS operations |
| Native codec | Expected-type frames, canonical leaves, complete consumption and aggregate limits |
| Proof host | Deployment authority, entry constructors, key authorization and independent publication/validation |
| Common interpreter | Local operations, state transitions, ordered effects and cleanup |

Copyability alone does not grant total mathematical operations, a wire codec or
cross-role availability. Every alternative is checked, including inactive ones.
No key or live resource can hide inside a message. Existing common generic
contracts remain constructor applications; the new construction observer uses
an explicit complete-Type input term. The declaration inventory is version `/2`
and records that port as `{"term": index}`. The generated executable catalog
combines common and non-generic declarations without widening common admission.

## Validation

- [Compiler clients](../../compiler/test/native_structured_proofs.py) exercise
  both BLS transcript suites, simplification/storage modes, unsupported-format refusal
  and standalone numeric frames.
- [Batch runtime client](../../crates/zkc-tools/examples/native_structured_proof.rs)
  exercises every alternative, empty and dynamic batches, recomputed dishonest
  transcripts, descriptor mutations and cleanup. A separate reference uses
  upstream transcript primitives and direct frame parsing.
- [PCS client](../../compiler/test/fixtures/mathematical/structured-opening.mlir)
  exercises optional opening payloads, composed calls and actual guarded
  terminals. Its reference verifies the opening with upstream pairing operations.
- [Codec controls](../../crates/zkc-backends/tests/structured_wire.rs) cover
  malformed tags/lengths/canonical leaves, inactive forbidden payloads, aggregate
  counts, retained-byte bounds, depth and setup identity.
- [Cross-build tests](../../tests/protocol/test_native_mathematical.py) run
  production and validation as independent CLI processes. Old Lean readers
  refuse these native formats; they are not a native execution oracle.

## Remaining work

Finite nested records with numeric vectors and
[runtime-count sequences](nested-data.md) are implemented. Sequences contain
records or independently shaped matrices with explicit storage and codec rules. MLIR tensors retain their admitted numeric element types; no tensor of
an arbitrary record is implied. A shared native codec plan is unnecessary for
the current bounded descriptors; measured repeated descriptor work could justify
one later without changing wire identity.

Common `data` operations still require total payloads. A future client needing
common construction of immutable non-total values must justify a separate
data-operation contract; local construction already handles the present PCS
case. Installed domain/key generalization and [authored transcript deployments](authored-transcripts.md)
execute; the [validation map](foundation-validation.md) records their evidence
and limits. Shrinking group/vector
compositions execute in the [composed-state clients](composed-state.md). Additional protocol libraries and native Lean semantics remain separate work.
