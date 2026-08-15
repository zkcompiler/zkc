# emit — the endpoint emitters and their runtime

This cargo workspace turns one persisted canonical OIR document into a
standalone Rust crate: `verify(statement, proof)` over untrusted bytes
from a verifier document, `prove(statement, witness)` from a prover
skeleton, both buildable and runnable without zkc. It is the third
consumer of the canonical format after the C++ interpreter and the
Python reference twin, written against `docs/spec/carrier.md` §6.2 alone
— that section's own charter is that a second implementation must be
derivable from it.

Both endpoints come out of one emitter and one walk. That is not an
implementation convenience: the two frames are projections of the same
sealed spine, so everything before the wire — the sponge, the absorbs,
the challenge derivations, the constants, the algebra — is literally the
same emitted code, and only the four rows where the wire reverses
direction differ.

## Members

- **`zkc-emit`** — the emitter. Recomputes the artifact identity from
  the document bytes before reading a row (`SHA256("zkc/oir\n" ‖ bytes)`),
  computes the provenance-independent semantic id by the §6.1 erasure,
  resolves one supplier binding, walks the row grammar once, and writes
  the crate. It is structured as the staged form of the reference
  interpreter: one emit function per row kind, in the reference
  dispatch's own order, so a semantic change over there has exactly one
  place to land over here.
- **`zkc-rt`** — the runtime the emitted crates share: the normative
  verdict vocabulary (`docs/spec/endpoints.md` §4), the proof cursor,
  the prover's observables and refusal type, the opaque witness
  `Payload`, and the supplier sets as concrete types. Feature `toy` is
  the SHA-256 chaining duplex, big-endian codecs, and the sigma fills;
  feature `plonky3` is zkc's spec-anchored lenpad duplex over the pinned
  upstream Poseidon2-16 permutation — the same revision the replay
  harness locks, with the pinned known-answer test as a test on both
  sides of the wire; feature `kzg` is the BLS12-381 codecs and the two
  opaque KZG check predicates over the arkworks curve kernel,
  implemented exactly as their content-addressed predicate
  specifications state them. Feature `zeroize` zeroes witness payloads
  on drop; it is off by default because memory hygiene is a claimable
  property only when the whole call chain cooperates.
- **`bindings/`** — supplier bindings: `toy`, `toy-cheat` (the same set
  with one fill replaced by a boundary-conformant wrong algebra, so the
  reject boundary is observable end to end), `plonky3` (artifact-id iv),
  `plonky3-zero-iv` (the value-faithful counterpart start), and
  `kzg-toy` (the toy duplex with BLS12-381 `fr`/`g1` codecs and the two
  KZG check adapters; its `tau_g2` is known-τ test setup material, where
  a deployment binding pins a ceremony point).

## The emit-time refusal surface

A binding gap — a codec class, sponge construction, construction-digest
pin, algebra, check adapter, or hole fill the document needs and the
binding does not supply — is an emitter error naming the gap: the
E400-family profile refusals of the reference executor, moved to emit
time. What the emitted crate can report at run time shrinks
accordingly. A verifier judges proofs (the normative reject classes) or
reports malformed caller input, and never says "cannot judge". A prover
has no verdict channel at all — acceptance belongs to verifiers — so it
either produces bytes or refuses, naming the out-of-range statement
value or the fill that reported a defect; a missing witness payload is
not a run-time arm either, because every payload is a named field.

## What an emitted crate contains

Baked identities (`ARTIFACT_ID`, `SEMANTIC_ID`, `SOURCE_PIR_ID`, the
binding name and file digest), a typed `Statement` in ABI order, the
straight-line entry point, and a generated conformance suite carrying
the golden vectors it was emitted with. A prover crate adds a typed
`Witness` of opaque payloads and the `COUNTERPARTY` rows naming the
checks it delegates. Emission is byte-deterministic in (document,
binding, emitter version); the `test/Emit/` suites diff a double
emission.

Witness payloads are move-only values. The carrier's rule that a handle
is consumed exactly once (`zkc-E149`) is checked during the walk and
then enforced again by the borrow checker in the emitted crate, which is
why the generated prover needs no run-time linearity bookkeeping.

Two rules keep the generated text honest. Labels, class names, domains,
and identities are protocol content, so a string reaching generated Rust
is untrusted input entering a language: `zkc-emit`'s `rust` module is the
only path it may take, and it has one constructor per position — an
identifier (checked, and unique within its struct), a string literal
(escaped), a line comment (unable to end early). And the crate's
preamble is written from what the walk recorded emitting, not from a
second reading of the rows, so a body that never squeezes, reads,
writes, or names its statement declares nothing it then leaves alone.

## Verification

Rings exercised by `test/Emit/`:

1. **Differential** — the same golden vector files the reference
   executor replays (`zkc-run --vectors`, `zkc-run --prove`) drive the
   emitted crates. For a verifier, verdicts and ordered challenge logs
   must match; for a prover, the proof bytes and the challenge log must
   match, which puts the whole output under test rather than a
   classification.
2. **Embedded conformance** — `cargo test` inside the emitted crate:
   vectors with a positive control, the refusal battery with its
   classification, ABI label, and supplier sentence, the permutation
   known-answer test on plonky3 bindings, and the identity binding.
3. **Emitted round trip** — the emitted prover's bytes into the emitted
   verifier of the same projection, in one process, with entry-for-entry
   equal challenge logs; and the `toy-cheat` prover's bytes rejected by
   that same verifier at `check_failure`, transcript consistency intact
   (`emit-schnorr-prover.test`).
4. **Upstream fill** — the value-faithful FRI artifact's wire, filled
   by the pinned Plonky3 crates through the replay runner, accepted by
   the emitted crate (`emit-plonky3-real-fill.test`), with the corrupted
   control rejected.

These establish behavior for the exercised artifacts under the named
bindings and pins. They are not a claim of protocol soundness, zero
knowledge, backend conformance beyond the fixtures, or a stable public
schema for the binding files.
