# emit — the verifier emitter and its runtime

This cargo workspace turns one persisted canonical OIR verifier document
into a standalone Rust crate: `verify(statement, proof)` over untrusted
bytes, buildable and runnable without zkc. It is the third consumer of
the canonical format after the C++ interpreter and the Python reference
twin, written against `docs/spec/carrier.md` §6.2 alone — that section's
own charter is that a second implementation must be derivable from it.

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
  and the supplier sets as concrete types. Feature `toy` is the SHA-256
  chaining duplex and big-endian codecs; feature `plonky3` is zkc's
  spec-anchored lenpad duplex over the pinned upstream Poseidon2-16
  permutation — the same revision the replay harness locks, with the
  pinned known-answer test as a test on both sides of the wire; feature
  `kzg` is the BLS12-381 codecs and the two opaque KZG check predicates
  over the arkworks curve kernel, implemented exactly as their
  content-addressed predicate specifications state them.
- **`bindings/`** — supplier bindings: `toy`, `plonky3` (artifact-id
  iv), `plonky3-zero-iv` (the value-faithful counterpart start), and
  `kzg-toy` (the toy duplex with BLS12-381 `fr`/`g1` codecs and the two
  KZG check adapters; its `tau_g2` is known-τ test setup material, where
  a deployment binding pins a ceremony point).

## The emit-time refusal surface

A binding gap — a codec class, sponge construction, construction-digest
pin, or algebra the document needs and the binding does not supply — is
an emitter error naming the gap: the E400-family profile refusals of the
reference executor, moved to emit time. The emitted crate consequently
has no "cannot judge" outcome; at run time it judges proofs (the
normative reject classes) or reports malformed caller input, nothing
else. An opaque `check_call` dispatches by contract digest to a bound
adapter and refuses when the binding carries none; every prover-frame
row refuses — this emitter takes verifier documents.

## What an emitted crate contains

Baked identities (`ARTIFACT_ID`, `SEMANTIC_ID`, `SOURCE_PIR_ID`, the
binding name and file digest), a typed `Statement` in ABI order, the
straight-line `verify`, and a generated conformance suite carrying the
golden vectors it was emitted with. Emission is byte-deterministic in
(document, binding, emitter version); `test/Emit/emit-schnorr.test`
diffs a double emission.

## Verification

Three rings, exercised by `test/Emit/`:

1. **Differential** — the same golden vector files the reference
   executor replays (`zkc-run --vectors`) drive the emitted crate;
   verdicts and ordered challenge logs must both match.
2. **Embedded conformance** — `cargo test` inside the emitted crate:
   vectors with the accepting control first, the permutation
   known-answer test on plonky3 bindings, and the identity binding.
3. **Upstream fill** — the value-faithful FRI artifact's wire, filled
   by the pinned Plonky3 crates through the replay runner, accepted by
   the emitted crate (`emit-plonky3-real-fill.test`), with the corrupted
   control rejected.

These establish acceptance behavior for the exercised artifacts under
the named bindings and pins. They are not a claim of protocol soundness,
zero knowledge, backend conformance beyond the fixtures, or a stable
public schema for the binding files.
