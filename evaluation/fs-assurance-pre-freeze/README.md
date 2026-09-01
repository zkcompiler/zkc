# Fiat--Shamir assurance pre-freeze pressure instrument

This bounded package falsifies the idea that one transcript check or one
formally verified verifier can stand in for the complete Fiat--Shamir assurance
chain. It is a temporary research instrument, not zkc authority, an FS
implementation, a profile compiler, or a cryptographic proof.

The finite model separates ten layers:

1. exact logical challenge prefixes;
2. closed external-Statement correspondence;
3. typed, unambiguous encoding;
4. concrete state-transition binding;
5. challenge-sampler adequacy;
6. adaptive oracle-process correspondence;
7. interactive source properties and theorem application;
8. static OIR projection preservation;
9. realization and parser conformance; and
10. deployment and composition separation.

The tests include positive controls and mutations for weak Fiat--Shamir,
missing prior and last-challenge material, ambiguous concatenation, free
trailing-zero limbs, high-bit truncation, biased decoding, unmodeled rejection
failure, session/Statement confusion, static-law loss, weak lowering, trailing
proof bytes, a BCS label without a state-restoration premise, and an invalid
classical-to-QROM upgrade. The finite limb and truncation cases are
**advisory-shaped witnesses**: they demonstrate the class of semantic
distinction exposed by CVE-2026-46654 but do not reproduce Plonky3's field,
permutation, exploit, or patched code.

Run the focused gate from the repository root:

```sh
python3 -B evaluation/fs-assurance-pre-freeze/run.py --check
```

## What a passing gate means

A passing gate means only that the selected finite controls and mutations
produce the expected qualified outcomes in this Python model. In particular:

- a typed length-delimited control has no collision in the enumerated domain;
- the deliberately ambiguous encoders have explicit aliases;
- structural exactness does not hide those aliases;
- total exact-uniform and conditional-with-failure sampler contracts remain
  different;
- an exact static projection and bounded realization vectors detect selected
  substitutions; and
- a security request remains incomplete when theorem, source-property, ROM, or
  QROM premises are absent.

It does not prove injectivity outside the selected finite domains, collision
resistance, sponge security, random-oracle correspondence, state-restoration or
round-by-round soundness, theorem truth, OIR correctness, compiler correctness,
implementation conformance, parser safety, QROM security, or deployment
readiness. Even the all-green finite qualification case retains evidence kind
`bounded-control`; it cannot be reinterpreted as any of those claims.

The exact research mapping, source corpus, current-target audit, and freeze
recommendation live in
[`docs-next/notes/semantic-revalidation-and-redesign/semantic-closure-and-freeze/fs-assurance-pre-freeze/`](../../docs-next/notes/semantic-revalidation-and-redesign/semantic-closure-and-freeze/fs-assurance-pre-freeze/).
