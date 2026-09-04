# F1-R1A target-profile basis and substitution discriminator

This bounded research gate closes only the first prerequisite of exact target
reification: the selected `pir.interaction` profile and its owner source are
available as exact, independently reconstructed inputs. It also demonstrates
why neither a K2 fixture ID nor the same fixture body hashed under the target
profile is an admitted target `InteractiveCore`.

It is not a target Core body compiler, target admission evaluator, static-view
evaluator, Q1 source-correspondence result, formal proof, cryptographic result,
or compiler component.

Run the focused gate from the repository root:

```sh
python3 -B evaluation/formal-source-target-basis-f1r1a/run.py --check
```

Print the complete derived evidence record with:

```sh
python3 -B evaluation/formal-source-target-basis-f1r1a/run.py --print-evidence
```

## What the gate checks

The positive side reuses both implementations in
[`semantic-profile-publication/`](../semantic-profile-publication/README.md)
and checks that they reproduce byte-identical `pir.interaction` profile bodies
and references. The result must also equal the frozen v0 row in
[`published-identities.json`](../../docs-next/pir/profiles/published-identities.json).
The gate then checks the owner routing for the Core and Fresh Protocol body
compilers, admission law, static-view law, and evaluator signature. A small
source-shape discriminator confirms that Appendix A names fourteen top-level
Core fields and two top-level Protocol fields. This is not a complete grammar
parser or executable law interpreter.

The negative side forms the retained K2 Schnorr fixture and checks:

- its witness-local Interaction profile differs from `pir.interaction`;
- its Core body has eight top-level fields rather than the target fourteen;
- Foundation can nevertheless form a new `pir.interactive-core` typed ID by
  hashing those bytes under the target profile;
- the resulting identity still encloses a shape-invalid target body;
- its Fresh Protocol wrapper has the same two top-level field ordinals as the
  target wrapper but references the fixture Core; and
- recursively replacing that Core reference with the newly formed ID still
  cannot supply target Core admission.

The focused gate therefore passes ten expected boundary results: five
Affirmative target-basis observations, one `KindMismatch`, and four Refused
substitution attempts. These are heterogeneous expected outcomes, not ten
positive conformance claims.

## Design finding

The executable distinction is:

```text
typed identity formation
  != target carrier validation
  != target semantic admission
  != owner-issued exact view
```

The published profile commits the body grammar and laws, but the Foundation
identity primitive intentionally does not execute those owner laws. Profile
binding is therefore necessary and not sufficient. Protocol admission must
retain the exact admitted Core dependency, and a formal-source package must
consume owner-issued or independently reconstructed exact views rather than
infer admission from a typed digest.

## Next gate

The subsequent F1-R1B gate now supplies one complete fourteen-field target
Fresh Schnorr Core and its two-field Protocol, exact-used semantic modules and
declarations, a separately written body re-encoder, and a bounded
implementation of the applicable target admission sequence. The following
[`F1-R1C0 audit`](../formal-source-owner-views-f1r1c/README.md) preserves that
admitted subject but returns `CannotAnswer` for exact owner-view source
determinacy, reopening F0-V at the PIR schema/publication boundary. F1-R1C
waits on that repair; F1-R1D then integrates the target values with
Relations/correspondence roots and the F1-R0 package checker. F1-I remains the
separate live-handle and source-authority gate.

The retained K2 witness remains useful as an execution and mutation oracle,
but it cannot be promoted by profile substitution. A complete semantic bridge
would have to translate K2 data into the target carrier and independently
validate the target result; equality of labels, field counts, or IDs is not
that bridge.
