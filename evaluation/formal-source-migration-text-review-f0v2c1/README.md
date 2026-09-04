# Migrated owner-text freeze review

## Exact question

Does the current migrated PIR owner text close all seventeen verification
questions: decision fidelity, the terminal contract, public-coin transfer,
owner-name closure, manifest closure, publication-compiler agreement, family
body closure, PIR reference closure, static-view law selection, declaration-body
closure, Interface completion derivability, source-authority preimage equations,
the checked-construction checker contract, heterogeneous challenge-transition
representability, required-influence exactness, the Analysis owner-read join,
and public-setup view totality?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check
```

## Frozen answer

Yes. All seventeen findings are affirmative and the frozen aggregate is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`. The three blockers retained by
the previous freeze are closed, and the checker-contract question added in
this round is affirmative.

For completion derivability, the owner defines `SamplingInputTypes(c)` as the
transcript bytes followed by the challenge's public conditions and prior joint
members. The Interface names exactly those two trailing operand sequences; it
does not present the transcript bytes as a replay operand. Each non-occurrence
operand is a protocol-fixed constant, a slot-bound public input, or a derived
value of those. Although the raw `ValueRef` carrier has a verifier-private arm,
the Core transfer rule and canonical Fiat--Shamir admission rule refuse a
verifier-private dependency from an admitted public condition. The previous
occurrence-valued countermodel is refused when its
`ExternalApplication` transport entry is absent and passes this admission gate
when the entry is present. The owner transition and replay equations then make
each draw, acceptance result, and final state a function of the presented
operand values and prefix state.

The completion coordinate types remain within the Foundation bounds. The fixed
worst tuples are `(11,1,0,0)` for the challenge natural, `(12,1,0,0)` for the
receipt-count natural, and `(64,3,2,1)` for the domain-payload record. Both
state coordinates inherit the construction's stricter tagged-completion
preflight, and the six coordinate constructors match the six body arms.

For source authority, the audit scans every top-level PIR Markdown page,
fourteen identity-constructor sites, and twenty-four profile compiler
definitions. It forms the binding payload, capability requirement, no-policy,
and policy-closure subjects for canonical-framed execution and checked
construction routes and for the corresponding duplex compiler arms. All
sixteen encoded subject bodies are byte-equal to independently assembled owner
equations. The two issued canonical bindings also carry the four expected
identities; the duplex comparison exercises the executable compiler directly
because this bounded model has no duplex issuer.

The checked-construction payload now carries the owner-defined checker
contract. For the canonical-framed family, the evaluator-signature,
semantic-law, and failure-schema references resolve at catalog ordinals
`(1,3,1)`; for the duplex family they resolve at `(1,6,1)`. Both bind the
checker-contract body compiler at ordinal 5. The canonical body is 1,871 bytes
with SHA-256
`f8f79c99a8e74702367b7bfa6fc0a7ccc16427282aae23f24666c0c2ceff97fb`
and live identity
`zkcidv0:pir.checker-contract:ebe686d6fb48030f03b79f1cfe72994705c40ea2414afc59a44ff149b8dfd701`.
The duplex body is 5,243 bytes with SHA-256
`75eb2fe3aa516c17e0ae365df9bd8d4c7c218c7a8852ae39e1dc927ee5b64765`
and live identity
`zkcidv0:pir.checker-contract:393ff59dfef32f77fee523fc0708dbe591c964369fb2b9461947ff93d9c83210`.
The executable bodies equal the owner equations byte for byte, while the former
package-local checker coordinate is rejected.

For public setup, the occurrence-derived countermodel still projects exactly
to empty `entries` and `run_established = [0]`. The repaired statement is now
uniqueness per protocol and invocation, up to the quotient's covered-value
equivalence. A second executable discriminator gives distinct view bodies to
two invocations of one protocol whose covered public input differs, exactly as
that statement requires. The fixed-setup premise owned by Analysis is outside
this round's scope and is recorded as `OutsideScope`, not converted into a
`CannotAnswer` finding.

The heterogeneous two-rule transition and symbolic prior-draw countermodels
remain exact. The Analysis read catalog still contains ten literal selections
and 66 selected fields, all resolved to owner body fields and exact ordinal
subtrees. The ten earlier verification questions also remain affirmative.

## Publication reconstruction

The reference and independent publication compilers agree on all eighteen
profiles at the current tree, the earlier comparison tree, and the migration
base. Relative to the previous round, fourteen profiles rotate; `interaction`,
`verifier-derived-query-plan`, `oir-endpoint-graph`, and `analysis-kernel`
remain stable. Relative to the earlier comparison tree, sixteen profiles rotate and
only `oir-endpoint-graph` and `analysis-kernel` remain stable. Relative to the
migration base, seventeen profiles rotate and only `analysis-kernel` remains
stable. Foundation is unchanged. The check does not write the publication
table; the checked-in legacy table is expected to differ for six profiles.

## What a passing check establishes

A passing `--check` establishes that the exact pinned sources reproduce the
seventeen frozen outcomes and evidence digest, including the replay-input
countermodel, all sixteen source-subject byte comparisons, both live
checker-contract equations, the per-invocation public-setup discriminator, and
agreement of the two publication compilers.

It does not publish or bless an identity, prove an owner law for arbitrary
values, validate an external compiler, runtime, provider, backend, or endpoint,
establish relation satisfaction or theorem truth, or prove Fiat--Shamir,
random-oracle, concrete-sponge, quantum-random-oracle, protocol-security,
deployment, or production-readiness claims. It makes no finding about the
Analysis-owned fixed-setup premise and does not edit any owner source or
manifest.

## The stacked Analysis branch

The Analysis branch carries this package unchanged while its own pages rotate
the Analysis profiles. The rotation cones are therefore asserted relative to
the pinned migration head: the current tree may rotate, beyond each recorded
cone, exactly the profiles that differ from that head, and every such profile
must be Analysis-owned. On the migration branch the current tree equals the
head, so the recorded cones apply unchanged; on the Analysis branch the
kernel and the five Analysis profiles rotate additionally, and the frozen
metrics digest of this copy records that.

