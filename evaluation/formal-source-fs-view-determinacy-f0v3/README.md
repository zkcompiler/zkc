# F0-V3B Fiat--Shamir family view bodies and rotation cone

This package asks one exact question:

> Do the two explicit proposed owner fragments close the eleven F0-V3
> description obligations as eight finite FS-family view schemas such that both
> schema compilers agree, every view value inhabitable by the K2 and duplex
> witnesses is byte-identical on typed and cold derivation paths, and both
> publication compilers reproduce the same migration rotation cone?

The frozen answer is
`Affirmative/F0V3B-A-FS-VIEW-BODIES-AND-CONE`.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-fs-view-determinacy-f0v3/run.py --check
```

## Proposed owner text

The package does not edit either owner page or profile manifest. Instead,
[the canonical-framed packet](proposed/fiat-shamir-section-13.md) and
[the duplex packet](proposed/duplex-section-11.md) contain:

- the exact semantic and body-grammar insertion markers;
- one candidate body for every field covered by the eleven F0-V3 obligations;
- all assumptions introduced where the current owner text is silent;
- the exact closed finite-description JSON used by the check; and
- a frozen unified diff against the current owner page.

The paired
[canonical manifest overlay](proposed/canonical-framed-manifest-overlay.json)
and [duplex manifest overlay](proposed/duplex-sponge-manifest-overlay.json)
give the exact generated-definition and dependency additions. They are applied
only in memory on top of the common F0-V2C migration candidate. The
`pir.static-view-schema` rows are generated definitions, not runtime subject
kinds, so the supported-subject lists do not change.

The original field census remains important: of 97 displayed fields, 37 have
an exact current owner-body basis, 40 are prose placeholders, and 20 use
undefined symbols. Each original obligation therefore remains
`CannotAnswer` until an owner selects or rejects the proposal. The F0-V3B
affirmative is about the exact candidate and its measured consequences, not
about current-page determinacy.

## Schema and inhabitance checks

`proposal.py` parses and authenticates both packets, reconstructs
`schema-source.json` from their family-local bodies, and checks each frozen
page diff. The recursive compiler in `model.py` and the separately organized
iterative compiler in `independent.py` compile all four canonical-framed and
all four duplex schemas to byte-identical expanded descriptions.

The typed and cold paths separately derive and validate every value the pinned
witnesses can inhabit:

- four canonical-framed values for each of the K2 Schnorr and Oracle checked
  constructions; and
- three construction-owned values for the duplex witness.

The duplex witness has no checked-result issuer, so the fourth duplex schema is
compiled and mutation-tested but no result value is invented. For all eleven
inhabitable values, the check compares the exact diagnostic body bytes and
freezes byte lengths and SHA-256 digests.

Both validators reject a duplicated schema ordinal, substituted owner, exact
law, or canonical-body compiler. They also reject a canonical view kind under
the duplex family discriminator and reject a canonical checked-result value
with an extra `result_ref` whose payload is bytes.

## Rotation cone

`migration.py` overlays the two page fragments and manifest additions on the
common migration candidate, then invokes both publication compilers. It never
writes `published-identities.json`.

Relative to the published baseline, the combined migration rotates exactly 16
profiles:

```text
interaction
canonical-framed-fiat-shamir
duplex-sponge-fiat-shamir
public-setup
commitment-opening
oracle-commitment
verifier-derived-query-plan
interface-plan
endpoint-source-view
oir-projection-relation
relations
analysis-cryptographic-property
analysis-afk-transport
analysis-afk-theorem-source-validation
analysis-incremental-composition
analysis-incremental-composition-source-validation
```

Relative to the common candidate, the FS overlay contributes exactly this
11-profile cone:

```text
canonical-framed-fiat-shamir
duplex-sponge-fiat-shamir
interface-plan
endpoint-source-view
oir-projection-relation
relations
analysis-cryptographic-property
analysis-afk-transport
analysis-afk-theorem-source-validation
analysis-incremental-composition
analysis-incremental-composition-source-validation
```

The candidate family identities are:

| Profile | Revision | Profile digest | Body SHA-256 |
|---|---:|---|---|
| `canonical-framed-fiat-shamir` | 1 | `299c33c95c5a9cffdd3cac9dc4636575e6cdbd92f0903523241d28cbc9d2ecf8` | `f7b47f840afee87298ed4c26af9bb4e4b3d359aeb9b978fcf941739e2796c6c5` |
| `duplex-sponge-fiat-shamir` | 1 | `85856b74b316436629122871d3c70e430a7775b4b1361180688f84b90696690e` | `ef7a6466ccee5a0618069c7931816253319d1c416d790af536122b60c2ac7e6f` |

The frozen findings record the candidate revision, profile digest, and body
digest for every profile in the 16-profile cone, plus exact before/after
manifest and owner-page hashes.

## What a pass establishes

A pass establishes only that the two exact proposal packets still reconstruct
all eight schemas; both schema compilers agree; all eleven available typed and
cold witness values validate and byte-compare; the six mutation classes fail
closed on both paths; both publication compilers reproduce the frozen total
and incremental cones and candidate digests; and the published identity table
is unchanged.

It does not adopt or publish the proposed text, resolve the eleven current
owner obligations, create a durable owner evaluator, establish implementation
or backend correspondence, authenticate or apply a theorem, prove
Fiat--Shamir soundness, knowledge soundness, zero knowledge, ROM/QROM or
concrete-instantiation security, or establish production support.
