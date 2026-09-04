# Checked-construction checker contracts through the owner equation

> **State:** the canonical-framed and duplex-sponge checker-contract identities
> are owner-derived in the executable reference model; the affected family cone
> is re-pinned without changing an owner page, owner manifest, or publication
> table.

## 1. Exact question and answer

The exact question is: do the current canonical-framed and duplex-sponge owner
sources determine the declaration references, result descriptions, body
compiler, and owning profile needed to form each checked-construction checker
contract, and can the executable checked payloads use those identities while
rejecting the predecessor package-local coordinate?

Yes, at the finite reference-model boundary. The resulting findings are:

| Finding | Outcome |
|---|---|
| checked-construction checker identity | `Affirmative/F0V2C1-A-CHECKER-CONTRACT-IDENTITY-DERIVED` |
| source-authority model alignment | `Affirmative/F0V2C1-A-SOURCE-AUTHORITY-MODEL-ALIGNED` |

The predecessor `CannotAnswer` findings were correct for the source that
preceded commit `0df294a3`. They are superseded by the owner definitions at
that commit; the historical note that recorded them remains unchanged.

## 2. Exact source basis

The derivation uses only current owner-selected material:

| Input | Owner coordinate |
|---|---|
| canonical result and checker contract | `docs-next/pir/fiat-shamir.md` lines 1090-1102 and 1153-1181 |
| canonical body equations | `docs-next/pir/fiat-shamir.md` lines 1669-1682 |
| duplex result and checker contract | `docs-next/pir/duplex-sponge-fiat-shamir.md` lines 764-783 and 832-860 |
| duplex component descriptions | `docs-next/pir/duplex-sponge-fiat-shamir.md` lines 1002-1011 and 1137-1142 |
| duplex body equations | `docs-next/pir/duplex-sponge-fiat-shamir.md` lines 1279-1292 |
| canonical declarations and subject route | `docs-next/pir/profiles/canonical-framed-fiat-shamir.json` lines 85-91 and 240-270 |
| duplex declarations and subject route | `docs-next/pir/profiles/duplex-sponge-fiat-shamir.json` lines 239-293 |

The publication compiler builds a separate name sequence for each declaration
kind in manifest order and assigns the local ordinal by enumeration. That rule
is executable at
`evaluation/semantic-profile-publication/reference_model.py` lines 668-680.
The family-determinacy gate independently confirms that the warm and cold
publication compilers produce the same current profile trees.

## 3. Owner equation and derived values

For either family, the executable contract body is the exact four-field owner
record:

```text
R {
  0: ProfileDeclarationRefBody(check operation),
  1: ProfileDeclarationRefBody(checked same-Core law),
  2: ProfileDeclarationRefBody(defect schema),
  3: PIRDescriptionBody(checked-result schema)
}
```

The first three fields are resolved by name in the owning profile's actual
catalog, not copied as free-standing labels. The fourth field is the complete
family-local result description. Canonical reference maps use `PIRReference`
for both endpoints. The duplex description additionally includes its instance
projection, material coordinate and schema, and prover and verifier schedule
correspondences. The contract is then identified as
`ProfiledSemanticId<"pir.checker-contract">` under the same profile.

The compiled values are:

| Family | Profile | Operation, law, defect ordinals | Contract body | Contract identity |
|---|---|---|---|---|
| canonical-framed | revision 5, digest `180a1a793a899f6a16aa17e3e02dcbcef0bf0baa54f88ec2d9f5610a02cd4809` | `(1, 3, 1)` | 1,871 bytes; SHA-256 `f8f79c99a8e74702367b7bfa6fc0a7ccc16427282aae23f24666c0c2ceff97fb` | `zkcidv0:pir.checker-contract:ebe686d6fb48030f03b79f1cfe72994705c40ea2414afc59a44ff149b8dfd701` |
| duplex-sponge | revision 4, digest `0116b0df403b01b34fd0858745da83a4efb5d38d4b54c8946ecbf5bc4095d1a6` | `(1, 6, 1)` | 5,243 bytes; SHA-256 `75eb2fe3aa516c17e0ae365df9bd8d4c7c218c7a8852ae39e1dc927ee5b64765` | `zkcidv0:pir.checker-contract:393ff59dfef32f77fee523fc0708dbe591c964369fb2b9461947ff93d9c83210` |

Both manifests place `checker-contract-body-v0` at body-compiler ordinal 5 and
route `pir.checker-contract` through it. The checked-construction binding body
retains the owner-selected six fields; field 4 is the same complete result
description and field 5 is `ContentRef` of the contract identified under that
binding's selected profile.

## 4. Executable discriminators and consumer cone

The protocol reference suite reconstructs each expected contract from explicit
declaration references and an independently written result description. For
canonical-framed execution it compares the emitted owner-compiled payload and
the live issued binding byte for byte with that expected equation. For duplex
it compiles the checked-construction arm with the live owner profile and makes
the same byte comparison. Both controls substitute the former
`pir.fs-construction-checker-contract` identity over the symbolic bounded-check
record and require inequality.

The reference profile now carries the named declaration catalogs and the
`pir.checker-contract` subject kind. A profile without that kind refuses before
issuing checked authority. Its finite witness profile is
`zkcidv0:foundation.semantic-language-profile:4f3fe82bebe7fd1dc54edbfb220ba73067f8c0d68eb5ff7f61c5b6056af40852`,
so the same canonical body yields the finite executable checker contract
`zkcidv0:pir.checker-contract:448babeabf337b1daf7a0a276547cab5475221375a89a37f189ce58f5d5e9c3b`.
The live-source identities in Section 3 are independent controls; the witness
profile does not impersonate either published target profile.

The dependent-surface model imports the changed profile but forms no checked
binding of its own. The Analysis model consumes the protocol model's
owner-derived binding; its selected statement digest therefore changes from
`13d270f6f386241d7c1d62e1a007432fd8522b1ad00b26f9ede5a91312505a1c`
to
`0aa14752b5f6bae7fdde366a9eab073f69eacbb2bd3b572f9a5b113adf5521df`.

The runtime corpus is regenerated because the canonical profile identity is a
transcript-domain input. Independent replay still matches all 108 records and
kills all six directed record mutations. The retrying corpus remains 22
accepted and 32 rejected; the one-shot corpus is now 20 accepted and 34
rejected. This is a measured consequence of the owner-profile identity re-pin,
not a hidden replay mismatch.

The owner-view repair gate re-pins the two profile revisions. The Interaction-
only owner-view audit remains unchanged: it checks compiler topology but does
not form either family checker contract. The family view audit re-pins the two
profile identities, the source lines shifted by the inserted owner text, and
all profile-bound fixture values; it still does not claim a checked duplex
result because its duplex witness supplies none.

The owner-view topology package's `baseline-identities.json` intentionally
retains the predecessor identities: it is the before-side of the exact rotation
assertion, not a current-profile pin.

## 5. Checkpoint classification

The required pre-edit checkpoint ran 63 checks in 1,217.120724 seconds: 54
passed and 9 failed. Each baseline red is classified by its first required
repair:

| Check | Classification | Evidence |
|---|---|---|
| `research.profile-publication` | excluded | publication hold; untouched |
| `research.expressibility-axes` | pin | current canonical owner-page bytes |
| `research.family-instance-probe` | pin | canonical owner-page and protocol-model source digests |
| `research.owner-view-publication-topology` | pin | current family revisions |
| `research.semantic-migration-candidate` | pin | current family pages and manifests |
| `research.migration-text-review` | excluded | concurrent source-review refreeze; untouched |
| `research.holdout-readjudication` | excluded | concurrent holdout refreeze; untouched |
| `research.owner-view-fs-family-determinacy` | pin | eight unchanged body starts shifted by 30 lines, plus family page, manifest, and profile-identity pins |
| `research.fs-runtime` | pin | the current canonical profile identity and every certificate derived from it |

After the direct pins moved, two authored consequences were kept visible. The
family audit's copied expected revisions were retranscribed from 4 and 3 to 5
and 4. The Analysis source statement changed because it includes the re-derived
checked binding, so its independently checked statement digest was rotated as
a semantic consequence. Runtime identities, challenge values, lane counts,
view bodies, and certificates were regenerated and independently replayed;
none was treated as a digest-only repair.

## 6. Owner completeness and result boundary

No owner delta is proposed. The profile catalogs determine every required
kind, name, and ordinal; the owner pages determine both complete result
descriptions and body equations; and the manifests determine the subject kind,
body compiler, law, evaluator, failure schema, revision, and owning profile.
No missing evidence was converted into an affirmative.

A passing in-scope matrix establishes these two exact checker-contract
preimages and identities, canonical and duplex checked-payload byte equality,
rejection of the former local coordinate, dynamic use of the canonical identity
by the finite checker, and successful replay of the affected finite cone.

It does not publish either profile identity, alter the owner contract, implement
a duplex checker or checked duplex result, prove either checker correct, cover
arbitrary profiles or result schemas, establish implementation or provider
correspondence, prove theorem applicability or truth, prove protocol soundness
or zero knowledge, establish random-oracle or quantum-random-oracle security,
validate a concrete hash for production, prove sampling totality, or establish
production readiness.

## Handoff

### Files changed

The complete working tree contains 28 changed paths:

- `evaluation/k2-protocol-fiat-shamir/README.md`, `reference_model.py`, and
  `tests/test_reference_model.py` form both owner equations, require the new
  subject kind, use the canonical equation in execution, and add independent
  byte-equality and predecessor-coordinate discriminators;
- `evaluation/k3-analysis-closure/README.md`, `reference_model.py`, and
  `tests/test_reference_model.py`, plus
  `evaluation/k3-dependent-surfaces/README.md`, record the resulting consumer
  boundary and rotate the independently checked Analysis statement digest;
- `evaluation/formal-source-fs-runtime-f0v3c/README.md`,
  `derivation-vectors.json`, `derivation-vectors-one-shot.json`,
  `expected-findings.json`, `expected-runs.json`, and
  `expected-runs-one-shot.json` are the regenerated and replayed runtime cone;
- `evaluation/formal-source-fs-view-determinacy-f0v3/README.md`,
  `expected-findings.json`, `field-audit.json`, `independent.py`, `model.py`,
  `schema-source.json`, and `support.py` re-pin the current family sources,
  profiles, copied revisions, and derived fixtures;
- `evaluation/formal-source-owner-view-repair-f0v/README.md`, `independent.py`,
  and `model.py` re-pin the two family revisions;
- `evaluation/expressibility-axes/run.py`,
  `evaluation/family-instance-probe/expected-findings.json`, and
  `evaluation/semantic-migration-candidate/candidate-contract.json` re-pin
  current source bytes;
- `evaluation/README.md` records the revised package outcomes; and
- this note records the frozen derivation, classifications, and handoff.

No package, check, manifest, lifecycle entry, owner page, owner manifest,
publication table, docs-next directory README, or private ledger was added or
changed. The three excluded evaluation packages were not edited.

### Commands and outcomes

Durations are wall times unless explicitly identified as runner time.

| Command | Exit | Duration and outcome |
|---|---:|---|
| pre-edit `checks/run.py run --tier research-checkpoint --keep-going` | 1 | result duration 1,217.120724 s; 54 pass, 9 fail |
| protocol reference package `run.py --check` | 0 | 6.40 s; 86/86 tests pass |
| family-view `run.py --refresh` then `run.py --check` | 0, 0 | 0.85 s and 0.82 s; frozen projection agrees |
| dependent-surfaces `run.py --check` | 0 | 3.584 s; 50/50 tests pass |
| Analysis closure `run.py --check` | 0 | runner time 1,691.088 s; 206/206 tests pass |
| runtime `run.py --write` | 0 | direct wall timer was not retained; the two corpora and all five frozen artifacts were regenerated before the timed replays |
| alternate-index `checks/run.py validate` | 0 | 0.04 s; 77 checks and 6 tiers valid |
| alternate-index `checks/run.py run --tier developer` | 0 | 1.96 s; 9/9 checks pass |
| alternate-index `checks/run.py run --check research.fs-runtime` | 0 | 351.83 s wall, 351.770 s check time; pass |
| alternate-index `checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1,331.62 s wall, 1,331.565831 s result duration; 60 pass, exactly 3 excluded failures |

All alternate-index commands used `GIT_INDEX_FILE=.cache/lane-index`, a
clone-local object store with the real object store as an alternate, and
`UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=.cache/uv`. The real `.git/index`
SHA-256 was
`50960d3985a4c2faa783bd1d09bba051e21cf7824e2deb2ca002a7b63185ec6c`
before the matrix and remained byte-identical afterward. The alternate index
and its object store were removed after validation.

### Aggregate outcome

Every one of the 60 in-scope checkpoint checks passes. The final checkpoint's
three failures are exactly the exclusions in the brief:

| Excluded check | Exact final outcome |
|---|---|
| `research.profile-publication` | exit 1 in 3.264538 s; 34 tests ran and 8 failed: six frozen-profile byte pins (`interaction`, `canonical-framed-fiat-shamir`, `duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`, and `oracle-commitment`), the public-setup descendant-rotation fixture, and the published identity table |
| `research.migration-text-review` | exit 1 in 0.449365 s; stderr: `migration text review failed: a migrated profile revision differs` |
| `research.holdout-readjudication` | exit 1 in 0.042138 s; the actual aggregate remains `F0V2C2-A-HOLDOUTS-READJUDICATED`, but the frozen projection mismatches because current source yields `CannotAnswer/F0V2C2-C-MIGRATED-OWNER-DRIFT` and `CannotAnswer/F0V2C2-C-MIGRATION-AXIS-DRIFT`, alongside the retained `CannotAnswer/F0V2C2-C-EXACT-TERMINAL-CARRIERS` |

The owner equation is complete for both families, so there is no
`CannotAnswer` and no Proposed delta in this lane. Main may commit this working
tree with subject `test: form the checker contract through the owner equation
and re-pin the family cone`.

### Non-claims

The result boundary in Section 6 is controlling.

### Surprises and where the brief was wrong

The brief anticipated a kernel-mechanization source-pin red, but that check
passed at baseline and again in the final matrix, where it took 80.980 seconds;
no kernel file was changed. The clone had no root `AGENTS.md`, so the required
file was read from the read-only primary checkout. During diagnosis, one shell
redirect mistakenly created `/tmp/zkc-checker-owner-view.out` outside the
clone; it was removed immediately, no source or private artifact was written,
and no outside-clone artifact remains. Two intermediate Analysis runs were
nonfinal: the first exposed the stale statement digest and the second was
stopped after locating its mirrored test pin; the completed run passed 206/206.
No other premise in the brief proved wrong.
