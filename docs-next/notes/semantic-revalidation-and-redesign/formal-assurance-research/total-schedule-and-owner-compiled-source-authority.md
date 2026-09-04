# Total-schedule projection and owner-compiled source authority

> **State:** total-schedule projection repaired; executable source-authority
> dispatch repaired for every represented owner family; checked-construction
> correspondence remains conditional on one missing owner identity constructor
> **Authority:** None. This verification lane does not edit or publish an owner
> page, profile manifest, publication table, or migration decision.
> **Executable evidence:**
> [family view-body check](../../../../evaluation/formal-source-fs-view-determinacy-f0v3/README.md),
> [finite runtime check](../../../../evaluation/formal-source-fs-runtime-f0v3c/README.md),
> [protocol reference instrument](../../../../evaluation/k2-protocol-fiat-shamir/README.md),
> [dependent-surface instrument](../../../../evaluation/k3-dependent-surfaces/README.md),
> and [Analysis closure instrument](../../../../evaluation/k3-analysis-closure/README.md)

## 1. Exact question and answer

At migration head `661c939b`, can the finite canonical-framed transition and
execution views project every challenge through its exact total Core schedule
position and optional frame coordinate, and can every executable
`pir.source-*` identity be re-formed through the selected owner profile's
compiler over its tagged family-local body, without retaining the generic
authority preimage or inventing an owner coordinate?

The schedule question is affirmative. In both finite Schnorr subjects,
challenge 0 occurs at total Core schedule position 1. It is an unconditional
challenge with no public conditions, so Section 4 derives no frame and the
execution view carries `frame_schedule_coordinate = None`. The transition
rule still carries position 1. The family determinacy package also forms the
formerly missing Oracle transition value from the same distinction.

The source-authority question is affirmative for every static, public-setup,
and Interface family that these executable models form. The common protocol
helper selects the Interaction, canonical-framed, or public-setup compiler;
the dependent Interface route selects the Interface/Plan compiler. All four
subject identities use the selected compiler's family arm. Direct
discriminators reconstruct canonical-framed and duplex static-view preimages
and reject the predecessor six-field record and an Interaction-family body.

The complete checked-construction correspondence remains `CannotAnswer`.
Both Fiat--Shamir owner pages require
`ContentRef(x.checker_contract)` in the checked-construction binding payload,
but neither page defines the content identity or canonical preimage of that
contract. The finite protocol model uses an explicit package-local coordinate
so that the required six-field shape and arm-1 dispatch can be exercised; it
does not present that coordinate as owner-derived.

| Finding | Outcome and stable code |
|---|---|
| total-schedule challenge projection | `Affirmative/F0V3-A-TOTAL-SCHEDULE-CHALLENGE-POSITION` |
| finite transition and execution projection | `Affirmative/F0V3C-A-TOTAL-SCHEDULE-PROJECTION` |
| represented owner-compiler dispatch | `Affirmative/F0V2C1-A-OWNER-COMPILER-DISPATCH` |
| checked-construction checker identity | `CannotAnswer/F0V2C1-C-CHECKER-CONTRACT-IDENTITY` |
| combined source-authority correspondence | `CannotAnswer/F0V2C1-C-SOURCE-AUTHORITY-MODEL-ALIGNMENT` |

## 2. Exact source basis and identity movement

The canonical-framed profile is now revision 4. The two independent profile
compilers reproduce:

| Coordinate | Current value |
|---|---|
| canonical-framed profile digest | `026c8bf37837d1de698d859626debd118c1141d4d0679f22e2f91af30b08d41e` |
| canonical-framed profile body SHA-256 | `a0216af58cd0cc80a7c89c4f6ec006fd9b5b7caca7750c5a808b4a8979d27878` |
| canonical-framed owner-page SHA-256 | `edb11d719330ddbb181d95168506ed902ae64ba0c7e3bc71f8cabd3bed1ea25a` |
| Interaction owner-page SHA-256 | `e2905145539988292e70c80ec881f8b9e447aecc2b3c161687d17d36e1d857af` |

The canonical-framed profile, its law declaration, challenge-transition
schema, and execution schema rotate under the adopted total-schedule rule.
Every finite construction, transformed Protocol, construction view, execution
view, run table, and certificate that depends on that profile was re-derived.
This is an evidence-tree re-pin. It neither writes the publication table nor
asserts that the profile has been published.

The source-authority identities below are identities of the finite executable
profile witnesses. They changed because the executable preimages changed from
generic records to owner-compiled tagged values. They are not the repository's
published owner identities.

| Represented source | Binding payload | No-policy | Requirement | Closure |
|---|---|---|---|---|
| Fresh execution | `aa746d0bef1e2f6bce058db93ccf5ffba4427f9691c874fa1c60a1d69f55cfdb` | `87daec7ecc4381aab5b542993b7953347ba60cc3605147fbd018b3c4938c4da1` | `379841cfb45e51e016187d7f1728d176191eb6a0a2881b6c35a33450e171c6d5` | `143a8e3fabcf79310b3d05e86ac250d12f23a094a21e05ea10b3d465cea39fcc` |
| canonical-framed execution | `02f0b2f29a104f252861cf55711abaf72293b109c866bd1ec0455543d799aa54` | `2d9d6e3b070b1df58a1a190b9856aa85d8d31d628ba79d00efeeab206a09b6d6` | `23699d59c52d66d6065f17cf46229105f2901e3f50759b3f19d4caf65bb46b37` | `fc5b84690f8c49cf79cdfdc1dde1ddd1ba4bc39a30464a79b2c8f4557c6547d9` |
| checked construction | `4ea0426d756b462e807e56b6e94a30f3b27608fa02ab779fd3dd8d4eab19720f` | `7e357fc2663c16a8486ba7ad4022a7b5c59344dfabc2b06e9d2f0605f2137379` | `cdd93f0c1257885cf1a020dd1f0eb0dc0de573462d945e21327b90e4a0ddbdf5` | `a904dad573861a7ab3fa5a07502bc8917c7e1b111b7b027ef84f368685a1acd0` |
| public setup | `096435cc499453bcd9e9a66e53f6a4431ca1a0d943e0fba0e1a2509968476297` | `66321a904da796970536753906963246cf1b09edc3f875020bf7c0ef91fb357e` | `3012d9bddcfdd2cdf07b0754c7651a523ff7d97849c33246fede6972cd48e023` | `ac2a83c45cbbbaa645e687ea46641428e6d873beeabc9ebd3ace5264190ac7d4` |

The table omits the common `zkcidv0:pir.source-*:` prefix. Re-running the
protocol and Analysis fixtures derives these values from source objects; no
serialized fixture alias preserves a predecessor identity.

## 3. Total-schedule projection

### 3.1 Owner rule

Fiat--Shamir Section 13 now separates two coordinates:

1. `ChallengeTransitionRule.position` is the challenge occurrence's position
   in the exact total Core schedule; every admitted challenge has exactly one.
2. `frame_schedule_coordinate` is `None` when Section 4 derives no frame and
   is `Some(the exact frame_schedule entry)` otherwise.

The model derives a total `ChallengeRef -> occurrence position` map by scanning
the Core schedule. It rejects a missing or duplicate challenge occurrence.
Construction transition rules index that total map. Execution coordinates use
the same total position for decoding and a separate lookup in the framed-only
schedule.

### 3.2 Finite results

Both finite Schnorr subjects project:

```text
challenge_ref = 0
occurrence_ref = 1
ChallengeTransitionRule.position = 1
frame_schedule_coordinate = None
```

The runtime freeze contains 108 complete records. The retrying subject has 22
accepted and 32 rejected records; the one-shot subject has 18 accepted and 36
rejected records. The `Aborted`, `InterpretationFailed`, `StrategyStopped`, and
`OperationalNoncompletion` counts are zero for both subjects. All 108 records
replay through the independent path, and all required construction and
execution views form. Zero observed sampling failures in these finite tables
is not a totality result.

The separate projection-pressure carrier retains challenge positions 1 and 3,
distinct decoder result types, draw bounds `(1,1)` and `(2,3)`, two root public
bindings, and one symbolic earlier-draw entry. This prevents the repaired
single-challenge case from erasing the heterogeneous-rule control.

The family package now byte-compares eleven typed and cold values: four finite
Schnorr values, four canonical-framed Oracle values, and three duplex values.
Its 91-field schema census, dual schema compilers, mutation controls, and
profile-rotation reconstruction all pass.

## 4. Owner compiler dispatch

### 4.1 Common equations

For owner profile `P`, subject kind `K`, family tag `F`, and family-local body
`y`, the repaired executable equation is:

```text
SubjectId(P,K,F,y) =
  ProfiledSemanticId<K>(B, P, SourceSubjectBody(P,K)(F(y)))
```

The common consumer and purpose role bodies are now direct records, as required
by Interactive Core lines 2809--2822:

```text
ConsumerRoleBody = R{0:family,1:ContentRef(consumer_coordinate)}
PurposeRoleBody  = R{0:family,1:ContentRef(purpose_coordinate)}
```

The predecessor model placed the content reference inside an extra variant.
That wrapper was removed. For each selected family, the four local values are:

```text
binding payload = the owner family-local payload body
requirement     = R{0:ContentRef(consumer_role_id),
                    1:ContentRef(purpose_role_id)}
no-policy       = R{0:ContentRef(owner_profile_id)}
closure         = R{0:ContentRef(binding_payload_id),
                    1:ContentRef(no_policy_id),
                    2:ContentRef(capability_requirement_id)}
```

Each value is then wrapped by the selected owner's family arm before identity
formation. No-policy has no confidential-family arm where the owner specifies
a bound disclosure policy instead.

### 4.2 Closed dispatch table

| Owner compiler | Family | Payload, requirement, closure arm | No-policy arm |
|---|---|---:|---:|
| Interaction | `StaticView` | 0 | 0 |
| Interaction | `ConfidentialInitialOracle` | 1 | absent |
| canonical-framed | `StaticView` | 0 | 0 |
| canonical-framed | `CheckedConstruction` | 1 | 1 |
| duplex | `StaticView` | 0 | 0 |
| duplex | `CheckedConstruction` | 1 | 1 |
| public setup | `PublicSetupInvocationView` | 0 | 0 |
| Interface/Plan | `InterfaceView` | 0 | 0 |
| Interface/Plan | `ConfidentialPlanWitness` | 1 | absent |

The executable routes in this repository currently form Interaction static
views, canonical-framed static and checked-construction subjects, public-setup
subjects, and Interface-view subjects. The duplex discriminator compiles the
current duplex profile from owner source and checks its compiler directly at
the byte level because this finite protocol model has no duplex issuer. No
executable `pir.source-*` constructor currently forms an
endpoint, confidential initial-Oracle, or confidential Plan-witness subject.
Those absences are reported rather than filled by a neighboring family's arm.

### 4.3 Family-local bodies

The represented static-view payload is:

```text
R{0:owner-specific view-coordinate body,
  1:S[owner-specific field-coordinate bodies in manifest order]}
```

Interaction and canonical-framed coordinates use their different owner arms.
The canonical checked-result coordinate contains the four durable IDs and
result-schema description, never the process-local result reference. Each
finite manifest entry carries an owner path and atomic boundary. The compact
protocol model represents one symbolic atomic leaf for each selected
top-level field; it does not claim to implement the owner's durable recursive
subtree resolver.

The checked-construction family-local payload has the required six fields:
source Protocol, target Protocol, shared Core, transcript construction, full
finite result-schema description, and checker-contract content reference. The
first five are owner-derived. Section 5 records the sixth-field limitation.

The public-setup local payload is exactly the two-field owner body containing
the view ID and Protocol ID. The Interface local payload contains the exact
Interface ID and a canonical sequence of represented path-and-boundary
coordinates. The finite Interface carrier maps each represented read kind to
its owner field ordinal and selected element ordinal; it is not a claim of a
general recursive Interface resolver.

### 4.4 Executable formation census

The repository-wide search covered the four `pir.source-*` kind strings,
`binding_payload`, both common helpers, and every helper caller. The locations
below distinguish formation from parsing or consumption.

| Location | Role before repair | Current equation |
|---|---|---|
| `evaluation/k2-protocol-fiat-shamir/reference_model.py:2257-2472` | Formed role IDs and four PIR identities through one generic envelope | Direct common role bodies; selected owner compiler over a tagged local payload, requirement, no-policy, and closure |
| same file, static issue and validation at lines 3258 and 3377 | Passed symbolic owner/source and field-name sequences into the generic envelope | Interaction or canonical `StaticView` arm 0 over owner coordinate plus ordered field-coordinate bodies |
| same file, checked issue and validation at lines 3978 and 4083 | Passed a checked-result record and symbolic full-field manifest into the generic envelope | canonical `CheckedConstruction` arm 1 over the six-field checked payload |
| same file, public-setup issue and validation at lines 4341 and 4444 | Passed a three-field source record and symbolic manifest into the generic envelope | public-setup arm 0 over `R{view_id,protocol_id}` |
| `evaluation/k3-dependent-surfaces/reference_model.py:1239-1409` | Used the same six-field shape for PIR and Relations namespaces | Dispatches PIR through the selected owner compiler; preserves the existing Relations namespace equations |
| same file, Interface helper and issue/validation at lines 1666--1683, 1827, and 1920 | Passed an Interface ID plus an abstract read manifest to the generic PIR branch | Interface/Plan `InterfaceView` arm 0 over Interface ID plus path-and-boundary manifest |
| `evaluation/k3-analysis-closure/reference_model.py:16521-16529` | Consumed bindings produced by the protocol model | Still consumes them, but now receives dynamically re-derived owner-compiled identities |
| owner-view repair and audit models | Parsed owner compiler declarations and compared profile topology; formed no runtime source identity | Unchanged compiler/source audit; revision and source pins re-pinned to current owner bytes |
| migration review model | Audits source equations and executable source text; forms no production binding | Left untouched because its concurrent refreeze is excluded |
| protocol tests | Had no owner-equation discriminator | Reconstruct canonical and duplex payload equations; reject the old record and wrong-family bodies |

Before repair, both executable helpers used these equations for PIR subjects:

```text
payload = R{owner_domain,family,source_body,manifest_body,
            consumer_role_ref,purpose_role_ref}
no-policy = R{family,payload_ref,
              "owner-defines-no-additional-operation-policy"}
requirement = R{family,payload_ref,consumer_role_ref,purpose_role_ref,
                "fresh-identical-bearer-capability"}
closure = R{family,payload_ref,no_policy_ref,requirement_ref}
```

The dependent helper continues to use those namespace-specific equations for
`relations.source-*` subjects. They were not silently reinterpreted as PIR
subjects. No other executable PIR body or identity constructor was found.

### 4.5 Discriminators and downstream regeneration

The canonical execution discriminator independently forms the
canonical-framed coordinate, ordered field-coordinate sequence, arm-0 body,
and all four resulting identities. It requires equality with the issued
binding and inequality with both the predecessor six-field body and an
Interaction coordinate wrapped under the canonical profile.

The duplex discriminator compiles the live duplex profile without consulting
the publication table, then independently forms a duplex execution coordinate,
field coordinate, static local body, and arm-0 payload identity. It rejects
the predecessor six-field body and an Interaction coordinate. It also checks
both static and checked-construction arms for all four duplex compilers and
checks that Interaction has no confidential no-policy arm.

The Analysis and dependent packages store no serialized authority-ID fixture;
their constructors re-derive the IDs on each run. Their complete test suites
were rerun, so every consumer now observes the new identities. The owner-view
repair and audit packages pin owner profile bytes and compiler declarations,
not the finite helper's derived IDs; their current revision/source pins and
documentation were rechecked. The repository-wide search found no additional
certificate or expected-finding file containing an identity derived from the
predecessor generic preimage.

## 5. Checked-construction identity boundary

Fiat--Shamir lines 1135--1151 require the exact binding to record a checker
contract. Its source body at lines 1639--1646 places
`ContentRef(x.checker_contract)` in field 5. The duplex page makes the same
requirement at lines 820--830 and 1249--1255. Neither page, either profile
manifest, nor another PIR owner page defines:

- the subject kind of that content ID;
- the canonical body compiled into it;
- the profile under which it is formed; or
- the exact dependency on the checker operation or evaluation contract.

The finite model names its local coordinate
`pir.fs-construction-checker-contract` over a symbolic bounded-check body. This
keeps the arm-1 payload deterministic and falsifiable, but the name and body
are model choices. Missing owner evidence is therefore not promoted to an
affirmative correspondence finding.

## Proposed delta

**Owner pages and sections.** `docs-next/pir/fiat-shamir.md`, Section 10.1 and
Section 13, especially lines 1135--1151 and 1639--1646; and
`docs-next/pir/duplex-sponge-fiat-shamir.md`, Sections 10 and 11, especially
lines 820--830 and 1249--1255.

**Exact change.** For each checked construction family, define a
profile-owned checker-contract content ID and its complete canonical body.
The body must identify the exact checked operation, its result schema, its
qualified outcome schema, the owner law that defines every affirmative and
negative comparison, and any evaluation contract on which rechecking depends.
Bind `x.checker_contract` in the checked-construction payload equation to that
constructor. Add the subject kind and body compiler to the owning profile
manifest. State whether the canonical and duplex operations use distinct
subject kinds or one common kind under distinct owner profiles.

**Identity effect.** Defining the constructor changes each affected owner
profile and its import dependents. Within a checked-construction binding, the
binding-payload ID and policy-closure ID rotate because they contain the
checker-contract reference. The no-policy and capability-requirement IDs need
not rotate merely from that local field because their owner equations contain
the owner profile and role IDs rather than the payload; they do rotate if the
owner profile identity itself changes. Dependent finite Analysis fixtures must
then replace the package-local coordinate with the owner-derived ID.

**Evidence and gate.** The missing constructor is detected as
`CannotAnswer/F0V2C1-C-CHECKER-CONTRACT-IDENTITY`. The protocol, dependent,
and Analysis checks exercise the resulting checked authority path; the source
review can close it only after the owner constructor is exact.

**Reversal condition.** Withdraw this proposal if an existing authoritative
PIR source already defines the complete content-ID equation for
`x.checker_contract`, including its subject kind, body, profile, and exact
dependencies, and both checked-construction pages bind field 5 to that
equation. A local symbol, callback object, prose label, or inferred law
reference is insufficient.

**Non-claims.** This proposal does not select the checker contract, publish a
profile, prove that either checker is correct, establish capability freshness,
or prove any Fiat--Shamir or duplex security property.

## 6. Baseline checkpoint classification

The required pre-edit checkpoint ran 63 checks in 1099.050505 seconds: 50
passed and 13 failed. Each red check is classified by the first material repair
needed at that baseline.

| Check | Classification | Evidence |
|---|---|---|
| `research.profile-publication` | excluded | publication hold; untouched |
| `research.expressibility-axes` | pin | current Interaction, canonical-framed, and Interface source bytes |
| `research.family-instance-probe` | pin | protocol-model source digest |
| `research.owner-view-publication-topology` | pin | canonical-framed revision and profile identity |
| `research.semantic-migration-candidate` | pin | current owner pages and canonical manifest |
| `research.migration-text-review` | excluded | concurrent source-review refreeze; untouched |
| `research.holdout-readjudication` | excluded | concurrent holdout refreeze; untouched |
| `research.owner-view-fs-family-determinacy` | semantic consequence | total-schedule position makes the missing value formable and rotates frozen values |
| `research.fs-runtime` | semantic consequence | transition/execution values, construction identities, run partitions, tables, and certificates change |
| `research.schnorr-relations-plan-coupling` | pin | current Interface bytes; re-pin exposed copied source-range drift, which was retranscribed |
| `research.schnorr-relations-plan-candidates` | pin | current Interface bytes; re-pin exposed copied source-range drift, which was retranscribed |
| `research.provider-interpretation` | excluded | current provider round is owned on another branch; untouched |
| `research.kernel-mechanization-feasibility` | pin | current Interactive Core and holdout source bytes; re-pin exposed a generated Terminal provenance vector, which was regenerated |

The two transition packages are the only baseline reds whose owner change
alters computed semantics. The relation and kernel packages initially failed
their byte pins; after those were corrected, their copied line/provenance data
also had to follow the same current source. Those follow-up edits are reported
instead of being hidden inside a digest replacement.

## 7. Result boundary

A passing in-scope matrix establishes the exact finite total-position and
optional-frame projection, agreement of the typed and cold family projectors,
exhaustive replay of the two 54-record runtime corpora, selected owner-compiler
dispatch for all represented PIR authority routes, rejection of the two named
predecessor/wrong-family payloads, and dynamic downstream use of the resulting
finite identities.

It does not establish a durable recursive field resolver, arbitrary-view or
arbitrary-family coverage, an owner-derived checker-contract identity,
publication, implementation or provider correspondence, compiler correctness,
theorem truth or applicability, protocol soundness, zero knowledge,
Fiat--Shamir security, duplex security, random-oracle or quantum-random-oracle
security, concrete-hash suitability, sampling totality, or production
readiness.

## Handoff

### Files changed

- Repaired and regenerated the finite total-schedule projections in
  `evaluation/formal-source-fs-view-determinacy-f0v3/` and
  `evaluation/formal-source-fs-runtime-f0v3c/`.
- Replaced the generic PIR authority helper, added owner-coordinate and
  family-local body compilers, and added canonical and duplex discriminators in
  `evaluation/k2-protocol-fiat-shamir/`.
- Routed the Interface view through its owner compiler in
  `evaluation/k3-dependent-surfaces/`; documented the dynamically re-derived
  identities in that package and `evaluation/k3-analysis-closure/`.
- Re-pinned current owner bytes, profile revisions, source ranges, and derived
  provenance in `evaluation/expressibility-axes/`,
  `evaluation/family-instance-probe/`,
  `evaluation/formal-source-owner-view-repair-f0v/`,
  `evaluation/formal-source-owner-views-f1r1c/`,
  `evaluation/semantic-migration-candidate/`,
  `evaluation/formal-schnorr-relations-plan-f2p0/`,
  `evaluation/formal-schnorr-relations-plan-f2p1/`, and
  `evaluation/formal-kernel-mechanization-m0/`.
- Updated the existing package rows in `evaluation/README.md` and added this
  note. No package, check, or lifecycle entry was added.

The exact 43-file inventory is:

```text
docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/total-schedule-and-owner-compiled-source-authority.md
evaluation/README.md
evaluation/expressibility-axes/README.md
evaluation/expressibility-axes/run.py
evaluation/family-instance-probe/README.md
evaluation/family-instance-probe/expected-findings.json
evaluation/formal-kernel-mechanization-m0/README.md
evaluation/formal-kernel-mechanization-m0/source-pins.json
evaluation/formal-kernel-mechanization-m0/vectors/terminal-contract.json
evaluation/formal-schnorr-relations-plan-f2p0/README.md
evaluation/formal-schnorr-relations-plan-f2p0/contract-ledger.json
evaluation/formal-schnorr-relations-plan-f2p1/README.md
evaluation/formal-schnorr-relations-plan-f2p1/source-pins.json
evaluation/formal-source-fs-runtime-f0v3c/README.md
evaluation/formal-source-fs-runtime-f0v3c/derivation-vectors-one-shot.json
evaluation/formal-source-fs-runtime-f0v3c/derivation-vectors.json
evaluation/formal-source-fs-runtime-f0v3c/expected-findings.json
evaluation/formal-source-fs-runtime-f0v3c/expected-runs-one-shot.json
evaluation/formal-source-fs-runtime-f0v3c/expected-runs.json
evaluation/formal-source-fs-runtime-f0v3c/model.py
evaluation/formal-source-fs-runtime-f0v3c/run.py
evaluation/formal-source-fs-runtime-f0v3c/views.py
evaluation/formal-source-fs-view-determinacy-f0v3/README.md
evaluation/formal-source-fs-view-determinacy-f0v3/cold_projection.py
evaluation/formal-source-fs-view-determinacy-f0v3/expected-findings.json
evaluation/formal-source-fs-view-determinacy-f0v3/independent.py
evaluation/formal-source-fs-view-determinacy-f0v3/model.py
evaluation/formal-source-fs-view-determinacy-f0v3/run.py
evaluation/formal-source-fs-view-determinacy-f0v3/schema-source.json
evaluation/formal-source-fs-view-determinacy-f0v3/support.py
evaluation/formal-source-fs-view-determinacy-f0v3/typed_projection.py
evaluation/formal-source-owner-view-repair-f0v/README.md
evaluation/formal-source-owner-view-repair-f0v/independent.py
evaluation/formal-source-owner-view-repair-f0v/model.py
evaluation/formal-source-owner-views-f1r1c/README.md
evaluation/k2-protocol-fiat-shamir/README.md
evaluation/k2-protocol-fiat-shamir/reference_model.py
evaluation/k2-protocol-fiat-shamir/tests/test_reference_model.py
evaluation/k3-analysis-closure/README.md
evaluation/k3-dependent-surfaces/README.md
evaluation/k3-dependent-surfaces/reference_model.py
evaluation/semantic-migration-candidate/README.md
evaluation/semantic-migration-candidate/candidate-contract.json
```

No owner page, owner manifest, publication table, check manifest, lifecycle
catalog, lifecycle count pin, docs-next directory README, private ledger,
primary checkout, real Git index, or Git object under `.git/` was changed. The
working tree is intentionally uncommitted for Main. Clone-local alternate
index, object, dependency-cache, bytecode, Lean-build, and check-result
artifacts were removed before handoff.

### Commands and outcomes

All check-runner commands used `UV_NO_SYNC=1`, `UV_OFFLINE=1`, and a
clone-local dependency cache where dependency resolution was possible. The
lifecycle-sensitive final matrix used a clone-local alternate index and object
directory, with the checkout object store as a read-only alternate.
The real `.git/index` SHA-256 was
`5e8d18f49880feeb9a956a6fc37796d5d40a2e3394240df06bb8f95ea23f5431`
before and after validation.

| Command | Exit | Wall time | Outcome |
|---|---:|---:|---|
| pre-edit `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1099.05 s | 50 pass, 13 fail; classification source above |
| runtime fixture regeneration | 0 | 332.9 s | re-derived both run tables, both derivation-vector tables, and frozen findings |
| complete Analysis reference run | 0 | 1587.33 s | 206 of 206 tests passed and consumed re-derived source bindings |
| repaired protocol reference run after final discriminator | 0 | 4.90 s | 85 of 85 tests passed |
| first intermediate `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1215.22 s | 58 pass, four excluded failures, and one stale determinacy source pin |
| second intermediate `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1215.50 s | 58 pass, four excluded failures, and one stale family-probe source pin; all semantic observations matched |
| `python3 -B checks/run.py validate` with alternate index | 0 | 0.05 s | 77 checks, six tiers, and the current manifest validated |
| `python3 -B checks/run.py run --tier developer` with alternate index | 0 | 1.78 s | 9 of 9 checks passed |
| `python3 -B checks/run.py run --check research.owner-view-fs-family-determinacy` | 0 | 0.72 s | focused family projection passed |
| `python3 -B checks/run.py run --check research.interactive-fiat-shamir` | 0 | 5.19 s | focused protocol and live-profile duplex source-authority gate passed |
| `python3 -B checks/run.py run --check research.dependent-surfaces` | 0 | 3.28 s | focused Interface and dependent-surface gate passed |
| `python3 -B checks/run.py run --check research.fs-runtime` | 0 | 356.80 s | both 54-record runtime corpora passed |
| `python3 -B checks/run.py run --check research.family-instance-probe` | 0 | 0.33 s | final imported protocol-model source pin passed |
| third intermediate `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1209.61 s | 59 pass and exactly four excluded failures before the final live-profile test strengthening |
| final `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1214.97 s | 59 pass and exactly the four excluded failures below on the final source and test tree |

The strengthened duplex discriminator compiles the current owner profile from
source without reading the stale publication table. Its final direct protocol
run exited 0 after 4.98 seconds with 85 of 85 tests passing.

One relative-path kernel diagnostic exited 1 after 88.16 seconds because its
Lean artifact path resolved from the package directory; the canonical runner
with repository-root artifact paths passed in 79.51 seconds. The first kernel
run after its source re-pin exited 1 after 75.41 seconds and correctly detected
the stale generated Terminal vector; regenerating that vector closed the gate.

An attempted determinacy refresh used the unsupported `--write` option and
exited 2; the immediately following stale check exited 1. Their combined wall
time was 0.62 seconds. The package's actual `--refresh` operation followed by
`--check` exited 0 in 1.31 seconds.

### Aggregate outcome

The total-schedule packages are affirmative, every represented executable PIR
authority route now selects its owner compiler, and all 59 in-scope checkpoint
checks pass in the final matrix. The combined source-authority
answer remains
`CannotAnswer/F0V2C1-C-SOURCE-AUTHORITY-MODEL-ALIGNMENT` because the checked
construction payload's required checker-contract identity is not defined by
the owner sources. The finite package-local coordinate keeps the executable
testable without claiming that missing correspondence.

The final checkpoint process exits 1 solely for the four excluded checks:

| Excluded check | Exit and wall time | Exact final outcome |
|---|---:|---|
| `research.profile-publication` | 1; 3.190 s | 34 tests ran with eight failures: six frozen upstream profile-byte identities differ, the public-setup mutation needle is absent from current owner text, and the published identity table differs from live compilation |
| `research.migration-text-review` | 1; 0.453 s | `migration text review failed: a migrated profile revision differs` |
| `research.holdout-readjudication` | 1; 0.043 s | stdout retains aggregate `F0V2C2-A-HOLDOUTS-READJUDICATED`; stderr is `frozen finding projection mismatch` after current owner/migration byte drift |
| `research.provider-interpretation` | 1; 1.609 s | `provider interpretation gate failed: untrusted generation drifted`; the terminal generator error is `generated certificate drifted` |

### Non-claims

This lane does not publish any repaired identity, close the publication hold,
refreeze either concurrent migration package, update the separately owned
provider interpretation, define the missing checker contract, establish a
general evaluator or source-authority implementation, prove a theorem or
security property, or authorize the proposed owner-page delta. Passing finite
checks, generated vectors, and identity comparisons remain bounded evidence.

### Surprises and where the brief was wrong

- The source pages adopted the family dispatch equation, but they still do not
  define the checked-construction `checker_contract` content ID required by
  their own payloads. The brief's requested all-family affirmative alignment is
  therefore underdetermined at that exact field.
- The predecessor helper's role bodies also contained an extra variant around
  the consumer and purpose content references. Repairing only the six-field
  payload would have left requirement and closure identities inconsistent with
  the common owner role equation.
- No executable source-authority constructor for duplex, endpoint, or either
  confidential family exists in the searched evaluation tree. Duplex has a
  direct byte discriminator; the absent routes were not manufactured.
- The relation-plan source re-pins exposed copied Interface line-range drift,
  and the kernel source re-pin exposed a stale generated Terminal provenance
  vector. Both were repaired as authored/provenance consequences rather than
  described as pin-only changes.
- `AGENTS.md` is absent from this clone. Its read-only primary-checkout copy
  supplied the required repository instruction; every repository write
  remained inside this dedicated clone.
- The general package discipline mentions manifest and lifecycle additions,
  while the task-specific instruction forbids those edits. These are repairs
  to existing registered packages, so no inventory count changes.
- The first alternate-index location was visible to `git add -A` and selected
  itself. It was discarded before any check and rebuilt under ignored
  `.cache/`; the real index remained byte-identical throughout.
- One diagnostic comparison mistakenly wrote its transient JSON to
  `/tmp/zkc-family-current.json`, outside the clone. It was removed immediately;
  no source, cache, or durable artifact remains there.

Main should commit this complete working tree with subject:

```text
test: project the total-schedule position and form source-authority subjects through the owner compilers
```
