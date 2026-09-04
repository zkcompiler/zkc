# Repaired source re-pin and canonical-framed view projection

> **State:** source consumers repaired; finite runtime aggregate remains
> `CannotAnswer/F0V3C-C-FS-RUNTIME` at one owner-text gap
> **Authority:** None. This lane does not edit or publish an owner page,
> manifest, profile identity, or migration decision.
> **Executable evidence:**
> [family view-body check](../../../../evaluation/formal-source-fs-view-determinacy-f0v3/README.md),
> [finite runtime check](../../../../evaluation/formal-source-fs-runtime-f0v3c/README.md),
> and the source-pinning packages classified below

## 1. Exact question and answer

At migration head `16eed00f`, after the authored setup, influence, and
completion repairs, can every non-excluded research-checkpoint consumer be
re-pinned or retranscribed to the current owner bytes, and can the finite
canonical-framed executor project the repaired public-setup,
challenge-transition, required-influence, and execution-resolver bodies
without an executor-local semantic choice?

The source-consumer part is affirmative for the 25 baseline-red checks in
scope. Pure source pins now name the current bytes and identities, and the
models that copy owner structures now copy their repaired structures. The
public-setup view includes `run_established`; the finite Schnorr fixtures
correctly project it as empty. A directed two-challenge carrier projects the
new per-rule transition body and the exact static influence atom algebra.

The complete answer is nevertheless `CannotAnswer`. The finite Schnorr
challenge is an `Always` occurrence with no conditions. Section 4.3 says that
such an occurrence emits no guard frame, while Section 13 requires both its
transition rule and execution resolver to name that challenge occurrence's
entry in the framed-only `frame_schedule`. No such entry exists. The executor
therefore refuses to invent a coordinate and freezes
`CannotAnswer/F0V3C-C-UNFRAMED-CHALLENGE-POSITION`.

## 2. Source and identity re-pin

The lane reads the repaired owner pages and manifests at the migration head.
It does not preserve predecessor bytes under current labels. The source
consumers now agree on these material current values:

| Subject | Current value |
|---|---|
| canonical-framed profile digest | `1a7fe8cc7427590110bd5ea7ddc4713ebd3e65c8d9bfe997a426eae031af4222` |
| canonical-framed profile body SHA-256 | `3668965eaca7973ca1953cd4a45abe7b65196564cbfb47e17d001deba68f745b` |
| duplex-sponge profile digest | `9629ae8ab75f343b2b32f7ccd1d68a90a96bdc9c75ac4e7ea049c8a389cac7ee` |
| duplex-sponge profile body SHA-256 | `c2f4af9d27e0ed12051a0a404d14a4290e1cb38c50a84ab6bb77d5aba2187b36` |
| Interaction profile digest | `0af785eb8159ca2182843c62f72898e3c17266c5a7d9b317cfe2ae463d840474` |
| finite Schnorr Core | `zkcidv0:pir.interactive-core:b1f9e272e88b994475911a42fb016f7ac6bf8acf039c69d094907801c24fcca6` |
| finite Schnorr Fresh Protocol | `zkcidv0:pir.protocol:7c80f2a4cddb51626acec79d26e0ec873f15fb673896e0b3c0a91c87e926113b` |

The family view-body census is now 91 fields. The two independent publication
compilers agree that 17 profile identities rotate and that the Analysis
kernel profile remains stable. This is a reproduction of the current
migration cone, not publication authority.

The generated provider-observable artifacts were regenerated from the
current exact source closure. Their elaboration receipts remain bounded
checks of those generated modules; they are not provider publication or proof
of a general correspondence.

## 3. Repaired body projection

### 3.1 Public setup

Interactive Core Section 13.4, lines 2995--3023, adds
`run_established: CanonicalSeq<BindingRef>` as field 3 of
`PublicSetupInvocationViewBody`. Lines 3041--3068 divide the relevant
bindings into invocation-determined entries and run-established references.

The public-setup reference evaluator now serializes field 3, carries it in
the manifest body, and issues an empty sequence for the finite Schnorr
fixtures. The Analysis conformance consumer compares that field across the
Fresh and transformed views and refuses a nonempty value where its fixed
setup premise requires emptiness.

### 3.2 Challenge transitions

Fiat--Shamir Section 13, lines 1323--1340, now places the varying fields in a
`CanonicalSeq<ChallengeTransitionRule>`. The executor projects one rule per
construction challenge, in ascending `ChallengeRef` order, with that rule's
own:

- `challenge_ref`;
- position;
- acceptance ABI;
- decoder ABI; and
- squeeze length and maximum-draw bound.

There is no construction-wide singleton ABI or draw-bound field. The directed
carrier has two rules at total-schedule occurrence positions 1 and 3. Their
decoder result types differ, and their draw bounds are `(1,1)` and `(2,3)`.
This kills the ambiguity in which two producers could select different
singleton values for one multi-rule construction.

### 3.3 Required influence

The repaired body at lines 1293--1315 uses
`StaticInfluenceAtom = Atom(InfluenceAtom) | EveryActualDrawOf(ChallengeRef)`
and an entry-local `required: MetaBoolean`. The executor now enumerates each
challenge's complete static schedule universe in total-schedule transition
order, encodes each concrete atom with the Appendix A `InfluenceAtomBody`
variant and payload, inserts one symbolic `EveryActualDrawOf` entry at each
earlier challenge's position, and computes `required` from the static
projection law in lines 1366--1389.

The directed carrier opens one scope containing two public bindings and has
two challenges. Its second challenge retains two distinct
`PublicBindingAtom` entries and exactly one symbolic entry for every actual
draw of the first challenge. The runtime draw count does not leak into the
static body.

### 3.4 Execution resolver

The execution projector now resolves each challenge's decoding coordinate to
its own `challenge_rules` entry and its frame coordinate to the exact
transcript schedule entry. It no longer derives either coordinate from a
construction-wide singleton. This code path fails closed when the owner
schedule has no challenge entry, which is the finite Schnorr case described
in Section 1.

## 4. Baseline red-check classification

The baseline research checkpoint ran 63 checks in 1015.698271 seconds: 34
passed and 29 failed. Each of the 25 in-scope failures belongs to exactly one
of the requested categories below.

Category (a), **source pin**, means the model remains semantically unchanged
and only current page bytes, manifest bytes, line ranges, identities, or
derived frozen artifacts move.

| Check | Classification |
|---|---|
| `research.expressibility-axes` | (a) source pin |
| `research.family-instance-probe` | (a) source pin |
| `research.formal-source-target-basis` | (a) source pin |
| `research.formal-source-target-core` | (a) source pin |
| `research.owner-view-publication-topology` | (a) source pin |
| `research.owner-view-bounded-derivation` | (a) source pin |
| `research.owner-view-foundation-projections` | (a) source pin |
| `research.owner-view-oracle-projections` | (a) source pin |
| `research.owner-view-claim-reduction-projections` | (a) source pin |
| `research.owner-view-module-projections` | (a) source pin |
| `research.owner-view-terminal-projections` | (a) source pin |
| `research.owner-view-integrated-pcgraph` | (a) source pin |
| `research.semantic-migration-candidate` | (a) source pin |
| `research.owner-view-fresh-run-schema` | (a) source pin |
| `research.owner-view-integrated-projections` | (a) source pin |
| `research.provider-observable-audit` | (a) source pin |
| `research.schnorr-relations-plan-coupling` | (a) source pin |
| `research.schnorr-relations-plan-candidates` | (a) source pin |
| `research.provider-observable-audit-integrated` | (a) source pin |
| `research.kernel-mechanization-feasibility` | (a) source pin |

Category (b), **authored transcription**, means the package copies owner text
into a model and must copy the repaired fields or owner-subject cases rather
than merely updating a digest.

| Check | Classification |
|---|---|
| `research.formal-source-owner-views` | (b) authored transcription |
| `research.owner-view-body-determinacy` | (b) authored transcription |
| `research.owner-view-constructor-census` | (b) authored transcription |

Category (c), **semantic consequence**, means the repaired definition changes
what the model computes, so both executable logic and frozen findings move.

| Check | Classification |
|---|---|
| `research.owner-view-fs-family-determinacy` | (c) semantic consequence |
| `research.fs-runtime` | (c) semantic consequence |

Four baseline-red checks are expressly out of scope and remain untouched:

| Check | Reason excluded |
|---|---|
| `research.profile-publication` | publication hold |
| `research.migration-text-review` | concurrent review lane owns its refreeze |
| `research.holdout-readjudication` | concurrent review lane owns its refreeze |
| `research.provider-interpretation` | current round is owned on the Analysis branch |

## 5. Semantic consequences in the finite executor

Repaired profile and source identities change transcript namespaces and hence
the finite hash partitions. Re-freezing those outputs is not a pin-only
operation. For the retrying construction, the predecessor corpus had 24
accepted, 24 rejected, and six interpretation failures caused by exhausted
sampling; the current corpus has 24 accepted, 30 rejected, and no sampling
failures. For the one-shot construction, the predecessor corpus had 22
accepted and 32 rejected; the current corpus has 20 accepted and 34 rejected.

The current retrying construction and transformed Protocol are:

```text
zkcidv0:pir.transcript-construction:6bfe6bd860dffbe99ae9aaca09f333154c6ba1a3eeaad3d9cf249b36d79eb172
zkcidv0:pir.protocol:886af07bc6b90e05dc8618218bd7af7e9e875d9e0b7dcd0dabfee6045bb2df92
```

The current one-shot construction and transformed Protocol are:

```text
zkcidv0:pir.transcript-construction:26c2fe4fb19dd4b85672edda0fd590e011fa38ceae507889740cc0c83cdbdf5a
zkcidv0:pir.protocol:12112c333504fa0e6184997c5fd44c0d773cc39803d845ea83c44d4d9add6f64
```

All 108 current finite runs replay exactly through the independent path, and
the frozen mutation controls still refuse. Zero observed sampling failures in
these two finite corpora is not evidence that rejection sampling is total.

## Proposed delta

**Owner page and section.** `docs-next/pir/fiat-shamir.md`, Sections 4.3 and
13, specifically the framed-only schedule statement at lines 1364--1365, the
transition-position rule at lines 1391--1395, and the execution resolver at
lines 1547--1555.

**Exact change.** Preserve `frame_schedule` as the schedule of framed
occurrences. Define `ChallengeTransitionRule.position` as the challenge
occurrence's position in the exact total Core schedule, not as an entry in
`frame_schedule`. Change the execution field to:

```text
frame_schedule_coordinate:
  None | Some(the challenge occurrence's entry in frame_schedule)
```

and state that it is `None` exactly when Section 4 derives no frame for that
challenge occurrence, and otherwise is the unique matching schedule entry.
Keep `decoding_coordinate` as the challenge's own entry in
`challenge_rules`.

**Identity effect.** This owner change would rotate the canonical-framed
profile identity and every construction, transformed Protocol, and static
view identity that depends on it. It would not change the admitted Core or the
Interaction profile body merely to manufacture a frame.

**Evidence.** `research.owner-view-fs-family-determinacy` detects the missing
Oracle transition value as
`CannotAnswer/F0V3-C-UNFRAMED-CHALLENGE-POSITION`;
`research.fs-runtime` detects the same missing coordinate in the finite
Schnorr transition and execution views as
`CannotAnswer/F0V3C-C-UNFRAMED-CHALLENGE-POSITION`.

**Reversal condition.** Withdraw this proposal if the current owner closure
already contains an exact rule that gives an unframed `Always` challenge a
`frame_schedule` entry, or an exact admission rule that excludes every
unframed challenge from canonical-framed construction. A convenient inferred
coordinate is not a reversal condition.

**Non-claims.** This delta does not select or publish owner text, authorize an
identity migration, add an otherwise absent transcript frame, or establish
the semantic or cryptographic suitability of either coordinate design.

## 6. Result boundary

A passing check establishes current source-pin consistency for the finite
packages, agreement of the paired view-body projectors on every formable
value, exact projection of the repaired public-setup field and directed
multi-rule influence bodies, exhaustive execution and independent replay for
the two frozen 54-run corpora, and fail-closed treatment of the missing
unframed coordinate.

It does not establish owner publication, migration closure, arbitrary-Core
coverage, general evaluator correctness, compiler or backend correspondence,
provider conformance, theorem applicability or truth, protocol soundness,
zero knowledge, Fiat--Shamir security, random-oracle or quantum-random-oracle
security, concrete-hash suitability, sampling totality, or production
readiness.

## Handoff

### Files changed

- Added this note and updated the two affected rows in `evaluation/README.md`.
- Repaired the canonical-framed family projector and frozen evidence in
  `evaluation/formal-source-fs-view-determinacy-f0v3/{README.md,cold_projection.py,expected-findings.json,field-audit.json,independent.py,model.py,run.py,schema-source.json,support.py,typed_projection.py}`.
- Repaired the finite executor, portable pressure carrier, and all four frozen
  runtime tables in
  `evaluation/formal-source-fs-runtime-f0v3c/{README.md,derivation-vectors-one-shot.json,derivation-vectors.json,expected-findings.json,expected-runs-one-shot.json,expected-runs.json,model.py,run.py,views.py}`.
- Added `run_established` to the public-setup evaluator and conformance
  consumer in
  `evaluation/k2-protocol-fiat-shamir/{reference_model.py,tests/test_reference_model.py}`
  and
  `evaluation/k3-analysis-closure/{reference_model.py,tests/test_reference_model.py}`.
- Re-pinned the constructor and view-schema source chain in
  `evaluation/formal-source-constructor-closure-f0v2b2a/{expected-findings.json,inventory.json,run.py}`,
  `evaluation/formal-source-view-bodies-f0v2b1/expected-findings.json`,
  `evaluation/formal-source-view-body-audit-f0v2b0/{expected-findings.json,run.py}`,
  and
  `evaluation/formal-source-view-schema-f0v2b2b/{expected-findings.json,independent.py,model.py,schema-source.json}`.
- Re-pinned the terminal-to-Fresh dependency chain in
  `evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/{README.md,expected-findings.json,independent.py,model.py,run.py,schema-delta.json}`,
  `evaluation/formal-source-integrated-graph-f0v2b2d1/run.py`,
  `evaluation/formal-source-fresh-run-schema-f0v2b2d2/{independent.py,model.py,run.py,schema-delta.json}`,
  and
  `evaluation/formal-source-integrated-views-f0v2b2d3/{expected-findings.json,f2o1-six-view-ledger.json}`.
- Re-pinned the remaining owner, target, migration, and expressibility
  consumers in `evaluation/expressibility-axes/run.py`,
  `evaluation/family-instance-probe/expected-findings.json`,
  `evaluation/formal-source-owner-projections-f0v2b2c1b1/independent.py`,
  `evaluation/formal-source-owner-view-repair-f0v/{expected-findings.json,independent.py,model.py}`,
  `evaluation/formal-source-owner-views-f1r1c/{audit_model.py,expected-findings.json}`,
  `evaluation/formal-source-target-basis-f1r1a/{candidate-interaction.json,run.py}`,
  `evaluation/formal-source-target-core-f1r1b/expected-identities.json`, and
  `evaluation/semantic-migration-candidate/{candidate-contract.json,expected-findings.json}`.
- Regenerated or re-pinned provider, relation-plan, and kernel evidence in
  `evaluation/formal-provider-observables-f2o0/{elaboration-receipt.json,generated/Schnorr.lean,generated/ledger.json}`,
  `evaluation/formal-provider-observables-f2o1/{checker.py,elaboration-receipt.json,expected-findings.json,generated/ledger.json,generator.py}`,
  `evaluation/formal-schnorr-relations-plan-f2p0/{contract-ledger.json,expected-findings.json}`,
  `evaluation/formal-schnorr-relations-plan-f2p1/{expected-findings.json,source-pins.json}`, and
  `evaluation/formal-kernel-mechanization-m0/{source-pins.json,vectors/terminal-contract.json}`.

No owner page, owner manifest, check manifest, lifecycle file, docs-next
directory README, primary checkout, private ledger, Git index, or Git object under
`.git/` was changed. The 75-file working tree consists of 74 tracked-file
modifications and this one untracked note.

### Commands and outcomes

All check-runner commands used `UV_NO_SYNC=1`, `UV_OFFLINE=1`, a clone-local
`UV_CACHE_DIR`, and, after the note was added, a clone-local alternate index
and object directory under the ignored `target/` tree.

| Command | Exit | Wall time | Outcome |
|---|---:|---:|---|
| baseline `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1015.70s | 34 pass, 29 fail; classification source |
| `python3 -B checks/run.py validate` | 0 | 0.05s | 77-check manifest valid |
| `python3 -B checks/run.py run --tier developer` | 0 | 1.70s | 9 of 9 pass |
| `python3 -B checks/run.py run --check research.fs-runtime` | 0 | 356.28s | focused runtime check passes |
| focused `research.kernel-mechanization-feasibility` after its final source/vector re-pin | 0 | 80.06s | mechanized kernel check passes |
| first final `research.owner-view-fs-family-determinacy` after public-terminology cleanup | 1 | 0.74s | source-hash guard detected the changed Schnorr model bytes |
| corrected final `research.owner-view-fs-family-determinacy` | 0 | 0.75s | exact source digest re-pinned; focused family check passes |
| final `research.interactive-fiat-shamir` | 0 | 4.75s | public-setup model and tests pass |
| authoritative `python3 -B checks/run.py run --tier research-checkpoint --keep-going` | 1 | 1196.39s | 59 pass, exactly 4 excluded fail; result `target/checks/20260904T012702Z/result.json` |

The authoritative checkpoint's four failures are exactly
`research.profile-publication`, `research.migration-text-review`,
`research.holdout-readjudication`, and `research.provider-interpretation`.
They were expressly excluded and none of their package files was edited. The
checkpoint command therefore returns 1 even though every in-scope check
passes.

### Aggregate outcome

All 25 baseline-red checks in scope pass at current owner bytes. The repaired
setup and construction bodies project on their exact finite carriers, 108
runtime records independently replay, and all dependent source pins close.
The finite runtime research aggregate remains
`CannotAnswer/F0V3C-C-FS-RUNTIME`, solely because the current owner text does
not determine a frame-schedule coordinate for the unframed Schnorr
challenge. That is an intended fail-closed finding, not a failed executable
check.

### Non-claims

This lane does not publish any repaired identity, close the publication hold,
adjudicate either concurrent migration package, update the Analysis-owned
provider interpretation, establish a theorem or security result, prove a
general executor, or authorize the proposed owner-page delta. Passing finite
checks and elaboration receipts remain bounded evidence only.

### Surprises and where the brief was wrong

- The brief implicitly expected the finite Schnorr transition and execution
  views to be projectable after the two body repairs. They are not determined:
  Section 4.3 makes the `Always` challenge unframed, while Section 13 demands
  its entry in a schedule containing only framed occurrences. The lane records
  `CannotAnswer` and proposes, but does not apply, an owner change.
- `research.owner-view-constructor-schema` was green in the baseline and so
  was absent from the requested red-check classification. Re-pinning its
  predecessor constructor census necessarily changed the census bytes, which
  exposed a second-order source-pin cone through terminal, integrated, Fresh,
  provider, and kernel packages. Those pins and their derived digest-only
  evidence had to move as well; no semantic carrier changed in that cone.
- A final public-terminology audit removed newly added legacy fixture labels
  from diagnostics and a source comment. The family package's source-hash
  guard correctly rejected the changed Schnorr model bytes once; its exact
  digest was re-pinned and both affected focused checks then passed.
- The instruction that all checks must pass cannot include the complete
  research checkpoint while simultaneously excluding four known-red checks.
  The manifest validation, developer tier, and lane-owned focused check all
  pass; the checkpoint retains exactly those four exclusions and no others.

Main may commit the complete working tree with subject:
`test: re-pin the source packages and project the repaired view bodies`.
