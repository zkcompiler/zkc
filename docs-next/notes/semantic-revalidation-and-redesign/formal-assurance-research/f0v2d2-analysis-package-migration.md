# Analysis named-premise package migration

> **State:** the four migrated executable checks are locally affirmative, but
> the exact question remains
> `CannotAnswer/F0V2D2-C-OWNER-IDENTITIES-UNDERDETERMINED`: two required owner
> identities are represented only by documented candidate encodings
> **Authority:** None. This note and the evaluation packages neither edit nor
> publish Analysis, Protocol IR, Relations, or Foundation owner text.

## 1. Exact question

Do the existing Analysis packages reproduce the owner text's premise-bearing
identities?

The aggregate answer is `CannotAnswer`. The four migrated checks reproduce the
owner-determined carrier fields, branch partitions, vector shapes, and
downstream identity propagation in their finite cases, and they fail closed on
the requested mutations. They cannot reproduce the two identities that the
owner text leaves contradictory or without an authenticated source coordinate;
Section 5 identifies those exact gaps and the candidate-only treatment.

## 2. Baseline before edits

Each command below completed at clone head `dd70634`; no result is inferred
from partial output.

| Check | Runner outcome | Exit | Wall time |
|---|---|---:|---:|
| `research.property-analysis` | pass in one process, 206/206 tests | 0 | 1572.69 s |
| `research.finite-cover` | pass | 0 | 23.92 s |
| `research.joined-semantic-boundary` | pass | 0 | 72.93 s |
| `research.analysis-premise-intake` | pass | 0 | 0.16 s |

The property check ran under a generous external timeout and completed on its
own after 1572.569 seconds of runner time. The other runner times were 23.798,
72.805, and 0.042 seconds respectively.

## 3. Migrated carrier and intake

The shared Analysis model now has the current closed ten-kind premise algebra,
including `OperationalCompletion`, and all eight coordinate arms. It encodes
the three bound-value arms, four source arms, three evidence depths, and four
model scopes. A premise body has six identity-bearing fields. Question and goal
bodies carry canonical requirements and bindings; hypothesis nodes, reachable
contexts, supports, and judgments carry only premise IDs derived from their
authenticated predecessors.

The intake operation authenticates each premise under the question's direct
profile and partitions failures before goal formation:

- absent question or premise formation evidence and missing binding keys are
  `CannotAnswer`;
- duplicate, reordered, noncanonical, or extra binding keys are `Malformed`;
- wrong kind, coordinate, direct profile, Fresh scope, oracle scope, exact
  subjects, or `RebindRequired` scope are `Refused`; and
- only the exact key set and admitted scopes are affirmative.

The relation-bound Fresh question carries six premises: Fresh distribution,
relation predicate, witness type, prover private state, honest commitment, and
honest response. Construction and family Fiat--Shamir questions each carry
their sampler and oracle-process pair. The fixed-extractor question carries the
relation/witness pair. Every family licensed as premise-free carries explicit
empty requirement and binding tuples.

The negative matrix independently mutates requirements and bindings by
omission, surplus, duplication, and reordering; removes source evidence;
substitutes kind, coordinate, profile, and each scope; changes canonical law
arguments, source, evidence depth, and scope; and omits or adds derived premise
IDs at node, context, support, and judgment. An admitted same-coordinate source
change rotates the premise, goal, proposition, support, and judgment while the
authenticated question remains fixed.

## 4. Dependent package results

The finite-cover goal now carries exactly the relation and witness premise
IDs. Its hypothesis context remains empty, while support and judgment derive
the same pair. Missing, extra, same-kind coordinate-swapped, and scope-mismatched
inputs stop before the arithmetic. The retained 308-member ordered stream and
its digest remain unchanged.

The joined consumer check confirms by bounded object-graph traversal that no
named-premise body, Analysis-local source handle, Analysis judgment or
capability, or premise identity enters either OIR endpoint branch. Swapping an
Analysis premise refuses before a changed Analysis goal forms and leaves both
independently formed OIR endpoint and projection-proposition identities fixed.

The intake probe now covers twelve proposal records over ten kinds. The
relation-bound case uses the owner-specified six-slot non-provider vector. Provider
maps are separate proposal-only questions: `Image(value)` occurs exactly for a
lane named by the provider declaration, every other lane is `Unmodelled`, and a
Boolean noncompletion-to-false collapse is `Malformed`. A separate
`OperationalCompletion` premise has a distinct identity. The option-layer and
tagged providers retain all five lane images; the added Boolean provider models
only Accepted and Rejected and leaves the other three Fresh lanes unmodelled.
The shared Analysis model refuses both provider kinds because the owner profile
currently publishes no provider declaration.

## 5. `CannotAnswer` owner findings

### Fixed-extractor exact-subject scope

`docs-next/analysis/cryptographic-properties.md` Section 3.2 lines 1262--1290
defines the fixed-extractor question by appending `Ext` to the relation-bound
subject sequence and then prescribes `SchnorrExtractorPremiseBindings(S)`.
Lines 2349--2350 define every relation and witness premise produced by that
helper with `ExactSubjectsOnly` of the shorter special-soundness question, and
lines 2548--2549 say the extractor helper merely selects those two existing
bindings. Exact intake therefore refuses the prescribed pair against the
fixed-extractor question. The executable package re-forms the same relation and
witness bodies with the fixed-extractor question's exact subjects. This is a
candidate repair and not an owner-determined premise identity.

### Fresh public-coin declaration coordinate

`docs-next/analysis/cryptographic-properties.md` Section 3.2 lines 2213--2239
requires a `ProtocolDeclarationRef<"pir.public-coin-law">`; lines 2522--2531
describe it as the declaration named by `S.challenge_ref`. The imported bounded
Protocol model exposes the exact static challenge-view coordinate but no
authenticated protocol-declaration reference or declared projection from that
coordinate. The candidate helper at
`evaluation/k3-analysis-closure/reference_model.py:15872` therefore binds the
exact static challenge coordinate. This does not establish the owner-required
declaration identity.

### Provider publication remains absent

`docs-next/analysis/cryptographic-properties.md` Section 3.2 lines 2586--2589
requires an exact provider declaration published in the selected profile and
says no provider-map premise can form until one exists. No such declaration is
published. The shared model consequently refuses provider-map and completion
premise formation. The standalone probe's three declarations, maps, and
completion body remain proposal data and supply no missing owner evidence.

### Migration-plan census and locator drift

The round-two migration plan in
`docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2d1-analysis-premise-text-review.md`
lines 660--667 calls for nine kinds and seven coordinate arms. The governing
kind law at
`docs-next/analysis/analysis-model.md` lines 2207--2250 has ten kinds, while its
coordinate use has eight arms after adding `OperationalCompletion` on the
Protocol outcome-partition coordinate. The direct task correctly names that
tenth kind and eighth arm, so the executable follows the owner page. Whether
the old counts denoted a superseded revision or intended to omit the new arm is
`CannotAnswer/F0V2D2-C-PLAN-CENSUS-DRIFT`, not evidence for a nine-kind codec.

The same plan at lines 695--699 says the baseline shared model has fourteen
lexical `AnalysisGoalBodyV0` calls. The file at clone head `dd70634` has eight;
its other listed counts are eight question, five node, four context, one
support, and one judgment call. Every actual call was migrated. The six absent
goal calls cannot be silently invented, so the discrepancy is
`CannotAnswer/F0V2D2-C-PLAN-CONSTRUCTOR-CENSUS-DRIFT`. Lines 706--707 also point
the empty-family license at `cryptographic-properties.md` lines 2393--2401,
which now define the Prover private-state premise. The actual empty-family
license is at lines 2596--2604 and is the evidence used here.

### Migration-plan scope conflict

The round-two plan includes the recursive-composition surrogate at lines
746--759 and profile publication at lines 761--772. The direct migration task,
however, enumerates and authorizes manifest changes for exactly
`research.property-analysis`, `research.finite-cover`,
`research.joined-semantic-boundary`, and `research.analysis-premise-intake`.
It also prohibits every `docs-next/pir/**` edit, while plan line 767 requires
regenerating `docs-next/pir/profiles/published-identities.json`. This lane left
both non-enumerated packages and the prohibited publication file unchanged.
It therefore makes no named-premise migration claim for the recursive
surrogate and cannot complete the publication step:
`CannotAnswer/F0V2D2-C-PLAN-SCOPE-CONFLICT`.

### Compact carrier index is stale but non-authoritative

`docs-next/analysis/analysis-model.md` Section 4.1 lines 1981--2042 still
describes question, goal, context, support, and judgment without all newly
identity-bearing premise fields. Lines 2045--2052 explicitly say this compact
index is not the exhaustive body table, so the later exact schemas determine
the executable encoding. Whether the compact descriptions are intentionally
lossy or stale remains `CannotAnswer`; they are not used as affirmative schema
evidence.

## 6. Proposed delta

These are owner-page proposals only. This lane did not edit an owner page.

### Give the fixed extractor its own exact premise scope

- **Owner page and section:**
  `docs-next/analysis/cryptographic-properties.md`, Section 3.2, the
  `SchnorrFixedExtractorWorksQuestion`, `SchnorrPremiseScope`, and
  `SchnorrExtractorPremiseBindings` definitions at lines 1262--1290,
  2349--2350, and 2548--2549.
- **Exact change:** define the extractor pair as freshly formed relation and
  witness premise bodies whose `ExactSubjectsOnly` value is exactly
  `SchnorrFixedExtractorWorksQuestion(S,Ext).exact_subjects`; do not reuse the
  shorter special-soundness premise IDs.
- **Identity effect:** both fixed-extractor premise IDs and every dependent
  goal, proposition, support, judgment, checked-result coordinate, and portable
  authority binding rotate. The special-soundness six-premise vector does not.
- **Evidence with gate IDs:** `research.property-analysis` and
  `research.finite-cover`.
- **Reversal condition:** withdraw if the owner instead removes `Ext` from the
  fixed-extractor exact subjects or publishes another exact scope law that
  makes the prescribed pair pass without inference.
- **Non-claims:** exact scope agreement does not prove either premise or the
  extractor conclusion.

### Define the Fresh declaration projection

- **Owner page and section:**
  `docs-next/analysis/cryptographic-properties.md`, Section 3.2, lines
  2213--2239 and 2522--2531.
- **Exact change:** define an authenticated PIR-owner projection from
  `S.challenge_ref` to the exact
  `ProtocolDeclarationRef<"pir.public-coin-law">`, or add that declaration
  reference explicitly to the subject tuple and require equality with the
  challenge occurrence. The premise helper must consume that reference, not a
  static-view leaf coordinate.
- **Identity effect:** the Fresh premise and all six-premise question
  descendants rotate; the imported PIR owner identity rotates only if PIR must
  add a new identity-bearing view field.
- **Evidence with gate IDs:** `research.property-analysis` and
  `research.analysis-premise-intake`.
- **Reversal condition:** withdraw if the PIR owner publishes an already
  authenticated declaration projection that the Analysis source can consume
  without adding or inferring a coordinate.
- **Non-claims:** a declaration reference identifies a premise coordinate; it
  does not establish uniformity, freshness, or independence.

### Refresh the compact carrier index

- **Owner page and section:** `docs-next/analysis/analysis-model.md`, Section
  4.1, lines 1981--2042.
- **Exact change:** mention named-premise requirements on questions, bindings
  on goals, exact derived premise IDs on contexts, supports, and judgments, and
  the per-node derived IDs. Keep the later exhaustive schemas authoritative.
- **Identity effect:** none if this compact index remains explanatory prose.
- **Evidence with gate IDs:** `research.property-analysis`.
- **Reversal condition:** withdraw if the owner states explicitly that compact
  entries intentionally omit all fields already present in the exhaustive
  table.
- **Non-claims:** editorial consistency does not change or validate a semantic
  body.

## 7. Non-claims

Passing tests are bounded executable and differential evidence. They do not
prove any named premise, relation satisfaction, witness typing, Plan honesty,
special soundness, knowledge soundness, theorem truth or applicability,
Fiat--Shamir security, ROM or QROM security, provider correspondence, compiler
or backend correctness, endpoint validity, implementation conformance, or
production readiness. They do not publish a semantic profile or owner identity.

## Handoff

- **Files changed:** `checks/manifest.json`; `evaluation/README.md`;
  `evaluation/k3-analysis-closure/{README.md,reference_model.py,tests/test_reference_model.py}`;
  `evaluation/finite-cover-analysis/{README.md,tests/test_finite_cover.py}`;
  `evaluation/k3-integrated-closure/{README.md,tests/test_reference_model.py}`;
  all six files in `evaluation/analysis-premise-intake-probe/`; and this note.
  No owner page, profile manifest, lifecycle registry, docs-next directory
  README, or review package was edited.
- **Required command results:** all commands below used the final clone-local
  alternate index, `UV_NO_SYNC=1`, `UV_OFFLINE=1`, and a clone-local uv cache
  where applicable.

  | Command | Result | Exit | Wall time |
  |---|---|---:|---:|
  | `python3 -B checks/run.py run --check research.property-analysis` | pass, 213/213 tests; runner 1684.182 s | 0 | 1684.24 s |
  | `python3 -B checks/run.py run --check research.finite-cover` | pass; runner 32.184 s | 0 | 32.24 s |
  | `python3 -B checks/run.py run --check research.joined-semantic-boundary` | pass; runner 116.615 s | 0 | 116.67 s |
  | `python3 -B checks/run.py run --check research.analysis-premise-intake` | pass; runner 0.039 s | 0 | 0.10 s |
  | `python3 -B checks/run.py validate` | pass, 77 checks and 6 tiers | 0 | 0.05 s |
  | `python3 -B checks/run.py run --tier developer` | pass, 9/9 checks | 0 | 1.76 s |
  | `git diff --cached --check` against the alternate index | pass | 0 | 0.01 s |
  | corrected `python3 -B -m py_compile` over every changed Python file | pass | 0 | 0.16 s |

  The research-checkpoint audit completed in 702.84 seconds with exit 1:
  33 checks passed and 30 failed. The anticipated
  `research.analysis-premise-text-review` failure was present, but it was not
  the only red check. The other 29 were
  `research.profile-publication`, `research.expressibility-axes`,
  `research.family-instance-probe`, `research.formal-source-target-basis`,
  `research.formal-source-target-core`, `research.formal-source-owner-views`,
  `research.owner-view-publication-topology`,
  `research.owner-view-body-determinacy`,
  `research.owner-view-bounded-derivation`,
  `research.owner-view-constructor-census`,
  `research.owner-view-foundation-projections`,
  `research.owner-view-oracle-projections`,
  `research.owner-view-claim-reduction-projections`,
  `research.owner-view-module-projections`,
  `research.owner-view-terminal-owner-contracts`,
  `research.owner-view-terminal-projections`,
  `research.owner-view-integrated-pcgraph`,
  `research.semantic-migration-candidate`, `research.migration-text-review`,
  `research.holdout-readjudication`, `research.owner-view-fresh-run-schema`,
  `research.owner-view-integrated-projections`,
  `research.owner-view-fs-family-determinacy`,
  `research.provider-observable-audit`,
  `research.schnorr-relations-plan-coupling`,
  `research.schnorr-relations-plan-candidates`,
  `research.provider-observable-audit-integrated`,
  `research.provider-interpretation`, and
  `research.kernel-mechanization-feasibility`. Their diagnostics report
  source, owner-view, generated-certificate, or frozen-finding drift in
  non-migrated packages. Because the tier had no pre-edit baseline, this lane
  does not attribute that drift to a particular prior edit. It did not alter
  those packages or the owner pages they pin.
- **Aggregate outcome:** the bounded four-check migration is affirmative, but
  the exact owner-identity question is `CannotAnswer` for the two gaps in
  Section 5. No commit was attempted because this lane's Git metadata is
  read-only.
- **Non-claims:** Section 7 remains the complete claim boundary.
- **Surprises and where the brief was wrong:** the plan's kind, coordinate,
  constructor, and empty-license locations are stale as recorded above. The
  wider plan conflicts with the direct four-check scope and prohibited
  publication path. The clone does not contain `AGENTS.md` or
  `.claude/CLAUDE.md`; their read-only primary-checkout copies supplied the
  required repository guidance. A first focused-test command used an
  unsupported `--pattern` option and exited 2 without running tests; a second
  filter spelling selected no tests and exited 5. One subsequently selected
  scope test exposed an incorrectly constructed wrong-profile fixture; that
  test was corrected before the full suite passed. Two long property-check
  attempts and one direct unittest attempt were deliberately interrupted after
  later edits made their snapshots stale; they exited 130 and no conclusion
  was drawn from them. An initial syntax-only command named a nonexistent
  joined-check test file and exited 1 before the corrected command passed.
  During the first alternate-index setup Git observed its own
  `.lane-index.lock`; that path was removed from the alternate index and never
  entered the real index. The brief's statement that the checkpoint tier could
  have only one red check did not match the observed 30-failure checkout-wide
  result; this lane kept the 29 additional non-migrated failures out of scope.
