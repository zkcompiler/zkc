# Decision review packet: what an adversarial reader should try to break

> **Kind:** review packet (formal-assurance research)
> **State:** Prepared 2026-09-03 after the migration text closed at its sixth
> review round and the Analysis premise text at its fourth; every decision
> below is already in owner text on the migration or Analysis branch, and
> none is published.
> **Authority:** None. The packet lists decisions, the evidence each rests
> on, and the condition under which each is reversed; it changes nothing.

## 1. Why a human pass is still needed

Six review rounds on the migration text and four on the Analysis text were
run by independent agent lanes with executable checkers. They found real
defects in rounds three, five, and six that rounds one and two had passed,
each time because a new question was asked. That history says the remaining
risk is in questions nobody has asked, and an adversarial human reader asks
different questions from a checker. The decisions are grouped by what a
reader would have to show to reverse them.

## 2. The migration decisions (`f0-v2c-decision-inputs.md`, Section 10)

| Decision | What it fixes | Evidence | Reverse it by showing |
|---|---|---|---|
| A2: views keep identities; the consumer holds the authenticated algorithm and module preimages | a static view is exact without copying algorithm bodies | `research.owner-view-*`, `research.formal-source-owner-views` | a consumer that cannot obtain a preimage it needs from the closure |
| B2: the nominal coin law stays the hook; Analysis binds a distribution as a named premise | sampling is an assumption, not a Core fact | `research.analysis-premise-intake`, `research.provider-interpretation` | a Core fact that depends on the distribution rather than on the coordinate |
| C1: one PIR-owned outcome partition; provider carriers mapped in Analysis; `StrategyStopped` a lane, not a record | every run ends in exactly one lane; consumers map, never read verdicts | `research.owner-view-fresh-run-schema`, `research.holdout-readjudication` | a run that ends in two lanes or in none, or a consumer that must read a verdict |
| D2's five owner choices | the Fresh run schema's receipts, fixation, and partial records | `research.owner-view-fresh-run-schema` | a receipt prefix or partial record the schema cannot express |
| Section 11 wording by the D1 and M1 readings | transfer coordinates by node, lattice precedence, exact sinks | `research.owner-view-integrated-pcgraph`, M1 | a public-coin graph the transfer coordinates misplace |
| F0-V3 family view catalogs in the same migration | the two Fiat--Shamir profiles own exact view bodies | `research.owner-view-fs-family-determinacy` (95 fields exact) | a family field that two compilers could fill differently |
| P2 identity pin (prose fragment identity) | transcription discrepancies are named reopenings | both publication compilers | two compilers that disagree on a fragment digest |
| Freeze scope: load-bearing kernel only | satellites are frozen as declared, unexercised | the migration record, Section 8 | a consumer that relies on a satellite as if exercised |

## 3. The Terminal contract (`terminal-contract-reopening-2026-09-03.md`)

| Decision | Evidence | Reverse it by showing |
|---|---|---|
| First-active terminal semantics with sorted-unique required checks, applied reductions, and terminal claims | M3, M4, M5 (Lean), `research.migration-text-review` | a protocol whose accepting condition cannot be stated as a first-active terminal with a guard |
| Guards on the attempt only; scope openings deterministic and unguarded | M3, the guard-implication boundary note | a protocol whose scope must open conditionally |
| Closed forward state: `Region`, `Implies`, `Disjoint`, `ClaimStatus`, `LiveClaims`, with `Unknown` refused | M4 (Region exactness, Live/Dead soundness), 18,282 claim-path cases | a live claim the region calculus judges `Unknown` or `Dead` |
| Claim sources take their binding scope's opening or their reduction occurrence's region | round four, M5 | an initial claim whose liveness depends on a guard its scope opening does not see |
| Syntactic guard implication (required reductions unconditional or identically guarded) | the guard-implication boundary note | a portfolio protocol that needs the must-fact exactness extension |

## 4. The provider carrier (`f2o2-provider-carrier-decision-2026-09-03.md`)

| Decision | Evidence | Reverse it by showing |
|---|---|---|
| A provider declaration names its `modelled_lanes`; a lane image is `Image(v)` or `Unmodelled`; no lane is collapsed onto another | F2-O2 round two (five clauses, 81 runs), Analysis round four | a provider whose execution realizes a lane the declaration cannot name, or a transport that needs a collapsed image |
| The tenth premise kind `OperationalCompletion` for statements over the whole partition | Analysis round four | a whole-partition statement that transports soundly without it |
| VCVio's declaration: carrier `Bool`, modelled lanes `Accepted` and `Rejected` (item 3, unpublished) | F2-O2 round two, the VCVio source at the pinned revision | a VCVio execution path that fails to complete inside the oracle computation |

## 5. Static views (rounds five and six)

| Decision | Evidence | Reverse it by showing |
|---|---|---|
| `PIRReference` is the closed union of the Core-local dense-ordinal references, `ValueRef`, and the declaration references a profile recognizes | round six (386 leaves under one arm each) | a view leaf of a reference type outside the union |
| Every law-valued field names one declaration through the profile's selection table | round five (35 fields, ordinals stable) | a law-valued field whose proposition is stated by a declaration the table does not name |

## 6. Decisions still open, with the recommended answer

| Item | Recommendation | Where |
|---|---|---|
| Publication of the identity table and the staged refreeze | publish; the rehearsal has re-pinned 22 packages against the candidate table | `f0-v2c-refreeze-rehearsal.md` |
| Schnorr claim binding | fixture-side repair: one initial claim at the statement binding's scope opening | `schnorr-claim-binding-reopening-2026-09-03.md` |
| Family and instance | Core instance-only; the generator a Compiler transition; family theorems bound pointwise through per-member premises | `../family-and-instance/decision-inputs.md` |
| Pull request 27 | keep the notes as an appendix and land after the migration | the private ledger |
| VCVio declaration | publish item 3 as Section 4a of the carrier packet states it | `f2o2-provider-carrier-decision-2026-09-03.md` |

## 7. Non-claims

Nothing here establishes cryptographic security, theorem applicability,
implementation correspondence, or production validity. The evidence column
names bounded executable results and mechanized statements over stated
abstractions; the reversal column names what a counterexample must exhibit.
