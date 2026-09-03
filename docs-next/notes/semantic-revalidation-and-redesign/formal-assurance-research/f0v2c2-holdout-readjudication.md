# Cold Protocol Holdout Readjudication Against Migrated PIR

> **State:** `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; five fitting rows,
> three boundary-breaking rows, no bends, and no verdict disagreements
> **Authority:** None. This verification note neither edits nor publishes an
> owner page, source profile, or semantic identity.
> **Executable evidence:**
> [`evaluation/formal-source-holdout-readjudication-f0v2c2`](../../../../evaluation/formal-source-holdout-readjudication-f0v2c2/README.md)

## 1. Exact question and answer

Do the migrated PIR terminal, owner-view, and outcome contracts represent every
cold protocol holdout at its recorded boundary, with the same verdict as both
the adjudication record and the structural-axes matrix?

Yes, at the exact frozen source bytes. The five holdouts produce eight rows
because WARPfold, multiparty Sumcheck, and the Galois-ring case each have a
finite or virtual subcase distinct from a broader source claim. The migrated
owner text leaves five rows fitting and three breaking at already named
boundaries. No row bends and no verdict changes.

The migration does change one concrete carrier shape. WHIR's earlier schedule
guarded the fold by a proper subset of the accepting Checks. Scope openings are
deterministic and unguarded, and the owner admits a guarded producer only when
its guard is `Always` or textually identical to the consumer guard. The
corrected carrier therefore delays both Reductions under the exact accepting
guard and retains one unconditional fallback with the initial Claim. This is a
schedule restructuring inside an otherwise fitting Core, not a reopened owner
boundary or an assertion that the source's earlier Reduction timing was exact.

## 2. Migrated decision law used here

The migrated `TerminalDecl` authors required-true Checks, required-applied
Reductions, and the exact terminal Claim set; rejection and abort discharge
that set while acceptance consumes it
([Interaction Core Section 6.4, lines 896-945](../../../pir/interactive-core.md#64-terminals)).
Admission then requires every named Check output to be a direct terminal-guard
input whose positive literal occurs in `MustWhenTrue`, every named Reduction to
be attempted whenever the terminal is attempted, and one invariant live-Claim
set at every activation
([Interaction Core Section 10, lines 1427-1509](../../../pir/interactive-core.md#10-core-admission-and-consistency)).

For direct Check outputs `c0 ... cn`, this note uses the closed term shape:

```text
And(c0,...,cn) =
  if c0 then
    if c1 then
      ...
        if cn then true else false
      ...
    else false
  else false

MustWhenTrue(And(c0,...,cn)) =
  { Positive(c0), ..., Positive(cn) }
```

A semantic `and` primitive would contribute no literal and would not admit a
required Check. A final `Always` terminal can therefore name no required Check.
Each Reduction is unconditional or has a guard textually identical to every
consumer of its output. A semantically valid implication between different
guards is not inferred; Section 10 expressly leaves checked guard implication
outside this regime. Scope declarations cannot supply a guard.

The six normalized view bodies are exact owner projections, not consumer-made
tuples
([Interaction Core Sections 13.1-13.2, lines 2088-2537](../../../pir/interactive-core.md#13-pir-owned-source-views)).
Their closure reaches referenced producers, laws, types, dependencies, and the
selected Protocol interpretation; algorithm preimages remain in the admitted
dependency closure held by the consumer
([lines 2583-2619](../../../pir/interactive-core.md#132-exact-view-bodies-and-read-closure)).
Canonical and duplex transcript constructions add separate family-owned views
([canonical Section 13, lines 1235-1510](../../../pir/fiat-shamir.md#13-exact-source-view-contracts);
[duplex Section 11, lines 839-1154](../../../pir/duplex-sponge-fiat-shamir.md#11-exact-pir-source-views)).

Finally, every admitted `GenerateRun` ends in exactly one of `Accepted`,
`Rejected`, `Aborted`, optionally `InterpretationFailed`, `StrategyStopped`, or
`OperationalNoncompletion`. `InterpretationFailed` is a typed completed failure
of the selected challenge interpretation, not a Core terminal; it is absent for
Fresh and duplex protocols and present for the canonical-framed profile
([Interaction Core Sections 12.3-12.4, lines 1828-1854 and 1954-1985](../../../pir/interactive-core.md#124-run-and-replay-records)).
Endpoint and OIR projection retain the three terminal obligation sets exactly
([Endpoint Sections 7.2-7.3, lines 1056-1137](../../../pir/endpoint-projection-views.md#73-claims-reductions-and-role-closure);
[OIR projection lines 300-340 and 895-923](../../../oir/projection-contract.md)).

## 3. Verdict comparison

The earlier portfolio record is at
[Section 2, lines 36-49](../semantic-closure-and-freeze/cold-protocol-holdouts/portfolio-adjudication-and-freeze-decision.md#2-portfolio-results).
The matrix rows are at
[`cases.json`, lines 248-333](../../../../evaluation/expressibility-axes/cases.json).
The matrix already projects `ProfileOrModule` to fits and projects the two
source-level `Undetermined` results to their exact break boundaries.

| Source form | This readjudication | Earlier record | Matrix prediction | Disagreement |
|---|---|---|---|---|
| WHIR finite constructive member | fits | `ProfileOrModule` -> fits | fits | none |
| Circle STARK finite instance | fits | `ProfileOrModule` -> fits | fits | none |
| WARPfold finite fold | fits | `ProfileOrModule` -> fits | fits | none |
| WARPfold broad cross-system application | breaks at `B-CROSS-EXECUTION` and `B-IMPORTED-CHALLENGE` | `Undetermined` -> those boundaries | breaks there | none |
| Physical multiparty Sumcheck | breaks at `B-MULTIPARTY` | `IntentionalBoundary` -> that boundary | breaks there | none |
| Commitment-anchored virtual Sumcheck proof | fits | `ProfileOrModule` -> fits | fits | none |
| Complete noninteractive Galois-ring argument | breaks at `B-SOURCE-INCOMPLETE` | `Undetermined` -> that boundary | breaks there | none |
| Explicit interactive Galois-ring components | fits | `ProfileOrModule` -> fits | fits | none |

The aggregate is affirmative because every holdout has a verdict and every row
agrees with both comparison sources. The source-level and matrix-description
disagreements found below are separate findings; neither changes a verdict.

## 4. WHIR finite constructive member

The exact source schedule has five Checks, then a fold Reduction, a final
Reduction, an accepting terminal, and one fallback reject
([constructive encoding Sections 4-5, lines 144-269](../semantic-closure-and-freeze/cold-protocol-holdouts/whir-constructive-encoding.md#4-complete-ordered-occurrence-trace)).
The claim graph is `initial -> folded -> none`.

### 4.1 Terminal contract

Let `c0,c1` be the initial and main-loop Sumcheck Checks and `c2,c3,c4` the two
final-consistency Checks and final weighted-sum Check. Define:

```text
G_accept = And(c0,c1,c2,c3,c4)
```

The corrected schedule is:

| Position | Guard | Required true Checks | Required Reductions | Terminal Claims |
|---|---|---|---|---|
| fold Reduction | `G_accept` | n/a | n/a | replaces initial with folded Claim |
| final Reduction | `G_accept` | n/a | n/a | consumes folded Claim |
| Accept | `G_accept` | all five | fold and final | empty |
| fallback Reject | `Always`, after the accepting terminal | empty | empty | initial Claim |

`MustWhenTrue(G_accept)` contains all five positive literals. Both Reductions
and their accepting consumer have the same guard, so `GuardImplies` and
`AttemptedWhenever` hold syntactically. If any Check is false, neither
Reduction is active and the fallback sees exactly the initial Claim. Exhausting
all 32 Check valuations yields one accepting valuation, 31 fallback valuations,
and one activation of each Reduction.

The legacy source schedule is refused because its fold and final guards differ
from their consumers; an unguarded scope cannot mediate that difference. The
corrected carrier delays the fold relative to the source prose. Proving that
this delay preserves a chosen source semantics would require an exact
source-correspondence argument or a future checked guard-implication regime;
this package establishes neither.

### 4.2 Views

| View | Analysis-observable fields |
|---|---|
| `PublicBindingView` | finite member descriptor, initial Claim input binding, scopes, binding classes, exact types |
| `StrategyDecisionView` | logical folded-Oracle publication, Sumcheck messages, out-of-domain reply, final polynomial, guards, legal move types, exact prior reads |
| `PublicCoinView` | all challenge refs, types, domains and laws, joint shift/final-sample correlations, public conditions, reduction consumers, complete public-coin graph |
| `EffectView` | ordered messages, logical-Oracle fixation/query/answer occurrences, derived values, five Checks, two Reductions under `G_accept`, and two terminal frontiers |
| `ClaimReductionView` | initial/folded Claims, fold/final Reductions under `G_accept`, creation and consumers, accepting consumption, and fallback initial-Claim disposition |
| `ExecutionView` | Fresh or selected transformed Protocol identity, resolver coordinates, receipts, complete record schema, outcome partition |
| canonical family views | transcript declaration, required influence, challenge transition, and checked construction result after the logical Oracles first receive the separately checked commitment route |

No required PIR observable is missing. Round-local decoding, agreement, and
soundness premises remain Analysis propositions rather than omitted PIR
coordinates. A logical Oracle cannot be hashed directly merely because the
views expose its access events; the migrated public-coin and canonical-family
closures preserve that separation.

### 4.3 Outcome partition and verdict

All Checks true reaches `Accepted`; an ordinary false Check reaches the
fallback `Rejected` terminal without activating either Reduction. A source-authored malformed-value or unavailable-
access event may reach `Aborted`. Canonical sampling exhaustion, if that exact
construction is selected, is `InterpretationFailed`; prover refusal is
`StrategyStopped`; unsupported evaluation or resource exhaustion is
`OperationalNoncompletion`. No WHIR termination mode lacks a lane after the
terminal repair.

Verdict: **fits**, matching both earlier sources.

## 5. Circle STARK finite instance

The boundary analysis identifies trace, quotient, folded Oracles, batching and
fold coins, one out-of-domain point, derived DEEP values, explicit Claims and
Reductions, and final Checks
([Sections 3.2-4.2, lines 81-176](../semantic-closure-and-freeze/cold-protocol-holdouts/circle-starks-boundary-analysis.md#32-circle-fri)).
It does not author one exact Core table, and it leaves an out-of-field answer as
“refuse or abort” according to the later selected construction (lines 131-134).

### 5.1 Terminal contract

Let `Q_circle` be the selected finite set of AIR, batch, DEEP, fold, opening,
and final Checks; let `R_circle` be its selected AIR, quotient, DEEP, and Circle
FRI Reductions; and let `L0` and `L_accept` be the exact initial and accepting
live-Claim sets.

An admissible all-or-nothing carrier guards every member of `R_circle` with
`And(outputs(Q_circle))`, applies them in dependency order, then reaches Accept
under that textually identical nested conjunction with
`required_true_checks = Q_circle`,
`required_applied_reductions = R_circle`, and
`terminal_claims = L_accept`. A following root Reject has `Always`, empty
required sets, and `terminal_claims = L0`. `MustWhenTrue` proves every required
positive literal because each Check output is a direct nested guard input.

If field-membership failure is a semantic source event, the selected Core must
author an earlier Abort branch and its exact live-Claim frontier. If it is a
typed evaluator refusal, it is not silently converted to Reject or Abort.
Because the boundary analysis does not select between those forms or enumerate
the exact refs, the full carrier is `CannotAnswer` until source specialization;
the normalized structure itself fits and exposes no owner-page defect.

### 5.2 Views

| View | Analysis-observable fields |
|---|---|
| `PublicBindingView` | AIR statement, domain and parameter bindings, scopes, exact circle/base/extension types |
| `StrategyDecisionView` | dimension-gap scalar, trace/quotient/folded Oracles, claimed evaluations, final object, guards and prior reads |
| `PublicCoinView` | batch/fold/out-of-domain/query challenges, domains, correlations, reduction use and public-coin graph |
| `EffectView` | complete message/Oracle schedule, query and answer occurrences, derived DEEP/batch values, checks and terminals |
| `ClaimReductionView` | AIR, quotient, DEEP, batch, and Circle FRI Claims and transforms |
| `ExecutionView` | selected challenge interpretation, resolver and receipts, record schema and outcomes |
| family views | canonical framing, influence, transition, retry/failure, and checked-result fields only after an exact commitment/transcript construction is separately selected |

No observable needed for a finite PIR/Analysis subject lacks a coordinate.
Circle algebra and theorem premises are resolved through authenticated modules,
Relations, and Analysis. The source's unresolved field-failure choice is absent
source specialization, not absent target vocabulary.

### 5.3 Outcome partition and verdict

Success is `Accepted`; a false verifier equation is `Rejected`; a selected
explicit typed-failure event is `Aborted`; canonical out-of-domain sampling
exhaustion is `InterpretationFailed`; strategy refusal is `StrategyStopped`;
and a non-authored typed refusal, unsupported operation, or resource limit is
`OperationalNoncompletion`. No selected termination mode lacks a lane, but the
source must decide which typed-failure route applies.

Verdict: **fits**, matching both earlier sources.

## 6. WARPfold

The finite fold sends one cross-term polynomial, checks its constant
coefficient, samples one bounded challenge, and derives the folded public
instance. Degradation and reinforced-copy checks remain inside the outer
Relations subject rather than becoming duplicate Core Checks
([Sections 3.2 and 4.2, lines 79-113 and 170-185](../semantic-closure-and-freeze/cold-protocol-holdouts/warpfold-boundary-analysis.md#32-strict-plus-relaxed-fold)).

### 6.1 Finite-fold terminal contract

A minimal source-faithful Core needs one Check `c_const`, no PIR Claim or
Reduction, Accept guarded directly by `c_const` with that one required Check,
and a final `Always` Reject. Both terminal Claim sets and both required
Reduction sets are empty. `MustWhenTrue(c_const) = {Positive(c_const)}`.
An exact selected profile may instead introduce a fold Claim/Reduction; if so,
each Reduction is unconditional or uses the exact guard of each consumer. A
selected typed-failure source event needs an earlier Abort branch with no
invented positive Check requirement.

The boundary analysis does not enumerate exact refs or choose that failure
guard, so the complete carrier remains `CannotAnswer` pending source
specialization. This is not evidence against the minimal fitting structure.

### 6.2 Finite-fold views and outcomes

| View | Analysis-observable fields |
|---|---|
| `PublicBindingView` | strict/relaxed instances, commitments, degradation counter, scopes and types |
| `StrategyDecisionView` | cross-term polynomial decision, guard, type and prior reads |
| `PublicCoinView` | one bounded challenge, its exact domain/law, correlation and public-coin graph |
| `EffectView` | message, challenge, deterministic typed field-injection `Apply` nodes, constant-coefficient Check, public folded outputs and terminals |
| `ClaimReductionView` | empty in the minimal Core, or the exact selected fold Claim graph |
| `ExecutionView` | interpretation, receipts, record schema and outcome partition |
| family views | canonical construction fields for the separately checked hash-derived variant |

Check true is `Accepted`; check false is `Rejected`; an authored typed failure
is `Aborted`; canonical challenge failure is `InterpretationFailed`; strategy
refusal is `StrategyStopped`; continuation issuance failure and resource or
algorithm failure are `OperationalNoncompletion`. At the degradation maximum,
the current fold may still have accepted; a separately invoked next-step
relation/precondition check can reject. The accepted continuation is a static
endpoint/Plan contract, not another outcome lane
([Endpoint lines 1056-1072](../../../pir/endpoint-projection-views.md#72-exact-static-requirements)).

Finite-fold verdict: **fits**, matching both earlier sources.

### 6.3 Broad cross-system application

The broad motivation supplies neither two exact protocol executions nor a
source-complete imported-challenge contract
([WARPfold Section 4.6, lines 277-288](../semantic-closure-and-freeze/cold-protocol-holdouts/warpfold-boundary-analysis.md#46-crossing-proof-system-boundaries-is-not-a-value-bridge)).
The six normalized views can describe each admitted execution separately, and
the family views can describe a challenge derived within one selected
construction. None carries cross-execution causal state or authority for a
challenge whose semantics are imported from another execution. Likewise, an
individual execution can end in an ordinary PIR lane, but “cross-system
handoff completed” has no `ProtocolOutcomeLane` because no such Protocol exists.

Verdict: **breaks at `B-CROSS-EXECUTION` and `B-IMPORTED-CHALLENGE`**, matching
both earlier sources. Reopening requires an exact composition source naming
both protocols, deciders, encodings, setup/commitment assumptions, imported
challenge authority, and the connecting theorem; the present source does not
supply it.

## 7. Multiparty Sumcheck

The earlier analysis deliberately separates a commitment-anchored virtual
two-role transcript from physical participants who jointly construct messages,
verify locally, hold shares, use correlated randomness, and reason about abort
([Sections 4.1-4.2, lines 138-183](../semantic-closure-and-freeze/cold-protocol-holdouts/multiparty-sumcheck-boundary-analysis.md#4-what-the-frozen-model-can-represent)).

### 7.1 Virtual terminal contract

Let `Q_virtual` contain every selected commitment/opening, recurrence, and final
evaluation Check; let `R_virtual` be the selected Sumcheck Claim chain; and let
`L0` and `L_accept` be its exact live-Claim sets. Reductions and Accept use the
same all-check nested conjunction, followed by the root fallback Reject, with
the same required-set shape as Circle. `MustWhenTrue` proves every member of
`Q_virtual`; the fallback names no required Check. A source-authored malformed
opening may instead take an earlier Abort frontier.

The source record does not publish exact commitment and Claim-table refs, so
that exact carrier remains `CannotAnswer` until source specialization. Its
shape fits.

### 7.2 Virtual views and outcomes

| View | Analysis-observable fields |
|---|---|
| `PublicBindingView` | commitment/sharing anchors, public statement, scopes and types |
| `StrategyDecisionView` | masked sum, each round polynomial, final opening and exact prior reads |
| `PublicCoinView` | common challenge occurrences, domains/laws, correlations, reduction consumers and graph |
| `EffectView` | virtual message/opening/check schedule and terminals |
| `ClaimReductionView` | committed-polynomial Claim and Sumcheck reduction chain |
| `ExecutionView` | Fresh interpretation, receipts, record schema and outcomes |
| family views | only a separately checked transform of the virtual proof |

Virtual success, ordinary false checks, and authored malformed openings map to
`Accepted`, `Rejected`, and `Aborted`; strategy refusal maps to
`StrategyStopped`; unsupported commitment work and resource limits map to
`OperationalNoncompletion`. No virtual mode lacks a lane.

Virtual-proof verdict: **fits**, matching both earlier sources.

### 7.3 Physical protocol boundary

The current Core fixes one Prover and one Verifier, and the durable composition
boundary explicitly leaves multiprover and distributed-verifier knowledge to a
future extension
([Interaction Core Section 14, lines 3382-3401](../../../pir/interactive-core.md#14-composition-and-finite-recurrence-boundary)).
Consequently no faithful physical terminal contract exists: one global guard
cannot establish each participant's local decision or a common-agreement fact.

The six views can expose only the collapsed virtual transcript. They have no
coordinates for participant identities, participant-local views/state, shares,
correlated private randomness, broadcast/delivery, corrupted coalitions, local
terminal decisions, or common-abort agreement. `StrategyStopped` is one Prover
strategy lane, not a participant-indexed abort model. Even if a future
projection mapped globally agreed accept/reject/abort to the three terminal
lanes, selective delivery, decision disagreement, and coalition-controlled
abort presently have no lane.

Verdict: **breaks at `B-MULTIPARTY`**, matching both earlier sources. The named
reopening condition is charter-level inclusion of multiparty security,
threshold/distributed proof generation as a semantic subject, or per-party
implementation-security claims
([analysis lines 260-336](../semantic-closure-and-freeze/cold-protocol-holdouts/multiparty-sumcheck-boundary-analysis.md#6-why-the-boundary-is-intentional-rather-than-a-local-defect)).

## 8. Transparent arguments over Galois rings

The source gives explicit interactive polynomial-commitment, Sumcheck, and
ZeroCheck schedules, but calls a final construction noninteractive without
specifying transcript framing, challenge derivation, retry/failure, or another
compiler
([lines 45-64](../semantic-closure-and-freeze/cold-protocol-holdouts/galois-ring-snarks-boundary-analysis.md#2-source-lock-and-evidence-boundary)).

### 8.1 Interactive terminal contract

For any selected explicit component, let `Q_ring` contain its exact Merkle,
encoding, linear-combination, Sumcheck, ZeroCheck, and final Checks;
`R_ring` its exact commitment and polynomial-interactive-oracle Claim
transforms; and `L0`, `L_accept` its live-Claim sets. Reductions and the
accepting terminal use the same all-check conjunction, followed by the root
fallback, as in the other fitting boundary analyses. The accepting
`MustWhenTrue` proves all
required direct Check literals. A selected partial ring operation may use an
earlier Abort frontier; otherwise failure remains qualified noncompletion.

The source does not select one exact component composition or enumerate its
Core refs. Exact carrier formation is therefore `CannotAnswer` pending source
specialization, while the normalized structure fits.

### 8.2 Interactive views and outcomes

| View | Analysis-observable fields |
|---|---|
| `PublicBindingView` | setup/ring parameters, statement, scopes and exact base/extension types |
| `StrategyDecisionView` | matrices, ring polynomials, claimed combinations, openings and prior reads |
| `PublicCoinView` | random-matrix, ring, and query Challenges, domains/correlations, reduction consumers and graph |
| `EffectView` | messages, logical accesses, Merkle/encoding/ring Checks and terminals |
| `ClaimReductionView` | commitment, Sumcheck, ZeroCheck, Libra, or HyperPlonk Claim transforms selected by the exact profile |
| `ExecutionView` | Fresh interpretation, receipts, record schema and five-lane outcome partition |
| family views | only a separately sourced and checked transcript construction |

Success is `Accepted`; false equations are `Rejected`; an authored partial-
operation or malformed-proof event is `Aborted`; strategy refusal is
`StrategyStopped`; unsupported algorithms and resource limits are
`OperationalNoncompletion`. A Fresh interactive component has no
`InterpretationFailed` lane. If a future, separately sourced canonical
construction is selected, its sampling exhaustion would use that sixth lane.

Interactive-component verdict: **fits**, matching both earlier sources.

### 8.3 Complete noninteractive source claim

The target has coordinates for canonical and duplex transcript declarations,
influence/coverage, transitions, results, and execution. The source supplies no
value that can inhabit either family without importing an independent
construction. Missing source observables are the transcript declaration,
required influence, challenge transition and retry/failure law, checked result,
and complete noninteractive terminal semantics. No complete noninteractive
terminal guard exists for `MustWhenTrue`, and no source-selected Protocol
exists whose outcome lane can be chosen.

Verdict: **breaks at `B-SOURCE-INCOMPLETE`**, matching both earlier sources.
Reopening requires a separate primary source for the exact transform and its
security theorem; adding one would define a new checked construction rather
than prove literal correspondence to the omitted transform
([analysis Sections 5.5 and 7-9, lines 299-310 and 348-416](../semantic-closure-and-freeze/cold-protocol-holdouts/galois-ring-snarks-boundary-analysis.md#55-call-the-interactive-construction-a-noninteractive-snark)).

## 9. Disagreement findings

There are no verdict disagreements. The executable emits one affirmative
comparison finding for each of the eight rows and would emit a row-specific
`CannotAnswer` finding and a nonaffirmative aggregate if any record or matrix
verdict changed.

Two narrower corrections are frozen:

1. The legacy WHIR schedule is refused because its Reduction guards differ
   from their consumers and deterministic scope openings cannot supply another
   guard. The two-terminal carrier above gives both Reductions and Accept the
   exact `G_accept` guard and retains an `Always` fallback. The verdict remains
   fits, while correspondence to the source's earlier fold timing is not
   claimed.
2. The termination-axis meaning now states that canonical interpretation
   failure is a separate completed failure record and outcome lane, never a
   Core terminal
   ([`axes.json`, termination axis](../../../../evaluation/expressibility-axes/axes.json)).
   No case vector, destination, matrix prediction, or holdout verdict changes.

## 10. No owner-page delta

No migrated target section is underdetermined or wrong for this question, so
this note proposes no owner-page change. The four boundary analyses' missing
exact Check, Reduction, Claim, and failure-guard refs are source-profile gaps.
The cross-system, physical multiparty, and complete noninteractive gaps are the
same named boundaries already recorded. The structural-axis correction was a
research-instrument repair, not an owner-page change.

## 11. Nonclaims

The 25-finding result is finite executable evidence over exact document bytes.
It does not establish an admitted Circle, WARPfold, multiparty, or Galois-ring
Core; live implementation correspondence; Plan or Relations correctness;
relation satisfaction; endpoint, OIR, backend, or deployment validity; theorem
truth or applicability; soundness, knowledge soundness, zero knowledge,
Fiat--Shamir security, multiparty security, or production readiness. No passing
row publishes a source profile, changes an owner page, or rotates an identity.

## Round-one handoff (historical)

Files changed:

- `evaluation/formal-source-holdout-readjudication-f0v2c2/README.md`
- `evaluation/formal-source-holdout-readjudication-f0v2c2/adjudication.json`
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`
- `evaluation/formal-source-holdout-readjudication-f0v2c2/expected-findings.json`
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c2-holdout-readjudication.md`
- `checks/manifest.json`
- `evaluation/lifecycle.json`
- `evaluation/README.md`
- `checks/tests/test_evaluation_lifecycle.py`

Validation used `GIT_INDEX_FILE=$PWD/.lane-index` and, because `.git/objects`
is read-only, a clone-local temporary object directory with the repository
object directory configured as a read-only alternate.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `python3 -B checks/run.py validate` | 0 | 0.04 s | manifest valid; 71 checks and 6 tiers |
| `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=$PWD/.lane-uv-cache python3 -B checks/run.py run --tier developer` | 0 | 1.09 s | 8 of 8 checks passed, including lifecycle inventory |
| `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=$PWD/.lane-uv-cache python3 -B checks/run.py run --check research.holdout-readjudication` | 0 | 0.15 s | focused check passed |
| `git diff --check` | 0 | less than 0.1 s | no whitespace errors |

The literal example `GIT_INDEX_FILE=$PWD/.lane-index git add -A` first exited
128 in 0.1 s because Git still attempted to write new blob objects beneath the
read-only `.git`. Repeating index formation with the clone-local object
directory exited 0 in 0.5 s. The temporary index, object directory, and local
`uv` cache were removed after validation; the real index was never changed.

A post-cleanup diagnostic invocation of the lifecycle unit test without the
alternate index exited 1 in 0.2 s and reported exactly the new package as
untracked. The required developer-tier run above used the alternate index and
passed the same lifecycle test; the diagnostic failure is the expected reason
for the brief's alternate-index instruction, not a lifecycle regression.

Aggregate outcome: `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; five fits,
three breaks, zero bends, zero verdict disagreements. Exact terminal carrier
refs remain `CannotAnswer` for the four boundary-analysis fitting rows until a
concrete source profile is selected.

Nonclaims are those of Section 11. In particular, this lane does not claim
owner publication, implementation correspondence, theorem truth, security, or
production readiness.

Surprises and brief corrections:

- the clone does not contain `AGENTS.md` or `.claude/CLAUDE.md`; their primary-
  checkout copies were read read-only, and neither was copied or edited here;
- the workflow asks a finishing lane to append the private status ledger, while
  this brief expressly forbids writes outside the clone and the ledger is
  read-only; this public handoff is provided instead;
- WHIR's previously adequate two-terminal sketch is not adequate under the
  migrated exact-live-Claim rule; and
- the structural-axis description of interpretation failure still reflects
  the pre-migration terminal model, although its holdout verdict predictions
  remain correct.


## Handoff

Main should commit this working tree with subject:

```text
test: rerun the migration text review and correct the holdout carrier
```

Files changed:

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md`;
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md`;
- `evaluation/expressibility-axes/axes.json`, `run.py`, and `README.md`;
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c1-migration-text-review.md`;
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c2-holdout-readjudication.md`;
- `checks/manifest.json`; and
- `evaluation/README.md`.

No owner page, profile manifest, publication table, directory README,
lifecycle entry, lifecycle count pin, real Git index, or private ledger was edited.
No lifecycle count moves because this lane adds no package.

Validation and evidence:

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `git log --oneline -12` and the migration commit diffs | 0 | under 0.1 s each | migration and repair history inspected before editing |
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.64 s | seven affirmative findings, no blocker |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | 25 findings, five fits, three breaks, no verdict disagreement |
| `python3 -B evaluation/expressibility-axes/run.py --check` | 0 | 0.12 s | 18 frozen findings; aggregate unchanged |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.31 s | both compilers reconstructed 18 identities; the review derives the 17-profile cone |
| `python3 -B checks/run.py validate` with the alternate index | 0 | 0.04 s | 74-check manifest valid |
| `python3 -B checks/run.py run --tier developer` with the alternate index and clone-local offline cache | 0 | 1.11 s | eight of eight developer checks passed |
| `python3 -B checks/run.py run --check research.migration-text-review` with the same environment | 0 | 0.69 s | focused review check passed |
| `python3 -B checks/run.py run --check research.holdout-readjudication` with the same environment | 0 | 0.10 s | focused holdout check passed |
| `python3 -B checks/run.py run --check research.expressibility-axes` with the same environment | 0 | 0.19 s | focused axis check passed |
| `git diff --check` | 0 | 0.06 s | no whitespace errors |

The temporary alternate index, object store, and clone-local cache were removed
after validation; the real index was never changed.

Aggregate outcome: the migration review is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`; all four former negatives close.
The holdout aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; the WHIR and axis corrections
change no verdict. Four source-specialized fitting carriers remain
`CannotAnswer` for exact references.

Nonclaims: these passes establish bounded, byte-pinned source-text and
instrument consistency only. They do not publish identities, establish
implementation or backend correspondence, prove relation satisfaction or
theorem truth, establish any security property, validate endpoints or
deployment, or show that delaying the WHIR fold preserves a selected source
semantics.

Surprises: the first developer-tier attempt exited 1 in 0.35 s because listing
the candidate packet files as manifest sources made one check route to two
evaluation packages. Removing those cross-package manifest routes preserved
the runner's direct byte pins and the rerun passed. The alternate index also
needed a clone-local object directory and explicit removal of its transient
lockfile from the index inventory.

Where the brief was wrong: `AGENTS.md` and `.claude/CLAUDE.md` are absent
from this clone, so their read-only primary-checkout copies were used. The
workflow's private status-ledger append conflicts with this lane's express
outside-clone write prohibition and the read-only mount, so status is recorded
here. The example alternate-index command also needs a writable object store
under this mount.
