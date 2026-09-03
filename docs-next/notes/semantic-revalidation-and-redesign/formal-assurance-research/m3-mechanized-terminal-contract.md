# Mechanized Terminal Contract and Must-Fact Analysis

> **State:** `CannotAnswer/TERMINAL-C-OWNER-TEXT-UNDERDETERMINED`;
> universal local proofs and both executable paths pass, one predecessor
> family is refused by the newly executed claim-closure rule, and five
> owner-text choices remain unspecified
> **Authority:** None. This research result neither edits nor publishes PIR,
> Foundation, a source profile, or a semantic identity.
> **Executable evidence:**
> [`evaluation/formal-kernel-mechanization-m0`](../../../../evaluation/formal-kernel-mechanization-m0/README.md)

## 1. Question and result

Can core-only Lean transcribe the Terminal contract in Interaction Core
Section 10, prove the first-active and must-fact implications for arbitrary
inputs rather than a sampled oracle, decide the resulting finite contract, and
reconstruct the frozen predecessor and holdout results through two executable
paths without filling owner-text gaps?

The local proof answer is affirmative:

- `AttemptedWhenever` is sound for every valuation of opaque structural guard
  atoms;
- `MustEnv` facts are sound against the existing portable-term evaluator for
  every term, fuel, primitive denotation, and successful evaluation, including
  symmetric true and false regions and both impossible-region corollaries; and
- the Boolean Terminal decision is proved equivalent to the transcribed
  proposition.

The finite comparison answer is mixed. Lean and an independently structured
Python checker agree on all 24 normalized records. The exact terminal
projection admits its positive carrier and refuses all 15 representable
mutations, exactly matching its predecessor. The minimal WARPfold finite-fold
shape is admitted. The five integrated graph carriers are refused because
their reusable initial claim remains live but is absent from every authored
terminal claim set. Two projection mutations and the exact holdout carriers
lie outside the available decision coordinates.

The aggregate is `CannotAnswer` because Section 10 leaves five choices without
a unique mechanized reading. The package records those boundaries and uses
conservative local behavior only where soundness permits it.

## 2. Frozen source boundary

The work starts from exact head
`975d1e98a61880b800f92efe9c115dd728260113` of
`docs/pir-migration-v2c`. `source-pins.json` authenticates the migrated owner
text; the terminal-projection, integrated-graph, and holdout predecessor
records; their reconstruction sources; and the retained graph vectors.

The live integrated graph exporter cannot be imported on the migrated branch:
its historical synthetic profile overlay repeats the now-live
`pir.body-compiler/source-purpose-role-body-v0` definition. The runner freezes
this as
`CannotAnswer/TERMINAL-C-SYNTHETIC-PROFILE-OVERLAY-COLLISION` and replays the
committed graph vector only after authenticating its digest. A stale synthetic
overlay is not described as live regeneration.

No owner page is modified. The proof text is an experiment over pinned source,
not semantic authority.

## 3. First-active execution

The abstraction contains a total finite occurrence schedule, deterministic
unguarded scope openings as occurrence metadata, either `Always` or one opaque
atom naming a complete structurally authenticated `EvaluateBoolean` guard
body, and a terminal marker that stops the run when active. Repeated atoms have
structural identity and share one valuation. Scope openings add no attempt
guards, matching owner lines 1427--1435.

`Attempted` means that the occurrence exists, its guard holds, and no earlier
active terminal stopped execution. `AttemptedWhenever` is the exact order and
guard-subset condition from lines 1437--1442.

`attemptedWhenever_sound` quantifies over the schedule, valuation, earlier
position, and later position. Every guard of the earlier occurrence holds
because it is also a guard of the later occurrence, and any terminal earlier
than the earlier occurrence is also earlier than the later occurrence. This is
a theorem for every valuation; no truth-table enumeration, SAT solver, or
external oracle occurs in the statement or proof. The frozen finding is
`Affirmative/TERMINAL-A-FIRST-ACTIVE-UNIVERSAL`.

## 4. Must facts over the portable calculus

The analysis is defined directly on the retained fifteen-constructor `Term`
datatype. It transcribes the owner clauses for Boolean literals, de Bruijn
variables, call-by-value let binding, conditionals using union and meet, and
primitive calls that contribute no literal.

The owner gives no clause for the ten remaining constructors. The experiment
returns the empty possible fact set for each. This can lose precision but
cannot invent a fact, and is explicitly package-local.

`mustEnv_sound_evalCore` is proved by induction on evaluator fuel against the
actual retained `evalCore`, not a duplicate semantics. It is universal over
the term, concrete and abstract environments, primitive denotation, and
successful result. The initial Boolean environment pairs input ordinal `i`
with `InputMust(i)`. Its corollaries establish:

```text
evaluation returns true  -> every literal in when_true holds
evaluation returns false -> every literal in when_false holds
when_true = Impossible   -> evaluation cannot return true
when_false = Impossible  -> evaluation cannot return false
```

All statements quantify over every Boolean input assignment. The frozen
finding is `Affirmative/TERMINAL-A-MUST-FACT-SOUND`.

## 5. Decision and independent reconstruction

`TerminalContract` is represented as three finite clauses:

1. every required Check satisfies `AttemptedWhenever`, the terminal has a
   guard term, its true region is not impossible, and one direct guard input is
   output zero of that Check with the corresponding positive must literal;
2. every required Reduction satisfies `AttemptedWhenever`; and
3. every active-path live-claim set equals the authored terminal claim set.

The admission wrapper also checks that each authored reference list is
strictly increasing, reflecting the earlier sorted-unique boundary.
`terminalContractDecision_correct` proves the Boolean decision equivalent to
the proposition and freezes
`Affirmative/TERMINAL-A-DECISION-CORRECT`.

The two paths share only normalized JSON. Lean parses each schedule, builds the
portable guard terms, computes the forward abstract claim state, and runs the
proved decision. `terminal_checker.py` independently implements guard
splitting, claim transfer, must facts, and the Terminal clauses in Python. They
agree on decisions and active live-claim sets for all 24 records, freezing
`Affirmative/TERMINAL-A-TWO-PATH-AGREEMENT`. This is implementation diversity
over finite carriers, not an independent proof of owner law.

## 6. Carrier comparison

### 6.1 Exact terminal projection

Sixteen records are inside the Terminal decision surface: one positive carrier
and 15 mutations. The positive terminal live-claim sets are `[1]`, `[2]`, and
`[2]`. Both paths admit it. Every mutation is refused and each outcome matches
the pinned predecessor, freezing
`Affirmative/TERMINAL-A-PROJECTION-COMPARISON`.

The predecessor also has `check-abi` and `claim-output-ssa` mutations. The
first belongs to the earlier Core typing step, and the second to the earlier
claim-source/output bijection. Neither is a `TerminalContract` coordinate.
They freeze as
`CannotAnswer/TERMINAL-C-CHECK-ABI-AND-CLAIM-SSA-OUTSIDE-SURFACE`.

### 6.2 Five integrated graph carriers

The integrated source declares claim 0 reusable and claims 1 and 2 as reusable
reduction outputs
(`evaluation/formal-source-integrated-graph-f0v2b2d1/model.py`, lines
957--975). Its reductions consume claim 0 only if linear; because it is
reusable, claim 0 remains live while claims 1 and 2 are created. Interaction
Core lines 804--808 and 830--834 require exactly that behavior.

Every active terminal therefore sees `[0, 1, 2]`. The integrated terminal
declarations author `[1, 2]` or `[2]` (`model.py`, lines 1076--1127).
Interaction Core lines 916--922 require the terminal set to equal all live
claims, reusable claims included. All five carriers are consequently refused
by both paths.

The pinned graph predecessor reports affirmative because it never executed the
repaired terminal live-claim closure. The result is frozen as
`Refused/TERMINAL-R-INTEGRATED-REUSABLE-CLAIM-LIVE`. This is an
evaluation-instrument gap to route to Main, not evidence for changing owner
text.

### 6.3 Holdouts

The WARPfold note supplies a minimal finite shape: one direct Check, an Accept
guarded by it, a final `Always` Reject, and no claims or reductions (holdout
readjudication lines 257--269). That shape is admitted by both paths, freezing
`Affirmative/TERMINAL-A-WARPFOLD-SHAPE`.

It is not an exact admitted WARPfold carrier. The same lines leave exact refs,
types, terms, and the failure guard to source specialization. Circle STARK,
virtual Sumcheck, and interactive Galois-ring components likewise have no
exact carrier in the readjudication. WHIR's proposed carrier additionally puts
occurrences inside a scope opened by `G_fold` (lines 135--151), whereas the
migrated owner makes scope openings deterministic and unguarded (owner lines
1427--1435). The migration record, lines 163--170, says to re-author that
sketch with unconditional reductions, but does not supply an exact replacement
occurrence schedule, references, guard terms, or claim table. The package does
not silently choose those coordinates. Exact holdout comparison therefore freezes
`CannotAnswer/TERMINAL-C-HOLDOUT-COORDINATES-ABSENT`.

## 7. Exact CannotAnswer boundaries

| Frozen finding | Owner lines | Why no unique mechanized reading exists |
|---|---|---|
| `TERMINAL-C-MUST-ENV-CONSTRUCTORS-UNDEFINED` | 1454--1470 | Clauses exist for variables, Boolean constants, lets, conditionals, and primitive calls, but not for ten constructors in the admitted portable `Term` datatype. |
| `TERMINAL-C-NONBOOLEAN-INPUT-MUST-UNDEFINED` | 1449 and 1492--1494 | `InputMust(i)` is stated without an input type; later prose says a non-Boolean binding carries no literal but does not define its complete `MustResult`, including impossible regions. |
| `TERMINAL-C-CONTRADICTION-NORMALIZATION-UNDEFINED` | 1471--1473 | Union and meet are defined, but no rule says whether a fact set containing both polarities for one input becomes `Impossible`. |
| `TERMINAL-C-IMPOSSIBLE-GUARD-PLACEMENT` | 1476--1484 and 1497--1499 | The displayed non-impossible test is inside the loop over required Checks, while prose refuses every impossible terminal guard. A terminal with zero required Checks separates the readings. |
| `TERMINAL-C-FORWARD-STATE-TRANSFER-NOT-CLOSED-HERE` | 1488--1489 and 1506--1509 | The contract references step 9's forward state, but Section 10 does not close path splitting, claim creation, linear consumption, reusable retention, invalid paths, and terminal stopping. |

The experiment chooses empty facts for unspecified constructors because that
is sound, transcribes the displayed impossible test literally, and uses an
explicit forward transfer only for finite carriers. None is asserted as owner
law. No owner delta is proposed.

## 8. Claim-closure experiment

The optional forward abstract state is implemented and exercised. It splits a
path only on the first occurrence of a structural guard atom, reuses that
decision on later identical guards, applies claim transfers on active
reductions, and removes an active terminal path from further execution.

For every finite represented carrier, the decision checks all recorded active
live-claim sets against `terminal_claims`. This establishes executable
claim-closure results for those carriers. It is not a universal theorem that
the package-local forward state is the owner's intended step-9 algorithm; that
point remains the exact `CannotAnswer` above.

## 9. Axioms and cost

The new theorem closures reported by `#print axioms` are:

| Theorem | Axioms |
|---|---|
| `attemptedWhenever_sound` | `propext` |
| `mustEnv_sound_evalCore` | `propext`, `Quot.sound` |
| `must_when_true_sound` | `propext`, `Quot.sound` |
| `must_when_false_sound` | `propext`, `Quot.sound` |
| `impossible_when_true_cannot_evaluate_true` | `propext`, `Quot.sound` |
| `impossible_when_false_cannot_evaluate_false` | `propext`, `Quot.sound` |
| `terminalContractDecision_correct` | `propext`, `Quot.sound` |

There is no `sorryAx`, declared axiom, or native-decision axiom. The project
uses core Lean only under `leanprover/lean4:v4.33.1`.

One warm full run measured 80.096 seconds:

| Component | Seconds |
|---|---:|
| portable-term and Terminal vector regeneration | 74.297 |
| warm Lean build | 0.411 |
| compiled Lean execution | 4.762 |
| axiom report | 0.507 |
| complete gate | 80.096 |

The final 71 findings contain 49 `Affirmative`, 21 `CannotAnswer`, and one
`Refused` result. Timings are observations, not stable performance claims.

## 10. Nonclaims and routing

This result does not establish normative semantics, complete Core admission,
exact admission of any cold holdout, general evaluator conformance, source or
runtime implementation correspondence, compiler/backend correctness, relation
satisfaction, theorem applicability, protocol soundness, Fiat--Shamir,
random-oracle or QROM security, constant-time behavior, deployment validity, or
production readiness.

There is no owner-page conclusion to record in the delta ledger. The
integrated reusable-claim refusal and obsolete synthetic profile overlay are
evaluation/instrument findings for Main to reconcile when selecting durable
successors.
