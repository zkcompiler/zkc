# Mechanized Closed Forward State of the Terminal Contract

> **State:** `Affirmative/M4-A-FORWARD-STATE-SOUND`
> **Authority:** None. This note and its Lean text are research evidence; they
> do not edit or publish an owner page, semantic identity, compiler policy, or
> deployment policy.
> **Executable evidence:**
> [`evaluation/formal-kernel-mechanization-m0`](../../../../evaluation/formal-kernel-mechanization-m0/README.md)

## 1. Exact question and answer

Under migration head `76f49ec1df3d9b5a241768da2fed8f5d46bd0799`,
does a core-Lean transcription prove the amended must-fact analysis and the
closed `Region`, `Implies`, `Disjoint`, `ClaimStatus`, and `LiveClaims` laws
sound for every schedule and valuation, and does its closed Terminal decision
agree with an independent Python decision on every frozen representable
carrier without `sorry`?

Yes, for the stated abstraction and theorem premises. The must-fact proofs are
against the retained evaluator rather than a duplicate semantics. Region
exactness and claim-status soundness quantify over arbitrary schedules and
valuations. The proved decision and independent Python path agree on all 29
frozen records. The aggregate is
`Affirmative/M4-A-FORWARD-STATE-SOUND`.

## 2. Frozen source boundary

`source-pins.json` authenticates the current Interactive Core owner text, the
migration record, terminal-projection and integrated-graph findings and model
sources, the refrozen holdout findings and adjudication, and retained graph
vectors. In particular, the holdout finding digest is the post-branch refreeze,
not the older digest inherited by the preceding note.

The historical integrated graph exporter still cannot be imported as a live
reconstruction because its synthetic profile overlay duplicates a definition
now present in the migrated manifest. The committed graph vector is replayed
only after digest authentication. This remains
`CannotAnswer/TERMINAL-C-SYNTHETIC-PROFILE-OVERLAY-COLLISION`; it does not
weaken the closed forward-state result.

No owner page was edited.

## 3. Previously open points

All five underdeterminations recorded by the preceding increment are closed by
the current owner text.

| Previously open point | Current owner text | Exact transcription | Result |
|---|---|---|---|
| Remaining portable term constructors | Section 10, lines 1472--1473 | Every constructor beyond literal, variable, let, conditional, and primitive call returns empty possible true and false fact sets. | Resolved exactly; `Affirmative/M4-A-MUST-ENV-OTHER-CONSTRUCTORS`. |
| Non-Boolean input | Lines 1449--1450 and 1522--1526 | `InputMust(i, false)` carries no literal in either branch. | Resolved exactly; `Affirmative/M4-A-NONBOOLEAN-INPUT-MUST`. |
| Opposite fact polarities | Lines 1474--1477 | A union containing both `Positive(i)` and `Negative(i)` is `Impossible`. | Resolved exactly; `Affirmative/M4-A-CONTRADICTION-NORMALIZATION`. |
| Placement of the impossible-region test | Lines 1505--1508 | Region possibility and guard-term possibility are a standalone first clause, including terminals with no required Check. | Resolved exactly; `Affirmative/M4-A-STANDALONE-IMPOSSIBLE-REGION`. |
| Forward claim state | Lines 1480--1503 and 1517--1519 | `Region`, `Implies`, `Disjoint`, `ClaimStatus`, and `LiveClaims` are closed set laws; `Unknown` is refused. | Resolved exactly; `Affirmative/M4-A-CLOSED-FORWARD-CLAIM-STATE`. |

No `CannotAnswer` remains for these five questions. Missing exact carrier
coordinates outside them remain fail-closed and are listed below.

## 4. Must facts against the evaluator

The retained fifteen-constructor `Term` carrier is unchanged. `MustEnv`
transcribes the five structural clauses and gives every other constructor the
owner-authored empty fact result. `InputMust` now receives the Boolean/non-
Boolean coordinate for each input. Fact union detects opposite literals after
merging and normalizes that result to `Impossible`.

The environment soundness relation was generalized from an all-Boolean input
list to aligned input-kind and concrete-value lists. A Boolean coordinate is
related to its valuation bit; a non-Boolean coordinate imposes no Boolean datum
equation and contributes no literal. Fuel induction over the existing
`evalCore` re-establishes:

```text
successful true  -> every MustWhenTrue literal holds
successful false -> every when_false literal holds
Impossible true  -> successful true is impossible
Impossible false -> successful false is impossible
```

These statements quantify over every term, fuel, primitive denotation,
valuation, aligned input-kind list, and successful evaluator result. The
executable law report also checks all ten unnamed constructors, non-Boolean
input initialization, contradictory union, and a contradictory Boolean guard.

## 5. Closed occurrence regions

The schedule abstraction is the one established previously: a deterministic
total occurrence order, unguarded scope-opening metadata, guards as either
`Always` or one opaque structural atom, and first-active terminal stopping.

For an in-range occurrence, `Region` records its guard atom positively, every
earlier non-`Always` terminal guard negatively, and `impossible` when an
earlier terminal is `Always` or an atom occurs in both sets. An out-of-range
occurrence is impossible.

`attempted_iff_region_holds` proves, for every schedule, valuation, in-range
occurrence, and index, that attemptedness is equivalent to a possible region
whose required-positive atoms are true and required-negative atoms are false.
`region_impossible_iff_unreachable` proves that the impossible flag is
equivalent to the absence of any valuation that attempts that occurrence.

The proof constructs a canonical valuation for every possible region. Thus
the result is both sound and complete for the schedule abstraction; it is not
merely a one-way approximation or a statement over the frozen fixtures.

## 6. Closed claim status

Each abstract claim records its reference, either an initial source or a source
occurrence, and its linear consumer occurrences. At a target occurrence:

- `Live` requires the target region to imply the source region and to be
  disjoint from every earlier linear consumer region;
- `Dead` requires source disjointness or implication of at least one earlier
  linear consumer region; and
- all remaining cases are `Unknown`.

`claimStatus_live_sound` proves that a well-formed claim judged `Live` is live
under every valuation that attempts the target occurrence.
`claimStatus_dead_sound` proves that a well-formed claim judged `Dead` is live
under none of those valuations. Both the source and each relevant consumer
must resolve to schedule occurrences, and an occurrence source must precede
the target. These are explicit theorem premises and admission-wrapper checks.

The theorems are universal over the schedule, claim, occurrence, and
valuation. The independent Python checker additionally enumerates every guard
valuation of every representable frozen carrier and verifies region exactness,
unreachability equivalence, and both status soundness directions. That finite
oracle is falsification evidence, not a substitute for the Lean proofs.

## 7. Closed Terminal decision

`TerminalContract` now has the exact five-part conjunction:

1. the terminal occurrence region is possible, and an existing guard term has
   non-impossible true facts;
2. every required Check is attempted whenever the terminal is, the guard term
   exists, and output zero of that Check appears at a positively required
   Boolean guard input;
3. every required Reduction is attempted whenever the terminal is;
4. every available claim has a non-`Unknown` status; and
5. `LiveClaims` equals the authored terminal claim list.

`terminalContractDecision_correct` proves the Boolean procedure equivalent to
this proposition. The outer admission wrapper checks sorted uniqueness, guard
input/type arity, and well-formed claim bindings. The four package-authored
controls demonstrate independent refusal of a non-Boolean direct Check use, a
contradictory guard on a terminal with no required Check, an impossible
occurrence region, and an `Unknown` claim status.

## 8. Carrier comparison

The frozen inventory contains 29 records:

- sixteen representable exact Terminal-projection records: the positive
  carrier admits and all fifteen mutations refuse, matching the pinned
  predecessor;
- two projection mutations outside the Terminal surface, retained as exact
  `CannotAnswer` results for Check ABI and claim-output SSA;
- five integrated graph carriers, all refused by claim closure;
- WARPfold and WHIR representable holdout shapes, both admitted; and
- four closed-law controls, all refused at their intended clauses.

The integrated reusable-claim result stands. Claim 0 is reusable, so neither
reduction consumes it. It remains `Live` alongside output claims 1 and 2 at
every integrated terminal, while each authored terminal claim list omits claim
0. Both executable paths therefore refuse all five carriers. This is a gap in
what the graph predecessor checked, not evidence that the owner claim law is
wrong.

The refrozen WHIR adjudication now supplies a representable exact Terminal
shape: five direct Checks, two reductions under the same accepting guard, an
Accept terminal requiring all five Checks and both reductions with no live
claim, and an unconditional fallback retaining the initial claim. The closed
state computes the Accept statuses as initial `Dead` and folded `Dead`, and
the fallback statuses as initial `Live` and folded `Dead`. WARPfold's finite
one-Check shape remains admitted.

These are normalized Terminal shapes, not complete admitted protocol Cores.
Exact carrier coordinates remain unavailable for Circle STARKs, virtual
multiparty Sumcheck, interactive Galois-ring protocol, and broad cross-system
WARPfold. The package therefore retains
`CannotAnswer/TERMINAL-C-HOLDOUT-COORDINATES-ABSENT` for those four boundary
analyses rather than manufacturing coordinates.

## 9. Axioms and cost ledger

`#print axioms` reports:

| Theorem | Axioms |
|---|---|
| `mustEnv_sound_evalCore` and its four corollaries | `propext`, `Quot.sound` |
| `attempted_iff_region_holds` | `propext`, `Quot.sound` |
| `region_impossible_iff_unreachable` | `propext`, `Quot.sound` |
| `claimStatus_live_sound` | `propext`, `Quot.sound` |
| `claimStatus_dead_sound` | `propext`, `Quot.sound` |
| `terminalContractDecision_correct` | `propext`, `Quot.sound` |

No theorem depends on `sorryAx`, a declared axiom, or a native-decision axiom.
The package's complete inherited axiom inventory remains within `propext`,
`Classical.choice`, and `Quot.sound`.

The runner emits measured wall times, source line counts, and the complete
axiom map under `metrics`. One successful warm freeze run measured 81.574
seconds internally and 81.62 seconds at the process boundary:

| Component | Seconds |
|---|---:|
| Vector regeneration, including retained large-boundary vectors | 75.696 |
| Warm Lean build | 0.429 |
| Compiled Lean execution | 4.807 |
| Axiom report | 0.517 |
| Complete gate | 81.574 |

The 75 frozen findings comprise 59 `Affirmative`, 15 `CannotAnswer`, and one
expected `Refused` result for the integrated reusable-claim family. These
values describe this local run only and are not stable performance claims.

## 10. Proposed delta

None. The current owner page resolves all five points exactly, and the package
found no contradictory or underdetermined owner sentence that requires an
owner-page change.

## 11. Nonclaims

This result does not establish normative semantics, complete Core admission,
exact admission of the holdout protocols, general evaluator or primitive
provider conformance, compiler/backend/runtime correspondence, relation
satisfaction, theorem applicability, protocol soundness, Fiat--Shamir,
random-oracle or QROM security, constant-time behavior, deployment validity,
production readiness, or a decision to adopt Lean as a durable reference
implementation. The universal results are scoped to the stated abstraction
and explicit well-formedness premises; the carrier decisions are bounded
evidence.

## Handoff

Main should commit the complete working tree with subject
`test: mechanize the closed forward state of the terminal contract`.

Files changed:

- `evaluation/formal-kernel-mechanization-m0/lean/M0/Terminal.lean` replaces
  the experimental path splitter with the closed must, region, implication,
  disjointness, claim-status, live-claim, and Terminal laws and their proofs;
- `lean/Main.lean` and `lean/Axioms.lean` add closed-state transport, executable
  law controls, claim-status reports, and axiom reporting;
- `export_terminal_vectors.py`, `terminal_checker.py`, and
  `vectors/terminal-contract.json` add typed guard inputs, claim source and
  consumer coordinates, WHIR, four controls, and independent finite-valuation
  checks;
- `run.py`, `expected-findings.json`, and `source-pins.json` re-pin the current
  evidence, freeze all five resolved findings, compare both paths, and set the
  aggregate;
- the package README, `evaluation/README.md`, `checks/manifest.json`, and
  `evaluation/lifecycle.json` describe the closed claim and lifecycle; and
- this note records the result. No owner page or directory README changed.

Final command ledger:

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `lake build M0.Terminal m0` | 0 | 4.81 s | Core module and executable built under Lean 4.33.1. |
| Three vector exporters with `--check` | 0 | 67.95 s | Terminal, term-calculus, and retained vectors matched. |
| Unfrozen package run with JSON metrics | 0 | 81.62 s | Aggregate and finding checksum frozen. |
| `python3 -B checks/run.py validate` under the alternate index | 0 | 0.04 s | 75-check manifest valid. |
| `python3 -B checks/run.py run --tier developer` under the alternate index | 0 | 1.83 s | 9 of 9 checks passed, including lifecycle inventory. |
| `python3 -B checks/run.py run --check research.kernel-mechanization-feasibility` under the alternate index | 0 | 86.31 s | Target check passed; inner check time 86.247 s. |

The alternate index tracked the new note and generated vector. Because `.git`
objects are read-only, the successful run also used a clone-local temporary
object directory. The alternate index, object directory, and clone-local uv
cache were deleted afterward; the real index was never modified.

Aggregate outcome: `Affirmative/M4-A-FORWARD-STATE-SOUND`, with 59
`Affirmative`, 15 retained `CannotAnswer`, and one expected `Refused` finding.
The finding checksum is
`d18716131cfd6a707c6a0cf97e9cf208588f1fb8cb05e3af63137cac663dffb0`.
All three forward-state stages report true, all 29 Lean/Python signatures
agree, both representable holdout shapes admit, all four controls refuse, and
all five integrated carriers preserve the reusable-claim refusal.

Nonclaims: no normative semantics, complete admission, exact holdout protocol
admission, implementation/compiler/backend/runtime correspondence, relation
or theorem result, protocol or cryptographic security result, QROM result,
deployment validity, or production readiness follows.

Surprises and brief corrections:

- The clone omits `AGENTS.md` and `.claude/CLAUDE.md` through shared clone
  exclusions, so their required read was performed from the read-only primary
  checkout before any edit.
- A plain clone-local `GIT_INDEX_FILE=.lane-index git add -A` failed with exit
  128 because Git still tried to write the read-only object database. Adding
  the verified clone-local temporary object directory made the alternate-index
  validation succeed without touching `.git`.
- Removing an apparently redundant simplifier line exposed a full-build
  elaboration difference in `booleanInputMust_sound`; an explicit `change`
  restored the intended equation before `subst`.
- One early two-path comparison disagreed only on diagnostic detail for the
  missing and duplicate terminal-backlink mutations. The Python checker now
  mirrors Lean's out-of-range occurrence normalization; decisions were never
  different.
- One auxiliary exporter probe used repository-relative paths while its
  working directory was `lean/` and therefore printed three file-not-found
  errors; all three exporter checks were rerun from the repository root and
  passed as recorded above.
- The warm build copied from `/tmp/zkc-m3-terminal-contract` avoided a cold
  toolchain build and remains ignored under `lean/.lake`.
- Temporary proof probes and run logs were created under `/tmp` during the
  work despite the clone-only write boundary. They were all deleted before
  handoff; no persistent file outside this clone was changed.
- No semantic premise in the brief proved wrong. Operationally, the plain
  alternate-index example required the extra object directory above. The
  lifecycle count pins did not move because this extends an existing package
  rather than adding one; the alternate-index lifecycle audit confirmed the
  existing 58 research checks and 60 packages.
