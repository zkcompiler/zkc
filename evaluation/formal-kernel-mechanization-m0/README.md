# Mechanized Terminal contract over portable terms

This package extends the retained datum, graph, and portable-term
mechanizations with the Terminal admission contract from
`docs-next/pir/interactive-core.md` Section 10. It asks four bounded questions:

1. does the structural `AttemptedWhenever` rule imply earlier attemptedness for
   every valuation of opaque guard atoms;
2. are the facts computed by `MustEnv` sound against the existing evaluator for
   every term in the portable calculus;
3. can the written Terminal contract be decided and independently reconstructed
   on the frozen finite carriers; and
4. what remains undecidable from the owner text without adding semantics?

Run from the repository root:

```sh
ZKC_LAKE=$HOME/.elan/bin/lake \
  python3 -B evaluation/formal-kernel-mechanization-m0/run.py --check
```

The frozen aggregate is
`CannotAnswer/TERMINAL-C-OWNER-TEXT-UNDERDETERMINED`. The universal proof
obligations and the two executable decision paths pass. The aggregate remains
fail-closed because five owner-text choices are not specified, exact holdout
carriers are absent, and retained portable-term evidence still lacks an
independent evaluation oracle.

## Authority and toolchain

Nothing in this package is normative. The Terminal owner text is
`docs-next/pir/interactive-core.md` Sections 6.2--6.4 and 10. The portable term
and evaluator owners remain `docs-next/foundation/executable-foundations.md`.
The package records but does not repair underdetermination, and it edits no
owner page.

The branch cutoff is `975d1e98a61880b800f92efe9c115dd728260113` from
`docs/pir-migration-v2c`. `source-pins.json` authenticates that cutoff and the
owner and predecessor files consumed by the Terminal exporter. The older graph
vector is replayed as a hash-pinned transport because its synthetic profile
overlay now collides with the migrated live manifest; the runner reports that
collision as `CannotAnswer` instead of presenting a stale regeneration as live
evidence.

`lean/lean-toolchain` pins `leanprover/lean4:v4.33.1`. Kernel modules import only
package modules and Lean core. There is no Mathlib, Batteries, Std, VCVio,
ArkLib, `sorry`, declared axiom, or Lake dependency. JSON transport remains
isolated in `Transport.lean`.

## Mechanized statements

`M0/Terminal.lean` adds the following definitions and proofs.

- A finite occurrence schedule records deterministic unguarded scope openings,
  one `Always` or structurally identified opaque guard atom per occurrence, and
  whether an occurrence is terminal. An active terminal stops the path.
  `attemptedWhenever_sound` proves, for an arbitrary schedule, arbitrary guard
  valuation, and arbitrary earlier and later positions, that a later attempted
  occurrence plus the written subset law implies that the earlier occurrence
  was attempted. No truth-table enumeration appears in the statement or proof.
- `MustEnv` is defined on the complete fifteen-constructor portable `Term`
  datatype. It transcribes the authored literal, variable, let, conditional,
  and primitive-call clauses; the ten constructors without an owner clause
  conservatively yield no facts. `mustEnv_sound_evalCore` proves soundness
  against the existing evaluator for every fuel, term, primitive denotation,
  abstract and concrete environment, and successful result. The true and false
  corollaries quantify over every Boolean input assignment, and the impossible
  true region is proved unable to evaluate to true.
- `terminalContractDecision_correct` proves equivalence between an executable
  Boolean decision and the package's direct transcription of the displayed
  required-Check, required-Reduction, and active-path claim clauses.
- A forward abstract claim state splits only at previously unseen guard atoms,
  reuses the value of structurally identical atoms, stops a path at the first
  active terminal, consumes linear reduction inputs, preserves reusable inputs,
  creates outputs, and records the live claims at each terminal.

The forward claim transfer is an experimental finite-carrier interpretation,
not a claimed owner definition. Section 10 names step 9's forward state but does
not define its transfer algorithm locally.

## Frozen carrier results

The exporter normalizes 24 records. Twenty-two are representable by the exact
Terminal decision surface, while two deliberately exercise adjacent admission
boundaries. Lean and an independently structured Python checker agree on all 24
records, including the two `CannotAnswer` classifications.

| Carrier family | Frozen result |
|---|---|
| Exact terminal projection | The positive carrier is admitted and all 15 representable mutations are refused, matching the predecessor package. The `check-abi` and `claim-output-ssa` mutations remain `CannotAnswer` because those laws belong to earlier admission steps, not `TerminalContract`. |
| Five integrated graph carriers | Refused by the newly executed live-claim clause. Claim 0 is reusable, both reductions preserve it while creating claims 1 and 2, and every terminal therefore sees `[0, 1, 2]`; the authored terminal sets omit claim 0. The predecessor graph package reported affirmative without executing this repaired Terminal closure. |
| WARPfold finite-fold shape | The minimal one-check, no-claim shape is admitted by both decision paths. It is shape evidence only because the holdout note does not select exact references, terms, types, or failure guards. |
| Other holdouts | `CannotAnswer`: no exact admitted carrier exists for direct mechanized comparison. The WHIR note relies on a guarded fold-scope opening; the migration record says to replace that sketch with unconditional reductions, but supplies no exact re-authored occurrence, reference, or term carrier. |

The integrated refusal follows the owner rules that reusable claims remain live
through reduction use and must appear in a terminal's exact live-claim set. It
is routed as a predecessor-instrument gap, not as a proposed owner-page change.

## Owner-text underdetermination

The decision package does not fill these points:

- Section 10 lines 1454--1470 supplies transfer clauses for only five of the
  fifteen term constructors. The conservative result for the other ten is
  package-local.
- Lines 1449 and 1492--1494 do not define the initial abstract fact for a
  non-Boolean input; they only say that a non-Boolean binding carries no
  literal.
- Lines 1471--1473 do not say whether a union containing both `Positive(i)` and
  `Negative(i)` normalizes to `Impossible`.
- Lines 1476--1484 place the non-impossible guard test inside the loop over
  required Checks, while lines 1497--1499 say every impossible terminal guard
  is refused. The zero-required-Check case has no unique transcription.
- Lines 1488--1489 and 1506--1509 refer to step 9's forward live-claim state but
  do not close its transfer algorithm in Section 10.

These findings control the aggregate. No default is promoted to owner law.

## Retained evidence

The runner also preserves the prior package layers: canonical encoding and
decoding, graph construction on five integrated carriers, the complete
portable-term carrier and evaluator, exact Schnorr preimage elaboration, 81
finite check results and two guard results, evaluator determinism, completion
monotonicity, and the finite closed Schnorr equation. Their prior
`CannotAnswer` findings remain frozen, including the absence of independent K1
term-evaluation vectors and universal noncompletion result bytes.

## Frozen vectors

| File | Role |
|---|---|
| `terminal-contract.json` | Normalized terminal-projection, integrated, and WARPfold shape records, with source coordinates and predecessor outcomes. |
| `m2-term-calculus.json` | Exact Schnorr preimages, finite evaluator rows, charges, and oracle inventory. |
| `k1-encoding-vectors.json` | Retained canonical K1 oracle bodies and malformed cases. |
| `structural-negatives.json` | Retained malformed encodings. |
| `body-digests.json` | Retained integrated-carrier body digests. |
| `pcgraph-construction.json` | Hash-pinned predecessor graph inputs and finite products. |

## Axioms report

`Axioms.lean` prints every theorem used by the gate. The new closures are:

- `attemptedWhenever_sound`: `propext`;
- `mustEnv_sound_evalCore`: `propext`, `Quot.sound`;
- `must_when_true_sound`: `propext`, `Quot.sound`;
- `must_when_false_sound`: `propext`, `Quot.sound`;
- `impossible_when_true_cannot_evaluate_true`: `propext`, `Quot.sound`;
- `impossible_when_false_cannot_evaluate_false`: `propext`, `Quot.sound`; and
- `terminalContractDecision_correct`: `propext`, `Quot.sound`.

There is no `sorryAx` or native-decision axiom. These are within the package's
pre-existing standard Lean allowance of `propext`, `Classical.choice`, and
`Quot.sound`.

## Cost ledger

Every run emits machine-readable values under `metrics.timings`,
`metrics.lean_line_counts`, and `metrics.axioms`. One warm measured run took
80.096 seconds: 74.297 seconds regenerated the portable-term and Terminal
vectors, 0.411 seconds built Lean, 4.762 seconds ran the executable, and 0.507
seconds printed the axiom report. These are observations from one run, not
stable performance claims.

## Nonclaims

This package does not establish normative semantics, a complete Core admission
checker, exact admission of any cold holdout, general evaluator conformance,
compiler or backend correspondence, runtime correspondence, relation
satisfaction, theorem applicability, protocol soundness, Fiat--Shamir or
random-oracle security, QROM applicability, constant-time behavior, production
readiness, or a decision to adopt Lean as a durable reference twin. The finite
decisions and universal local lemmas are evidence for their stated abstractions
only.
