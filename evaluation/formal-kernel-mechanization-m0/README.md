# Mechanized closed forward state of the Terminal contract

This package asks one exact question: under the pinned Interactive Core text,
does a core-Lean transcription prove the amended must-fact analysis and the
closed `Region`, `Implies`, `Disjoint`, `ClaimStatus`, and `LiveClaims` laws
sound for every schedule and valuation, and does its closed Terminal decision
agree with an independent Python decision on every frozen representable
carrier without `sorry`?

Run from the repository root:

```sh
ZKC_LAKE=$HOME/.elan/bin/lake \
  python3 -B evaluation/formal-kernel-mechanization-m0/run.py --check
```

The frozen answer is `Affirmative/M4-A-FORWARD-STATE-SOUND`.

## Authority and source boundary

Nothing in this package is normative. The owner is
`docs-next/pir/interactive-core.md`, particularly Sections 6.2--6.4 and 10;
the portable term and evaluator owner remains
`docs-next/foundation/executable-foundations.md`. The package changes no owner
page and publishes no semantic identity.

`source-pins.json` fixes migration head
`76f49ec1df3d9b5a241768da2fed8f5d46bd0799`, the current owner text, the
terminal projection and integrated graph findings, the refrozen holdout
findings and adjudication, and retained graph vectors. The historical
integrated exporter still collides with a live manifest definition, so its
already-frozen graph vector is replayed only after digest authentication. That
transport limitation remains an explicit `CannotAnswer` finding.

The project pins `leanprover/lean4:v4.33.1`. Kernel modules import only package
modules and Lean core. There is no Mathlib, Batteries, Std, VCVio, ArkLib,
Lake dependency, declared axiom, or `sorry`. JSON handling remains isolated in
`Transport.lean` and the executable entry point.

## Closed definitions and universal results

`Terminal.lean` transcribes all five owner closures:

- every portable term constructor other than literal, variable, let,
  conditional, and primitive call contributes no literal;
- a non-Boolean input contributes no literal on either Boolean result branch;
- fact union normalizes opposite polarities of one input to `Impossible`;
- non-impossible occurrence region and guard facts form a standalone first
  Terminal clause; and
- the forward state is the closed region and claim-status algebra, with
  `Unknown` refused.

The retained fuel induction against `evalCore` re-proves true- and false-fact
soundness for mixed Boolean and non-Boolean input environments. Both
`Impossible` corollaries follow from those universal results.

For every finite schedule and every opaque-guard valuation,
`attempted_iff_region_holds` proves that an occurrence is attempted exactly
when its positive and negative region literals hold and the region is
possible. `region_impossible_iff_unreachable` proves that `impossible` is
equivalent to absence of any attempted valuation.

For every well-formed claim binding and attempted occurrence,
`claimStatus_live_sound` proves that `Live` means live on every such path, and
`claimStatus_dead_sound` proves that `Dead` means live on none. These are
schedule-parametric theorems, not fixture enumeration. The executable carrier
comparison separately enumerates each finite carrier's guard valuations as an
independent falsification oracle.

`terminalContractDecision_correct` proves the Boolean decision equivalent to
the closed proposition: possible terminal region and guard facts, required
Check and Reduction attemptedness, direct positive Check use, no `Unknown`
claim, and exact `LiveClaims` equality. Sorted-unique lists, input-type arity,
claim-source order, and source existence remain admission-wrapper checks rather
than additions to `TerminalContract`.

## Frozen carrier results

The exporter freezes 29 records. Twenty-seven are representable by the closed
decision and two exact projection mutations intentionally remain outside this
Terminal surface. Lean and the independently structured Python checker agree
on every decision, region flag, claim status, and live-claim list.

| Carrier family | Result |
|---|---|
| Exact Terminal projection | The positive carrier is admitted and all 15 representable mutations are refused, matching the pinned predecessor. Check ABI and claim-output SSA mutations remain `CannotAnswer` because they belong to earlier admission steps. |
| Five integrated graph carriers | All are refused. Claim 0 is reusable, stays `Live`, and is omitted from the authored terminal sets; the predecessor graph check did not execute this closure. |
| WARPfold finite shape | The one-Check, no-claim accepting shape and unconditional fallback are admitted. |
| WHIR finite shape | The five direct Checks, two identically guarded linear reductions, accepting terminal with no live claim, and fallback with the initial claim are admitted. |
| Four controls | Non-Boolean direct-use, contradictory guard, impossible occurrence region, and `Unknown` claim status each refuse at the intended closed clause. |

The two holdout rows are normalized Terminal shapes from the refrozen
adjudication, not complete admitted source Cores. Exact carrier comparison for
Circle STARKs, virtual multiparty Sumcheck, interactive Galois-ring protocol,
and broad cross-system WARPfold remains `CannotAnswer` because those exact
coordinates are absent.

## Frozen artifacts

| File | Role |
|---|---|
| `vectors/terminal-contract.json` | Closed schedules, claim sources and linear consumers, Terminal declarations, controls, source hashes, and predecessor outcomes. |
| `export_terminal_vectors.py` | Deterministic normalization from pinned predecessor and owner evidence. |
| `terminal_checker.py` | Independent Python implementation plus exhaustive finite-valuation falsification. |
| `lean/M0/Terminal.lean` | Core definitions, universal soundness proofs, and proved Terminal decision. |
| `lean/Main.lean` | JSON transport and executable carrier reports. |
| `lean/Axioms.lean` | `#print axioms` inventory consumed by the runner. |
| `expected-findings.json` | Frozen finding names, outcomes, stable codes, checksum, and aggregate. |

The retained value, graph, and finite Schnorr vectors remain part of the same
package and are rechecked unchanged.

## Axioms and cost

The new region, claim-status, must-fact, and decision theorems use at most the
package's existing standard Lean allowance: `propext`, `Classical.choice`, and
`Quot.sound`. The emitted axiom inventory contains no `sorryAx` or native
decision axiom.

Every run records wall times, Lean source line counts, and theorem axiom sets
under `metrics`. These measurements characterize one local run only and are
not stable performance claims.

## Nonclaims

This package does not establish normative semantics, complete Core admission,
exact admission of the holdout protocols, general evaluator or primitive
provider conformance, compiler/backend/runtime correspondence, relation
satisfaction, theorem applicability, protocol soundness, Fiat--Shamir,
random-oracle or QROM security, constant-time behavior, deployment validity,
production readiness, or a decision to adopt Lean as a durable reference
implementation. Universal theorems apply only to the stated abstraction and
their explicit well-formedness premises; finite carrier decisions are bounded
evidence.
