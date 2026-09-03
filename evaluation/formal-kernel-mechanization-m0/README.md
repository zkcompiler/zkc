# Mechanized claim-source regions of the Terminal contract

This package asks one exact question: under the pinned Interactive Core text,
does a core-Lean transcription prove the repaired `BoundaryRegion`,
`ClaimSourceRegion`, `ClaimStatus`, and `LiveClaims` laws sound for every
schedule and guard valuation, while retaining the previous Terminal decision
and agreeing with an independent Python path on every frozen representable
carrier without `sorry`?

Run from the repository root:

```sh
ZKC_LAKE=$HOME/.elan/bin/lake \
  python3 -B evaluation/formal-kernel-mechanization-m0/run.py --check
```

The frozen answer is `Affirmative/M5-A-CLAIM-SOURCE-REGIONS-SOUND`.

## Authority and source boundary

Nothing in this package is normative. The owner is
`docs-next/pir/interactive-core.md`, particularly Sections 4.4 and 10; the
portable term and evaluator owner remains
`docs-next/foundation/executable-foundations.md`. The package changes no owner
page and publishes no semantic identity.

`source-pins.json` fixes migration head
`5105247d1b7aeebd67bb26a6dce2191cd4b9e034`, the two owner pages, and only the
raw inputs needed to reconstruct the retained carriers. It does not pin any
other package's `expected-findings.json` and does not pin a research note.
Holdout outcomes and shapes are read from that package's adjudication input,
not from its frozen findings. The historical integrated exporter still
collides with a live manifest definition, so its already-frozen graph vector
is replayed only after digest authentication. That transport limitation
remains an explicit `CannotAnswer` finding.

The project pins `leanprover/lean4:v4.33.1`. Kernel modules import only package
modules and Lean core. There is no Mathlib, Batteries, Std, VCVio, ArkLib,
Lake dependency, declared axiom, or `sorry`. JSON handling remains isolated in
`Transport.lean` and the executable entry point.

## Repaired source-region model

The mechanization resolves each source reference before applying the owner
law:

- `BoundaryRegion(Initially)` is possible and contains no literals;
- `BoundaryRegion(BeforeOccurrence(o))` contains only the negative guards of
  earlier terminal occurrences. It deliberately omits `o`'s own guard;
- an `InitialClaim(binding)` uses the opening of the binding's scope; and
- a `ReductionOutput(r, output)` uses `Region(o_r)`, where `o_r` is the
  occurrence of `ApplyReduction(r)`.

`ClaimStatus`, `LiveClaims`, and `TerminalContract` are restated over this
`ClaimSourceRegion`. A separate diagnostic computes the rejected occurrence
coercion for comparison only; it is not part of the contract or aggregate.

For every schedule and valuation,
`boundary_reached_iff_boundary_region_holds` proves exactness of both boundary
forms, and `claimSourceRegion_holds_iff_exists` lifts that equivalence to both
resolved claim-source forms. `claimStatus_live_sound` proves that a
well-formed claim judged `Live`
is live on every path reaching the target occurrence, and
`claimStatus_dead_sound` proves that one judged `Dead` is live on none. A
Reduction source must resolve to its earlier ApplyReduction occurrence. An
initial source must resolve to the deterministic opening of its binding's
scope. These are universal theorems, not fixture enumeration.

The owner text permits only the root scope to open `Initially`. The direct
carriers therefore cover the root initial boundary, child scopes opening
before an unguarded occurrence and before a guarded occurrence, and Reduction
outputs consumed at later guarded terminals. A child scope opening `Initially`
would fail Core scope-tree admission and is not fabricated as a positive
carrier.

## Retained Terminal results

The retained must-fact proof is still against the M2 evaluator. Region
exactness, first-active soundness, the closed Terminal decision, and its
standard-axiom report remain checked. The Python path independently enumerates
all guard valuations for each finite carrier and checks occurrence-region,
boundary-region, source-region, `Live`, and `Dead` exactness or soundness before
comparing its Terminal result with Lean.

The exporter freezes 33 records: the previous 29 plus four direct
claim-source-region discriminators. Thirty-one are representable by the closed
decision; two exact projection mutations remain outside this Terminal surface.

| Carrier family | Result |
|---|---|
| Exact Terminal projection | The positive carrier admits and all 15 representable mutations refuse, matching the pinned predecessor. Check ABI and claim-output SSA mutations remain `CannotAnswer` because they belong to earlier admission steps. |
| Five integrated graph carriers | All remain refused. Claim 0 is reusable, stays `Live`, and is omitted from the authored terminal sets. |
| WARPfold finite shape | The one-Check, no-claim accepting shape and unconditional fallback remain admitted. |
| WHIR finite shape | The accepting and fallback terminals retain their previous statuses and remain admitted. |
| Four closed-contract controls | Non-Boolean direct use, contradictory guard, impossible occurrence region, and `Unknown` claim status each refuse at the intended clause. |
| Four source-region discriminators | Root `Initially`, child-before-unguarded, child-before-guarded, and consumed Reduction-output cases all admit. The guarded child claim is `Live` on both reaching paths under `ClaimSourceRegion`; the rejected occurrence coercion says `Unknown`. |

No verdict among the previous 29 records changes. The guarded child-scope
discriminator isolates the semantic repair: its source exists before the
named occurrence's guard is evaluated, so the repaired law says `Live`, while
the pre-repair occurrence coercion incorrectly imports that guard and says
`Unknown`.

The two holdout rows are normalized Terminal shapes, not complete admitted
source Cores. Exact carrier comparison for Circle STARKs, virtual multiparty
Sumcheck, interactive Galois-ring protocol, and broad cross-system WARPfold
remains `CannotAnswer` because exact coordinates are absent.

## Frozen artifacts

| File | Role |
|---|---|
| `vectors/terminal-contract.json` | Schedules, resolved claim sources, consumers, Terminal declarations, controls, source hashes, and predecessor outcomes. |
| `export_terminal_vectors.py` | Deterministic normalization from pinned owner and raw package inputs. |
| `terminal_checker.py` | Independent Python implementation plus exhaustive finite-valuation falsification. |
| `lean/M0/Terminal.lean` | Core definitions, universal soundness proofs, and proved Terminal decision. |
| `lean/Main.lean` | JSON transport and executable carrier reports. |
| `lean/Axioms.lean` | `#print axioms` inventory consumed by the runner. |
| `expected-findings.json` | Frozen finding names, outcomes, stable codes, checksum, and aggregate. |

The retained value, graph, and finite Schnorr vectors remain part of the same
package and are rechecked unchanged.

## Axioms and cost

`boundary_reached_iff_boundary_region_holds`,
`claimSourceRegion_holds_iff_exists`, `claimStatus_live_sound`, and
`claimStatus_dead_sound` use only `propext` and `Quot.sound`. The complete
inherited package remains within `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or native-decision axiom.

The frozen result contains 78 findings: 62 `Affirmative`, 15 retained
`CannotAnswer`, and one expected `Refused`. Its checksum is
`f4a08f735b54ba9697f792be5be3c169921c0005e66c621efdfd935cd689b6ae`.
Every run records wall times, Lean source line counts, and theorem axiom sets
under `metrics`; these measurements characterize one local run only.

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
