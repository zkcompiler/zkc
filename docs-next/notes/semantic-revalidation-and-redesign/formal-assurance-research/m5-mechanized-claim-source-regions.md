# Mechanized Claim-Source Regions of the Terminal Contract

> **State:** `Affirmative/M5-A-CLAIM-SOURCE-REGIONS-SOUND`
> **Authority:** None. This note and its Lean text are research evidence; they
> do not edit or publish an owner page, semantic identity, compiler policy, or
> deployment policy.
> **Executable evidence:**
> [`evaluation/formal-kernel-mechanization-m0`](../../../../evaluation/formal-kernel-mechanization-m0/README.md)

## 1. Exact question and answer

At migration head `5105247d1b7aeebd67bb26a6dce2191cd4b9e034`, does
the repaired Section 10 law give exact, mechanizable regions to initial-Claim
and Reduction-output sources, preserve universal `Live` and `Dead` soundness,
and reproduce the frozen Terminal carriers through independent Lean and Python
paths without `sorry`?

Yes, for the resolved-source abstraction and its explicit well-formedness
premises. Lean proves deterministic boundary-region exactness for every guard
valuation and proves that `Live` holds on every path reaching the target while
`Dead` holds on none. The two executable paths agree on all 33 records. The
aggregate is `Affirmative/M5-A-CLAIM-SOURCE-REGIONS-SOUND`.

## 2. Frozen source boundary

`source-pins.json` authenticates only the two owner pages and the raw package
inputs used to reconstruct retained carriers. It contains no pin to another
package's `expected-findings.json` and no research-note digest. In particular,
the holdout rows are read from
`evaluation/formal-source-holdout-readjudication-f0v2c2/adjudication.json`, not
from that package's frozen findings.

The initial-Claim transport carries the binding, its resolved scope, and that
scope's resolved opening. The Reduction-output transport carries the Reduction
and output ordinals plus the resolved `ApplyReduction` occurrence. The Lean
law then operates on those resolved coordinates. Full Core table lookup and
reference-admission correctness remain outside this package; the package does
not silently replace them with a new authority.

The historical integrated graph exporter still cannot be imported live
because its synthetic profile overlay duplicates a definition now in the
migrated manifest. The package authenticates and replays its retained graph
input and keeps
`CannotAnswer/TERMINAL-C-SYNTHETIC-PROFILE-OVERLAY-COLLISION`.

No owner page was edited.

## 3. Exact transcription

The owner clauses are at Interactive Core lines 1495--1536 on the pinned head:

```text
BoundaryRegion(Initially) = empty possible region
BoundaryRegion(BeforeOccurrence(o)) = negative guards of earlier terminals
ClaimSourceRegion(InitialClaim(binding)) = boundary of binding scope opening
ClaimSourceRegion(ReductionOutput(r, k)) = Region(ApplyReduction(r))
```

The `BeforeOccurrence(o)` boundary does not include `o`'s own guard. Scope
opening is deterministic and unguarded: execution reaches that boundary after
all earlier terminals have remained inactive, before testing the named
occurrence. `ClaimStatus`, `LiveClaims`, and `TerminalContract` are restated
over the repaired `ClaimSourceRegion` exactly as lines 1512--1536 require.

For diagnostic comparison only, the executable also computes the rejected
coercion that maps `BeforeOccurrence(o)` to `Region(o)`. That value is reported
as `occurrence_coercion_status`; no contract decision or aggregate consumes it.

## 4. Universal proofs

`boundary_reached_iff_boundary_region_holds` proves for every schedule,
valuation, and opening that the boundary is reached exactly when its region
holds. For `Initially` both sides are unconditional. For
`BeforeOccurrence(o)`, both sides require every earlier guarded terminal to be
false and reject any earlier unconditional terminal. The named occurrence's
guard is absent from both sides.

`claimSourceRegion_holds_iff_exists` then proves for every well-formed resolved
source that source existence is equivalent to its source region: boundary
reachability for an initial Claim and attemptedness of the resolved
ApplyReduction occurrence for a Reduction output.

`claimStatus_live_sound` takes an attempted target and a well-formed claim.
For an initial source, target attemptedness reaches every no-later scope
boundary. For a Reduction source, the region implication transports target
attemptedness back to the resolved earlier ApplyReduction occurrence. Every
earlier linear consumer region is disjoint from the target region, so none can
have executed. The source therefore exists and remains unconsumed on every
valuation reaching the target.

`claimStatus_dead_sound` handles both owner alternatives. If target and source
regions are disjoint, source existence contradicts target attemptedness. If
the target region implies an earlier linear consumer region, that consumer is
attempted and the claim cannot remain live. Thus a `Dead` claim is live on no
valuation reaching the target.

These proofs quantify over arbitrary schedules and guard valuations. The
finite carrier oracle described next is an independent falsifier, not their
proof basis.

## 5. Independent finite reconstruction

The Python path enumerates every valuation of each carrier's opaque guard
atoms. For each valuation it executes occurrences in order, opens every listed
scope at its unguarded boundary, and stops at the first active terminal. It
then checks independently:

- occurrence attemptedness exactly matches `Region`;
- boundary reachability exactly matches `BoundaryRegion`;
- source existence matches `ClaimSourceRegion`;
- a `Live` result is live on every path reaching the target;
- a `Dead` result is live on none; and
- the closed Terminal result matches the separately compiled Lean path.

All six checks hold for every representable carrier and both paths have equal
signatures on all 33 records.

## 6. Repair discriminators

Four direct records isolate every source-region arm and relevant boundary
shape:

| Record | Reaching paths | Repaired result | Comparison result |
|---|---:|---|---|
| Root scope opening `Initially` | one per terminal | Initial claim is `Live` on every reaching path. | Same under the comparison. |
| Child scope before an unguarded occurrence | one per terminal | Initial claim is `Live` on every reaching path. | Same under the comparison because the occurrence has no guard. |
| Child scope before a guarded occurrence | 2 | Initial claim is `Live` on 2 of 2 paths. | Rejected occurrence coercion is `Unknown`. |
| Guarded Reduction output and later guarded consumer | 1 per terminal | At the guarded terminal the linear output is `Dead` and the reusable output is `Live`; at fallback both are `Dead`. | Same source arm; no boundary coercion applies. |

The guarded child-scope row is the exact semantic discriminator. Its binding
exists before the named occurrence's guard is tested, whether that guard later
holds or fails. `BoundaryRegion` therefore makes the source unconditional on
both paths reaching the later terminal. `Region(o)` would incorrectly add the
named guard and leave the status `Unknown`.

## 7. Retained carrier outcomes

The previous 29 records retain their verdicts:

- the positive Terminal projection admits and all fifteen representable
  mutations refuse; its two adjacent non-Terminal mutations remain
  `CannotAnswer`;
- all five integrated graph carriers remain refused because reusable claim 0
  is live but absent from the authored terminal claim sets;
- the normalized WARPfold and WHIR Terminal shapes remain admitted; and
- all four closed-contract controls remain refused at their intended clauses.

Adding the four source-region records brings the inventory to 33. The guarded
child-scope status changes from the diagnostic pre-repair coercion's `Unknown`
to the repaired law's `Live`; it is a new discriminator, not a changed verdict
among the previous frozen records.

Exact Check, Reduction, Claim, guard-input, and occurrence coordinates remain
absent for Circle STARKs, virtual multiparty Sumcheck, interactive Galois-ring
protocol, and broad cross-system WARPfold. The package therefore retains
`CannotAnswer/TERMINAL-C-HOLDOUT-COORDINATES-ABSENT` rather than manufacturing
carriers.

## 8. Axioms and cost ledger

`#print axioms` reports:

| Theorem | Axioms |
|---|---|
| `boundary_reached_iff_boundary_region_holds` | `propext`, `Quot.sound` |
| `claimSourceRegion_holds_iff_exists` and its forward corollary | `propext`, `Quot.sound` |
| `claimStatus_live_sound` | `propext`, `Quot.sound` |
| `claimStatus_dead_sound` | `propext`, `Quot.sound` |
| `terminalContractDecision_correct` | `propext`, `Quot.sound` |

No theorem depends on `sorryAx`, a declared axiom, or a native-decision axiom.
The complete inherited inventory remains within `propext`,
`Classical.choice`, and `Quot.sound`.

One successful warm unfrozen run measured 80.080 seconds internally:

| Component | Seconds |
|---|---:|
| Vector regeneration, including retained large-boundary vectors | 74.245 |
| Warm Lean build | 0.419 |
| Compiled Lean execution | 4.765 |
| Axiom report | 0.512 |
| Complete gate | 80.080 |

The 78 frozen findings comprise 62 `Affirmative`, 15 retained
`CannotAnswer`, and one expected `Refused`. Their checksum is
`f4a08f735b54ba9697f792be5be3c169921c0005e66c621efdfd935cd689b6ae`.
These timings characterize one local run only.

## 9. Brief correction and proposed delta

The brief requested a positive initial Claim in a child scope that opens
`Initially`. Interactive Core lines 578--580 and 592--596 say that scope 0 is
the unique root opening `Initially`, every other scope opens before an
occurrence, and root is the only initially due scope. Such a child scope is
therefore not an admitted Core case. The package uses the root for the
`Initially` arm and child scopes for the two `BeforeOccurrence` arms.

No owner-page delta is proposed. The repaired Section 10 clauses are precise
for this abstraction, and the fourth review round's seven questions reproduce
without a contradiction.

## 10. Nonclaims

This result does not establish normative semantics, complete Core admission,
binding-to-scope or Reduction-to-occurrence resolver correctness, exact
admission of holdout protocols, general evaluator or primitive-provider
conformance, compiler/backend/runtime correspondence, relation satisfaction,
theorem applicability, protocol soundness, Fiat--Shamir, random-oracle or QROM
security, constant-time behavior, deployment validity, production readiness,
or a decision to adopt Lean as a durable reference implementation. Universal
results are scoped to the stated abstraction and explicit well-formedness
premises; finite decisions are bounded evidence.

## Handoff

Main should commit the complete working tree with subject
`test: mechanize the claim-source regions of the terminal contract`.

Files changed:

- `evaluation/formal-kernel-mechanization-m0/lean/M0/Terminal.lean` adds the
  exact boundary and resolved source regions and re-proves universal claim
  soundness;
- `lean/Main.lean` and `lean/Axioms.lean` add source-coordinate transport,
  comparison reporting, and the expanded axiom inventory;
- `export_terminal_vectors.py`, `terminal_checker.py`, and
  `vectors/terminal-contract.json` add independent boundary/source checks and
  four direct discriminators;
- `run.py`, `expected-findings.json`, and `source-pins.json` remove
  cross-package finding and note pins, freeze the new checks, and set the
  aggregate;
- the package README, `checks/manifest.json`, and
  `evaluation/lifecycle.json` describe the repaired claim-source boundary; and
- this note records the result. No owner page, profile manifest, directory
  README, or other evaluation package changed.

Final command ledger:

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `lake build M0.Terminal m0` | 0 | 3.00 s | Core module and executable built under Lean 4.33.1. |
| Unfrozen package run | 0 | 80.08 s internal | Aggregate and finding checksum observed. |
| `python3 -B checks/run.py validate` under the alternate index | 0 | 0.05 s | 76-check manifest valid. |
| `python3 -B checks/run.py run --tier developer` under the alternate index | 0 | 1.90 s | 9 of 9 checks passed, including lifecycle inventory. |
| `python3 -B checks/run.py run --check research.kernel-mechanization-feasibility` under the alternate index | 0 | 81.32 s | Target check passed; inner check time 81.259 s. |

The alternate index tracked every intended file while leaving the real
read-only index untouched. The clone-local temporary object directory, index,
and UV cache were removed after validation.

Aggregate outcome: `Affirmative/M5-A-CLAIM-SOURCE-REGIONS-SOUND`, with 62
`Affirmative`, 15 retained `CannotAnswer`, and one expected `Refused` finding.
All 33 Lean/Python signatures agree, all four source-region discriminators
pass, and the previous 29 verdicts are unchanged.

No commit, push, pull request, owner-page edit, or delta-ledger block was made.
The private lane register was appended with this completion status as the
workflow requires. Main owns any later checkpoint and integration update.
