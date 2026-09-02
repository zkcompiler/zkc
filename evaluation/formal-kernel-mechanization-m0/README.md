# M1 mechanized kernel edges and canonicity

This package extends the M0 spike in place and answers one exact question:

> Can the admitted D1 Core bytes and used semantic-module declarations be
> decoded into all fourteen Core tables and used by core-only Lean 4 to derive
> the complete Section 11 PCGraph products for all five D1 carriers, while
> also proving decoder canonicity, topological-order independence of the class
> fold, and equivalence of a linear minimal-magnitude implementation, and while
> executing the exact `2^20`-octet natural boundary?

Run from the repository root:

```sh
python3 -B evaluation/formal-kernel-mechanization-m0/run.py --check
```

The frozen result is
`Affirmative/M1-A-KERNEL-EDGES-AND-CANONICITY`. The aggregate passes only if
every retained M0 vector, every M1 graph product, all named theorems and axiom
closures, the compiled-Lean boundary execution, and the K1 boundary decision
agree with their frozen expectations. The Section 11 wording gaps remain
explicit `CannotAnswer` findings and do not make the aggregate negative,
because the experiment implements the already selected D1 readings and does
not claim that those readings are uniquely determined by the owner text.

## Authority and toolchain

Nothing in this package is normative. The owner texts remain
`docs-next/foundation/executable-foundations.md` Section 2.1 and
`docs-next/pir/interactive-core.md` Section 11 and Appendix A. The Lean text is
definition and proof text under measurement, and D1 is a bounded comparison
oracle. No target owner page is edited by M1.

`lean/lean-toolchain` pins `leanprover/lean4:v4.33.1`. Kernel modules import
only package modules and Lean core; there is no Mathlib, Batteries, Std,
VCVio, ArkLib, `sorry`, declared axiom, or Lake dependency. JSON transport is
isolated in `Transport.lean`. If the pinned installed toolchain is unavailable,
Lean-dependent findings become `Unsupported/M0-U-LEAN-TOOLCHAIN` and the
frozen gate fails.

## Construction trust boundary

`evaluation/formal-source-integrated-graph-f0v2b2d1/export_m1_vectors.py`
exports, for each D1 carrier, only these construction inputs:

- canonical admitted Core-domain bytes;
- canonical bodies for the semantic-module declarations actually referenced
  by that Core, keyed by exact module reference and local ordinal.

Nodes, edges, Kahn order, class table, sinks, acceptance sinks, private
predecessors, LogicalAccess cones, and acceptance intersections are expected
outputs. They are never supplied to Lean as construction inputs. The committed
`vectors/pcgraph-construction.json` is regenerated and compared byte-for-byte
on every run.

`Core.lean` decodes the fourteen Core tables and the selected module
declarations using the M0 datum decoder. `PCGraph.lean` then constructs items
1--6 of Section 11: producer, scope, binding, guard and activity dependencies;
terminal-preemption control edges; constructor operands; Oracle
publication/Query/Answer edges; occurrence outputs; claim/reduction/terminal
states; and declaration-owned module control/output edges. It derives every
requested downstream product independently before comparing it with D1.

## Stages

| Stage | Checked result |
|---|---|
| Retained M0 basis | 22 canonical bodies still encode and round-trip byte-for-byte; two oracle and 23 crafted noncanonical inputs still refuse. |
| 1. Graph construction | All five carriers decode fourteen Core tables and three used module declarations. Their 91-node sets, 151 or 146 edges, Kahn order, class tables, sinks, acceptance sinks, private predecessors, LogicalAccess cones, and intersections equal D1 exactly. Every carrier exercises terminal-preemption, Oracle Query/Answer, and module edges. |
| 2. Decoder canonicity | `parse_canonical`: `parse fuel b = some (d,r) -> encode d ++ r = b`, and its complete-input corollary `decode_canonical`, both with no `sorry`. The strict parser performs the byte-for-byte re-encoding check required by Foundation Section 2.1 lines 94--97. |
| 3. Order independence | `class_fold_topological_order_independent`: for any two rank functions whose dependencies are strictly earlier, the recursively defined class folds are equal. `classFoldByRank_solves` connects each fold to the exact transfer equations, and uniqueness follows by well-founded induction. |
| 4. Magnitude and boundary | The accumulator-based magnitude performs linear list work. `magnitude_eq_quadratic` proves equality with the retained M0 recursive-right-append reference. The compiled Lean executable constructs a natural with a `1,048,567`-octet magnitude, obtains a complete `1,048,576`-octet encoding, and observes `encodeChecked` acceptance. |
| 5. K1 decision | `_magnitude_size` charges nine octets for naturals and ten for signed integers. The compact frozen oracle recipes contain one natural exactly at the bound (`Completed`) and one crossing by one octet (`Malformed`); reference and independent-oracle tests expand and check both. `M0-C-NAT-BYTE-BOUND` is therefore resolved as `M1-A-S5-M0-NAT-BYTE-BOUND-RESOLVED`. |
| 6. Cost and axioms | `Axioms.lean` prints every relied-on theorem. The gate permits only `propext`, `Classical.choice`, and `Quot.sound`, and records build, execution, export, proof-report, and total timings plus per-file line counts. |

## Mechanized statements

The retained encoder-side theorem is `parse_encode`: strict parsing of a
well-formed encoding with enough fuel returns the same datum and exact
remainder. Its corollaries retain decoder round-trip, injectivity, and prefix
freedom.

M1 names the structural recursion `parseRaw` and makes `parse` the
specification's strict parse-plus-re-encoding check. `parse_canonical` extracts
the exact requested remainder law from every successful strict parse;
`decode_canonical` adds the empty-remainder and constitutional-limit boundary
and concludes `encode d = b` for every accepted complete input.

For classes, `Transfer.dependencies` enumerates every coordinate read by each
transfer. `classFoldByRank` recursively evaluates those dependencies under an
arbitrary topological rank. `classFoldByRank_solves` proves that the resulting
function satisfies every transfer equation. A well-founded induction shows
that two complete solutions agree at each node, yielding equality of folds
for any two topological ranks. This theorem is general over the abstract
finite-index transfer graph; the five D1 comparisons separately establish
that the executable array fold and graph construction reproduce those exact
carriers.

For magnitudes, `magnitudeQuadratic` retains the M0 reference. `magnitudeCore`
conses low octets into an accumulator, and exact powers of 256 use the direct
one-followed-by-zeroes form so the constitutional edge is executable.
`magnitude_eq_quadratic` proves that both paths produce the same bytes.

## Frozen vectors

| File | Role |
|---|---|
| `k1-encoding-vectors.json` | Twelve canonical K1 oracle bodies, two malformed oracle bodies, skipped-case accounting, and the compact positive/negative natural-bound recipes. |
| `structural-negatives.json` | Twenty-three Foundation Section 2.1 malformed encodings, each also refused by K1 during export. |
| `body-digests.json` | Digests for five D1 profiled Core and five `PublicCoinView` bodies regenerated before use. |
| `pcgraph-construction.json` | Canonical Core/module input bytes and frozen D1 expected graph products for five carriers; edge tables are outputs only. |

The K1 compact recipe file is
`evaluation/k1-executable-foundations/oracle/cases/natural-byte-bound.json`.
It avoids committing multi-megabyte decimal and hexadecimal lines while still
freezing the input magnitude size and complete expected outcome.

## Section 11 `CannotAnswer` findings

M1 implements the D1 reading but cannot derive the following coordinates or
precedence uniquely from the current owner prose:

- `M1-C-S11-CHALLENGE-DEPENDENCY-ORDER`: lines 1490--1493 say "first failed
  dependency" without fixing positional order versus lattice priority. D1
  gives `Invalid` global priority. The fifteen carrier Challenges do not
  distinguish the readings.
- `M1-C-S11-PUBLIC-QUERY-COORDINATE`: lines 1486--1489 say a Public Query uses
  `Join(activity,index)` but do not state explicitly that this transfer is on
  the Query effect node and intentionally ignores the publication-effect
  incoming edge. M1 uses the D1 effect-node reading.
- `M1-C-S11-VERIFIER-MESSAGE-COORDINATE`: the same lines name a deterministic
  Verifier message but do not explicitly place `Join(activity,inputs)` on its
  output node, whose inputs are incoming to the effect node. M1 uses D1's
  output-node placement and named-coordinate read.
- `M1-C-S11-LOGICAL-PUBLICATION-COORDINATE`: line 1486 names an "Oracle
  publication output", but a LogicalAccess publication has no occurrence
  output. M1 applies `Publish(activity)` to the publication-effect node, as D1
  does.
- `M1-C-S11-PUBLIC-QUERY-SINK-COORDINATE`: lines 1508--1511 name a "public
  Query index" without enumerating whether the Query activity/effect is also a
  public-observation sink. M1 retains activity, effect, and index producer as
  D1 does.

These are wording findings against exact sections and line numbers, not owner
page edits. Missing wording evidence is not converted into an affirmative
claim.

## Cost ledger

The machine-readable ledger is emitted under `metrics.timings`,
`metrics.lean_line_counts`, and `metrics.axioms` on every run. A warm local M1
run builds, executes all five large carriers plus the million-octet Lean
boundary, and prints axioms in roughly ten seconds; the exact measured values
in the current run artifacts are authoritative for that run. K1's complete
131-test gate is recorded separately because it exercises the full K1 package,
not just M1's boundary probe.

The material implementation cost is one Core/module decoder, the complete
graph/product derivation, a proof-oriented rank fold, a canonicity guard and
proof, and the linear magnitude path. Per-file code and comment line counts
remain in the gate output instead of being copied into a drifting prose total.

## What a pass does and does not establish

A pass establishes only that, under the pinned Lean toolchain:

- the named definitions and proofs elaborate without `sorry` or nonstandard
  axioms;
- the exact five D1 carriers produce equal finite graph products from canonical
  Core/module bytes; and
- the exact K1 and Lean boundary vectors have the frozen outcomes.

A pass does not establish normative owner semantics, uniqueness of the D1
reading where the wording findings remain, arbitrary-Core correctness,
correspondence with compiler/C++/backend behavior, semantic-module host
conformance, relation satisfaction, theorem applicability, protocol
soundness, Fiat--Shamir security, random-oracle or concrete-sponge security,
QROM applicability, constant-time behavior, production readiness, or a
decision to adopt Lean as a durable reference twin.
