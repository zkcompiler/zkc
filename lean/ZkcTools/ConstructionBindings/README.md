# Source connection tools

`Generate` prints connections selected by declaration names through the shared
`Root`, `LibraryBuilder`, `Alignment`, input and readback tools. The maintained
SmallSumcheck and TwoSums connections live under
`ZkcExamples.Structured.Generated.Connections`; both roles use the same admitted
source and generic finite certificate engine. Generated syntax is a proposal.
The kernel checks the complete `SourceConnection.Connected` boundary, including
full return values, malformed input rows and independent reached-route coverage.
Family mathematics and property receipts remain separate consumers.

At internal applications, `Alignment` proposes a finite typed return selection
by substituting omitted components with absence in the actual continuation.
The kernel checks that the continuation syntax is unchanged. The shared
`ConnectionReturnProjection.bind_continuation` theorem composes the projected
successful leaves with that caller, retaining every operation and stop. Selected
components still require physical readback; complete root returns and the
independent route judgment use their original contracts. The mechanism supports
finite partial selections as well as fully ignored returns, and does not inline
ordinary callee templates or assume author-supplied semantic equations.

Reusable target bodies live in `ConnectionTargetPlacement`. A `Placement`
records the exact typed arguments, caller layout, symbolic frames, occurrence
context, return selection, actual instruction prefix and physical extent. A
`CheckedBody` is indexed by an exact `ConnectionLibrary.Entry`; its alignment
and extent are ordinary checked derivations. Define a family parameterized by
the placements it supports and register its constant with
`@[connection_target_body]`. Parameters may include typed readbacks and finite
route equalities. They must not require the proposer to construct another
alignment or checked body.

`Alignment` tries registered families at both existing application constructors.
It checks exact source-entry identity separately from the instantiated form,
matches every placement field, solves interface checks, and supplies projections
of the family application for `bodyCertificate` and `physicalExtent`. The
declaration value is referenced, without copying its body derivation. Existing
admission, continuation, history and root consumers still perform their checks.
`CheckedBody.prependCalculation` composes an admitted total auxiliary calculation
using the existing computation and readback rules.

This is parameterized checking, with explicitly admitted placement families;
there is no automatic transport of every existing closed alignment. In particular,
logical input aliases require valid typed readbacks and writes must preserve the
caller prefix. A different operation schedule or nominal domain needs a family
that actually proves it. Failed family discovery falls back to the original
exact-placement prover by default. Set
`set_option zkc.connection.requireReusableBodies true` to refuse that fallback
at applications, as the placement tests and cost experiments do. Failure means
the proposer has no admitted family, not that the semantic proposition is false.

The focused suites are `Tests.ConnectionTargetPlacement`,
`Tests.ConnectionTargetPlacementRoots`, `Tests.ConnectionTargetPlacementHistory`
and `Tests.ConnectionTargetPlacementControls`. `Tests.ConnectionPlacementMetrics`
audits generated declaration values and separates proposal from synchronous
declaration checking. The driver uses cached package outputs, builds no
dependencies and defaults to a small sharing check. Run the package build first.
A full exploratory matrix is explicit, from the repository root:

```sh
python3 lean/checks/check_target_placement_cost.py \
  --records build/experiments/target-placement \
  --sizes 1 4 16 --counts 1 2 4 8 --repetitions 3 --baseline-control --measure-memory
```

Proposal/kernel timings exclude imports and final serialization; concurrent
timings are exploratory. `--measure-memory` uses GNU time for each Lean
process peak RSS (including imports). Source/candidate syntax bytes and generated
module/object-file sizes are recorded separately; these are not native-export
byte sizes. Peak RSS is independent of the proposal/kernel timing split.

The experiment varies target-body size independently, includes two exact source
callees, and records shared-family references and embedded derivation constructors.
Its pure calculation fixtures normalize to empty returns; they measure proof
assembly, not GKR mathematics, actual native compilation or complete-root scaling.
`--baseline-control` additionally audits the original exact-placement declarations
with family discovery disabled. Its unrestricted cut discovery may distribute
pure target operations differently, so it is a structural control rather than
a matched timing baseline.

`Analysis` retains static source-call and SSA metadata for Sumcheck derivation
accounting. It imports no family source printer and supplies no semantic
connection. `Frames` supplies syntax-only repeat descriptors for tooling checks.

The core connection inventory is `Tests.ConnectionGeneration.selections`.
Regenerate it from the prepared core package:

```sh
lake env lean --run checks/RunGenerators.lean connections /tmp/zkc-connections
```

`checks/check_constructed_views.py` also schedules
`checks/check_connection_layout.py`. The latter prints fresh constructed views
and generic connections for both roles after inserting a pure SSA result into
the real SmallSumcheck callback. It checks changed yields, invalid candidate
arity/references, complete certificates and strict axiom/dependency audits.
It can be run independently from the prepared core package:

```sh
lake env python3 checks/check_connection_layout.py --records /tmp/zkc-connection-layout
```

The security controls `OriginalPairExecution`, `OriginalProducerBinding` and
`SourceReading` consume the maintained generated roots. `ConnectionABI` checks
both roots and roles at the generic return boundary; `ConnectionMetadata` keeps
the accounting metadata controls; `ConnectionRetirementAudit` checks assumptions,
shared connection facts and absence of retired route dependencies.
