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
