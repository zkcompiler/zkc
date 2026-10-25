# Ordered execution and terminal outcomes

Exec owns reached admission and fallible invocation. Data owns ordinary logical
values; Entry owns application selection, public association and deployment
metadata. Standard Func and CF own function and control-flow structure.
The [Entry format](../formats/entry.md#host-control-artifact) defines
publication and the independent executable reader.

## Outcome contract

An execution means `(outcome, residual state, ordered observations)`, where
`outcome` is either `returned(values)` or `stopped(cause)`. Continuing a returned
execution uses its actual residual state and appends observations. Continuing a
stopped execution preserves its cause, residual state and observation prefix;
it does not call the continuation. Cleanup follows the runtime's existing
primary-cause and diagnostic ordering. A returned `false` and a terminal stop
are distinct outcomes.

An adapter to another execution model supplies an interpretation of native
causes into the selected logical stop type and an explicit observation law,
as defined by the [representation contract](../realization/representations.md).
Logical stop equality does not require equality of diagnostic prose. A coarser
observer may omit additional cleanup diagnostics only under that law; it must
retain the primary logical failure, ordered interaction prefix and related
actual post-state, including cleanup's custody effects. The native runtime's
own diagnostic and cleanup contract remains unchanged.

The state and observation journal remain owned by the runtime. An SSA outcome
is interpreted in that actual state; it does not encode a fresh state or turn
live handles into context-free values. Additional resource refusals belong to
the existing [metered refinement](../verification/refinement.md), rather than
unlimited mathematical equality. Source formation checks all potential paths;
reached admission and invocation happen only on the selected path.

## Retained Host profile

A Host `func.func` takes ordinary logical arguments and returns one
`!exec.outcome<(T)>`. A zero-payload successful operation uses `!exec.outcome<>`.
`exec.returned` packs exactly the declared payload. `exec.failed` packs one
`!exec.stop`. `exec.stop` creates a terminal cause, never a Boolean or other
ordinary continuation value.

`func.call`, `exec.numeric`, `exec.invoke`, `exec.require` and `exec.drop` expose
outcomes. `exec.dispatch` eliminates an outcome with two successors: the first
receives its returned payload as block arguments; the second receives exactly
one stop carrier. Both successors have their declared types. The admitted Host
profile propagates every failed edge to one function-local failure block,
which returns `exec.failed`. No handler catches a stop or resumes its suffix.

Ordinary branching uses `cf.cond_br`; loop state uses `cf.br` block arguments.
A loop tests unsigned `index < upper`, invokes the body only on the true edge,
and increments by one after successful completion. Its back-edge carries the
actual body result. An empty loop skips its body. A reached finite descriptor
check before that loop still executes. Sum elimination uses `data.match`, whose
successor arguments are the selected payload followed by the actual captures;
it implements MLIR's branch interface with produced and forwarded operands.

`!data.value<schema>` retains nominal source schemas not represented by the
profile's `i1` and `i64` scalar types. `data.construct`, `data.unpack` and
`data.project` manipulate these logical values. The native mathematical
aggregate carrier and its existing Data operations have their own checked
representation contract; neither carrier is an alias for the other.

No Exec operation advertises purity or speculatability. Memory effects alone
do not describe terminal control, observation order or reached admission.
The selected branch interfaces expose CFG edges; they do not license reordering
an invocation. See the upstream [side-effect rationale](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
and [control-flow interface](https://mlir.llvm.org/docs/Interfaces/#branchopinterface).

## Independent admission

The exporter retains logical signatures and source block shape under Entry
attributes. The reader checks that shape against actual function signatures,
operations, descriptors, symbols, SSA operands, successor arguments and edges.
It verifies the loop predicate, increment and back-edge, complete sum coverage,
and terminal propagation. It consumes the complete block inventory, including
otherwise unreachable blocks. Reordered, inserted or deleted blocks require a
new checked correspondence; this original profile is not an arbitrary CFG
optimizer's equivalence checker.

The reader then compares the recovered functions with checked closed source.
Numerical definitions and child deployment packages have their existing
independent readers. Metadata alone is not executable authority, and the reader
does not replay the exporter. The Rust Host independently admits the one
current `zkc.host/0` executable schema and propagates its terminal failures.

MLIR verification establishes local formation, not source correspondence.
Exec payload and descriptor formation emits `execution-formation`; sum
elimination emits `data-match-formation`. Original admission reports malformed
IR as `target.admission`. A well-formed graph with altered source association
fails `source.correspondence`.
