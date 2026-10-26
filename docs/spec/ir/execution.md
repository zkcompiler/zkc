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

## Runtime scope and transfer views

`!runtime.scope` denotes an active execution scope. A function's scope arguments
are borrowed; `runtime.enter_scope` produces an acquired child scope through an
explicit outcome. Entry performs the existing preflight, reservation, backend
entry and body-scope opening. Failed entry acquires no caller cleanup obligation;
a failure after partial acquisition discharges it inside entry.

An entry retains its source site and one origin kind: `function` with the actual
callee, `conditional` with `then` or `else`, `iteration` with its current i64
coordinate, or `match` with the selected alternative. The enclosing executable
reader binds these facts to actual calls, branches and checked bounds. Ordinary
helper expansion and numerical realization do not acquire a frame merely
because a standard function call represents them.

`runtime.exit_scope` consumes an acquired scope and the body's explicit outcome.
For success, it pins returned backing, closes body bindings, and attempts backend
exit in that order. Failed exit releases the hold and withholds the payload.
For a stopped body it closes bindings and appends any failed cleanup to the
existing primary cause. Successful exit returns one
`!runtime.transfer<(T...)>` inside the outcome. Parent binding is separate from
exit; root publication follows its existing reservation contract.

A transfer retains an ordered tuple at one logical or represented stage.
`runtime.borrow_transfer` packages initial values already owned by the parent
without new allocation, retain or frame. `runtime.transfer_values` exposes its
payload while that transfer remains live. `runtime.accept_transfer` binds the
values into the parent before releasing their temporary hold, consuming the
transfer even on refusal. `runtime.release_transfer` consumes it without
publication. Borrowed initial transfers have no temporary pin to release.

`runtime.take_condition` consumes a transfer's leading Boolean and exposes an
ordinary i1 decision plus the remaining transfer. Failed inspection releases
the remaining carry. A loop holds the previous carry until the next body exits
successfully, then releases it before inspecting the new condition. Each failed
body path releases the previous carry before unwinding its parent. CF operand
transport itself creates no retained parent binding.

These types are execution views, not native carrier descriptors or authority
grants. The scope-ownership analysis follows actual `BranchOpInterface` mappings
on flat CFGs, including outcome-produced arguments. It requires matching live
ownership at joins, one consumption of returned or released transfers, no
consumption of borrowed scopes, and no abandoned ownership at return. It checks
every block and refuses graphs exceeding its analysis limit of one million
operations. Scope and transfer types are not MLIR TokenLike types.
Calls use the borrowed-scope contract; executable admission must check every
potential callee. A successful function-local check is not a closure check.

Shape and ownership checks alone do not establish payload-borrow lifetime,
parent/frame nesting, source association, reached operation identity, resource
equivalence, or native correspondence. Those remain obligations of the complete
executable-profile reader and its independent artifact comparison.

## Typed mathematical invocation

`exec.compute` borrows the containing function's first Runtime scope argument,
takes logical mathematical operands, and returns an explicit outcome of the
callee's mathematical results. Its nonempty `site` identifies the occurrence.
A flat `callee` reference names an actual private mathematical `func.func` in
the same symbol table. A single nested reference names the actual public entry
of a sibling named builtin module with the `exec.computation` profile. An
external signature, an outlined execution helper, or a deeper reference is not
a mathematical body. Operands and outcome payload match the actual signature.

Logical ports are total non-affine data, including retained formal polynomial
and quotient values; represented runtime payloads and capabilities are excluded.
An optional `policy` contains the three Boolean mathematical selection choices
in their existing order. It does not change the equation or grant authority.
The operation implements `SymbolUserOpInterface`. Its scope/outcome adaptation
does not satisfy the ordinary `CallOpInterface` data signature; generic call
inlining cannot erase that adaptation.

Operation formation checks the actual target and ports. Its consuming source or
selected-computation profile must separately admit the complete mathematical
closure, discharge actual call preconditions, bind source equations, and compare
the selected realization. None of those obligations follows from formation.
The shared finite-premise checker resolves this actual target and maps its
premise indices to data operands, excluding the scope. A CFG function's declared
premises apply to its original entry arguments. They do not automatically apply
to same-numbered successor arguments, reached guards or successful outcomes.
Realization occurs in the borrowed scope without adding a helper frame. Reached
admission, allocation and first-stop behavior remain ordered execution duties.
The prepared native profile must refuse an unresolved mathematical invocation.

The source-closure admission API checks all immediate scoped and mathematical
definitions, including dormant definitions and selected computation modules.
Selected modules undergo bounded structural verification before typed inspection
and mathematical closure admission. It checks declared entry preconditions and
their discharge at each actual call, then checks logical affine ownership with
private signatures derived from the admitted mathematical bodies. These
temporary signatures are not returned as executable declarations or accepted
from metadata. This admission permits mathematical calls with supported native
logical ports; formal polynomial/quotient invocation ports still require their
own realization. Ordered finite requests use the additional callback closure
checks below. Source-equation correspondence,
candidate comparison and executable extraction remain separate checks.

## Ordered finite requests

`exec.fold` and `exec.collect` retain finite computation before selection. Each
occurrence borrows its containing function's exact entry scope, references an
actual private Data domain and private Func callbacks, and returns one explicit
outcome. Fold data operands are domain arguments, initial state and captures;
collect data operands are domain arguments and captures. The outcome carries
the fold state or the collected value. A zero-state fold still returns an
outcome and retains reached domain checks, callbacks and stops.

Callbacks prepend a borrowed scope to the [finite callback ABI](finite.md#helper-and-operand-abi).
Their single result is an outcome carrying the step state, one collected element,
or the predicate Boolean. A callback can have multiple CFG blocks. The ABI
reader exposes actual entry formals and their ordered partitions; it does not
invent a returned expression or totality claim for that CFG. Binding retains
the supplied scope and distinct formal positions even when actual data aliases.
Declared data preconditions index actual function arguments, including the
scope position. Domain and capture premises are discharged against this
occurrence's actual operands; successor arguments do not inherit entry facts by
position. Exact fixed collection cardinality uses the same actual domain.

Source adapters call the selected ordinary source helper with the borrowed
scope and an explicit `runtime.site`. They package the callback result with
`exec.returned`; this is not a charged region completion. Contextually packed
product items use an actual match with a private identity region, charged
`exec.complete`, scope exit and transfer acceptance. Collected products use
`exec.variant`. Source-array materialization remains a mathematical function
invoked through `exec.compute`. Independent adapter comparison checks these
operations, actual ports, outlined bodies and dispatch edges; it does not
replace ordinary helper-body correspondence or whole-definition admission.
Delegated CFG operations count against the shared source work and operation
limits.

The operations implement `SymbolUserOpInterface`. They have no loop region or
induction argument and do not implement `LoopLikeOpInterface`. Their adapted
callback signatures do not implement ordinary `CallOpInterface`. They advertise
neither purity nor speculation. Total finite mathematics remains in Algebra;
selected ordered control uses standard Func/CF with explicit outcomes.

Formation checks symbols, port partitions, logical type policies and callback
premises. Whole-source admission additionally checks every potential body,
reference cycles, actual outcome dispatch and affine state behavior. The
mathematical result-dependency summary does not describe a scoped outcome.
The transient logical admission view retains actual step/body and predicate
definition edges. Its cycle and control-effect checks follow those edges:
an ordered signature cannot conceal a history transition inside a match.
Every referenced callback must have an admitted body, including callbacks of
empty or dormant requests. These derived views are internal admission data;
they are neither source declarations nor executable implementations.
Unrealized finite requests are excluded from executable extraction. Source
emission, selected realization and their independent comparisons must be
connected before this component replaces the default finite compilation path;
[status](../../status.md) records that migration boundary.

## Scoped native instruction profile

The local execution writer and reconstruction reader connect a bounded Func/CF
profile to the existing native program model. The writer first admits the model,
recovers exact native result types, outlines control bodies and verifies the
emitted CFG and scope ownership. It constructs no body metadata for the reader
to trust. Its caller loads the required native value-type dialects; missing
value types and an excessive outlined definition inventory are checked refusals.
The reader independently inspects actual instructions and edges. A function takes one borrowed Runtime scope
before its native arguments and returns one explicit outcome. Root functions
retain their logical origin in `runtime.origin`; private outlined region bodies
carry a unit `runtime.region` marker. The marker supplies no body or execution
authority: the reader checks the actual callee, arguments and body recursively.
The profile requires `no_inline` and refuses recursive outlining, unconsumed
blocks, unknown operations or attributes, and unchecked region definitions.

`runtime.binding` declares the logical operation contract, static arguments and
selected implementation/physical arguments. Both logical and physical profiles
use this one declaration. Its name is resolved within the actual symbol table;
the declaration alone grants no installed authority, timing permission or
invocation success. Installation still checks the complete potential closure,
and reached execution checks current operands, policy, custody and allowances.
The Func/CF execution writer, reader and independent comparison require no Local
dialect registration.

The standalone API accepts a closed, attribute-free builtin module. The
`readExecutionDefinitions` and `verifyExecutionDefinitions` APIs instead select
one actual symbol table inside an enclosing profile. They inspect every immediate
Runtime binding and Func definition, including dormant roots and outlined bodies;
all direct symbols must be unique before lookup. Calls resolve in that selected
table. Other declarations and enclosing stage/protocol associations remain the
caller's responsibility. These APIs verify the owned operations without invoking
the enclosing operation's region verifier recursively. Acceptance therefore does
not establish formation or admission of the entire enclosing module.

The reached instruction boundaries are:

| Operation | Native obligation |
|---|---|
| `exec.apply` | Tick and invoke the exact binding with its actual parameters and ports, returning the admitted outcome. The declaration owns selection; the call does not duplicate an implementation name. |
| `exec.boolean` / `exec.variant` | Tick, construct and bind an ordinary native value; variant construction uses the exact selected alternative payload. |
| `exec.test` | Tick and inspect the native Boolean before ordinary CF chooses an arm. |
| `exec.range` | Tick and check both native bounds and saturating range length, including empty and inverted ranges, before exposing two i64 counters. |
| `runtime.iteration` | Charge the reached iteration and allocate its native induction value at the current coordinate before child entry. |
| `exec.match` | Tick, inspect the native variant and validate the selected payload before entry. Its branch interface produces the payload or stop and forwards actual captures. |
| `exec.complete` | Perform the native return/yield instruction's tick and expose its exact return-or-stop outcome. Plain `exec.returned` packaging cannot replace this instruction. |
| `exec.reject` | Perform the native stop instruction's tick and expose its actual cause, including a prior tick failure. |
| `runtime.release_bindings` | Release admitted ordinary bindings with the existing no-tick storage accounting. Independent native admission rejects affine release and subsequent reads. |

Conditional and variant arms explicitly acquire a child scope, call their actual
outlined body, exit that scope with the body's exact outcome and accept the
resulting transfer into the actual parent. Their final ordinary branch carries
only those accepted values to the join. Variant payload types have one Data
owner shared by construction, dispatch and the current control consumer.

The loop profile checks actual Arith comparison and increment operands, one-step
advancement, initial borrowing, iteration/callee arguments, the success-only
carry replacement, failure release and final parent handoff. A conditional loop
inspects the newly returned transfer after releasing its predecessor. The false
edge reaches final handoff without another increment or iteration. These checks
reconstruct existing native `for` and `for_while` records; they do not install an
Arith interpreter or give an arbitrary CFG native execution semantics.

Reconstruction admits all returned native definitions and bindings at the
explicit logical or physical stage. It retains physical representations and
checks every potential region body. It rereads current SSA on each invocation;
an earlier successful read is not a cached validation grant. Bounds are 4,096
definitions, 64 active outlined bodies and one million inspected operations,
in addition to independent native model limits.

The local comparison API takes independently admitted native definitions and
compares their records against current actual SSA. It checks exact bindings,
full ports, origins, instructions, occurrences, values and CFG/scope transitions,
including all potential outlined bodies. It follows the expected records without
calling the reconstruction reader or replaying emission. SSA names may change;
operand order, capture association, constants and terminal causes may not.
Every invocation checks current bodies, so prior success grants no mutation cache.
This local boundary does not compare participant, service or entry declarations;
the complete artifact consumer must also check those owners.

Reconstruction and local record comparison remain separate from retained source
correspondence and complete decoded-artifact comparison. A well-formed same-typed arithmetic change yields a different
reconstructed program; binding that program to an earlier source remains the
source comparator's obligation. The [implementation status](../../status.md)
records whether this profile has reached the default compilation path.

## Source scoped helper profile

Before ordinary helper expansion, `readSourceExecutionDefinitions` and
`verifySourceExecutionDefinitions` inspect logical scoped functions in one
selected symbol table. They retain actual `func.call` targets, operands and
`runtime.site` occurrences as internal helper applications. A call borrows the
current function's exact scope and dispatches its explicit outcome; it creates
no child frame. Every potential helper body, including dormant definitions,
is checked, and the internal logical admission checks the complete acyclic
call closure. Standard symbol and function verification alone does not supply
these execution guarantees.

The same source table may also contain plain mathematical `func.func`
definitions. A scope, transfer, stop or outcome in a signature, or a Runtime
origin/region annotation, selects execution checking. Every other immediate
function is checked by the existing total mathematical owner, including dormant
functions and their finite-domain and bound premises. Neither absence nor
presence of an annotation grants admission. The mathematical inventory stays
in the same symbol table, preserving actual helper and domain references;
nested symbol tables remain their enclosing profile's responsibility.

A source helper returns through `exec.returned` followed by `func.return`.
Expansion removes this packaging, so it must not introduce a native return tick.
Outlined conditional, match and iteration bodies retain `exec.complete`: their
yield is an actual native instruction. Entering or publishing a native root
still requires the prepared profile's charged completion. The explicit source
API does not make plain packaging legal in that prepared profile, nor does it
permit unresolved calls in a published native program.

The independent comparison binds the actual callee, occurrence, ordered ports,
returned payload and failure continuation to admitted logical definitions. A
same-typed retargeting can form a different valid source graph while failing
comparison with the earlier graph. Each comparison rereads current SSA.
The returned native structural view contains only scoped definitions. The
comparison also rechecks mathematical admission, but does not bind those
equations to authored source: a different total equation can pass this
component. Language and mathematical correspondence must supply that check.
Mathematical and finite realization requests are not admitted by these APIs;
they need their separate actual-body, port and domain checks. These APIs neither
replace language-source correspondence nor establish the default compiler
cutover. The native record writer is not an authored-source emitter.

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
