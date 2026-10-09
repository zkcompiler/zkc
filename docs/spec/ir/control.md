# Structured local control

This compiler profile extends [local algorithms](functions.md) with
isolated conditional, finite-variant match and finite-loop regions. It applies inside local functions,
not protocol bodies. Language checks source captures and state results; native MLIR and executable
admission check their explicit representation.

## Formation

The portable records are:

```text
["if", site, condition, captures, then_body, else_body, outputs]
["for", site, induction, lower, upper, carried, captures, body, outputs]
["yield", values]
```

Each carried entry is `[region_argument, initial_outer_value]`. Every continuing
region has one final yield; an explicitly stopped region has no yield. A
continuing function has one final return. The program profile additionally admits
[bounded conditional termination](completion.md#bounded-local-termination)
through `local.condition` and its `for_while` record. Local function early return,
unbounded loops and arbitrary jumps are not admitted. Sites are unique throughout
a function, including both arms and all nested regions. Regions obey the same
source size, depth and value limits as other local instructions.

An `if` condition has type `bool`. Each arm receives only the listed captures,
under their given names. Both arms must form, regardless of the runtime condition,
and yield the same ordered types. Capturing an affine value consumes its outer
binding once; each arm checks its own affine uses. Dropping a value is permitted
by affinity. An outer value needed after the branch must be returned through its
results rather than reused after consumption.

A `for` has two index operands in the same representation. Its body receives the
induction index, ordered carried arguments and explicitly listed invariant
captures. Invariant captures must be duplicable; affine state must use carried
ports. Yield types equal the initial carried types, and outputs have those same
types. No hidden access to the enclosing environment is admitted.

Finite local variants and exhaustive matches follow
[the variant carrier contract](variants.md). Their active payload
arguments are generated on region entry. Only captures are forwarded unchanged
along MLIR region successor edges; the scrutinee is not an operand of the
payload's type.

## Execution

`if` and `match` execute exactly one arm. Both branch typing and source/candidate
correspondence inspect both arms; runtime effects and failures come only from
the selected arm. Execution does not speculate a branch. A terminal stop
propagates out of every enclosing local region and function. No match dispatch
or continuation converts it into a recoverable result value.

`for` evaluates its lower and upper operands once and executes successive indices
in `[lower, upper)`, with unit increments. Upper at or below lower yields the
initial carried state without entering the body. Each completed iteration supplies
the next iteration's carried state. Failure stops immediately, preserving prior
observable effects. Each bound must be at most 1,048,576 in this executable
profile, including an inverted interval. This magnitude limit is deliberately
stronger than a trip-count limit and is not the mathematical meaning of index.

The native machine permits at most 100,000 total entered iterations across
protocol and local loops and 1,000,000 executed instructions. Each executed
operation, conditional, loop, yield and return costs one instruction. Each entered
local region creates a backend child frame and charges its explicit inputs under
the [retained-value ledgers](../runtime/capacity.md#retained-values-and-logical-work):
inputs that share storage with their parent add none. A loop also charges its
induction index. The native runner validates every
backend-created induction value against the installed index representation
before entering the body. An untaken arm or zero-trip body creates
no frame. Region cleanup releases its retained charges, and returned values are
charged at the enclosing result bindings. Physical `release` has no instruction
cost and retains the ghost-accounting rule: released storage stays charged until
region cleanup, although a later allocation at a freed address is new storage.
These are retained-payload charges, not measurements of actual allocator memory
or constant-time execution.

Native local calls and nested regions use the same frame
lifecycle. A body stop remains primary when frame cleanup also fails; cleanup
errors are retained in the actual inner-to-outer order of frame exits. If the
body succeeds but its cleanup fails, the role stops with that backend error;
polling or retrying the consumed local cut cannot execute the body again. Completed
backend transitions are not rolled back by cleanup.

Bound rejection happens before the first body effect. Cumulative iteration or
instruction exhaustion may occur after earlier effects. Deterministic bound
rejection reports `exhausted:local-bound-limit`. Cumulative work exhaustion
retains its machine-limit cause. Comparisons preserve stop class, reached
prefix and resource state instead of identifying all failures with rejection.
Interpreter-work limits are separate.

Helper applications expand recursively before participant projection. Expansion
retains regions and does not unroll loops. Helpers introduce no runtime frames;
entered control regions do. Local origin paths append `["if", site, "then"]` or
`["if", site, "else"]`, and `["for", site, decimal_index]`, preserving the enclosing
call/participant origin. Source identities retain both branches and loop bodies,
including helper definitions reachable only inside a region.

## Analyses and construction

Analyses traverse every branch and retained body, while execution follows only
the chosen path. Exact resource-origin checks preserve actual affine successors
through control; unknown or conflicting origins refuse at the boundary that
requires them. See [resource origins](../../compiler/resource-origins.md).

Native transcript construction applies the selected
[proof policy](../formats/proof.md), including its loop, observation and state-chain
conditions. Local variant admission independently forbids specified history
operations inside matches. Neither structural control admission nor a local
Boolean result proves public transcript schedule safety.

## Formal interpretation and assurance boundary

`Zkc.Source.FiniteControl` treats admitted runtime bounds as a selection from a
family of existing finite `Region.iterate` terms. It proves count/zero/index
properties and reuses the selected branch/iteration denotations. Executable
adapters check bounds before instantiation. No unbounded process constructor is
added. Structural laws for a fixed typed region do not by themselves prove raw
frontend elaboration, candidate decoding or native execution correct.

Independent Lean models and model-specific tools interpret their own region and
carrier contracts. Their correspondence results are separate from the current
native executable. See [implementation and evidence](../../compiler/control.md).

## Explicit local stops

Executable local code spells a stop as `["stop", site, reason]`. Reasons are
`reject`, `abort`, `exhausted`, `incomplete` and `refused`. All are terminal,
including inside a match or called algorithm. They produce no result or invented
yield. Continuing alternatives retain their normal result/resource obligations.

## Conditional completion extension

The native mathematical path also supports [conditional entry completion and
bounded local termination](completion.md). Its executable records have no automatic correspondence to an independent
formal carrier.
