# Structured local control

This compiler profile extends [local algorithms](local-algorithms.md) with
isolated conditional, finite-variant match and finite-loop regions. It applies inside local functions,
not protocol bodies. The readable frontend infers captures and state results;
portable source, native MLIR and independent admission check them explicitly.

## Formation

The portable records are:

```text
["if", site, condition, captures, then_body, else_body, outputs]
["for", site, induction, lower, upper, carried, captures, body, outputs]
["yield", values]
```

Each carried entry is `[region_argument, initial_outer_value]`. Every continuing
region has one final yield; an explicitly stopped region has no yield. A
continuing function has one final return. Early return,
break/continue and arbitrary jumps are not admitted. Sites are unique throughout
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
[the variant carrier contract](local-variants.md). Their active payload
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
local region creates a backend child frame and charges its explicit inputs;
a loop also charges its induction index. An untaken arm or zero-trip body creates
no frame. Region cleanup releases its retained charges, and returned values are
charged at the enclosing result bindings. Physical `release` has no instruction
cost and retains the existing ghost-accounting rule. These are retained-payload
charges, not measurements of actual allocator memory or constant-time execution.

Bound rejection happens before the first body effect. Cumulative iteration or
instruction exhaustion may occur after earlier effects. Deterministic bound
rejection is reported as `exhausted:local-bound-limit`
by Rust and `exhausted` / `local-bound-limit` by Lean. Rust uses a coarse
machine-limit stop for cumulative budgets; Lean additionally names
`local-iteration-limit`. Comparisons must retain the stop
class, reached effect prefix and resource state, not identify all failures with
ordinary protocol rejection. Interpreter-work limits are separately reported.

Helper applications expand recursively before participant projection. Expansion
retains regions and does not unroll loops. Helpers introduce no runtime frames;
entered control regions do. Local origin paths append `["if", site, "then"]` or
`["if", site, "else"]`, and `["for", site, decimal_index]`, preserving the enclosing
call/participant origin. Source identities retain both branches and loop bodies,
including helper definitions reachable only inside a region.

## Analyses and construction

Consumers requiring an unconditional static primitive schedule refuse local
control with `execution-local-control-static-trace`. The artifact observer's full
static-manifest mode refuses with `artifact-observer-local-control-unsupported`;
ordinary execution and artifact execution with tracing disabled retain local
control. Refusal is preferable to silently flattening both arms or one iteration.

The current Fiat–Shamir constructor preserves an entire local body when its
boundary and every nested primitive signature contain only duplicable values.
This includes guards and ordinary fallible computation; it does not imply purity
or permission to reorder. Resource-bearing control and selected draws inside it
are refused (`construction-local-control-resource` / `-draw`). A demand to replay
such a body's output at the other participant is refused (`-replay`). These construction checks are separate from local variant admission's lexical
history-operation restriction. The latter does not track implicit dataflow
through a match result into a later conditional. Branch-dependent challenge schedules and cross-role control replay need separate design.

## Formal interpretation and assurance boundary

`Zkc.Source.FiniteControl` treats admitted runtime bounds as a selection from a
family of existing finite `Region.iterate` terms. It proves count/zero/index
properties and reuses the selected branch/iteration denotations. Executable
adapters check bounds before instantiation. No unbounded process constructor is
added. Structural laws for a fixed typed region do not by themselves prove raw
frontend elaboration, candidate decoding or native execution correct.

The independent Lean checker recursively admits source and candidate regions and
compares their control, types, captures, carries, operations and ordered effects.
Logical and bounded physical reference execution support differential tests.
This is not a general refinement theorem for the C++ or Rust implementation,
nor a cryptographic security or constant-time theorem. See the
[implementation and evidence](../../../compiler/local-control.md).

## Explicit local stops

The common source carrier spells a role-free local stop as
`["stop", site, "", reason]`; projected/physical local code spells it as
`["stop", site, reason]`. A common protocol-body stop supplies its participant
instead of the empty role. Reasons are `reject`, `abort`, `exhausted`, `incomplete`
and `refused`. Local source syntax is `stop reason;`. All are terminal, including
inside a match arm or a called algorithm. They produce no result or fabricated
yield. Continuing alternatives retain their normal result/resource obligations.
