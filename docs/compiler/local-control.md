# Structured local algorithms

Ordered local algorithms use typed calls, conditionals, alternatives and finite
state-carrying loops inside the common mathematical pipeline. The
[control profile](../spec/profiles/compiler/local-control.md) and
[variant profile](../spec/profiles/compiler/local-variants.md) own formation,
resource and failure contracts.

## Control and custody

A local conditional executes exactly one branch. Both branches form correctly
and agree on continuing result types. Captures are explicit and evaluated once.
Affine captures are consumed once on branch entry; each branch checks its own
uses. Loop invariants must be reusable, while affine state travels through
carried ports. Neither speculation nor cloning RNG/transcript state follows from
an ordinary value simplification.

A finite loop reads its bounds once and returns its initial state on zero trips.
Limit exhaustion is an explicit failure. Early bounded termination uses
`local.condition`; participant completion uses `protocol.finish_if`. Their
[completion contract](entry-completion.md) preserves reached work, cleanup and
return coordinates while skipping the remaining suffix.

## Representation and execution

`local.if`, `local.for`, `local.yield` and variant matching retain isolated typed
regions. Explicit block arguments expose captures and backedge mappings to MLIR.
They retain zkc's index, resource, failure and work semantics through physical
lowering. A future SCF or generated-kernel lowering needs an explicit relation to
those semantics.

Helper expansion recurses into regions without unrolling loops or executing both
branches. Physical planning inserts conversions within their actual control
region. Storage release respects each isolated block. The Rust Runner executes
the resulting structured program with managed frames and complete failure
cleanup. Independent Lean control models supply selected laws, not native
execution correspondence.

## Authoring boundary

[Mathematical source](../language/mathematical.md) exposes local control and
structured data. General dynamic protocol choice, unbounded execution and arbitrary
references/closures are outside this local-control profile. A local algorithm
cannot invent communication to obtain another participant's unavailable value.
