# Compiler limits

This native contract lists admission ceilings shared across operations.
An exhausted checker refuses; it does not establish semantic inequivalence.

| Boundary | Limit |
|---|---|
| Declared role roster | 1,024 roles |
| Helper depth and expanded helper analysis | 64 levels; 100,000 operations |
| Helper dependency analysis and availability replay | 1,000,000 words/indices within their separate budgets |
| Role expansion | 100,000 operation/port visits |
| Exact resource-origin analysis | 100,000 shared work units and 64 call/region levels |
| Pointwise map formulas and correspondence | Shared helper expansion budget; expanded formula within the Ring view limits of 65,536 nodes and depth 1,024; 1,000,000 matcher steps |
| Mathematical preparation helper copying | 100,000 operations and 1,000,000 operand/result slots, cumulative across realization stages |
| Optional finite recognition | Separate cumulative allowances of 100,000 structural, equation and extent/bound-evidence steps |
| Standalone finite formation facts | 65,536 shared extraction/derivation steps; nested queries do not reset the allowance |
| SSA fact extraction | At most 256 nested interpretation frames, including domain traversal, helper and actual/formal environments; exhaustion returns Capacity |
| Finite correspondence | 100,000 required-reader units per declaration or total expression; optional comparison capped at 100,000 and the reader's remaining allowance |
| Optional lane realization | 1,000,000 work units; exhaustion retains ordered execution |
| Required finite expressions and polynomial expansion | Separate cumulative allowances of 100,000 each |
| Kernel normalization and frontier | 2,000,000 shared copy/context/frontier work units per lowering subject; independent normalization readers have 4,000,000 units per closure, helper depth 64 and polynomial depth 128 |
| Kernel recipe materialization and correspondence | Separate allowances of 1,000,000 operation/slot units and 16 MiB generated-site text; discarded recipe construction has an additional cumulative reserve of the same sizes; existing recipe limits also apply |
| Native R1CS reduction adapter | BLS Fr; at most 8 rows, 128 columns and 1,024 nonzero terms |

Ring depth counts an input or literal as one level. Each addition or
multiplication adds one level, and `a - b` is `a + (-b)`, so it adds two levels on
the path of `b`. A chain of 1,023 additions therefore reaches the depth limit, as
do 511 steps of `x - acc` or of Horner's `acc * x + c`. Maps refuse a deeper
expanded formula with `algebra-map-formula` during preparation, while a scalar
`local.realize` of the same helper has no Ring depth limit.

Source expansion, runtime value capacity, wire size and execution work have
independent bounds. Larger bulk-kernel tests do not expand the scalar R1CS
adapter's envelope. Every original helper is checked before erasure, including
unreferenced private definitions. Unknown roots refuse independently of budget
exhaustion. The owning profiles define additional operation-specific limits.

Mathematical preparation shares its helper-copying allowance across formation
and algorithm selection. Kernel normalization owns separate bounded transient
proposals and independent readers. All prepared callbacks in one closure share
the helper-normalization allowance.
Optional recognition and candidate comparison have separate allowances from
ordered emission and checking. These limits bound compiler work; they are not
runtime cost estimates or mathematical assumptions.

Kernel recipe copy/site quotas are cumulative across calls and charge the
selected attempt, including scheduling and consumption of the actual schedule.
A terminal failure retains its construction debit. A discarded bulk proposal
instead charges separate cumulative copy/site reserves in the shared
realization work. Before a bulk attempt, both discarded-construction reserves
must cover the entire incoming copy/site quotas; otherwise construction selects
ordered execution directly. This conservative reservation may skip a smaller
bulk proposal that would have fit the unused discard reserve.
Only optional comparison capacity permits retry, and disabling bulk permits
at most one ordered retry per call. Required construction has its original
allowance on that retry; optional recognition and lane work remain cumulative.
Selected and discarded construction together therefore consume at most
2,000,000 charged operation/slot units and 32 MiB of charged generated-site text
across calls with default allowances. Independent correspondence readers retain
their own limits. These are charged construction bounds, not a bound on all
compiler instructions or allocations.
