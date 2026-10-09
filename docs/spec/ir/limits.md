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
