# Runtime-count nested data uses an explicit immutable sequence type

Use `!data.sequence<T>` for runtime-count immutable records and variable-size
payloads. Keep numeric vectors and matrices in their existing ranked tensor
representation. The [nested-data profile](../spec/ir/data.md)
owns formation, operations and realization.

## Alternatives and reason

An opening batch requires a runtime number of complete value/proof records. A
ragged trace batch requires a runtime number of independently shaped matrices.
Finite product/sum descriptors cannot provide that outer runtime count. Splitting
records into parallel vectors introduces separate length-agreement obligations
and loses one typed element boundary.

MLIR's [ranked tensor type](https://mlir.llvm.org/docs/Dialects/Builtin/#rankedtensortype)
permits dialect-defined element types; it does not itself define zkc's ownership,
wire or checked indexing semantics. Direct nested builtin tensors are excluded.
Wrapping a matrix in a dialect record merely to place it in a tensor obscures
this distinction and still requires a new storage/codec contract. Broadening all
tensor lowering to arbitrary records would mix numerical and nested-data rules.
An explicit sequence gives both clients common construction, length, indexing
and append contracts while preserving tensor arithmetic and layout.

The existing `data` dialect owns immutable domain-independent data. Sequence
formation and pure operations belong there; checked local execution uses the
same dialect's `exec` operations and existing kernel interfaces. Partial indexing
has ordered failure semantics. Existing local loops provide iteration. Another
IR stage or new control representation would duplicate established machinery.

Native storage uses an immutable element slice with cached expanded counts and
bytes. This keeps aliasing simple and makes limits independent of reference
counts. Appending copies the slice, so cumulative work is explicitly bounded.
Affine elements are excluded because variable-length affine ownership would
require a distinct resource contract. Local copyability does not authorize wire
transfer; recursive message admission still checks every alternative and leaf.

## Limits

A measured workload may make linear append insufficient or require a second
physical representation. Revisit formation when a concrete client requires
variable-count affine custody and can
state its creation, indexing, consumption and cleanup laws. Neither change is
implied by adding another protocol written with the existing contracts.
