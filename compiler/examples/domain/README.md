# Native domain contribution

This example installs an `envelope` nominal type and contract declarations,
its MLIR adapters, and a reversible typed field-add specialization. It checks
scoped Protocol IR and standalone typed adapters over the installed field types. The envelope type supplies
logical contract adapters; it has no native endpoint policy or executable
representation.

Configure the compiler with `-DZKC_CONTRIBUTION_FILES=/absolute/path/to/contribution.cmake`,
then install it into a fresh prefix. Configure `consumer/` against that prefix
using `CMAKE_PREFIX_PATH` and the same `MLIR_DIR`; build and run CTest. The consumer
checks nested type roundtrips, contributed operation signatures and strict
property parsing, logical-only representation refusal, and exact restoration
of typed adapter IR, including operation order, binding identities and locations.
The specialization illustrates reversible MLIR rewriting; it is not an alternate
executable route. Ordered protocol execution uses scoped Func/Exec operations.
Damaged restoration metadata must refuse decomposition. With
`-DEXPECT_ENVELOPE=OFF`, it checks a base installation lacks the contribution.
