# Native domain contribution

This example installs an `envelope` nominal type and contract declarations,
its native MLIR type, and a reversible mathematical field-add specialization.
It checks contributed contracts through scoped `exec.apply` invocations and
total mathematical operations over the installed field types. The envelope
type has no native endpoint policy or executable representation.

Configure the compiler with `-DZKC_CONTRIBUTION_FILES=/absolute/path/to/contribution.cmake`,
then install it into a fresh prefix. Configure `consumer/` against that prefix
using `CMAKE_PREFIX_PATH` and the same `MLIR_DIR`; build and run CTest. The consumer
checks nested type roundtrips, contributed operation signatures and strict
property parsing, logical-only representation refusal, and exact restoration
of mathematical IR, including operand order and diagnostic locations.
The specialization illustrates reversible MLIR rewriting; it is not an alternate
executable route. Ordered protocol execution uses scoped Func/Exec operations.
Damaged restoration metadata must refuse decomposition. With
`-DEXPECT_ENVELOPE=OFF`, it checks a base installation lacks the contribution.
