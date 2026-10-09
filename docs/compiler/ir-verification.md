# Native IR verification

`Zkc::IR` owns dialects, interfaces and mandatory profile verification.
`Zkc::Translation` owns Language emission/comparison, relation import and checked
program export. The [refinement specification](../spec/verification/refinement.md)
defines the semantic obligations beyond formation.

## Checking boundaries

| Check | Establishes |
|---|---|
| Local operation formation | Attributes, SSA types, signatures, binding applicability and region interfaces |
| Whole `protocol.module` | Profile rules, declaration closure, role availability, resources and control obligations |
| Relation assets/declarations | Canonical R1CS/AIR structure, exact identities, typed purposes and conflicts |
| Projection and later profiles | Required metadata, participant structure, executable readiness and physical bindings |
| Checked export | Complete verified physical IR and an admitted `zkc.program` model |
| Source-relative preservation | An explicit comparison against the retained input at the selected transformation boundary |

Standalone operation validity does not imply a valid complete program. External
clients call `mlir::verify` or checked export; private region-verifier hooks rely
on nested operation checking. Mutable IR must be checked again after an edit.

## Translation and executable reading

[Protocol translation](../../compiler/include/zkc/Translation/Protocol.h)
exports verified physical IR. The core
[execution reader](../../compiler/include/zkc/Dialect/Protocol/Execution.h)
reconstructs executable content without depending on Translation. Its internal
use by a root verifier does not recursively invoke export. Reading an executable
model alone does not establish mathematical or projection invariants.

Mathematical profiles retain native SSA until realization. The serialized
`zkc.program` boundary is physical-only. Relation adapters use
[Relations.h](../../compiler/include/zkc/Translation/Relations.h); relation
attribute reading belongs to the core dialect so transformations need not link
Translation. Register required dialects/interfaces before parsing native programs.

## Diagnostics and regression controls

[Diagnostic metadata](../../compiler/include/zkc/Dialect/Diagnostics.h) carries
owned refusal identifiers/details alongside MLIR locations, notes and rendered
text. Callers inspect identifiers without parsing message prose. Metadata is not
proof data or artifact identity; ordinary MLIR errors need not have a native code.

Component checks enforce source ownership and dependency direction. Installed IR,
Translation, Transforms and Compiler consumers exercise their declared
public APIs. Native mutation tests cover actual types, operands, effects and
retained interfaces. These are implementation controls, not a universal native
refinement or protocol-security theorem.
