#ifndef ZKC_TRANSFORMS_TABLESIMPLIFICATION_H
#define ZKC_TRANSFORMS_TABLESIMPLIFICATION_H

#include "mlir/IR/BuiltinOps.h"

namespace zkc {
/// Simplify one verified logical PIR or Plan program in place under the
/// installed table-protocol/1 interpretation. Replace poly.linear(a, a, r)
/// with a only when the endpoint SSA values are identical. Propagate explicit
/// capture aliases without changing region signatures or loop accumulators.
/// No other operation is removed, moved, or folded. Physical programs and
/// other libraries are refused before rewriting. Callers retaining a source
/// module must clone it before simplifying their candidate.
mlir::LogicalResult simplifyTableRegions(mlir::ModuleOp module);

} // namespace zkc

#endif
