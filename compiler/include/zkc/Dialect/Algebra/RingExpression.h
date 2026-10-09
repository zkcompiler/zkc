#ifndef ZKC_DIALECT_ALGEBRA_RINGEXPRESSION_H
#define ZKC_DIALECT_ALGEBRA_RINGEXPRESSION_H

#include "mlir/IR/Block.h"
#include "mlir/IR/ValueRange.h"
#include "zkc/Contracts/RingExpression.h"

namespace zkc::algebra {
/// Interpret a closed scalar SSA block as a formal ring expression. Every
/// non-terminator operation must be an admitted constant, add, subtract or
/// multiply, including unused operations. Operands cannot capture outer SSA
/// values. Calls must already have been expanded. All block arguments remain
/// ordered input slots, including unused ones; only live nodes are retained.
///
/// The result is a derived view of this block, not a stored second definition.
/// It does not establish totality, profile admission or native realization.
llvm::Expected<ring::Expression>
describeRingExpression(mlir::Block &block, mlir::ValueRange results);
} // namespace zkc::algebra
#endif
