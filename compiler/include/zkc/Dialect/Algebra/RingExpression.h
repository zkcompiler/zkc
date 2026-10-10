#ifndef ZKC_DIALECT_ALGEBRA_RINGEXPRESSION_H
#define ZKC_DIALECT_ALGEBRA_RINGEXPRESSION_H

#include "mlir/IR/Block.h"
#include "mlir/IR/ValueRange.h"
#include "zkc/Contracts/RingExpression.h"

namespace zkc::algebra {
/// Whether the Ring view admits `op` itself: a field constant with only its
/// literal, or an attribute-free field addition, subtraction or multiplication
/// whose operands have its result type. Captures, literal ranges and limits
/// are checked when a whole block is described.
bool isRingOperation(mlir::Operation &op);
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
