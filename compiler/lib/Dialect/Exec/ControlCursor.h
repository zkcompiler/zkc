#ifndef ZKC_DIALECT_EXEC_CONTROL_CURSOR_H
#define ZKC_DIALECT_EXEC_CONTROL_CURSOR_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::exec::detail {
// Bounded read-only navigation of a formed scoped Func body. The consumer owns
// operation meaning, source/record association, scope custody and every custom
// cleanup block. This utility only checks actual local CFG/outcome structure.
// It borrows one immutable body and its consumer's cumulative work allowance.
class ControlCursor {
public:
  ControlCursor(mlir::func::FuncOp function, unsigned &remaining)
      : function(function), remaining(remaining) {}
  bool enter(mlir::Block *block);
  // Reserve a block for explicit consumer inspection without changing the
  // current position. The consumer must check all its operations and edges.
  bool inspect(mlir::Block *block);
  mlir::Operation *take();
  mlir::Operation *peek() const;
  bool atEnd() const;
  mlir::Block *currentBlock() const { return current; }
  bool complete() const;
  bool failure(mlir::Block *block);
  bool dispatch(mlir::Value outcome,
                llvm::SmallVectorImpl<mlir::Value> &payload,
                mlir::Block *customFailure = nullptr);

private:
  mlir::func::FuncOp function;
  unsigned &remaining;
  mlir::Block *current = nullptr, *failed = nullptr;
  mlir::Block::iterator position;
  llvm::DenseSet<mlir::Block *> inspected;
  bool charge() { return remaining && (--remaining, true); }
};
} // namespace zkc::exec::detail
#endif
