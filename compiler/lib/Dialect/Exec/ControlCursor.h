#ifndef ZKC_DIALECT_EXEC_CONTROL_CURSOR_H
#define ZKC_DIALECT_EXEC_CONTROL_CURSOR_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLFunctionalExtras.h"

namespace zkc::exec::detail {
// Bounded read-only navigation of a formed scoped Func body. The consumer owns
// operation meaning, source/record association and whole-function ownership.
// Structured inspection checks actual local CFG, scope and transfer edges;
// consumers that use custom dispatch cleanup own its complete inspection.
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

  // Inspect the actual control/custody skeleton. The callback owns resolution,
  // signature and semantic comparison of the actual outlined call; its index
  // selects the source arm (zero for a loop). These methods do not inspect a
  // native record or reconstruct a source body. Results are actual join or
  // publication values. The entire body must still satisfy complete().
  using RegionCheck = llvm::function_ref<bool(mlir::func::CallOp, unsigned)>;
  bool conditional(mlir::Value condition, mlir::ValueRange captures,
                   llvm::StringRef site, RegionCheck body,
                   llvm::SmallVectorImpl<mlir::Value> &results);
  bool match(mlir::Value input, mlir::ValueRange captures,
             llvm::ArrayRef<std::string> alternatives, llvm::StringRef site,
             RegionCheck body, llvm::SmallVectorImpl<mlir::Value> &results);
  bool loop(mlir::Value lower, mlir::Value upper, mlir::ValueRange seeds,
            mlir::ValueRange captures, bool conditional, llvm::StringRef site,
            RegionCheck body, llvm::SmallVectorImpl<mlir::Value> &results);

private:
  mlir::func::FuncOp function;
  unsigned &remaining;
  mlir::Block *current = nullptr, *failed = nullptr;
  mlir::Block::iterator position;
  llvm::DenseSet<mlir::Block *> inspected;
  bool charge() { return remaining && (--remaining, true); }
  bool region(llvm::StringRef kind, llvm::StringRef site,
              llvm::StringRef selection, mlir::ValueRange inputs,
              RegionCheck body, unsigned index,
              llvm::SmallVectorImpl<mlir::Value> &results);
};
} // namespace zkc::exec::detail
#endif
