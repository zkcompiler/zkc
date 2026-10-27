#ifndef ZKC_TARGET_EXECUTION_PORTS_H
#define ZKC_TARGET_EXECUTION_PORTS_H

#include "mlir/IR/BuiltinOps.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Error.h"
#include <memory>

namespace zkc::target {
// Borrowed associations over one immutable, admitted executable subject.
// Administrative CFG/scope/outcome values are not numerical data ports.
// This index is neither a candidate nor permission to publish a transformed IR.
class ExecutionPorts {
public:
  using Values = llvm::SmallVector<mlir::Value>;
  struct Body {
    mlir::Operation *owner;
    mlir::Block *entry;
    Values arguments;
    llvm::SmallVector<mlir::Operation *> instructions;
  };
  struct Node {
    Values inputs, outputs;
    llvm::SmallVector<mlir::Block *> bodies;
    mlir::FunctionType callable;
    const protocol::SourceExecutionStep *step = nullptr;
    bool scoped = false;
  };
  struct Definition {
    mlir::Operation *owner;
    unsigned port;
    // Arguments belong to the owner's logical body. Outputs belong to the
    // actual semantic producer, even when the SSA value is a CFG argument.
    bool argument;
    unsigned block = 0;
  };
  struct Use {
    mlir::Operation *operation;
    unsigned operand;
  };

  static llvm::Expected<ExecutionPorts> read(mlir::ModuleOp module);
  const Node &get(mlir::Operation *op) const;
  const Body &body(mlir::Block *entry) const;
  mlir::ValueRange inputs(mlir::Operation *op) const { return get(op).inputs; }
  mlir::ValueRange outputs(mlir::Operation *op) const {
    return get(op).outputs;
  }
  llvm::ArrayRef<mlir::Operation *> callers(mlir::Operation *function) const;
  mlir::Block *enclosingBody(mlir::Operation *instruction) const;
  const Definition &definition(mlir::Value value) const;
  llvm::ArrayRef<Use> uses(mlir::Value value) const;
  llvm::ArrayRef<mlir::Operation *> operations() const { return ordered; }
  bool contains(mlir::Value value) const { return definitions.contains(value); }

private:
  std::shared_ptr<const protocol::SourceExecutionClosure> closure;
  llvm::SmallVector<mlir::Operation *> ordered;
  llvm::DenseMap<mlir::Operation *, Node> nodes;
  llvm::DenseMap<mlir::Block *, Body> bodies;
  llvm::DenseMap<mlir::Value, Definition> definitions;
  llvm::DenseMap<mlir::Operation *, llvm::SmallVector<mlir::Operation *>>
      incoming;
  llvm::DenseMap<mlir::Operation *, mlir::Block *> enclosing;
  llvm::DenseMap<mlir::Value, llvm::SmallVector<Use>> users;
};
} // namespace zkc::target
#endif
