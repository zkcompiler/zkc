#ifndef ZKC_PROTOCOL_RESOURCEORIGINS_H
#define ZKC_PROTOCOL_RESOURCEORIGINS_H

#include "zkc/Dialect/Operations.h"
#include "zkc/Dialect/Protocol/NativePolicy.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

namespace zkc::mathematical {
// Invocation-local, formal-relative summaries of formed, immutable IR. Missing
// entries mean unknown, not no continuation. Only repeat obligations demand
// work.
class ResourceOrigins {
  struct Summary {
    llvm::DenseMap<unsigned, unsigned> roots;
    bool continues = true;
    unsigned depth = 1;
  };
  using Environment = llvm::DenseMap<mlir::Value, unsigned>;
  mlir::SymbolTableCollection &symbols;
  NativeTypePolicies &types;
  llvm::DenseMap<mlir::Operation *, Summary> summaries;
  llvm::DenseSet<mlir::Operation *> active;
  uint64_t remaining;
  unsigned depthLimit;

  mlir::LogicalResult charge(mlir::Operation *op, uint64_t amount);
  mlir::LogicalResult limit(mlir::Operation *op, llvm::StringRef detail);
  bool affine(mlir::Value value);
  mlir::LogicalResult block(mlir::Block &body, bool local, unsigned depth,
                            Summary &result);
  mlir::LogicalResult call(mlir::Operation *op, unsigned depth,
                           const Summary *&result);
  mlir::LogicalResult control(mlir::Operation *op, unsigned depth,
                              Environment &environment, Summary &result);
  mlir::LogicalResult successors(mlir::Operation *op, Environment &environment);

public:
  // Injectable limits are private test seams, not source attributes or options.
  ResourceOrigins(mlir::SymbolTableCollection &symbols,
                  NativeTypePolicies &types, uint64_t work = 100000,
                  unsigned depth = 64)
      : symbols(symbols), types(types), remaining(work), depthLimit(depth) {}
  mlir::LogicalResult verify(protocol_ir::RepeatOp repeat);
};
} // namespace zkc::mathematical
#endif
