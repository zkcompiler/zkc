#ifndef ZKC_ANALYSIS_FINITE_H
#define ZKC_ANALYSIS_FINITE_H
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "llvm/ADT/BitVector.h"

namespace zkc::finite {
// A transient view of the verified typed IR. References never encode
// expressions.
struct Computation {
  mlir::Operation *operation = nullptr;
  data::DomainOp domain;
  mlir::Operation *helper = nullptr;
  mlir::Operation *predicate = nullptr;
  mlir::FunctionType signature;
  unsigned arguments = 0, states = 0, captures = 0;
  bool total = false, collect = false;
};
mlir::FailureOr<mlir::StringAttr> closureKey(mlir::Operation *op);
bool isComputation(mlir::Operation *op);
bool isDeclaration(mlir::Operation *op);
mlir::Type elementType(mlir::Type container, bool matrix = false);
mlir::LogicalResult describe(mlir::Operation *op, Computation &result,
                             mlir::Operation *symbolRoot = nullptr);
mlir::LogicalResult verify(mlir::Operation *op);
mlir::LogicalResult verifyClosure(mlir::Operation *unit);
mlir::LogicalResult verifyPreconditions(mlir::Operation *helper);
mlir::LogicalResult verifyCallPreconditions(mlir::Operation *call);
bool provesBound(mlir::Value index, mlir::Value container, unsigned axis);
bool provesEqualExtent(mlir::Value left, unsigned leftAxis, mlir::Value right,
                       unsigned rightAxis);
// Result sets are precise up to control/cardinality conservatism; consumers
// cloning whole operations must continue using operandDependencies instead.
struct Summary {
  llvm::SmallVector<llvm::BitVector> results;
  llvm::SmallVector<llvm::BitVector> formation;
};
mlir::LogicalResult summarize(mlir::Operation *op, Summary &result);
} // namespace zkc::finite
#endif
