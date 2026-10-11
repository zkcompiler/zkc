#ifndef ZKC_ANALYSIS_FINITE_H
#define ZKC_ANALYSIS_FINITE_H
#include "zkc/Contracts/MathematicalFacts.h"
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
enum class CallbackRole { Step, Body, Predicate };
enum class CallbackExit { Return, Stop };
struct EntryValues {
  mlir::ValueRange domain, initialState, captures;
};
struct CallbackValues {
  mlir::ValueRange state, items, domain, captures;
};
// Borrowed, checked views; rebuild after changing the source subject. These
// describe only the ABI, not helper closure admission or expression meaning.
struct CallbackView {
  mlir::Operation *symbol;
  mlir::Block *body;
  mlir::FunctionType signature;
  CallbackRole role;
  CallbackValues formals;
  mlir::Operation *terminator;
  CallbackExit exit;
  mlir::ValueRange returned;
};
struct CallEnvironment {
  CallbackView callback;
  // Complete formal order. Aliased actuals retain distinct formal positions.
  llvm::SmallVector<mlir::Value> actuals;
  mlir::FailureOr<mlir::Value> lookup(mlir::BlockArgument formal) const;
};
mlir::FailureOr<EntryValues> partitionEntry(const Computation &computation,
                                            mlir::ValueRange actuals);
mlir::FailureOr<CallbackView> readCallback(const Computation &computation,
                                           CallbackRole role);
mlir::FailureOr<CallEnvironment> bindCallback(const CallbackView &callback,
                                              CallbackValues actuals);
mlir::FailureOr<mlir::StringAttr> closureKey(mlir::Operation *op);
bool isComputation(mlir::Operation *op);
bool isDeclaration(mlir::Operation *op);
mlir::Type elementType(mlir::Type container, bool matrix = false);
mlir::LogicalResult describe(mlir::Operation *op, Computation &result,
                             mlir::Operation *symbolRoot = nullptr,
                             mlir::SymbolTableCollection *symbols = nullptr);
mlir::LogicalResult verify(mlir::Operation *op);
// Local shape and attributes do not traverse symbols. Symbol-user verification
// checks the referenced ABI and premises with MLIR's supplied symbol tables.
mlir::LogicalResult verifyLocal(mlir::Operation *op);
mlir::LogicalResult verifyReferences(mlir::Operation *op,
                                     mlir::SymbolTableCollection &symbols);
// Region-level closure checks after local and symbol-user verification.
mlir::LogicalResult verifyClosure(mlir::Operation *unit);
mlir::LogicalResult verifyPreconditions(mlir::Operation *helper);
mlir::LogicalResult verifyCallPreconditions(mlir::Operation *call);
// Mandatory checks and comparison readers retain Capacity explicitly. The
// caller owns this cumulative allowance; these queries never replenish it.
facts::Status boundStatus(mlir::Value index, mlir::Value container,
                          unsigned axis, uint64_t &remaining);
facts::Status equalExtentStatus(mlir::Value left, unsigned leftAxis,
                                mlir::Value right, unsigned rightAxis,
                                uint64_t &remaining);
bool provesBound(mlir::Value index, mlir::Value container, unsigned axis);
bool provesEqualExtent(mlir::Value left, unsigned leftAxis, mlir::Value right,
                       unsigned rightAxis);
// Enclosing analyses/checkers use these overloads to share cumulative work.
// False is conservative, including exhausted work; it grants no evidence.
bool provesBound(mlir::Value index, mlir::Value container, unsigned axis,
                 uint64_t &remaining);
bool provesEqualExtent(mlir::Value left, unsigned leftAxis, mlir::Value right,
                       unsigned rightAxis, uint64_t &remaining);
// Result sets are precise up to control/cardinality conservatism; consumers
// cloning whole operations must continue using operandDependencies instead.
struct Summary {
  llvm::SmallVector<llvm::BitVector> results;
  llvm::SmallVector<llvm::BitVector> formation;
};
mlir::LogicalResult summarize(mlir::Operation *op, Summary &result);
} // namespace zkc::finite
#endif
