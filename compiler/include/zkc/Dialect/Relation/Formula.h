#ifndef ZKC_DIALECT_RELATION_FORMULA_H
#define ZKC_DIALECT_RELATION_FORMULA_H
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/Support/Error.h"
#include <map>
namespace zkc::relation {
/// Representation identities for one immutable module and one phase budget.
/// Full logical input schema digests and purposes precede the sorted transitive
/// pure helper closure. Each helper is printed and hashed once. Names and
/// toolchain printing remain significant; this is not semantic equivalence.
/// The caller admits the module and must not mutate it during this lifetime.
class FormulaIdentities {
  struct Definition {
    std::string digest;
    llvm::SmallVector<mlir::func::FuncOp> dependencies;
  };
  mlir::SymbolTableCollection symbols;
  std::map<mlir::Operation *, Definition> definitions;
  uint64_t &remaining;
  uint64_t byteLimit;
  llvm::Expected<const Definition *> definition(mlir::func::FuncOp);

public:
  FormulaIdentities(uint64_t &remaining, uint64_t byteLimit)
      : remaining(remaining), byteLimit(byteLimit) {}
  llvm::Expected<std::string> get(mlir::func::FuncOp predicate,
                                  llvm::ArrayRef<std::string> logicalInputs,
                                  llvm::ArrayRef<std::string> purposes);
};
} // namespace zkc::relation
#endif
