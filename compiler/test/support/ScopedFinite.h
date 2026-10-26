#ifndef ZKC_TEST_SCOPEDFINITE_H
#define ZKC_TEST_SCOPEDFINITE_H

#include "../../lib/Transforms/ScopedPreparation.h"
#include "NativeCases.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include <memory>

namespace zkc::test::scopedFinite {
inline mlir::OwningOpRef<mlir::ModuleOp> clone(mlir::ModuleOp source) {
  return mlir::OwningOpRef<mlir::ModuleOp>(
      mlir::cast<mlir::ModuleOp>(source->clone()));
}
inline mlir::func::FuncOp function(mlir::ModuleOp module,
                                   llvm::StringRef name) {
  auto result = mlir::SymbolTable(&module.getBody()->front())
                    .lookup<mlir::func::FuncOp>(name);
  require(bool(result), "missing scoped function " + name);
  return result;
}
inline llvm::StringRef contract(exec::ApplyOp operation) {
  auto binding = mlir::SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
      operation, operation.getBindingAttr());
  require(bool(binding), "missing invocation binding");
  return binding.getContract();
}
inline llvm::SmallVector<exec::ApplyOp> applications(mlir::Operation *owner,
                                                     llvm::StringRef name) {
  llvm::SmallVector<exec::ApplyOp> result;
  owner->walk([&](exec::ApplyOp operation) {
    if (contract(operation) == name)
      result.push_back(operation);
  });
  return result;
}
inline exec::ApplyOp application(mlir::Operation *owner, llvm::StringRef name) {
  auto result = applications(owner, name);
  require(!result.empty(), "missing invocation " + name);
  return result.front();
}
struct AdmittedComputation : finite::Computation {
  std::shared_ptr<protocol::SourceExecutionClosure> source;
};
inline AdmittedComputation computation(mlir::ModuleOp module,
                                       mlir::Operation *operation = nullptr) {
  AdmittedComputation result;
  result.source = std::make_shared<protocol::SourceExecutionClosure>(
      take(protocol::readSourceExecutionClosure(&module.getBody()->front())));
  if (!operation)
    module.walk([&](exec::CollectOp found) { operation = found; });
  require(operation && mlir::succeeded(finite::describe(operation, result)),
          "missing admitted computation");
  result.scopedSource = result.source.get();
  return result;
}
inline mlir::OwningOpRef<mlir::ModuleOp>
prepare(mlir::ModuleOp source, MathematicalSelectionPolicy policy = {}) {
  mathematical::RealizationWork work;
  uint64_t copy = 1000000, bytes = 16 * 1024 * 1024;
  std::optional<CapacityCause> capacity;
  auto result = protocol::prepareScopedFinite(source, work, copy, bytes,
                                              capacity, policy);
  require(bool(result), "scoped finite preparation failed");
  return result;
}
inline mlir::LogicalResult compare(mlir::ModuleOp source,
                                   mlir::ModuleOp candidate) {
  mathematical::RealizationWork work;
  return protocol::verifyScopedFinitePreparation(source, candidate, work);
}
inline bool hasLoop(mlir::Operation *owner) {
  bool found = false;
  owner->walk([&](exec::RangeOp) { found = true; });
  return found;
}
} // namespace zkc::test::scopedFinite
#endif
