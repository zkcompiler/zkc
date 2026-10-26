#ifndef ZKC_TEST_SCOPEDFINITE_H
#define ZKC_TEST_SCOPEDFINITE_H

#include "../../lib/Transforms/ScopedPreparation.h"
#include "ComputationFixture.h"
#include "NativeCases.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/Finite.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include <functional>
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
// Enumerate actual invocation paths through a prepared scoped root. Retained
// dormant helper definitions are not occurrences of this execution.
inline llvm::SmallVector<exec::ApplyOp>
executionApplications(mlir::ModuleOp module, llvm::StringRef root,
                      llvm::StringRef name) {
  auto closure =
      take(protocol::readSourceExecutionClosure(&module.getBody()->front()));
  llvm::SmallVector<exec::ApplyOp> result;
  std::function<void(llvm::StringRef, unsigned)> visit =
      [&](llvm::StringRef function, unsigned depth) {
        require(depth < 64, "excessive test execution depth");
        for (const auto &step : closure.bodies.at(function.str())) {
          if (auto apply = mlir::dyn_cast<exec::ApplyOp>(step.operation))
            if (contract(apply) == name)
              result.push_back(apply);
          for (auto region : step.regions)
            visit(region.getSymName(), depth + 1);
          if (auto call = mlir::dyn_cast<mlir::func::CallOp>(step.operation))
            if (closure.bodies.count(call.getCallee().str()))
              visit(call.getCallee(), depth + 1);
        }
      };
  visit(root, 0);
  return result;
}
inline OwnedComputation computation(mlir::ModuleOp module,
                                    mlir::Operation *operation = nullptr) {
  if (!operation)
    module.walk([&](exec::CollectOp found) { operation = found; });
  require(operation, "missing scoped collection");
  return readComputation(module, operation);
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
