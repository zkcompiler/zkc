#ifndef ZKC_TEST_COMPUTATION_RECIPES_H
#define ZKC_TEST_COMPUTATION_RECIPES_H

#include "../../lib/Transforms/Computation/Support.h"
#include "NativeCases.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/MathematicalWork.h"
#include "llvm/ADT/STLExtras.h"

namespace zkc::test {
inline protocol_ir::ProtocolModuleOp
computationRecipeOutput(mlir::ModuleOp module) {
  require(module->getAttrs().empty() &&
              llvm::hasSingleElement(*module.getBody()),
          "computation recipe output must have one executable owner");
  auto owner =
      mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  require(owner && owner.getProfile() == protocol_ir::Profile::Exec &&
              owner.getBody().hasOneBlock(),
          "computation recipe output must use the Exec profile");
  unsigned entries = 0;
  for (auto &declaration : owner.getBody().front()) {
    if (auto function = mlir::dyn_cast<mlir::func::FuncOp>(declaration)) {
      require(protocol::isScopedExecutionFunction(function),
              "recipe output retained a mathematical source function");
      entries += !function->hasAttr("runtime.region");
    } else
      require(mlir::isa<runtime::BindingOp>(declaration),
              "computation recipe output retained a source declaration");
  }
  require(entries == 1, "computation recipe output must have one scoped entry");
  return owner;
}

// Keep the Protocol fixture immutable. An isolated mathematical recipe source
// owns pure standard functions and domains, including dormant mathematical
// definitions and their premises. Scoped source callers are separate owners.
inline mlir::OwningOpRef<mlir::ModuleOp>
computationRecipeUnit(mlir::Operation *sourceOwner) {
  mlir::OpBuilder builder(sourceOwner->getContext());
  mlir::OwningOpRef<mlir::ModuleOp> unit(
      mlir::ModuleOp::create(builder, sourceOwner->getLoc(), "numerical"));
  unit->getOperation()->setAttr("exec.computation", builder.getUnitAttr());
  builder.setInsertionPointToEnd(unit->getBody());
  for (auto &definition : sourceOwner->getRegion(0).front()) {
    if (!mlir::isa<mlir::func::FuncOp, data::DomainOp>(definition))
      continue;
    if (auto function = mlir::dyn_cast<mlir::func::FuncOp>(definition);
        function && protocol::isScopedExecutionFunction(function))
      continue;
    auto *copy = builder.clone(definition);
    mlir::SymbolTable::setSymbolVisibility(
        copy, mlir::SymbolTable::Visibility::Private);
  }
  return unit;
}

inline mlir::OwningOpRef<mlir::ModuleOp>
computationRecipeSource(mlir::Operation *sourceOwner, llvm::StringRef helper,
                        llvm::StringRef entryName) {
  auto unit = computationRecipeUnit(sourceOwner);
  auto prototype = mlir::SymbolTable(*unit).lookup<mlir::func::FuncOp>(helper);
  require(bool(prototype), "missing computation recipe helper");
  require(!mlir::SymbolTable(*unit).lookup(entryName),
          "computation recipe entry name collides with a dependency");
  mlir::OpBuilder builder(unit->getBody(), unit->getBody()->end());
  auto entry = mlir::cast<mlir::func::FuncOp>(builder.clone(*prototype));
  entry.setSymName(entryName);
  entry.setPublic();
  // Conditional callback fixtures retain their premises for isolated recipe
  // checks. They do not exercise admission of an unconditional computation
  // entry.
  return unit;
}

// Exercise recipe production directly, without normalizing away mutation
// targets or debiting the optional callback work during test setup.
inline mlir::OwningOpRef<mlir::ModuleOp>
realizeComputationEntry(mlir::ModuleOp source, llvm::StringRef callSite,
                        MathematicalSelectionPolicy policy,
                        mathematical::RealizationWork &work,
                        finite::VerificationLimits limits = {},
                        mathematical::RealizationTrace *trace = nullptr) {
  uint64_t remaining = 1000000, remainingBytes = 16 * 1024 * 1024;
  return computation::realizeEntry(source, callSite, policy, work, remaining,
                                   remainingBytes, limits, trace);
}

inline std::string computationRecipeSite(llvm::StringRef callSite,
                                         unsigned ordinal) {
  uint64_t remainingBytes = 16 * 1024 * 1024;
  auto site = protocol::algorithmSite({{callSite.str(), "kernel"}},
                                      std::to_string(ordinal), remainingBytes);
  require(bool(site), "computation recipe site capacity exhausted");
  return *site;
}
} // namespace zkc::test
#endif
