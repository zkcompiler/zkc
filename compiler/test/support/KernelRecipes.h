#ifndef ZKC_TEST_KERNEL_RECIPES_H
#define ZKC_TEST_KERNEL_RECIPES_H

#include "../../lib/Transforms/Kernel/Support.h"
#include "NativeCases.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/MathematicalWork.h"
#include "llvm/ADT/STLExtras.h"

namespace zkc::test {
inline protocol_ir::ProtocolModuleOp kernelRecipeOutput(mlir::ModuleOp module) {
  require(module->getAttrs().empty() &&
              llvm::hasSingleElement(*module.getBody()),
          "Kernel recipe output must have one executable owner");
  auto owner =
      mlir::dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  require(owner && owner.getProfile() == protocol_ir::Profile::Exec &&
              owner.getBody().hasOneBlock(),
          "Kernel recipe output must use the Exec profile");
  unsigned entries = 0;
  for (auto &declaration : owner.getBody().front()) {
    if (mlir::isa<local::FuncOp>(declaration))
      ++entries;
    else
      require(mlir::isa<local::OperationBindingOp>(declaration),
              "Kernel recipe output retained a source declaration");
  }
  require(entries == 1, "Kernel recipe output must have one Local entry");
  return owner;
}

// Keep the Protocol fixture immutable. A recipe source owns only standard
// functions and domains, including every original dependency and its premises.
inline mlir::OwningOpRef<kernel::ModuleOp>
kernelRecipeUnit(mlir::Operation *sourceOwner) {
  mlir::OpBuilder builder(sourceOwner->getContext());
  mlir::OwningOpRef<kernel::ModuleOp> unit(
      kernel::ModuleOp::create(builder, sourceOwner->getLoc(), "numerical"));
  unit->getBody().emplaceBlock();
  builder.setInsertionPointToEnd(&unit->getBody().front());
  for (auto &definition : sourceOwner->getRegion(0).front()) {
    if (!mlir::isa<mlir::func::FuncOp, data::DomainOp>(definition))
      continue;
    auto *copy = builder.clone(definition);
    mlir::SymbolTable::setSymbolVisibility(
        copy, mlir::SymbolTable::Visibility::Private);
  }
  return unit;
}

inline mlir::OwningOpRef<kernel::ModuleOp>
kernelRecipeSource(mlir::Operation *sourceOwner, llvm::StringRef helper,
                   llvm::StringRef entryName) {
  auto unit = kernelRecipeUnit(sourceOwner);
  auto prototype = mlir::SymbolTable(*unit).lookup<mlir::func::FuncOp>(helper);
  require(bool(prototype), "missing Kernel recipe helper");
  require(!mlir::SymbolTable(*unit).lookup(entryName),
          "Kernel recipe entry name collides with a dependency");
  mlir::OpBuilder builder(&unit->getBody().front(),
                          unit->getBody().front().end());
  auto entry = mlir::cast<mlir::func::FuncOp>(builder.clone(*prototype));
  entry.setSymName(entryName);
  entry.setPublic();
  // Conditional callback fixtures retain their premises for isolated recipe
  // checks. They do not exercise admission of an unconditional Kernel entry.
  return unit;
}

// Exercise recipe production directly, without normalizing away mutation
// targets or debiting the optional callback work during test setup.
inline mlir::OwningOpRef<mlir::ModuleOp>
realizeKernelEntry(kernel::ModuleOp source, llvm::StringRef callSite,
                   MathematicalSelectionPolicy policy,
                   mathematical::RealizationWork &work,
                   finite::VerificationLimits limits = {},
                   mathematical::RealizationTrace *trace = nullptr) {
  uint64_t remaining = 1000000, remainingBytes = 16 * 1024 * 1024;
  return kernel::realizeEntry(source, callSite, policy, work, remaining,
                              remainingBytes, limits, trace);
}

inline std::string kernelRecipeSite(llvm::StringRef callSite,
                                    unsigned ordinal) {
  uint64_t remainingBytes = 16 * 1024 * 1024;
  auto site = protocol::algorithmSite({{callSite.str(), "kernel"}},
                                      std::to_string(ordinal), remainingBytes);
  require(bool(site), "Kernel recipe site capacity exhausted");
  return *site;
}
} // namespace zkc::test
#endif
