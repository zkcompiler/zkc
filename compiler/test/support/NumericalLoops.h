#ifndef ZKC_TEST_SUPPORT_NUMERICAL_LOOPS_H
#define ZKC_TEST_SUPPORT_NUMERICAL_LOOPS_H

#include "KernelRecipes.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "llvm/Support/MemoryBuffer.h"

namespace zkc::test::loops {
inline constexpr MathematicalSelectionPolicy fused{false, false, true};
inline constexpr MathematicalSelectionPolicy ordered{false, false, false};

inline mlir::OwningOpRef<mlir::ModuleOp> clone(mlir::ModuleOp source) {
  return mlir::OwningOpRef<mlir::ModuleOp>(
      mlir::cast<mlir::ModuleOp>(source->clone()));
}
inline bool same(mlir::Operation *left, mlir::Operation *right) {
  return mlir::OperationEquivalence::isEquivalentTo(
      left, right, mlir::OperationEquivalence::IgnoreLocations);
}
inline mlir::OwningOpRef<mlir::ModuleOp>
fixture(mlir::MLIRContext &context, llvm::StringRef field = "bls12-381.fr",
        bool sequence = false) {
  auto bytes = llvm::MemoryBuffer::getFile(std::string(ZKC_LOOP_FIXTURES) +
                                           "/collect-fold.mlir");
  require(bool(bytes), "missing collect-fold fixture");
  auto text = (*bytes)->getBuffer().str();
  if (field != "bls12-381.fr") {
    size_t position = 0;
    while ((position = text.find("bls12-381.fr", position)) !=
           std::string::npos) {
      text.replace(position, 12, field.str());
      position += field.size();
    }
  }
  if (sequence) {
    auto position = text.find("!V = !algebra.field_vector<");
    auto end = text.find('\n', position);
    require(position != std::string::npos && end != std::string::npos,
            "missing nominal collection alias");
    text.replace(position, end - position, "!V = !data.sequence<!F>");
  }
  auto result = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
  require(bool(result) && mlir::succeeded(mlir::verify(*result)),
          "collect-fold fixture refused");
  return result;
}
inline mlir::OwningOpRef<kernel::ModuleOp>
source(mlir::MLIRContext &context, llvm::StringRef helper,
       llvm::StringRef field = "bls12-381.fr", bool sequence = false) {
  auto original = fixture(context, field, sequence);
  return kernelRecipeSource(&original->getBody()->front(), helper, "evaluate");
}
inline mlir::func::FuncOp helper(kernel::ModuleOp unit, llvm::StringRef name) {
  auto result = mlir::SymbolTable(unit).lookup<mlir::func::FuncOp>(name);
  require(bool(result), "missing numerical helper");
  return result;
}
inline local::OperationBindingOp primitiveBinding(mlir::Operation *user) {
  // Schedules declare bindings in builtin modules; executable fragments use
  // Protocol owners. Resolve in the user's lexical symbol table in both cases.
  auto *owner = mlir::SymbolTable::getNearestSymbolTable(user);
  auto reference = user->getAttrOfType<mlir::FlatSymbolRefAttr>("binding");
  require(owner && reference, "missing primitive binding reference");
  auto result = mlir::dyn_cast_or_null<local::OperationBindingOp>(
      mlir::SymbolTable::lookupSymbolIn(owner, reference));
  require(bool(result), "missing actual primitive binding");
  return result;
}
inline local::FuncOp entry(mlir::ModuleOp output) {
  auto result = mlir::SymbolTable(kernelRecipeOutput(output))
                    .lookup<local::FuncOp>("evaluate");
  require(bool(result), "missing executable numerical entry");
  return result;
}
inline llvm::SmallVector<mlir::Operation *> operations(mlir::Operation *root,
                                                       llvm::StringRef name) {
  llvm::SmallVector<mlir::Operation *> result;
  root->walk([&](mlir::Operation *op) {
    if (op->getName().getStringRef() == name)
      result.push_back(op);
  });
  return result;
}
inline llvm::SmallVector<local::LocalForOp> stateLoops(mlir::ModuleOp output) {
  llvm::SmallVector<local::LocalForOp> result;
  entry(output).walk([&](local::LocalForOp loop) {
    if (loop->getNumResults())
      result.push_back(loop);
  });
  return result;
}
inline mlir::OwningOpRef<mlir::ModuleOp>
realize(kernel::ModuleOp unit, MathematicalSelectionPolicy policy = fused,
        finite::VerificationLimits limits = {},
        mathematical::RealizationWork *available = nullptr) {
  mathematical::RealizationWork work;
  auto result = realizeKernelEntry(unit, "collect_fold", policy,
                                   available ? *available : work, limits);
  require(bool(result), "numerical realization failed");
  return result;
}
inline void accepts(kernel::ModuleOp unit, mlir::ModuleOp output,
                    MathematicalSelectionPolicy policy = fused,
                    finite::VerificationLimits limits = {}) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch, {}};
  require(mlir::succeeded(kernel::verifyEntryRecipes(
              unit, output, "collect_fold", policy, limits, &outcome)) &&
              outcome.status == finite::VerificationStatus::Verified,
          "original source does not match actual numerical output");
}
inline void mismatch(kernel::ModuleOp unit, mlir::ModuleOp output,
                     MathematicalSelectionPolicy policy = fused) {
  finite::VerificationResult outcome{finite::VerificationStatus::Verified, {}};
  require(mlir::failed(kernel::verifyEntryRecipes(unit, output, "collect_fold",
                                                  policy, {}, &outcome)) &&
              outcome.status == finite::VerificationStatus::Mismatch,
          "source/candidate difference was accepted or classified as capacity");
}
} // namespace zkc::test::loops
#endif
