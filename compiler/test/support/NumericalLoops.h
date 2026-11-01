#ifndef ZKC_TEST_SUPPORT_NUMERICAL_LOOPS_H
#define ZKC_TEST_SUPPORT_NUMERICAL_LOOPS_H

#include "ComputationRecipes.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
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
  // The dormant seeds are native literals too. Specializing the field must
  // specialize their canonical carrier width before structural parsing.
  auto literal = take(algebra::decodeFieldLiteral(
      algebra::FieldType::get(&context, field), "7"));
  auto width =
      mlir::cast<mlir::IntegerType>(literal.getValue().getType()).getWidth();
  std::string carrier = "ui" + std::to_string(width);
  size_t position = 0;
  while ((position = text.find("ui255", position)) != std::string::npos) {
    text.replace(position, 5, carrier);
    position += carrier.size();
  }
  if (sequence) {
    auto position = text.find("!V = !data.field_vector<");
    auto end = text.find('\n', position);
    require(position != std::string::npos && end != std::string::npos,
            "missing nominal collection alias");
    text.replace(position, end - position, "!V = !data.sequence<!F>");
  }
  auto result = mlir::parseSourceString<mlir::ModuleOp>(text, &context);
  require(bool(result) && mlir::succeeded(zkc::admitStage(*result)),
          "collect-fold fixture refused");
  return result;
}
inline mlir::OwningOpRef<mlir::ModuleOp>
source(mlir::MLIRContext &context, llvm::StringRef helper,
       llvm::StringRef field = "bls12-381.fr", bool sequence = false) {
  auto original = fixture(context, field, sequence);
  return computationRecipeSource(&original->getBody()->front(), helper,
                                 "evaluate");
}
inline mlir::func::FuncOp helper(mlir::ModuleOp unit, llvm::StringRef name) {
  auto result = mlir::SymbolTable(unit).lookup<mlir::func::FuncOp>(name);
  require(bool(result), "missing numerical helper");
  return result;
}
inline runtime::BindingOp primitiveBinding(mlir::Operation *user) {
  // Schedules declare bindings in builtin modules; executable fragments use
  // Protocol owners. Resolve in the user's lexical symbol table in both cases.
  auto *owner = mlir::SymbolTable::getNearestSymbolTable(user);
  auto reference = user->getAttrOfType<mlir::FlatSymbolRefAttr>("binding");
  require(owner && reference, "missing primitive binding reference");
  auto result = mlir::dyn_cast_or_null<runtime::BindingOp>(
      mlir::SymbolTable::lookupSymbolIn(owner, reference));
  require(bool(result), "missing actual primitive binding");
  return result;
}
inline mlir::func::FuncOp entry(mlir::ModuleOp output) {
  auto result = mlir::SymbolTable(computationRecipeOutput(output))
                    .lookup<mlir::func::FuncOp>("evaluate");
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
inline protocol::SourceExecutionStep loopStep(mlir::ModuleOp module,
                                              exec::RangeOp loop) {
  auto closure = take(
      protocol::readSourceExecutionClosure(computationRecipeOutput(module)));
  auto function = loop->getParentOfType<mlir::func::FuncOp>();
  for (const auto &step : closure.bodies.at(function.getSymName().str()))
    if (step.operation == loop.getOperation())
      return step;
  throw std::runtime_error("missing scoped loop occurrence");
}
inline llvm::SmallVector<exec::RangeOp> stateLoops(mlir::ModuleOp output) {
  auto closure = take(
      protocol::readSourceExecutionClosure(computationRecipeOutput(output)));
  llvm::SmallVector<exec::RangeOp> result;
  output.walk([&](exec::RangeOp loop) {
    auto function = loop->getParentOfType<mlir::func::FuncOp>();
    for (const auto &step : closure.bodies.at(function.getSymName().str()))
      if (step.operation == loop.getOperation() && !step.outputs.empty())
        result.push_back(loop);
  });
  return result;
}
inline mlir::OwningOpRef<mlir::ModuleOp>
realize(mlir::ModuleOp unit, MathematicalSelectionPolicy policy = fused,
        finite::VerificationLimits limits = {},
        mathematical::RealizationWork *available = nullptr) {
  mathematical::RealizationWork work;
  auto result = realizeComputationEntry(unit, "collect_fold", policy,
                                        available ? *available : work, limits);
  require(bool(result), "numerical realization failed");
  return result;
}
inline void accepts(mlir::ModuleOp unit, mlir::ModuleOp output,
                    MathematicalSelectionPolicy policy = fused,
                    finite::VerificationLimits limits = {}) {
  finite::VerificationResult outcome{finite::VerificationStatus::Mismatch, {}};
  require(mlir::succeeded(computation::verifyEntryRecipes(
              unit, output, "collect_fold", policy, limits, &outcome)) &&
              outcome.status == finite::VerificationStatus::Verified,
          "original source does not match actual numerical output");
}
inline void mismatch(mlir::ModuleOp unit, mlir::ModuleOp output,
                     MathematicalSelectionPolicy policy = fused) {
  finite::VerificationResult outcome{finite::VerificationStatus::Verified, {}};
  require(mlir::failed(computation::verifyEntryRecipes(
              unit, output, "collect_fold", policy, {}, &outcome)) &&
              outcome.status == finite::VerificationStatus::Mismatch,
          "source/candidate difference was accepted or classified as capacity");
}
} // namespace zkc::test::loops
#endif
