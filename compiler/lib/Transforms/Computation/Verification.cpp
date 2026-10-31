#include "Support.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
LogicalResult
checkLowering(mlir::ModuleOp original, mlir::ModuleOp candidate,
              MathematicalSelectionPolicy policy,
              ArrayRef<std::pair<std::string, std::string>> selections,
              mathematical::RealizationWork &work,
              mathematical::VerificationDecision &outcome, bool maps) {
  outcome = {mathematical::VerificationObservation::Mismatch,
             "numerical lowering differs"};
  if (!original || !candidate)
    return failure();
  std::optional<CapacityCause> capacity;
  if (!chargeCopy(original, work.numericalCheckCopy, &capacity) ||
      !chargeCopy(candidate, work.numericalCheckCopy, &capacity)) {
    if (!capacity)
      capacity = CapacityCause{WorkOwner::AlgorithmChecking};
    capacity->owner = WorkOwner::AlgorithmChecking;
    outcome = {mathematical::VerificationObservation::RequiredCapacity,
               "numerical admission inspection capacity", capacity};
    return failure();
  }
  if (failed(zkc::admitStage(original)) || failed(zkc::admitStage(candidate)))
    return failure();
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return diagnostics::emit(candidate.emitError(),
                             maps ? "numerical-lowering-correspondence"
                                  : "computation-realization-correspondence",
                             "module shape changed");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after)
    return failure();
  OwningOpRef<mlir::ModuleOp> pinned, normalized;
  mlir::ModuleOp source = original;
  if (!selections.empty()) {
    if (!chargeCopy(original, work.numericalCheckCopy)) {
      outcome = {mathematical::VerificationObservation::RequiredCapacity,
                 "numerical source pinning copy capacity"};
      return failure();
    }
    pinned = cast<mlir::ModuleOp>(original->clone());
    auto root = cast<protocol_ir::ProtocolModuleOp>(pinned->getBody()->front());
    for (auto binding : root.getBody().front().getOps<runtime::BindingOp>())
      for (const auto &[name, implementation] : selections)
        if (binding.getSymName() == name)
          binding.setImplementation(implementation);
    source = *pinned;
  }
  bool hasComputations = false;
  source.walk([&](Operation *op) {
    hasComputations |=
        (mathematical::isComputationUnit(op) || isa<exec::ComputeOp>(op));
  });
  llvm::DenseMap<Operation *, func::FuncOp> entries;
  SmallVector<OwningOpRef<mlir::ModuleOp>> units;
  bool frontier = false;
  if (hasComputations) {
    SmallVector<exec::ComputeOp> calls;
    source.walk([&](exec::ComputeOp call) { calls.push_back(call); });
    SymbolTableCollection symbols;
    for (auto call : calls) {
      auto raw = resolveInvocation(call, symbols);
      if (!raw)
        return failure();
      auto unit = dyn_cast<mlir::ModuleOp>(raw->getParentOp());
      OwningOpRef<mlir::ModuleOp> closed;
      if (!unit || !mathematical::isComputationUnit(unit)) {
        closed = closeComputation(raw, work.numericalCheckCopy);
        if (!closed) {
          outcome = {mathematical::VerificationObservation::RequiredCapacity,
                     "numerical closure copy capacity",
                     CapacityCause{WorkOwner::AlgorithmExpansion}};
          return failure();
        }
        unit = *closed;
      }
      llvm::DenseSet<Operation *> generated;
      capacity.reset();
      auto normalized =
          normalizeUnit(unit, work.numericalCheckCopy, generated, &capacity);
      if (!normalized) {
        if (capacity)
          outcome = {mathematical::VerificationObservation::RequiredCapacity,
                     "numerical unit normalization capacity", capacity};
        return failure();
      }
      if (!generated.empty()) {
        frontier = true;
        break;
      }
      entries[call] = mathematical::getComputationEntry(*normalized);
      units.push_back(std::move(normalized));
    }
  }
  if (frontier) {
    // Reconstruct and check mathematical normalization/frontier only. No
    // executable emitter, selected menu or producer receipt enters this edge.
    std::optional<CapacityCause> capacity;
    normalized = prepareComputationRealization(source, work.numericalCheckCopy,
                                               work, &capacity);
    if (!normalized) {
      if (capacity)
        outcome = {mathematical::VerificationObservation::RequiredCapacity,
                   capacity->owner == WorkOwner::AlgorithmChecking
                       ? "numerical normalization checking capacity"
                       : "numerical normalization copy capacity",
                   capacity};
      return failure();
    }
    source = *normalized;
  }
  auto subject = cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  return verifyScopedNumericalContext(subject, after, before, policy, work,
                                      outcome, frontier ? nullptr : &entries);
}
} // namespace
LogicalResult verifyComputationRealization(mlir::ModuleOp original,
                                           mlir::ModuleOp candidate,
                                           MathematicalSelectionPolicy policy) {
  mathematical::RealizationWork work;
  mathematical::VerificationDecision outcome;
  return checkLowering(original, candidate, policy, {}, work, outcome, false);
}
} // namespace zkc::computation

namespace zkc::mathematical {
LogicalResult verifyNumericalLowering(
    mlir::ModuleOp original, mlir::ModuleOp candidate,
    MathematicalSelectionPolicy policy,
    ArrayRef<std::pair<std::string, std::string>> selections,
    RealizationWork *shared, VerificationDecision *reported) {
  RealizationWork standalone;
  VerificationDecision outcome;
  auto result =
      computation::checkLowering(original, candidate, policy, selections,
                                 shared ? *shared : standalone, outcome, true);
  if (reported)
    *reported = outcome;
  return result;
}
} // namespace zkc::mathematical
