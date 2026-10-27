#include "Support.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
LogicalResult
checkLowering(mlir::ModuleOp original, mlir::ModuleOp candidate,
              MathematicalSelectionPolicy policy,
              ArrayRef<std::pair<std::string, std::string>> selections,
              mathematical::RealizationWork &work,
              mathematical::VerificationDecision &outcome, bool maps) {
  outcome = {mathematical::VerificationObservation::Mismatch,
             "numerical lowering differs"};
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return diagnostics::emit(candidate.emitError(),
                             maps ? "numerical-lowering-correspondence"
                                  : "kernel-lowering-correspondence",
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
  bool hasKernels = false;
  source.walk([&](Operation *op) {
    hasKernels |=
        (mathematical::isComputationUnit(op) || isa<exec::ComputeOp>(op));
  });
  if (hasKernels) {
    // Reconstruct and check mathematical normalization/frontier only. No
    // executable emitter, selected menu or producer receipt enters this edge.
    std::optional<CapacityCause> capacity;
    normalized =
        prepareKernelLowering(source, &work.numericalCheckCopy, &capacity);
    if (!normalized) {
      if (capacity)
        outcome = {mathematical::VerificationObservation::RequiredCapacity,
                   "numerical normalization copy capacity", capacity};
      return failure();
    }
    source = *normalized;
  }
  auto subject = cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  return verifyScopedNumericalContext(subject, after, before, policy, work,
                                      outcome);
}
} // namespace
LogicalResult verifyKernelLowering(mlir::ModuleOp original,
                                   mlir::ModuleOp candidate,
                                   MathematicalSelectionPolicy policy) {
  mathematical::RealizationWork work;
  mathematical::VerificationDecision outcome;
  return checkLowering(original, candidate, policy, {}, work, outcome, false);
}
} // namespace zkc::kernel

namespace zkc::mathematical {
LogicalResult verifyNumericalLowering(
    mlir::ModuleOp original, mlir::ModuleOp candidate,
    MathematicalSelectionPolicy policy,
    ArrayRef<std::pair<std::string, std::string>> selections,
    RealizationWork *shared, VerificationDecision *reported) {
  RealizationWork standalone;
  VerificationDecision outcome;
  auto result =
      kernel::checkLowering(original, candidate, policy, selections,
                            shared ? *shared : standalone, outcome, true);
  if (reported)
    *reported = outcome;
  return result;
}
} // namespace zkc::mathematical
