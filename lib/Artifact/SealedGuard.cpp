//===- SealedGuard.cpp - Action guard for sealed protocols ------*- C++ -*-===//
#include "zkc/Artifact/SealedGuard.h"

#include "mlir/IR/Action.h"
#include "mlir/IR/Operation.h"
#include "mlir/IR/Remarks.h"
#include "mlir/Rewrite/PatternApplicator.h"
#include "zkc/Dialect/Pir/PirOps.h"

using namespace mlir;
using namespace zkc;

/// Resolves the operation an IR unit belongs to.
static Operation *owningOp(const IRUnit &unit) {
  if (auto *op = llvm::dyn_cast_if_present<Operation *>(unit))
    return op;
  if (auto *region = llvm::dyn_cast_if_present<Region *>(unit))
    return region->getParentOp();
  if (auto *block = llvm::dyn_cast_if_present<Block *>(unit))
    return block->getParentOp();
  if (auto value = llvm::dyn_cast_if_present<Value>(unit))
    return value.getParentBlock()->getParentOp();
  return nullptr;
}

/// The refusal is audited, never silent (carrier.md §5). The
/// diagnostic stream always carries a plain remark for whoever is
/// watching; a configured remark engine (the upstream --remarks-*
/// flags, or a driver streamer) additionally receives the structured,
/// machine-readable failure remark under the `zkc-guard` category —
/// remark::failed is a no-op without an engine, so no conditional.
static void auditRefusal(Operation *sealed) {
  auto name = cast<pir::SealedOp>(sealed).getProtocolName();
  sealed->emitRemark("sealed-protocol guard refused a pattern application");
  remark::failed(sealed->getLoc(), remark::RemarkOpts::name("sealed-guard")
                                       .category("zkc-guard"))
      << remark::reason(
             "pattern application refused under sealed protocol '{0}'", name);
}

void zkc::installSealedGuard(MLIRContext &context) {
  context.registerActionHandler([](llvm::function_ref<void()> transform,
                                   const tracing::Action &action) {
    if (isa<ApplyPatternAction>(action)) {
      for (const IRUnit &unit : action.getContextIRUnits()) {
        for (Operation *op = owningOp(unit); op; op = op->getParentOp()) {
          if (!isa<pir::SealedOp>(op))
            continue;
          // Refuse by not running the transform: the pattern applicator
          // treats it as a failed match.
          auditRefusal(op);
          return;
        }
      }
    }
    transform();
  });
}
