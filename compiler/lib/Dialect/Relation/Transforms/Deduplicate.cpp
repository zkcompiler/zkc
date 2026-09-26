#include "mlir/IR/Builders.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Relations.h"

using namespace llvm;
using namespace mlir;
namespace zkc::relation {
namespace {
struct DeduplicateRelationsPass
    : PassWrapper<DeduplicateRelationsPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(DeduplicateRelationsPass)
  StringRef getArgument() const final { return "zkc-deduplicate-relations"; }
  StringRef getDescription() const final {
    return "Remove exact duplicate rank-one constraint rows";
  }
  void runOnOperation() final {
    for (auto op : getOperation().getOps<R1CSRelationOp>()) {
      auto relation = readR1CSOperation(op);
      if (!relation) {
        diagnostics::emit(op.emitOpError(), relation.takeError());
        signalPassFailure();
        return;
      }
      Builder b(op.getContext());
      op->setAttr("constraints",
                  encodeR1CSConstraints(b, relation->deduplicate()));
    }
  }
};
} // namespace
std::unique_ptr<Pass> createDeduplicateRelationsPass() {
  return std::make_unique<DeduplicateRelationsPass>();
}
} // namespace zkc::relation
