//===- TestSealedGuard.cpp - Guard instrumentation test pass ----*- C++ -*-===//
// Instrumentation for the sealing enforcement guard: tries to apply a
// rewrite pattern everywhere. The guard itself is installed by the
// driver (the dialect-load extension in zkc-opt.cpp), so this pass also
// proves that installation happened — the pattern must land inside open
// protocols and be refused inside sealed ones.
//===----------------------------------------------------------------------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"
#include "zkc/Dialect/Pir/PirOps.h"

using namespace mlir;
using namespace zkc;

namespace {

/// Rewrites the label of any slot labeled "marker".
struct RelabelMarker : public OpRewritePattern<pir::SlotOp> {
  using OpRewritePattern::OpRewritePattern;

  LogicalResult matchAndRewrite(pir::SlotOp slot,
                                PatternRewriter &rewriter) const override {
    if (slot.getLabel() != "marker")
      return failure();
    rewriter.modifyOpInPlace(slot, [&] { slot.setLabel("rewritten"); });
    return success();
  }
};

struct TestSealedGuardPass
    : public PassWrapper<TestSealedGuardPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSealedGuardPass)

  StringRef getArgument() const override { return "test-sealed-guard"; }
  StringRef getDescription() const override {
    return "install the sealed-protocol guard and attempt pattern "
           "applications everywhere";
  }

  void runOnOperation() override {
    RewritePatternSet patterns(&getContext());
    patterns.add<RelabelMarker>(&getContext());
    // Convergence failure is fine here; the test reads the IR.
    (void)applyPatternsGreedily(getOperation(), std::move(patterns));
  }
};

} // namespace

namespace zkc {
namespace test {
void registerTestSealedGuardPass() { PassRegistration<TestSealedGuardPass>(); }
} // namespace test
} // namespace zkc
