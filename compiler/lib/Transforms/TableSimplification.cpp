#include "zkc/Transforms/TableSimplification.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Plan/IR/Physical.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Table.h"
#include "llvm/ADT/DenseMap.h"

using namespace mlir;
namespace zkc {
namespace {
// Isolated regions introduce fresh block arguments for their explicit
// captures. Rename duplicate captures to the same local SSA value before
// visiting the region, so an outer linear alias also reaches nested chains.
// Keep every capture operand and block argument, including unused ones.
void propagateCaptureAliases(Operation *op, IRRewriter &rewriter) {
  bool repeat = isa<PIRRepeatOp, PlanRepeatOp>(op);
  bool binding = isa<PIRBindOp, PlanBindOp>(op);
  if (!repeat && !binding && !isa<PIRChooseOp, PlanChooseOp>(op))
    return;
  auto captures = op->getOperands().drop_front(binding ? 1 : 2);
  for (Region &region : op->getRegions()) {
    // The loop accumulator is a changing value, even when its initial operand
    // equals an invariant capture. Never include it in the capture alias map.
    auto arguments = region.front().getArguments().drop_front(repeat ? 2 : 1);
    llvm::DenseMap<Value, Value> aliases;
    for (auto [capture, argument] : llvm::zip(captures, arguments)) {
      auto [found, inserted] = aliases.try_emplace(capture, argument);
      if (!inserted)
        rewriter.replaceAllUsesWith(argument, found->second);
    }
  }
}

struct SimplifyPass : PassWrapper<SimplifyPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SimplifyPass)
  StringRef getArgument() const final { return "simplify-table-regions"; }
  StringRef getDescription() const final {
    return "Remove identical-endpoint table linear interpolation in logical "
           "regions without eliminating other operations";
  }
  void getDependentDialects(DialectRegistry &registry) const override {
    registerDialects(registry);
  }
  void runOnOperation() override {
    if (failed(simplifyTableRegions(getOperation())))
      signalPassFailure();
  }
};
} // namespace

LogicalResult simplifyTableRegions(ModuleOp module) {
  if (!llvm::hasSingleElement(*module.getBody()) ||
      !isa<PIRProgramOp, PlanProgramOp>(module.getBody()->front()))
    return module.emitError("expected-logical-program");
  if (failed(verify(module)))
    return failure();
  Operation *program = &module.getBody()->front();
  if (isPhysicalProgram(program))
    return program->emitError("expected-logical-program");
  auto library = resolveProgramLibrary(program);
  if (!library)
    return program->emitError(llvm::toString(library.takeError()));
  if ((*library)->dependencies() !=
      llvm::json::Value(
          llvm::json::Array{llvm::json::Array{"table-protocol", "1"}}))
    return program->emitError("unsupported-simplification-library");

  // A verified program consists of single-block structured regions: each
  // definition precedes its uses. A top-down forward walk therefore resolves
  // chains in one traversal, including aliases passed into nested regions.
  // IRRewriter replaces only the requested operation; no greedy driver, fold
  // hook, canonicalizer, or implicit DCE participates in this pass.
  IRRewriter rewriter(module.getContext());
  program->walk<WalkOrder::PreOrder>([&](Operation *op) {
    if (auto linear = dyn_cast<LinearOp>(op)) {
      if (linear.getAtZero() == linear.getAtOne()) {
        rewriter.replaceOp(linear, linear.getAtZero());
        // MLIR's pre-order walker requires skipping an erased operation.
        return WalkResult::skip();
      }
    }
    propagateCaptureAliases(op, rewriter);
    return WalkResult::advance();
  });
  return verify(module);
}

std::unique_ptr<Pass> createSimplifyTableRegionsPass() {
  return std::make_unique<SimplifyPass>();
}
} // namespace zkc
