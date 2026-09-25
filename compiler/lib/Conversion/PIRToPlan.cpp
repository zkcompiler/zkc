#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Transforms/Passes.h"
#include "zkc/Translation/Table.h"
using namespace mlir;
namespace zkc {
namespace {
class LowerControl : public ConversionPattern {
public:
  LowerControl(MLIRContext *context, StringRef source, StringRef target)
      : ConversionPattern(source, 1, context), target(target.str()) {}
  LogicalResult
  matchAndRewrite(Operation *op, ArrayRef<Value> operands,
                  ConversionPatternRewriter &rewriter) const override {
    OperationState state(op->getLoc(), target);
    state.addOperands(operands);
    state.addTypes(op->getResultTypes());
    state.addAttributes(op->getAttrs());
    for (unsigned i = 0; i < op->getNumRegions(); ++i)
      state.addRegion();
    Operation *replacement = rewriter.create(state);
    for (unsigned i = 0; i < op->getNumRegions(); ++i)
      rewriter.inlineRegionBefore(op->getRegion(i), replacement->getRegion(i),
                                  replacement->getRegion(i).end());
    rewriter.replaceOp(op, replacement->getResults());
    return success();
  }

private:
  std::string target;
};
struct LowerPass : PassWrapper<LowerPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(LowerPass)
  StringRef getArgument() const final { return "lower-pir-to-plan"; }
  StringRef getDescription() const final {
    return "Select direct stopped control while retaining logical domain "
           "operations";
  }
  void getDependentDialects(DialectRegistry &registry) const override {
    registerDialects(registry);
  }
  void runOnOperation() override {
    if (failed(lowerToPlan(getOperation())))
      signalPassFailure();
  }
};
} // namespace
LogicalResult lowerToPlan(ModuleOp module) {
  if (failed(verify(module)))
    return failure();
  for (auto &op : module.getBody()->getOperations())
    if (!isa<PIRProgramOp, PlanProgramOp>(op))
      return diagnostics::emit(op.emitOpError(), "expected-finite-program");
  ConversionTarget target(*module.getContext());
  target.addLegalDialect<PIRDialect, PlanDialect, AlgebraDialect,
                         PolynomialDialect>();
  target.addLegalOp<ModuleOp>();
  target.markUnknownOpDynamicallyLegal(
      [](Operation *op) { return isa<SourceOpInterface>(op); });
  target.addIllegalOp<PIRProgramOp, PIRReturnOp, PIRStopOp, PIRChooseOp,
                      PIRRepeatOp, PIRBindOp>();
  RewritePatternSet patterns(module.getContext());
  for (StringRef name :
       {"program", "return", "stop", "choose", "repeat", "bind"})
    patterns.add<LowerControl>(module.getContext(), ("pir." + name).str(),
                               ("plan." + name).str());
  return applyFullConversion(module, target, std::move(patterns));
}
std::unique_ptr<Pass> createLowerPIRToPlanPass() {
  return std::make_unique<LowerPass>();
}
} // namespace zkc
