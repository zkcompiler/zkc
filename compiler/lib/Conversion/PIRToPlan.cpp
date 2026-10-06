#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Table/IR/Program.h"
#include "zkc/Transforms/Passes.h"
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
    if (!isa<zkc::table::PIRProgramOp, zkc::table::PlanProgramOp>(op))
      return diagnostics::emit(op.emitOpError(), "expected-finite-program");
  ConversionTarget target(*module.getContext());
  target.addLegalDialect<zkc::table::TableDialect, zkc::plan::PlanDialect,
                         zkc::algebra::AlgebraDialect,
                         zkc::poly::PolynomialDialect>();
  target.addLegalOp<ModuleOp>();
  target.markUnknownOpDynamicallyLegal(
      [](Operation *op) { return isa<SourceOpInterface>(op); });
  target.addIllegalOp<zkc::table::PIRProgramOp, zkc::table::PIRReturnOp,
                      zkc::table::PIRStopOp, zkc::table::PIRChooseOp,
                      zkc::table::PIRRepeatOp, zkc::table::PIRBindOp>();
  RewritePatternSet patterns(module.getContext());
  const std::pair<StringRef, StringRef> controls[] = {
      {table::PIRProgramOp::getOperationName(),
       table::PlanProgramOp::getOperationName()},
      {table::PIRReturnOp::getOperationName(),
       table::PlanReturnOp::getOperationName()},
      {table::PIRStopOp::getOperationName(),
       table::PlanStopOp::getOperationName()},
      {table::PIRChooseOp::getOperationName(),
       table::PlanChooseOp::getOperationName()},
      {table::PIRRepeatOp::getOperationName(),
       table::PlanRepeatOp::getOperationName()},
      {table::PIRBindOp::getOperationName(),
       table::PlanBindOp::getOperationName()},
  };
  for (const auto &[source, destination] : controls)
    patterns.add<LowerControl>(module.getContext(), source, destination);
  return applyFullConversion(module, target, std::move(patterns));
}
std::unique_ptr<Pass> createLowerPIRToPlanPass() {
  return std::make_unique<LowerPass>();
}
} // namespace zkc
