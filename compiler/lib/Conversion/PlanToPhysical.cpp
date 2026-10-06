#include "mlir/IR/Verifier.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Table/IR/Physical.h"
#include "zkc/Dialect/Table/IR/Program.h"
#include "zkc/Transforms/Passes.h"
using namespace mlir;
using namespace llvm;
namespace zkc {
namespace {
LogicalResult lowerToPhysical(ModuleOp, StringRef mode);

class LowerPhysical : public ConversionPattern {
public:
  LowerPhysical(TypeConverter &types, MLIRContext *context, StringRef mode,
                const llvm::DenseMap<Operation *, std::string> &descriptors)
      : ConversionPattern(types, MatchAnyOpTypeTag(), 1, context),
        mode(mode.str()), descriptors(descriptors) {}
  LogicalResult
  matchAndRewrite(Operation *op, ArrayRef<Value> operands,
                  ConversionPatternRewriter &rewriter) const override {
    bool control = isa<zkc::table::PlanProgramOp, zkc::table::PlanReturnOp,
                       zkc::table::PlanStopOp, zkc::table::PlanChooseOp,
                       zkc::table::PlanRepeatOp, zkc::table::PlanBindOp>(op);
    auto descriptor = descriptors.find(op);
    if (!control && descriptor == descriptors.end())
      return failure();
    SmallVector<Type> results;
    if (failed(getTypeConverter()->convertTypes(op->getResultTypes(), results)))
      return failure();
    StringRef name = control ? op->getName().getStringRef()
                     : isa<zkc::table::EvaluateOp>(op) ? "table.plan.prepare"
                                                       : "table.plan.invoke";
    OperationState state(op->getLoc(), name);
    state.addOperands(operands);
    state.addTypes(results);
    if (control) {
      NamedAttrList attrs(op->getAttrs());
      if (isa<zkc::table::PlanProgramOp>(op)) {
        auto result = op->getAttrOfType<TypeAttr>("resultType");
        attrs.set("resultType", TypeAttr::get(physicalType(result.getValue())));
        attrs.set("realization", rewriter.getStringAttr("table-physical-plan"));
      }
      state.addAttributes(attrs);
    } else {
      state.addAttribute(
          isa<zkc::table::EvaluateOp>(op) ? "mode" : "descriptor",
          rewriter.getStringAttr(
              isa<zkc::table::EvaluateOp>(op) ? mode : descriptor->second));
    }
    for (unsigned i = 0; i < op->getNumRegions(); ++i)
      state.addRegion();
    Operation *replacement = rewriter.create(state);
    for (unsigned i = 0; i < op->getNumRegions(); ++i) {
      Region &region = replacement->getRegion(i);
      rewriter.inlineRegionBefore(op->getRegion(i), region, region.end());
      if (failed(rewriter.convertRegionTypes(&region, *getTypeConverter())))
        return failure();
    }
    rewriter.replaceOp(op, replacement->getResults());
    return success();
  }

private:
  std::string mode;
  const llvm::DenseMap<Operation *, std::string> &descriptors;
};
struct PhysicalPass : PassWrapper<PhysicalPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(PhysicalPass)
  explicit PhysicalPass(StringRef selectedMode) { mode = selectedMode.str(); }
  PhysicalPass(const PhysicalPass &other) : PassWrapper(other) {}
  Option<std::string> mode{*this, "mode",
                           llvm::cl::desc("lazy or materialized"),
                           llvm::cl::init("lazy")};
  StringRef getArgument() const final { return "lower-plan-to-physical"; }
  StringRef getDescription() const final {
    return "Select immutable scalar preparation and convert region signatures";
  }
  void getDependentDialects(DialectRegistry &registry) const override {
    registerDialects(registry);
  }
  void runOnOperation() override {
    if (failed(lowerToPhysical(getOperation(), mode)))
      signalPassFailure();
  }
};
LogicalResult lowerToPhysical(ModuleOp module, StringRef mode) {
  if (mode != "lazy" && mode != "materialized")
    return diagnostics::emit(module.emitError(),
                             "unsupported-preparation-mode");
  // A closed direct plan is the admitted input of this representation pass.
  if (failed(verify(module)))
    return failure();
  if (!llvm::hasSingleElement(*module.getBody()) ||
      !isa<zkc::table::PlanProgramOp>(module.getBody()->front()))
    return diagnostics::emit(module.emitError(), "expected-plan-program");
  Operation &program = module.getBody()->front();
  if (isPhysicalProgram(&program))
    return diagnostics::emit(program.emitError(), "expected-direct-plan");
  auto library = resolveProgramLibrary(&program);
  if (!library)
    return diagnostics::emit(program.emitError(), library.takeError());
  if (printJson((*library)->dependencies()) != "[[\"table-protocol\",\"1\"]]")
    return diagnostics::emit(program.emitError(),
                             "unsupported-physical-library");
  llvm::DenseMap<Operation *, std::string> descriptors;
  module.walk([&](Operation *op) {
    if (auto source = dyn_cast<SourceOpInterface>(op))
      descriptors.try_emplace(op, printJson(source.getSourceDescriptor()));
  });
  TypeConverter types;
  types.addConversion([](Type type) { return physicalType(type); });
  ConversionTarget target(*module.getContext());
  target.addLegalOp<ModuleOp, zkc::table::PrepareOp, zkc::table::InvokeOp>();
  target.addDynamicallyLegalOp<zkc::table::PlanProgramOp>(
      [&](zkc::table::PlanProgramOp op) {
        return isPhysicalProgram(op) && types.isLegal(op) &&
               types.isLegal(&op.getBody()) &&
               types.isLegal(op.getResultType());
      });
  target
      .addDynamicallyLegalOp<zkc::table::PlanReturnOp, zkc::table::PlanStopOp,
                             zkc::table::PlanChooseOp, zkc::table::PlanRepeatOp,
                             zkc::table::PlanBindOp>([&](Operation *op) {
        return types.isLegal(op) &&
               llvm::all_of(op->getRegions(), [&](Region &region) {
                 return types.isLegal(&region);
               });
      });
  target.addIllegalOp<UnrealizedConversionCastOp>();
  RewritePatternSet patterns(module.getContext());
  patterns.add<LowerPhysical>(types, module.getContext(), mode, descriptors);
  if (failed(applyFullConversion(module, target, std::move(patterns))))
    return failure();
  return verify(module);
}
} // namespace

std::unique_ptr<Pass> createLowerPlanToPhysicalPass(StringRef mode) {
  return std::make_unique<PhysicalPass>(mode);
}
} // namespace zkc
