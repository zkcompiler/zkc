#include "envelope/Specialization.h"
#include "envelope/Envelope.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Dialect/IR.h"
#include "zkc/Dialect/Protocol/Execution.h"
#include "llvm/Support/Error.h"

using namespace mlir;

namespace envelope {
namespace {
// The bounded witness handles logical field.add only. Physical operations and
// extension attributes require a separately reviewed applicability rule.
bool logicalAttributes(DictionaryAttr attributes) {
  if (!attributes || attributes.size() != 3)
    return false;
  auto site = attributes.getAs<StringAttr>("site");
  auto binding = attributes.getAs<FlatSymbolRefAttr>("binding");
  auto parameters = attributes.getAs<ArrayAttr>("parameters");
  return site && !site.getValue().empty() && binding && parameters &&
         parameters.empty();
}

bool fieldSum(Operation *op) {
  if (!op || !isa<zkc::algebra::FieldSumOp>(op) || op->getNumOperands() != 2 ||
      op->getNumResults() != 1 || !logicalAttributes(op->getAttrDictionary()))
    return false;
  Type type = op->getResult(0).getType();
  return isa<zkc::algebra::FieldType>(type) &&
         op->getOperand(0).getType() == type &&
         op->getOperand(1).getType() == type;
}

class Specialize final : public OpRewritePattern<zkc::algebra::FieldSumOp> {
public:
  using OpRewritePattern::OpRewritePattern;
  LogicalResult matchAndRewrite(zkc::algebra::FieldSumOp second,
                                PatternRewriter &rewriter) const override {
    if (!fieldSum(second))
      return failure();
    Operation *first = second->getOperand(0).getDefiningOp();
    if (!fieldSum(first) || first->getNextNode() != second.getOperation() ||
        !first->getResult(0).hasOneUse())
      return failure();
    // Both dictionaries are retained separately, including distinct binding and
    // occurrence identities. No source binding declaration is added or removed.
    rewriter.setInsertionPoint(first);
    OperationState state(second.getLoc(), FieldSumChainOp::getOperationName());
    state.addOperands(
        {first->getOperand(0), first->getOperand(1), second->getOperand(1)});
    state.addTypes(second->getResultTypes());
    state.addAttribute("first_attributes", first->getAttrDictionary());
    state.addAttribute("second_attributes", second->getAttrDictionary());
    state.addAttribute("first_location", first->getLoc());
    state.addAttribute("second_location", second.getLoc());
    Operation *composite = rewriter.create(state);
    rewriter.replaceOp(second, composite->getResults());
    rewriter.eraseOp(first);
    return success();
  }
};

class Decompose final : public OpRewritePattern<FieldSumChainOp> {
public:
  using OpRewritePattern::OpRewritePattern;
  LogicalResult matchAndRewrite(FieldSumChainOp composite,
                                PatternRewriter &rewriter) const override {
    // Check the complete shape before using generated accessors: a C++ client
    // can construct malformed IR without running the textual parser.
    if (composite->getNumOperands() != 3 || composite->getNumResults() != 1 ||
        composite->getNumRegions() || composite->getNumSuccessors() ||
        composite->getAttrs().size() != 4)
      return failure();
    auto first = composite->getAttrOfType<DictionaryAttr>("first_attributes");
    auto second = composite->getAttrOfType<DictionaryAttr>("second_attributes");
    auto firstLocation =
        composite->getAttrOfType<LocationAttr>("first_location");
    auto secondLocation =
        composite->getAttrOfType<LocationAttr>("second_location");
    Type type = composite->getResult(0).getType();
    if (!logicalAttributes(first) || !logicalAttributes(second) ||
        !firstLocation || !secondLocation ||
        !isa<zkc::algebra::FieldType>(type) ||
        llvm::any_of(composite->getOperandTypes(),
                     [type](Type input) { return input != type; }))
      return failure();
    rewriter.setInsertionPoint(composite);
    auto restore = [&](Location location, DictionaryAttr attributes, Value lhs,
                       Value rhs) {
      OperationState state(location,
                           zkc::algebra::FieldSumOp::getOperationName());
      state.addOperands({lhs, rhs});
      state.addTypes(type);
      state.addAttributes(attributes.getValue());
      return rewriter.create(state)->getResult(0);
    };
    Value partial = restore(firstLocation, first, composite->getOperand(0),
                            composite->getOperand(1));
    Value result =
        restore(secondLocation, second, partial, composite->getOperand(2));
    rewriter.replaceOp(composite, result);
    return success();
  }
};

LogicalResult admitted(ModuleOp module) { return mlir::verify(module); }
} // namespace

void populateFieldSumSpecializationPatterns(RewritePatternSet &patterns) {
  patterns.add<Specialize>(patterns.getContext());
}

void populateFieldSumDecompositionPatterns(RewritePatternSet &patterns) {
  patterns.add<Decompose>(patterns.getContext());
}

LogicalResult specializeFieldSums(ModuleOp module) {
  if (failed(admitted(module)))
    return failure();
  module.getContext()->getOrLoadDialect<EnvelopeDialect>();
  Specialize pattern(module.getContext());
  PatternRewriter rewriter(module.getContext());
  // Post-order walking permits erasing the current operation. A match erases
  // only it and its already-visited immediate predecessor. Unlike a greedy
  // canonicalizer this does not fold or delete unrelated admitted operations.
  module.walk([&](zkc::algebra::FieldSumOp op) {
    (void)pattern.matchAndRewrite(op, rewriter);
  });
  return success();
}

LogicalResult decomposeFieldSums(ModuleOp module) {
  ConversionTarget target(*module.getContext());
  target.addIllegalOp<FieldSumChainOp>();
  // This conversion discharges only the contribution's temporary abstraction.
  // All other operations still pass whole-module verification below;
  // conversion legality is not an executable-support or semantic proof.
  target.markUnknownOpDynamicallyLegal([](Operation *) { return true; });
  RewritePatternSet patterns(module.getContext());
  populateFieldSumDecompositionPatterns(patterns);
  if (failed(applyFullConversion(module, target, std::move(patterns))))
    return failure();
  return admitted(module);
}
} // namespace envelope
