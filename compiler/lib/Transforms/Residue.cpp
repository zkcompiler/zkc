#include "zkc/Transforms/Residue.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Func/Transforms/FuncConversions.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/DialectConversion.h"
#include "zkc/Dialect/Residue/IR/ResidueOps.h"

using namespace mlir;
namespace zkc::residue {
namespace {
class Words : public TypeConverter {
public:
  Words() {
    addConversion([](Type type) { return type; });
    addConversion([](ValueType type) -> Type {
      return IntegerType::get(type.getContext(), type.getWidth());
    });
  }
};
Value constant(ConversionPatternRewriter &builder, Location location,
               const llvm::APInt &value) {
  return arith::ConstantOp::create(
      builder, location,
      builder.getIntegerAttr(builder.getIntegerType(value.getBitWidth()),
                             value));
}
Value widen(ConversionPatternRewriter &builder, Location location, Value value,
            unsigned width) {
  auto current = cast<IntegerType>(value.getType()).getWidth();
  if (current == width)
    return value;
  return arith::ExtUIOp::create(builder, location,
                                builder.getIntegerType(width), value);
}
Value narrow(ConversionPatternRewriter &builder, Location location, Value value,
             unsigned width) {
  if (cast<IntegerType>(value.getType()).getWidth() == width)
    return value;
  return arith::TruncIOp::create(builder, location,
                                 builder.getIntegerType(width), value);
}
struct Constant : OpConversionPattern<ResidueConstantOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(ResidueConstantOp op, OpAdaptor,
                  ConversionPatternRewriter &builder) const override {
    builder.replaceOp(op, constant(builder, op.getLoc(),
                                   op.getValue().getValue().getValue()));
    return success();
  }
};
template <typename Op> struct Binary : OpConversionPattern<Op> {
  using OpConversionPattern<Op>::OpConversionPattern;
  LogicalResult
  matchAndRewrite(Op op, typename Op::Adaptor args,
                  ConversionPatternRewriter &builder) const override {
    auto residue = dyn_cast<ValueType>(op.getResult().getType());
    if (!residue)
      return builder.notifyMatchFailure(
          op, "scalarize tensors before word lowering");
    unsigned width = residue.getWidth();
    unsigned wide =
        std::is_same_v<Op, ResidueMultiplyOp> ? 2 * width : width + 1;
    auto loc = op.getLoc();
    Value x = widen(builder, loc, args.getLhs(), wide);
    Value y = widen(builder, loc, args.getRhs(), wide);
    Value q =
        constant(builder, loc, residue.getModulus().getValue().zext(wide));
    Value result;
    if constexpr (std::is_same_v<Op, ResidueMultiplyOp>)
      result = arith::MulIOp::create(builder, loc, x, y);
    else if constexpr (std::is_same_v<Op, ResidueSubtractOp>) {
      auto sum = arith::AddIOp::create(builder, loc, x, q);
      result = arith::SubIOp::create(builder, loc, sum, y);
    } else
      result = arith::AddIOp::create(builder, loc, x, y);
    result = arith::RemUIOp::create(builder, loc, result, q);
    builder.replaceOp(op, narrow(builder, loc, result, width));
    return success();
  }
};
struct Project : OpConversionPattern<ResidueProjectOp> {
  using OpConversionPattern::OpConversionPattern;
  LogicalResult
  matchAndRewrite(ResidueProjectOp op, OpAdaptor args,
                  ConversionPatternRewriter &builder) const override {
    auto residue = dyn_cast<ValueType>(op.getResult().getType());
    if (!residue)
      return builder.notifyMatchFailure(
          op, "scalarize tensors before word lowering");
    unsigned wide =
        std::max(residue.getWidth(),
                 cast<IntegerType>(args.getInput().getType()).getWidth());
    auto input = widen(builder, op.getLoc(), args.getInput(), wide);
    auto modulus = constant(builder, op.getLoc(),
                            residue.getModulus().getValue().zextOrTrunc(wide));
    Value result = arith::RemUIOp::create(builder, op.getLoc(), input, modulus);
    builder.replaceOp(op,
                      narrow(builder, op.getLoc(), result, residue.getWidth()));
    return success();
  }
};
template <typename Op> struct Lift : OpConversionPattern<Op> {
  using OpConversionPattern<Op>::OpConversionPattern;
  LogicalResult
  matchAndRewrite(Op op, typename Op::Adaptor args,
                  ConversionPatternRewriter &builder) const override {
    auto residue = dyn_cast<ValueType>(op.getInput().getType());
    auto word = dyn_cast<IntegerType>(op.getResult().getType());
    if (!residue || !word)
      return builder.notifyMatchFailure(
          op, "scalarize tensors before word lowering");
    auto loc = op.getLoc();
    Value result = widen(builder, loc, args.getInput(), word.getWidth());
    if constexpr (std::is_same_v<Op, ResidueCenteredLiftOp>) {
      auto q = residue.getModulus().getValue().zextOrTrunc(word.getWidth());
      auto threshold = constant(builder, loc, q.lshr(1) + (q & 1));
      auto negative = arith::CmpIOp::create(
          builder, loc, arith::CmpIPredicate::uge, result, threshold);
      auto centered = arith::SubIOp::create(builder, loc, result,
                                            constant(builder, loc, q));
      result =
          arith::SelectOp::create(builder, loc, negative, centered, result);
    }
    builder.replaceOp(op, result);
    return success();
  }
};
} // namespace
OwningOpRef<ModuleOp> lowerArithmetic(ModuleOp source) {
  if (failed(verify(source)))
    return {};
  auto *context = source.getContext();
  context->getOrLoadDialect<arith::ArithDialect>();
  context->getOrLoadDialect<func::FuncDialect>();
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  Words words;
  RewritePatternSet patterns(context);
  patterns.add<Constant, Binary<ResidueAddOp>, Binary<ResidueSubtractOp>,
               Binary<ResidueMultiplyOp>, Project, Lift<ResidueLiftOp>,
               Lift<ResidueCenteredLiftOp>>(words, context);
  populateFunctionOpInterfaceTypeConversionPattern<func::FuncOp>(patterns,
                                                                 words);
  populateReturnOpTypeConversionPattern(patterns, words);
  ConversionTarget target(*context);
  target.addLegalOp<ModuleOp>();
  target.addDynamicallyLegalOp<func::FuncOp>([&](func::FuncOp op) {
    return words.isSignatureLegal(op.getFunctionType()) &&
           words.isLegal(&op.getBody());
  });
  target.addDynamicallyLegalOp<func::ReturnOp>(
      [&](func::ReturnOp op) { return words.isLegal(op); });
  target.addDynamicallyLegalDialect<arith::ArithDialect>(
      [&](Operation *op) { return words.isLegal(op); });
  if (failed(applyFullConversion(*candidate, target, std::move(patterns))) ||
      failed(verify(*candidate)))
    return {};
  return candidate;
}
} // namespace zkc::residue
