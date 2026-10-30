#include "zkc/Transforms/StructuredComputation.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Linalg/Transforms/Transforms.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/CSE.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Algebra/RingExpression.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
constexpr unsigned workLimit = 1000000;
struct Signature {
  algebra::FieldType field;
  RankedTensorType lanes;
  SmallVector<Type> inputs;
  unsigned firstRow;
};
FailureOr<Signature> signature(Block &formula, ArrayRef<bool> rowwise) {
  if (formula.empty() || formula.getNumArguments() != rowwise.size() ||
      rowwise.size() > ring::Limits::inputs ||
      !llvm::is_contained(rowwise, true) ||
      formula.back().getNumOperands() != 1)
    return failure();
  auto field =
      dyn_cast<algebra::FieldType>(formula.back().getOperand(0).getType());
  if (!field || llvm::any_of(formula.getArgumentTypes(),
                             [&](Type type) { return type != field; }))
    return failure();
  auto expression =
      algebra::describeRingExpression(formula, formula.back().getOperands());
  if (!expression) {
    consumeError(expression.takeError());
    return failure();
  }
  auto lanes = RankedTensorType::get({ShapedType::kDynamic}, field);
  SmallVector<Type> inputs;
  for (bool row : rowwise)
    inputs.push_back(row ? Type(lanes) : Type(field));
  return Signature{field, lanes, std::move(inputs),
                   unsigned(llvm::find(rowwise, true) - rowwise.begin())};
}

} // namespace

OwningOpRef<ModuleOp> proposeStructuredComputation(Block &formula,
                                                   ArrayRef<bool> rowwise,
                                                   StructuredResult result) {
  auto sig = signature(formula, rowwise);
  if (failed(sig))
    return {};
  auto *context = sig->field.getContext();
  context->getOrLoadDialect<linalg::LinalgDialect>();
  context->getOrLoadDialect<tensor::TensorDialect>();
  context->getOrLoadDialect<arith::ArithDialect>();
  auto location = formula.getParentOp()->getLoc();
  OwningOpRef<ModuleOp> candidate(ModuleOp::create(location));
  OpBuilder builder(context);
  builder.setInsertionPointToEnd(candidate->getBody());
  Type output =
      result == StructuredResult::Map ? Type(sig->lanes) : Type(sig->field);
  auto function =
      func::FuncOp::create(builder, location, "compute",
                           builder.getFunctionType(sig->inputs, {output}));
  auto *entry = function.addEntryBlock();
  builder.setInsertionPointToEnd(entry);
  auto extent = tensor::DimOp::create(
      builder, location, entry->getArgument(sig->firstRow), int64_t(0));
  auto initial = tensor::EmptyOp::create(
      builder, location, ArrayRef<int64_t>{ShapedType::kDynamic}, sig->field,
      ValueRange{extent});
  auto identity = AffineMap::getMultiDimIdentityMap(1, context);
  auto broadcast = AffineMap::get(1, 0, {}, context);
  SmallVector<AffineMap> maps;
  for (bool row : rowwise)
    maps.push_back(row ? identity : broadcast);
  maps.push_back(identity);
  auto mapped = linalg::GenericOp::create(
      builder, location, TypeRange{sig->lanes}, entry->getArguments(),
      ValueRange{initial}, maps,
      ArrayRef<utils::IteratorType>{utils::IteratorType::parallel},
      [&](OpBuilder &nested, Location loc, ValueRange args) {
        IRMapping mapping;
        mapping.map(formula.getArguments(), args.drop_back());
        for (Operation &op : formula.without_terminator())
          nested.clone(op, mapping);
        linalg::YieldOp::create(nested, loc,
                                mapping.lookup(formula.back().getOperand(0)));
      });
  Value returned = mapped.getResult(0);
  if (result == StructuredResult::Sum) {
    auto zero = algebra::ConstantFieldOp::create(
        builder, location, sig->field,
        cantFail(algebra::makeFieldLiteral(sig->field, llvm::APInt(1, 0))));
    auto seed = tensor::FromElementsOp::create(
        builder, location, RankedTensorType::get({}, sig->field),
        ValueRange{zero});
    auto reduced = linalg::GenericOp::create(
        builder, location, TypeRange{seed.getType()}, ValueRange{returned},
        ValueRange{seed}, ArrayRef<AffineMap>{identity, broadcast},
        ArrayRef<utils::IteratorType>{utils::IteratorType::reduction},
        [&](OpBuilder &nested, Location loc, ValueRange args) {
          auto sum = algebra::FieldAddOp::create(nested, loc, sig->field,
                                                 args.back(), args.front());
          linalg::YieldOp::create(nested, loc, sum.getResult());
        });
    returned = tensor::ExtractOp::create(builder, location,
                                         reduced.getResult(0), ValueRange{});
  }
  func::ReturnOp::create(builder, location, returned);
  return candidate;
}

LogicalResult optimizeStructuredComputation(ModuleOp candidate) {
  if (!readStructuredComputation(candidate))
    return failure();
  RewritePatternSet patterns(candidate.getContext());
  linalg::populateElementwiseOpsFusionPatterns(
      patterns, [](OpOperand *) { return true; });
  // Only the selected fusion is allowed here. Generic folding and constant
  // hoisting could introduce unsupported identities or captures. Scalar CSE
  // remains local to each closed region below.
  GreedyRewriteConfig config;
  config.setUseTopDownTraversal().enableFolding(false).enableConstantCSE(false);
  config.setMaxNumRewrites(workLimit);
  if (failed(applyPatternsGreedily(candidate, std::move(patterns), config)))
    return failure();
  IRRewriter rewriter(candidate.getContext());
  DominanceInfo dominance(candidate);
  candidate.walk([&](linalg::GenericOp generic) {
    eliminateCommonSubExpressions(rewriter, dominance, generic.getRegion());
  });
  return success(bool(readStructuredComputation(candidate)));
}

} // namespace zkc::mathematical
