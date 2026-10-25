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
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
constexpr unsigned workLimit = 1000000;
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "structured-computation", detail);
}
bool attrs(Operation *op, ArrayRef<StringRef> names) {
  return llvm::all_of(op->getAttrs(), [&](NamedAttribute attr) {
    return llvm::is_contained(names, attr.getName().getValue());
  });
}
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

// Ordered expression bisimulation reads both independently constructed arenas.
// It accepts different sharing and traversal orders, while keeping constants,
// nominal fields, input coordinates and noncommutative operand positions exact.
// It neither invokes CSE nor compares producer-generated correspondence maps.
bool equivalent(const ring::Expression &source,
                const ring::Expression &candidate) {
  if (source.inputs().size() != candidate.inputs().size() ||
      source.outputs().size() != candidate.outputs().size())
    return false;
  for (auto [a, b] : llvm::zip(source.inputs(), candidate.inputs()))
    if (a.field != b.field)
      return false;
  SmallVector<std::pair<unsigned, unsigned>> pending;
  for (auto [a, b] : llvm::zip(source.outputs(), candidate.outputs()))
    pending.emplace_back(a, b);
  llvm::DenseSet<std::pair<unsigned, unsigned>> visited;
  unsigned remaining = workLimit;
  while (!pending.empty()) {
    if (!remaining--)
      return false;
    auto pair = pending.pop_back_val();
    if (!visited.insert(pair).second)
      continue;
    const auto &a = source.nodes()[pair.first];
    const auto &b = candidate.nodes()[pair.second];
    if (a.kind != b.kind || source.facts()[pair.first].field !=
                                candidate.facts()[pair.second].field)
      return false;
    switch (a.kind) {
    case ring::Kind::Input:
      if (a.input != b.input)
        return false;
      break;
    case ring::Kind::Constant:
      if (a.constant != b.constant)
        return false;
      break;
    case ring::Kind::Add:
    case ring::Kind::Mul:
      pending.emplace_back(a.right, b.right);
      [[fallthrough]];
    case ring::Kind::Neg:
    case ring::Kind::Embed:
      pending.emplace_back(a.left, b.left);
      break;
    }
  }
  return true;
}

// Reject nested or oversized packets before invoking recursive MLIR services.
// The admitted profile has only a module, a function and scalar generic bodies.
bool boundedPacket(ModuleOp candidate) {
  if (!candidate || !candidate.getBodyRegion().hasOneBlock() ||
      !llvm::hasSingleElement(*candidate.getBody()))
    return false;
  auto function = dyn_cast<func::FuncOp>(candidate.getBody()->front());
  if (!function || !function.getBody().hasOneBlock())
    return false;
  uint64_t remaining = workLimit;
  auto charge = [&](Operation &op) {
    uint64_t cost = 1 + op.getNumOperands() + op.getNumResults();
    if (cost > remaining || op.getNumSuccessors())
      return false;
    remaining -= cost;
    return true;
  };
  for (Operation &op : function.front()) {
    if (!charge(op))
      return false;
    if (auto generic = dyn_cast<linalg::GenericOp>(op)) {
      if (!generic.getRegion().hasOneBlock())
        return false;
      for (Operation &scalar : generic.getRegion().front())
        if (!charge(scalar) || scalar.getNumRegions())
          return false;
    } else if (op.getNumRegions()) {
      return false;
    }
  }
  return true;
}

// Read and compose the actual pointwise SSA graph. Tensor values map to their
// element formulas; this interpretation is valid only under the separately
// checked common-extent premise. There are no producer correspondence labels.
OwningOpRef<func::FuncOp> read(ModuleOp candidate, const Signature &sig,
                               StructuredResult result) {
  if (!boundedPacket(candidate) || failed(verify(candidate)) ||
      !candidate->getAttrs().empty())
    return {};
  auto function = cast<func::FuncOp>(candidate.getBody()->front());
  Type output =
      result == StructuredResult::Map ? Type(sig.lanes) : Type(sig.field);
  if (!attrs(function, {"sym_name", "function_type"}) ||
      function.getFunctionType() !=
          FunctionType::get(candidate.getContext(), sig.inputs, {output}))
    return {};
  OpBuilder builder(candidate.getContext());
  SmallVector<Type> scalarInputs(sig.inputs.size(), sig.field);
  OwningOpRef<func::FuncOp> scalar(
      func::FuncOp::create(function.getLoc(), "scalar",
                           builder.getFunctionType(scalarInputs, {sig.field})));
  auto *target = scalar->addEntryBlock();
  builder.setInsertionPointToEnd(target);
  auto &body = function.front();
  llvm::DenseMap<Value, Value> terms;
  for (auto [from, to] : llvm::zip(body.getArguments(), target->getArguments()))
    terms[from] = to;
  Value zeroIndex, extent, empty, zeroField, seed, reduction, extracted;
  auto identity = AffineMap::getMultiDimIdentityMap(1, candidate.getContext());
  auto broadcast = AffineMap::get(1, 0, {}, candidate.getContext());
  unsigned generics = 0;
  for (Operation &op : body) {
    if (auto zero = dyn_cast<arith::ConstantIndexOp>(op)) {
      if (zeroIndex || zero.value() != 0 || !attrs(zero, {"value"}))
        return {};
      zeroIndex = zero;
    } else if (auto dim = dyn_cast<tensor::DimOp>(op)) {
      if (extent || !zeroIndex || !dim->getAttrs().empty() ||
          dim.getSource() != body.getArgument(sig.firstRow) ||
          dim.getIndex() != zeroIndex)
        return {};
      extent = dim;
    } else if (auto init = dyn_cast<tensor::EmptyOp>(op)) {
      if (empty || !extent || !init->getAttrs().empty() ||
          init.getType() != sig.lanes ||
          init.getDynamicSizes() != ValueRange{extent})
        return {};
      empty = init;
    } else if (auto zero = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (zeroField || zero.getValue() != "0" || !attrs(zero, {"value"}) ||
          zero.getType() != sig.field)
        return {};
      zeroField = zero;
    } else if (auto init = dyn_cast<tensor::FromElementsOp>(op)) {
      if (seed || !zeroField || !init->getAttrs().empty() ||
          init.getType() != RankedTensorType::get({}, sig.field) ||
          init.getElements() != ValueRange{zeroField})
        return {};
      seed = init;
    } else if (auto generic = dyn_cast<linalg::GenericOp>(op)) {
      ++generics;
      auto iterators = generic.getIteratorTypesArray();
      bool sum = iterators ==
                 ArrayRef<utils::IteratorType>{utils::IteratorType::reduction};
      if (reduction ||
          (!sum &&
           iterators !=
               ArrayRef<utils::IteratorType>{utils::IteratorType::parallel}) ||
          (sum && result != StructuredResult::Sum) ||
          !attrs(generic,
                 {"indexing_maps", "iterator_types", "operandSegmentSizes"}) ||
          generic.getNumResults() != 1)
        return {};
      Value destination = sum ? seed : empty;
      if (!destination || generic.getOutputs() != ValueRange{destination} ||
          generic.getResult(0).getType() != destination.getType())
        return {};
      auto maps = generic.getIndexingMapsArray();
      auto inputs = generic.getInputs();
      auto &region = generic.getRegion().front();
      if (maps.size() != inputs.size() + 1 ||
          maps.back() != (sum ? broadcast : identity) ||
          region.getNumArguments() != inputs.size() + 1 || region.empty() ||
          llvm::any_of(region.getArgumentTypes(),
                       [&](Type t) { return t != sig.field; }))
        return {};
      IRMapping mapping;
      for (auto [index, input] : llvm::enumerate(inputs)) {
        bool row = input.getType() == sig.lanes;
        if ((!row && input.getType() != sig.field) ||
            maps[index] != (row ? identity : broadcast) ||
            !terms.contains(input))
          return {};
        mapping.map(region.getArgument(index), terms.lookup(input));
      }
      auto yield = dyn_cast<linalg::YieldOp>(region.back());
      if (!yield || yield.getNumOperands() != 1 || !yield->getAttrs().empty())
        return {};
      Value term = yield.getOperand(0);
      Operation *combiner = nullptr;
      auto accumulator = region.getArguments().back();
      if (sum) {
        auto add = term.getDefiningOp<algebra::FieldAddOp>();
        if (!add || add->getBlock() != &region || add->getNextNode() != yield ||
            !add->getAttrs().empty() || add.getOperand(0) != accumulator ||
            !accumulator.hasOneUse())
          return {};
        term = add.getOperand(1);
        combiner = add;
      } else if (!accumulator.use_empty()) {
        return {};
      }
      // This independently admits every scalar operation, including dead ones,
      // and rejects values captured from the containing function or other maps.
      auto expression =
          algebra::describeRingExpression(region, ValueRange{term});
      if (!expression) {
        consumeError(expression.takeError());
        return {};
      }
      auto used = expression->usedInputs({0});
      if (!used) {
        consumeError(used.takeError());
        return {};
      }
      if (llvm::is_contained(*used, unsigned(inputs.size())))
        return {};
      for (Operation &scalarOp : region.without_terminator())
        if (&scalarOp != combiner)
          builder.clone(scalarOp, mapping);
      terms[generic.getResult(0)] = mapping.lookup(term);
      if (sum)
        reduction = generic.getResult(0);
    } else if (auto extract = dyn_cast<tensor::ExtractOp>(op)) {
      if (extracted || !reduction || !extract->getAttrs().empty() ||
          extract.getTensor() != reduction || !extract.getIndices().empty())
        return {};
      extracted = extract;
      terms[extracted] = terms.lookup(reduction);
    } else if (auto ret = dyn_cast<func::ReturnOp>(op)) {
      if (&op != &body.back() || !generics || !ret->getAttrs().empty() ||
          ret.getNumOperands() != 1 || !terms.contains(ret.getOperand(0)) ||
          (result == StructuredResult::Sum &&
           (!extracted || ret.getOperand(0) != extracted)))
        return {};
      func::ReturnOp::create(builder, ret.getLoc(),
                             terms.lookup(ret.getOperand(0)));
    } else {
      return {};
    }
  }
  return scalar;
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
    auto zero =
        algebra::ConstantFieldOp::create(builder, location, sig->field, "0");
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
  if (!boundedPacket(candidate) || failed(verify(candidate)))
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
  return success();
}

LogicalResult verifyStructuredComputation(Block &formula,
                                          ArrayRef<bool> rowwise,
                                          StructuredResult result,
                                          ModuleOp candidate) {
  auto sig = signature(formula, rowwise);
  if (failed(sig))
    return refuse(candidate, "original scalar profile");
  auto actual = read(candidate, *sig, result);
  if (!actual)
    return refuse(candidate, "candidate structure or bindings");
  auto source =
      algebra::describeRingExpression(formula, formula.back().getOperands());
  auto target = algebra::describeRingExpression(
      actual->front(), actual->front().back().getOperands());
  if (!source || !target) {
    if (!source)
      consumeError(source.takeError());
    if (!target)
      consumeError(target.takeError());
    return refuse(candidate, "scalar expression admission");
  }
  if (!equivalent(*source, *target))
    return refuse(candidate, "scalar expression differs from the original");
  return success();
}

OwningOpRef<func::FuncOp> consumeStructuredComputation(Block &formula,
                                                       ArrayRef<bool> rowwise,
                                                       StructuredResult result,
                                                       ModuleOp candidate) {
  if (failed(verifyStructuredComputation(formula, rowwise, result, candidate)))
    return {};
  auto sig = signature(formula, rowwise);
  auto actual = read(candidate, *sig, result);
  if (!actual)
    return {};
  return actual;
}
} // namespace zkc::mathematical
