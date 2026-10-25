#include "zkc/Transforms/StructuredComputation.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/CSE.h"
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

struct Readback {
  func::FuncOp function;
  linalg::GenericOp generic;
  Value term;
  Operation *combiner = nullptr;
};
// Read a bounded, complete packet. All values below are actual candidate SSA.
// In particular, no metadata declares which tensor supplies a dimension or
// which scalar value the function returns.
FailureOr<Readback> read(ModuleOp candidate, const Signature &sig,
                         ArrayRef<bool> rowwise, StructuredResult result) {
  unsigned remaining = workLimit;
  auto scan = candidate->walk([&](Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining)
      return WalkResult::interrupt();
    remaining -= cost;
    return WalkResult::advance();
  });
  if (scan.wasInterrupted() || failed(verify(candidate)) ||
      !candidate->getAttrs().empty() ||
      !llvm::hasSingleElement(*candidate.getBody()))
    return failure();
  auto function = dyn_cast<func::FuncOp>(candidate.getBody()->front());
  Type output =
      result == StructuredResult::Map ? Type(sig.lanes) : Type(sig.field);
  if (!function || function.isExternal() || !function.getBody().hasOneBlock() ||
      !attrs(function, {"sym_name", "function_type"}) ||
      function.getFunctionType() !=
          FunctionType::get(candidate.getContext(), sig.inputs, {output}))
    return failure();
  auto &body = function.front();
  auto cursor = body.begin();
  auto take = [&]() -> Operation * {
    if (cursor == body.end())
      return nullptr;
    return &*cursor++;
  };
  Value initial;
  if (result == StructuredResult::Map) {
    auto zero = dyn_cast_or_null<arith::ConstantIndexOp>(take());
    auto dim = dyn_cast_or_null<tensor::DimOp>(take());
    auto empty = dyn_cast_or_null<tensor::EmptyOp>(take());
    if (!zero || zero.value() != 0 || !attrs(zero, {"value"}) || !dim ||
        !dim->getAttrs().empty() ||
        dim.getSource() != body.getArgument(sig.firstRow) ||
        dim.getIndex() != zero.getResult() || !empty ||
        !empty->getAttrs().empty() || empty.getType() != sig.lanes ||
        empty.getDynamicSizes() != ValueRange{dim.getResult()})
      return failure();
    initial = empty.getResult();
  } else {
    auto zero = dyn_cast_or_null<algebra::ConstantFieldOp>(take());
    auto seed = dyn_cast_or_null<tensor::FromElementsOp>(take());
    if (!zero || zero.getValue() != "0" || !attrs(zero, {"value"}) ||
        zero.getType() != sig.field || !seed || !seed->getAttrs().empty() ||
        seed.getType() != RankedTensorType::get({}, sig.field) ||
        seed.getElements() != ValueRange{zero.getResult()})
      return failure();
    initial = seed.getResult();
  }
  auto generic = dyn_cast_or_null<linalg::GenericOp>(take());
  if (!generic ||
      !attrs(generic,
             {"indexing_maps", "iterator_types", "operandSegmentSizes"}) ||
      generic.getInputs() != body.getArguments() ||
      generic.getOutputs() != ValueRange{initial} ||
      generic.getNumResults() != 1 ||
      generic.getResult(0).getType() != initial.getType() ||
      !generic.getRegion().hasOneBlock())
    return failure();
  auto maps = generic.getIndexingMapsArray();
  if (maps.size() != rowwise.size() + 1)
    return failure();
  auto identity = AffineMap::getMultiDimIdentityMap(1, candidate.getContext());
  auto scalar = AffineMap::get(1, 0, {}, candidate.getContext());
  for (auto [i, row] : llvm::enumerate(rowwise))
    if (maps[i] != (row ? identity : scalar))
      return failure();
  if (maps.back() != (result == StructuredResult::Map ? identity : scalar) ||
      generic.getIteratorTypesArray() !=
          ArrayRef<utils::IteratorType>{result == StructuredResult::Map
                                            ? utils::IteratorType::parallel
                                            : utils::IteratorType::reduction})
    return failure();
  auto &region = generic.getRegion().front();
  if (region.getNumArguments() != rowwise.size() + 1 || region.empty() ||
      llvm::any_of(region.getArgumentTypes(),
                   [&](Type t) { return t != sig.field; }))
    return failure();
  auto yield = dyn_cast<linalg::YieldOp>(region.back());
  if (!yield || yield.getNumOperands() != 1 || !yield->getAttrs().empty())
    return failure();
  Value term = yield.getOperand(0);
  Operation *combiner = nullptr;
  auto accumulator = region.getArguments().back();
  if (result == StructuredResult::Sum) {
    auto add = term.getDefiningOp<algebra::FieldAddOp>();
    if (!add || add->getBlock() != &region || add->getNextNode() != yield ||
        !add->getAttrs().empty() || add.getOperand(0) != accumulator ||
        !accumulator.hasOneUse())
      return failure();
    term = add.getOperand(1);
    combiner = add;
  } else if (!accumulator.use_empty()) {
    return failure();
  }
  // Admit every scalar operation, including unused values; reject captures.
  auto expression = algebra::describeRingExpression(region, ValueRange{term});
  if (!expression) {
    consumeError(expression.takeError());
    return failure();
  }
  auto used = expression->usedInputs({0});
  if (!used) {
    consumeError(used.takeError());
    return failure();
  }
  if (llvm::is_contained(*used, unsigned(rowwise.size())))
    return failure();
  Value returned = generic.getResult(0);
  if (result == StructuredResult::Sum) {
    auto extract = dyn_cast_or_null<tensor::ExtractOp>(take());
    if (!extract || !extract->getAttrs().empty() ||
        extract.getTensor() != returned || !extract.getIndices().empty())
      return failure();
    returned = extract.getResult();
  }
  auto ret = dyn_cast_or_null<func::ReturnOp>(take());
  if (!ret || !ret->getAttrs().empty() ||
      ret.getOperands() != ValueRange{returned} || cursor != body.end())
    return failure();
  return Readback{function, generic, term, combiner};
}

OwningOpRef<func::FuncOp> extract(Readback readback) {
  auto &body = readback.generic.getRegion().front();
  SmallVector<Type> inputs(body.getArgumentTypes());
  inputs.pop_back();
  OpBuilder builder(readback.function.getContext());
  OwningOpRef<func::FuncOp> function(func::FuncOp::create(
      readback.function.getLoc(), "scalar",
      builder.getFunctionType(inputs, {readback.term.getType()})));
  auto *block = function->addEntryBlock();
  builder.setInsertionPointToEnd(block);
  IRMapping mapping;
  mapping.map(body.getArguments().drop_back(), block->getArguments());
  for (Operation &op : body.without_terminator())
    if (&op != readback.combiner)
      builder.clone(op, mapping);
  func::ReturnOp::create(builder, readback.function.getLoc(),
                         mapping.lookup(readback.term));
  return function;
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
  Value initial;
  if (result == StructuredResult::Map) {
    auto extent = tensor::DimOp::create(
        builder, location, entry->getArgument(sig->firstRow), int64_t(0));
    initial = tensor::EmptyOp::create(builder, location,
                                      ArrayRef<int64_t>{ShapedType::kDynamic},
                                      sig->field, ValueRange{extent});
  } else {
    auto zero =
        algebra::ConstantFieldOp::create(builder, location, sig->field, "0");
    initial = tensor::FromElementsOp::create(
        builder, location, RankedTensorType::get({}, sig->field),
        ValueRange{zero});
  }
  auto identity = AffineMap::getMultiDimIdentityMap(1, context);
  auto scalar = AffineMap::get(1, 0, {}, context);
  SmallVector<AffineMap> maps;
  for (bool row : rowwise)
    maps.push_back(row ? identity : scalar);
  maps.push_back(result == StructuredResult::Map ? identity : scalar);
  auto generic = linalg::GenericOp::create(
      builder, location, TypeRange{initial.getType()}, entry->getArguments(),
      ValueRange{initial}, maps,
      ArrayRef<utils::IteratorType>{result == StructuredResult::Map
                                        ? utils::IteratorType::parallel
                                        : utils::IteratorType::reduction},
      [&](OpBuilder &nested, Location loc, ValueRange args) {
        IRMapping mapping;
        mapping.map(formula.getArguments(), args.drop_back());
        for (Operation &op : formula.without_terminator())
          nested.clone(op, mapping);
        Value term = mapping.lookup(formula.back().getOperand(0));
        if (result == StructuredResult::Sum)
          term = algebra::FieldAddOp::create(nested, loc, sig->field,
                                             args.back(), term);
        linalg::YieldOp::create(nested, loc, term);
      });
  Value returned = generic.getResult(0);
  if (result == StructuredResult::Sum)
    returned =
        tensor::ExtractOp::create(builder, location, returned, ValueRange{});
  func::ReturnOp::create(builder, location, returned);
  return candidate;
}

LogicalResult optimizeStructuredComputation(ModuleOp candidate) {
  if (failed(verify(candidate)))
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
  auto actual = read(candidate, *sig, rowwise, result);
  if (failed(actual))
    return refuse(candidate, "candidate structure or bindings");
  auto scalar = extract(*actual);
  auto source =
      algebra::describeRingExpression(formula, formula.back().getOperands());
  auto target = algebra::describeRingExpression(
      scalar->front(), scalar->front().back().getOperands());
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
  auto actual = read(candidate, *sig, rowwise, result);
  if (failed(actual))
    return {};
  return extract(*actual);
}
} // namespace zkc::mathematical
