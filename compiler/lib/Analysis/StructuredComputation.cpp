#include "zkc/Analysis/StructuredComputation.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
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
  return op ? diagnostics::emit(op->emitOpError(), "structured-computation",
                                detail)
            : failure();
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
  if (!candidate->getAttrs().empty())
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

std::optional<StructuredComputation>
readStructuredComputation(ModuleOp candidate) {
  // Bound nesting and work before recursive MLIR verification or traversal.
  if (!boundedPacket(candidate) || failed(verify(candidate)))
    return std::nullopt;
  auto function = cast<func::FuncOp>(candidate.getBody()->front());
  auto type = function.getFunctionType();
  if (type.getNumResults() != 1 || !type.getNumInputs() ||
      type.getNumInputs() > ring::Limits::inputs)
    return std::nullopt;
  auto output = type.getResult(0);
  auto tensor = dyn_cast<RankedTensorType>(output);
  auto field =
      dyn_cast<algebra::FieldType>(tensor ? tensor.getElementType() : output);
  if (!field)
    return std::nullopt;
  auto lanes = RankedTensorType::get({ShapedType::kDynamic}, field);
  if (tensor && tensor != lanes)
    return std::nullopt;
  SmallVector<bool> rowwise;
  for (auto input : type.getInputs()) {
    if (input != field && input != lanes)
      return std::nullopt;
    rowwise.push_back(input == lanes);
  }
  auto first = llvm::find(rowwise, true);
  if (first == rowwise.end())
    return std::nullopt;
  Signature signature{field, lanes, SmallVector<Type>(type.getInputs()),
                      unsigned(first - rowwise.begin())};
  auto result = tensor ? StructuredResult::Map : StructuredResult::Sum;
  auto scalar = read(candidate, signature, result);
  if (!scalar)
    return std::nullopt;
  return StructuredComputation{std::move(scalar), std::move(rowwise), result};
}

OwningOpRef<func::FuncOp> consumeStructuredComputation(Block &formula,
                                                       ArrayRef<bool> rowwise,
                                                       StructuredResult result,
                                                       ModuleOp candidate) {
  auto actual = readStructuredComputation(candidate);
  if (!actual || formula.empty() || formula.back().getNumOperands() != 1 ||
      actual->rowwise != rowwise || actual->result != result ||
      !llvm::equal(actual->scalar->getFunctionType().getInputs(),
                   formula.getArgumentTypes()) ||
      actual->scalar->getFunctionType().getResult(0) !=
          formula.back().getOperand(0).getType()) {
    (void)refuse(candidate, "candidate structure or bindings");
    return {};
  }
  auto source =
      algebra::describeRingExpression(formula, formula.back().getOperands());
  auto target = algebra::describeRingExpression(
      actual->scalar->front(), actual->scalar->front().back().getOperands());
  if (!source || !target) {
    if (!source)
      consumeError(source.takeError());
    if (!target)
      consumeError(target.takeError());
    (void)refuse(candidate, "scalar expression admission");
    return {};
  }
  if (!equivalent(*source, *target)) {
    (void)refuse(candidate, "scalar expression differs from the original");
    return {};
  }
  return std::move(actual->scalar);
}

LogicalResult verifyStructuredComputation(Block &formula,
                                          ArrayRef<bool> rowwise,
                                          StructuredResult result,
                                          ModuleOp candidate) {
  return success(
      bool(consumeStructuredComputation(formula, rowwise, result, candidate)));
}
} // namespace zkc::mathematical
