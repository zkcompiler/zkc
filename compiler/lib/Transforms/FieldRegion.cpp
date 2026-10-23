#include "FieldRegion.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Transforms/CSE.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
Operation *scalar(OpBuilder &builder, Location loc, StringRef name, Type type,
                  ValueRange operands, ArrayRef<NamedAttribute> attrs = {}) {
  OperationState state(loc, name);
  state.addTypes(type);
  state.addOperands(operands);
  state.addAttributes(attrs);
  return builder.create(state);
}
RankedTensorType tensor(Type field, bool lanes) {
  return RankedTensorType::get(lanes ? ArrayRef<int64_t>{ShapedType::kDynamic}
                                     : ArrayRef<int64_t>{},
                               field);
}
} // namespace

void registerFieldRegionDialects(DialectRegistry &registry) {
  registry.insert<linalg::LinalgDialect, tensor::TensorDialect>();
}

Expected<OwningOpRef<ModuleOp>>
createFieldRegion(const FieldRegionSource &source, Type field) {
  auto *context = field.getContext();
  context->getOrLoadDialect<linalg::LinalgDialect>();
  context->getOrLoadDialect<tensor::TensorDialect>();
  OpBuilder builder(context);
  auto loc = builder.getUnknownLoc();
  OwningOpRef<ModuleOp> module(ModuleOp::create(loc));
  SmallVector<Type> types{builder.getIndexType()};
  SmallVector<AffineMap> maps;
  for (const auto &slot : source.slots) {
    types.push_back(tensor(field, slot.lanes));
    maps.push_back(slot.lanes ? builder.getDimIdentityMap()
                              : AffineMap::get(1, 0, {}, context));
  }
  maps.push_back(builder.getDimIdentityMap());
  builder.setInsertionPointToEnd(module->getBody());
  auto function = func::FuncOp::create(
      builder, loc, "compute",
      builder.getFunctionType(types, {tensor(field, true)}));
  auto *entry = function.addEntryBlock();
  builder.setInsertionPointToEnd(entry);
  auto empty = tensor::EmptyOp::create(
      builder, loc, ArrayRef<int64_t>{ShapedType::kDynamic}, field,
      ValueRange{entry->getArgument(0)});
  auto generic = linalg::GenericOp::create(
      builder, loc, TypeRange{tensor(field, true)},
      entry->getArguments().drop_front(), ValueRange{empty}, maps,
      ArrayRef<utils::IteratorType>{utils::IteratorType::parallel},
      [&](OpBuilder &body, Location bodyLoc, ValueRange args) {
        llvm::DenseMap<Value, Value> values;
        // Bind in the same source order used by admission. Native bindings can
        // alias; those aliases do not change the region's input inventory.
        unsigned next = 0;
        auto bind = [&](Value value) {
          if (source.bindings.contains(value) && value.getType() == field)
            values[value] = args[next++];
        };
        for (Value arg : source.body.getArguments())
          bind(arg);
        for (Operation &op : source.body.without_terminator()) {
          auto result = op.getResult(0);
          if (source.bindings.contains(result)) {
            bind(result);
            continue;
          }
          if (!source.live.contains(result))
            continue;
          if (auto literal = finite::fieldConstant(&op)) {
            values[result] =
                scalar(
                    body, bodyLoc, algebra::ConstantFieldOp::getOperationName(),
                    field, {},
                    {body.getNamedAttr("value", body.getStringAttr(*literal))})
                    ->getResult(0);
            continue;
          }
          auto identity = finite::semantics(&op)->identity;
          StringRef name = identity == MathematicalIdentity::FieldAdd
                               ? algebra::FieldAddOp::getOperationName()
                           : identity == MathematicalIdentity::FieldMultiply
                               ? algebra::FieldMultiplyOp::getOperationName()
                               : algebra::SubtractFieldOp::getOperationName();
          values[result] = scalar(body, bodyLoc, name, field,
                                  {values.lookup(op.getOperand(0)),
                                   values.lookup(op.getOperand(1))})
                               ->getResult(0);
        }
        Value result = values.lookup(source.terms.front());
        for (Value term : ArrayRef<Value>(source.terms).drop_front())
          result = scalar(body, bodyLoc,
                          source.combine == MathematicalIdentity::FieldMultiply
                              ? algebra::FieldMultiplyOp::getOperationName()
                              : algebra::FieldAddOp::getOperationName(),
                          field, {result, values.lookup(term)})
                       ->getResult(0);
        linalg::YieldOp::create(body, bodyLoc, result);
      });
  func::ReturnOp::create(builder, loc, generic.getResults());
  // Upstream CSE owns scalar sharing in the isolated pure region. Its output
  // is independently interpreted before either native consumer can use it.
  IRRewriter rewriter(context);
  DominanceInfo dominance(*module);
  eliminateCommonSubExpressions(rewriter, dominance, *module);
  if (failed(verify(*module)))
    return zkc::error("field-region-transformation");
  return std::move(module);
}

Expected<ring::Expression> readFieldRegion(ModuleOp module, StringRef domain,
                                           ArrayRef<bool> lanes) {
  auto invalid = [] { return zkc::error("field-region-profile"); };
  if (!module || module->getAttrs().size() ||
      !module.getBodyRegion().hasOneBlock() ||
      !llvm::hasSingleElement(*module.getBody()) ||
      lanes.size() > ring::Limits::inputs)
    return invalid();
  // The upstream verifier establishes operation/property invariants; the
  // stricter reader below establishes the admitted implementation semantics.
  unsigned operations = 0;
  if (module
          .walk([&](Operation *) {
            return ++operations > 2 * ring::Limits::nodes + ring::Limits::inputs
                       ? WalkResult::interrupt()
                       : WalkResult::advance();
          })
          .wasInterrupted())
    return zkc::error("field-region-capacity");
  if (failed(verify(module)))
    return invalid();
  auto function = dyn_cast<func::FuncOp>(module.getBody()->front());
  auto field = algebra::FieldType::get(module.getContext(), domain);
  if (!function || function.getSymName() != "compute" ||
      !function.getBody().hasOneBlock() ||
      function.getNumArguments() != lanes.size() + 1 ||
      function.getNumResults() != 1 ||
      function.getResultTypes()[0] != tensor(field, true) ||
      !function.getArgument(0).getType().isIndex() ||
      function->getAttrs().size() != 2 || function.getArgAttrsAttr() ||
      function.getResAttrsAttr())
    return invalid();
  for (auto [i, lane] : llvm::enumerate(lanes))
    if (function.getArgument(i + 1).getType() != tensor(field, lane))
      return invalid();
  Block &entry = function.front();
  if (entry.getOperations().size() != 3)
    return invalid();
  auto empty = dyn_cast<tensor::EmptyOp>(entry.front());
  auto generic = dyn_cast<linalg::GenericOp>(*std::next(entry.begin()));
  auto returned = dyn_cast<func::ReturnOp>(entry.back());
  if (!empty || empty.getType() != tensor(field, true) ||
      empty.getDynamicSizes() != ValueRange{function.getArgument(0)} ||
      !empty->getAttrs().empty() || !generic || !returned ||
      !returned->getAttrs().empty() ||
      returned.getOperands() != generic.getResults() ||
      generic.getNumResults() != 1 ||
      generic.getResult(0).getType() != tensor(field, true) ||
      !llvm::equal(generic.getDpsInputs(), entry.getArguments().drop_front()) ||
      generic.getDpsInits() != ValueRange{empty.getResult()} ||
      generic.getIteratorTypesArray() !=
          ArrayRef<utils::IteratorType>{utils::IteratorType::parallel} ||
      generic.getIndexingMapsArray().size() != lanes.size() + 1 ||
      generic->getAttrs().size() != 3 || !generic.getRegion().hasOneBlock())
    return invalid();
  auto maps = generic.getIndexingMapsArray();
  auto identity = AffineMap::getMultiDimIdentityMap(1, module.getContext());
  auto broadcast = AffineMap::get(1, 0, {}, module.getContext());
  for (auto [i, lane] : llvm::enumerate(lanes))
    if (maps[i] != (lane ? identity : broadcast))
      return invalid();
  if (maps.back() != identity)
    return invalid();
  Block &body = generic.getRegion().front();
  if (body.empty() || body.getNumArguments() != lanes.size() + 1 ||
      llvm::any_of(body.getArgumentTypes(),
                   [&](Type t) { return t != field; }) ||
      !body.getArguments().back().use_empty())
    return invalid();
  auto yield = dyn_cast<linalg::YieldOp>(body.back());
  if (!yield || yield.getNumOperands() != 1 || !yield->getAttrs().empty())
    return invalid();
  // Read SSA directly, with no producer map or source-derived result labels.
  std::vector<ring::Input> inputs(lanes.size(), {domain.str()});
  std::vector<ring::Node> nodes;
  llvm::DenseMap<Value, uint32_t> values;
  for (unsigned i = 0; i < lanes.size(); ++i) {
    values[body.getArgument(i)] = nodes.size();
    nodes.push_back(ring::Node::slot(i));
  }
  for (Operation &op : body.without_terminator()) {
    if (nodes.size() > 2 * ring::Limits::nodes + ring::Limits::inputs - 2)
      return zkc::error("field-region-capacity");
    if (op.getNumResults() != 1 || op.getResult(0).getType() != field ||
        op.getNumRegions() || op.getNumSuccessors())
      return invalid();
    if (auto literal = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (op.getNumOperands() || op.getAttrs().size() != 1)
        return invalid();
      auto node = ring::Node::literal(domain.str(), literal.getValue().str());
      auto checked = ring::Expression::create({}, {node}, {0});
      if (!checked)
        return checked.takeError();
      nodes.push_back(std::move(node));
    } else {
      if (!isa<algebra::FieldAddOp, algebra::SubtractFieldOp,
               algebra::FieldMultiplyOp>(op) ||
          !op.getAttrs().empty() || op.getNumOperands() != 2 ||
          !values.contains(op.getOperand(0)) ||
          !values.contains(op.getOperand(1)))
        return invalid();
      auto left = values.lookup(op.getOperand(0)),
           right = values.lookup(op.getOperand(1));
      if (isa<algebra::SubtractFieldOp>(op)) {
        nodes.push_back(ring::Node::neg(right));
        right = nodes.size() - 1;
      }
      nodes.push_back(isa<algebra::FieldMultiplyOp>(op)
                          ? ring::Node::mul(left, right)
                          : ring::Node::add(left, right));
    }
    values[op.getResult(0)] = nodes.size() - 1;
  }
  if (!values.contains(yield.getOperand(0)))
    return invalid();
  uint32_t root = values.lookup(yield.getOperand(0));
  std::vector<bool> live(nodes.size());
  live[root] = true;
  for (size_t i = nodes.size(); i-- > 0;)
    if (live[i]) {
      const auto &node = nodes[i];
      if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul)
        live[node.left] = live[node.right] = true;
      else if (node.kind == ring::Kind::Neg)
        live[node.left] = true;
    }
  std::vector<uint32_t> positions(nodes.size());
  std::vector<ring::Node> retained;
  for (size_t i = 0; i < nodes.size(); ++i) {
    if (!live[i])
      continue;
    auto node = nodes[i];
    if (node.kind == ring::Kind::Add || node.kind == ring::Kind::Mul) {
      node.left = positions[node.left];
      node.right = positions[node.right];
    } else if (node.kind == ring::Kind::Neg)
      node.left = positions[node.left];
    positions[i] = retained.size();
    retained.push_back(std::move(node));
  }
  return ring::Expression::create(std::move(inputs), std::move(retained),
                                  {positions[root]});
}

Error compareFieldExpressions(const ring::Expression &source,
                              const ring::Expression &candidate) {
  auto mismatch = [] { return zkc::error("field-region-correspondence"); };
  if (source.inputs().size() != candidate.inputs().size() ||
      source.outputs().size() != candidate.outputs().size())
    return mismatch();
  for (auto [a, b] : llvm::zip(source.inputs(), candidate.inputs()))
    if (a.field != b.field)
      return mismatch();
  SmallVector<std::pair<uint32_t, uint32_t>> pending;
  llvm::DenseSet<std::pair<uint32_t, uint32_t>> visited;
  for (auto [a, b] : llvm::zip(source.outputs(), candidate.outputs()))
    pending.emplace_back(a, b);
  while (!pending.empty()) {
    auto pair = pending.pop_back_val();
    if (!visited.insert(pair).second)
      continue;
    if (visited.size() > 2 * ring::Limits::nodes)
      return zkc::error("field-region-capacity");
    const auto &a = source.nodes()[pair.first],
               &b = candidate.nodes()[pair.second];
    if (a.kind != b.kind || a.field != b.field || a.constant != b.constant ||
        a.input != b.input)
      return mismatch();
    if (a.kind == ring::Kind::Add || a.kind == ring::Kind::Mul) {
      pending.emplace_back(a.left, b.left);
      pending.emplace_back(a.right, b.right);
    } else if (a.kind == ring::Kind::Neg)
      pending.emplace_back(a.left, b.left);
    else if (a.kind == ring::Kind::Embed)
      return mismatch();
  }
  return Error::success();
}

Expected<ring::Expression> checkFieldRegion(const LaneFormula &formula) {
  if (!formula.region || formula.expression.outputs().size() != 1)
    return zkc::error("field-region-profile");
  SmallVector<bool> lanes;
  for (const auto &slot : formula.slots)
    lanes.push_back(slot.lanes);
  auto field =
      formula.expression.facts()[formula.expression.outputs()[0]].field;
  auto actual = readFieldRegion(*formula.region, field, lanes);
  if (!actual)
    return actual.takeError();
  if (auto error = compareFieldExpressions(formula.expression, *actual))
    return std::move(error);
  return std::move(*actual);
}
} // namespace zkc::mathematical
