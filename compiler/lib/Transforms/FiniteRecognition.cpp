#include "FiniteSupport.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "llvm/ADT/DenseSet.h"
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
Collection collection(Type type) {
  Collection c;
  auto bound = protocol::encodeBoundType(type, false);
  if (!bound) {
    consumeError(bound.takeError());
    return c;
  }
  c.element = elementType(type, bound->kind == "matrix");
  c.family = bound->kind == "groups" ? "curve" : bound->kind;
  if (c.family == "sequence") {
    auto item = protocol::encodeBoundType(c.element, false);
    if (item)
      c.arguments.push_back(item->spelling());
    else
      consumeError(item.takeError());
  } else if (auto field = dyn_cast<algebra::FieldType>(c.element)) {
    c.arguments.push_back(field.getDomain().str());
    if (c.family == "field_array")
      c.arguments.push_back(
          std::to_string(cast<RankedTensorType>(type).getDimSize(0)));
  } else if (auto group = dyn_cast<algebra::GroupType>(c.element))
    c.arguments.push_back(group.getDomain().str());
  return c;
}
StringRef arithmetic(Operation *op) {
  if (isa<algebra::SubtractFieldOp>(op))
    return "field.sub";
  if (isa<algebra::ConstantFieldOp>(op))
    return "field.constant";
  if (isa<data::BoundedAtOp>(op))
    return "vector.get";
  if (isa<data::BoundedMatrixAtOp>(op))
    return "matrix.get";
  if (isa<algebra::FieldAddOp>(op))
    return "field.add";
  if (isa<algebra::FieldMultiplyOp>(op))
    return "field.mul";
  if (isa<algebra::GroupAddOp>(op))
    return "curve.add";
  if (isa<algebra::GroupScaleOp>(op))
    return "curve.scale";
  if (!op->hasAttr("binding"))
    return {};
  auto binding = op->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto decl = dyn_cast_or_null<local::OperationBindingOp>(
      SymbolTable::lookupNearestSymbolFrom(op, binding));
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  if (!decl || !decl.getImplementation().empty() || !parameters ||
      (decl.getContract() == "field.constant" ? parameters.size() != 1
                                              : !parameters.empty()))
    return {};
  return decl.getContract();
}
void domainLeaves(Value descriptor, SmallVectorImpl<Operation *> &out) {
  auto *op = descriptor.getDefiningOp();
  if (isa<data::DomainZipOp>(op))
    for (Value v : op->getOperands())
      domainLeaves(v, out);
  else
    out.push_back(op);
}
std::optional<Reduction> recognizeReduction(Computation c) {
  if (c.collect || c.states != 1 || c.predicate)
    return std::nullopt;
  auto &body = c.helper->getRegion(0).front();
  if (body.empty() || body.back().getNumOperands() != 1)
    return std::nullopt;
  Value returned = body.back().getOperand(0);
  auto *combine = returned.getDefiningOp();
  if (!combine || combine->getNumOperands() != 2 ||
      combine->getOperand(0) != body.getArgument(0))
    return std::nullopt;
  auto combineName = arithmetic(combine);
  if (combineName != "field.add" && combineName != "field.mul" &&
      combineName != "curve.add")
    return std::nullopt;
  SmallVector<Operation *> domains;
  domainLeaves(c.domain.getBody().front().back().getOperand(0), domains);
  for (auto *domain : domains)
    if (!isa<data::DomainElementsOp, data::DomainMatrixRowOp,
             data::DomainMatrixColumnOp>(domain))
      return std::nullopt;
  auto item = [&](Value value) -> std::optional<unsigned> {
    auto arg = dyn_cast<BlockArgument>(value);
    if (!arg || arg.getOwner() != &body || arg.getArgNumber() < 1 ||
        arg.getArgNumber() > domains.size())
      return std::nullopt;
    return arg.getArgNumber() - 1;
  };
  Reduction r;
  r.combine = combineName.str();
  Value term = combine->getOperand(1);
  Operation *termOp = term.getDefiningOp();
  unsigned expected = 2;
  if (auto i = item(term); i && combineName != "curve.add") {
    r.kernel = combineName == "field.add" ? "vector.sum" : "vector.product";
    r.items.push_back(*i);
  } else if (termOp && termOp->getNumOperands() == 2) {
    auto a = item(termOp->getOperand(0)), b = item(termOp->getOperand(1));
    if (!a || !b)
      return std::nullopt;
    if (arithmetic(termOp) == "field.mul" && combineName == "field.add") {
      r.kernel = "vector.dot";
      r.items = {*a, *b};
    } else if (arithmetic(termOp) == "curve.scale" &&
               combineName == "curve.add") {
      r.kernel = "curve.msm";
      r.items = {*b, *a};
    } else
      return std::nullopt;
    ++expected;
  } else
    return std::nullopt;
  // Do not remove unused operations, effects or failures from a Local helper.
  if (body.getOperations().size() != expected)
    return std::nullopt;
  for (unsigned i : r.items) {
    auto d = domains[i];
    if (!isa<data::DomainElementsOp>(d)) {
      if (r.kernel != "vector.dot")
        return std::nullopt;
      r.kernel = isa<data::DomainMatrixRowOp>(d)
                     ? "matrix.mul_vector"
                     : "matrix.transpose_mul_vector";
      if (r.items.front() != i)
        std::swap(r.items[0], r.items[1]);
      if (!isa<data::DomainElementsOp>(domains[r.items[1]]) ||
          collection(domains[r.items[1]]->getOperand(0).getType()).family !=
              "vector")
        return std::nullopt;
      break;
    }
    auto col = collection(d->getOperand(0).getType());
    if (col.family != "vector" && col.family != "curve")
      return std::nullopt;
  }
  return r;
}

} // namespace zkc::finite

namespace zkc::finite {
std::optional<std::string> fieldConstant(Operation *op) {
  if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
    return constant.getValue().str();
  if (arithmetic(op) != "field.constant")
    return std::nullopt;
  auto parameters = op->getAttrOfType<ArrayAttr>("parameters");
  if (!parameters || parameters.size() != 1)
    return std::nullopt;
  auto value = dyn_cast<StringAttr>(parameters[0]);
  return value ? std::optional<std::string>(value.getValue().str())
               : std::nullopt;
}
std::optional<Elementwise> recognizeElementwise(Computation c) {
  if (!c.collect || c.predicate ||
      collection(c.signature.getResult(0)).family != "vector")
    return std::nullopt;
  auto field =
      dyn_cast<algebra::FieldType>(elementType(c.signature.getResult(0)));
  if (!field)
    return std::nullopt;
  SmallVector<Operation *> factors;
  domainLeaves(c.domain.getBody().front().back().getOperand(0), factors);
  auto &body = c.helper->getRegion(0).front();
  if (body.empty() || !isa<func::ReturnOp, local::ReturnOp>(body.back()) ||
      body.back().getNumOperands() != 1)
    return std::nullopt;
  Elementwise plan;
  llvm::DenseMap<Value, Value> indices;
  for (auto [i, factor] : enumerate(factors)) {
    if (!isa<data::DomainElementsOp, data::DomainIndicesOp>(factor) ||
        collection(factor->getOperand(0).getType()).family != "vector")
      return std::nullopt;
    Value item = body.getArgument(i);
    if (isa<data::DomainIndicesOp>(factor)) {
      plan.modes[item] = FormulaMode::Index;
      auto container = cast<BlockArgument>(factor->getOperand(0));
      indices[item] =
          body.getArgument(factors.size() + container.getArgNumber());
    } else {
      if (item.getType() != field)
        return std::nullopt;
      plan.modes[item] = FormulaMode::Rows;
    }
  }
  for (auto argument : body.getArguments().drop_front(factors.size())) {
    plan.modes[argument] = argument.getType() == field ? FormulaMode::Scalar
                           : collection(argument.getType()).family == "vector"
                               ? FormulaMode::Container
                               : FormulaMode::Unused;
  }
  for (auto &op : body.without_terminator()) {
    if (op.getNumRegions() || op.getNumResults() != 1 ||
        op.getResult(0).getType() != field)
      return std::nullopt;
    if (fieldConstant(&op)) {
      plan.modes[op.getResult(0)] = FormulaMode::Scalar;
      continue;
    }
    StringRef name = arithmetic(&op);
    if (op.getNumOperands() != 2)
      return std::nullopt;
    auto left = plan.modes.lookup(op.getOperand(0)),
         right = plan.modes.lookup(op.getOperand(1));
    if (name == "vector.get" && left == FormulaMode::Container &&
        right == FormulaMode::Index &&
        indices.lookup(op.getOperand(1)) == op.getOperand(0)) {
      plan.modes[op.getResult(0)] = FormulaMode::Rows;
      plan.lookups[op.getResult(0)] = op.getOperand(0);
      continue;
    }
    if (!is_contained(
            ArrayRef<StringRef>{"field.add", "field.sub", "field.mul"}, name) ||
        (left != FormulaMode::Scalar && left != FormulaMode::Rows) ||
        (right != FormulaMode::Scalar && right != FormulaMode::Rows))
      return std::nullopt;
    plan.modes[op.getResult(0)] =
        left == FormulaMode::Rows || right == FormulaMode::Rows
            ? FormulaMode::Rows
            : FormulaMode::Scalar;
  }
  auto mode = plan.modes.lookup(body.back().getOperand(0));
  if (mode != FormulaMode::Rows && mode != FormulaMode::Scalar)
    return std::nullopt;
  return plan;
}
} // namespace zkc::finite

namespace zkc::finite {
std::optional<Bilinear> recognizeBilinear(Computation c) {
  if (c.collect || c.states != 1 || c.predicate)
    return std::nullopt;
  auto product = c.domain.getBody()
                     .front()
                     .back()
                     .getOperand(0)
                     .getDefiningOp<data::DomainProductOp>();
  if (!product || product.getNumOperands() != 2)
    return std::nullopt;
  Value matrix, left, right;
  for (unsigned axis = 0; axis < 2; ++axis) {
    auto zip = product.getOperand(axis).getDefiningOp<data::DomainZipOp>();
    if (!zip || zip.getNumOperands() != 2)
      return std::nullopt;
    auto indices = zip.getOperand(0).getDefiningOp<data::DomainIndicesOp>();
    auto elements = zip.getOperand(1).getDefiningOp<data::DomainElementsOp>();
    if (!indices || !elements || indices.getAxis() != axis ||
        collection(indices.getInput().getType()).family != "matrix" ||
        collection(elements.getInput().getType()).family != "vector")
      return std::nullopt;
    if (matrix && matrix != indices.getInput())
      return std::nullopt;
    matrix = indices.getInput();
    (axis ? right : left) = elements.getInput();
  }
  auto &body = c.helper->getRegion(0).front();
  if (body.getOperations().size() != 5 ||
      !isa<func::ReturnOp, local::ReturnOp>(body.back()) ||
      body.back().getNumOperands() != 1)
    return std::nullopt;
  auto *add = body.back().getOperand(0).getDefiningOp();
  if (!add || arithmetic(add) != "field.add" ||
      add->getOperand(0) != body.getArgument(0))
    return std::nullopt;
  SmallVector<Value> terms;
  std::function<void(Value)> flatten = [&](Value value) {
    auto *definition = value.getDefiningOp();
    if (definition && arithmetic(definition) == "field.mul") {
      flatten(definition->getOperand(0));
      flatten(definition->getOperand(1));
    } else
      terms.push_back(value);
  };
  flatten(add->getOperand(1));
  if (terms.size() != 3 || !is_contained(terms, body.getArgument(2)) ||
      !is_contained(terms, body.getArgument(4)))
    return std::nullopt;
  Value cell;
  for (Value term : terms)
    if (term != body.getArgument(2) && term != body.getArgument(4))
      cell = term;
  auto *lookup = cell ? cell.getDefiningOp() : nullptr;
  if (!lookup || arithmetic(lookup) != "matrix.get" ||
      lookup->getNumOperands() != 3 ||
      lookup->getOperand(0) !=
          body.getArgument(5 + cast<BlockArgument>(matrix).getArgNumber()) ||
      lookup->getOperand(1) != body.getArgument(1) ||
      lookup->getOperand(2) != body.getArgument(3))
    return std::nullopt;
  return Bilinear{matrix, left, right};
}
} // namespace zkc::finite
