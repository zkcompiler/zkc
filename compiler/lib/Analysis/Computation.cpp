#include "zkc/Analysis/Computation.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include <functional>

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
  } else if (auto field = dyn_cast_if_present<algebra::FieldType>(c.element)) {
    c.arguments.push_back(field.getDomain().str());
    if (c.family == "field_array")
      c.arguments.push_back(
          std::to_string(cast<RankedTensorType>(type).getDimSize(0)));
  } else if (auto group = dyn_cast_if_present<algebra::GroupType>(c.element))
    c.arguments.push_back(group.getDomain().str());
  return c;
}
const protocol::ComputationContract *semantics(Operation *op) {
  if (!op || op->getNumRegions() || op->getNumResults() != 1)
    return nullptr;
  protocol::BindingApplication application;
  SmallVector<std::string> parameters;
  if (op->hasAttr("binding")) {
    for (auto attribute : op->getAttrs())
      if (!is_contained(ArrayRef<StringRef>{"binding", "parameters", "site"},
                        attribute.getName().getValue()))
        return nullptr;
    auto binding = protocol::operationBinding(op);
    if (!binding) {
      consumeError(binding.takeError());
      return nullptr;
    }
    application = std::move(binding->application);
    if (!protocol::operationSupportsContract(op->getName().getStringRef(),
                                             application.contract))
      return nullptr;
    auto attrs = op->getAttrOfType<ArrayAttr>("parameters");
    if (!attrs)
      return nullptr;
    for (auto attr : attrs) {
      auto value = dyn_cast<StringAttr>(attr);
      if (!value)
        return nullptr;
      parameters.push_back(value.getValue().str());
    }
  } else {
    // A mathematical interface alone is not a closed profile admission rule.
    if (!isa<algebra::ConstantFieldOp, algebra::FieldAddOp,
             algebra::SubtractFieldOp, algebra::FieldMultiplyOp,
             algebra::GroupAddOp, algebra::GroupScaleOp, data::BoundedAtOp,
             data::BoundedMatrixAtOp>(op))
      return nullptr;
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (op->getAttrs().size() != 1 || !constant.getValueAttr())
        return nullptr;
      parameters.push_back(constant.getValue().str());
    } else if (!op->getAttrs().empty())
      return nullptr;
    auto mathematical = dyn_cast<MathematicalOpInterface>(op);
    auto identity =
        mathematical ? mathematical.getMathematicalIdentity() : std::nullopt;
    auto *facet = identity ? protocol::computationContract(*identity) : nullptr;
    if (!facet)
      return nullptr;
    application.contract = facet->key.str();
    auto result = protocol::encodeBoundType(op->getResult(0).getType(), false);
    if (!result) {
      consumeError(result.takeError());
      return nullptr;
    }
    application.arguments.push_back(result->identity);
  }
  SmallVector<protocol::BoundType> inputs, outputs;
  auto read = [](TypeRange types, SmallVectorImpl<protocol::BoundType> &out) {
    for (Type type : types) {
      auto bound = protocol::encodeBoundType(type, false);
      if (!bound) {
        consumeError(bound.takeError());
        return false;
      }
      out.push_back(std::move(*bound));
    }
    return true;
  };
  if (!read(op->getOperandTypes(), inputs) ||
      !read(op->getResultTypes(), outputs))
    return nullptr;
  return protocol::admitComputationContract(application, inputs, outputs,
                                            parameters);
}
std::optional<std::string> fieldConstant(Operation *op) {
  auto *facet = semantics(op);
  if (!facet || facet->identity != MathematicalIdentity::FieldConstant)
    return std::nullopt;
  if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
    return constant.getValue().str();
  return cast<StringAttr>(op->getAttrOfType<ArrayAttr>("parameters")[0])
      .getValue()
      .str();
}
void domainLeaves(Value descriptor, SmallVectorImpl<Operation *> &out) {
  SmallVector<Value> pending{descriptor};
  while (!pending.empty()) {
    auto *op = pending.pop_back_val().getDefiningOp();
    if (isa_and_nonnull<data::DomainZipOp>(op))
      for (Value value : llvm::reverse(op->getOperands()))
        pending.push_back(value);
    else
      out.push_back(op);
  }
}
namespace {
Block *helperBody(Computation c) {
  if (!c.helper || c.helper->getNumRegions() != 1 ||
      !c.helper->getRegion(0).hasOneBlock())
    return nullptr;
  auto &body = c.helper->getRegion(0).front();
  if (body.empty() || !isa<func::ReturnOp, local::ReturnOp>(body.back()) ||
      body.back().getNumOperands() != 1)
    return nullptr;
  return &body;
}
Value domainResult(Computation c) {
  return c.domain.getBody().front().back().getOperand(0);
}
unsigned itemCount(Computation c) {
  return cast<data::DomainType>(domainResult(c).getType())
      .getItemTypes()
      .size();
}
std::optional<unsigned> domainInput(Computation c, Value value) {
  auto arg = dyn_cast<BlockArgument>(value);
  if (!arg || arg.getOwner() != &c.domain.getBody().front())
    return std::nullopt;
  return arg.getArgNumber();
}
std::optional<unsigned> helperInput(Computation c, Value value) {
  auto arg = dyn_cast<BlockArgument>(value);
  auto *body = helperBody(c);
  unsigned base = c.states + itemCount(c);
  if (!arg || arg.getOwner() != body || arg.getArgNumber() < base)
    return std::nullopt;
  unsigned input = arg.getArgNumber() - base;
  input += input < c.arguments ? 0 : c.states;
  return input < c.signature.getNumInputs() ? std::optional<unsigned>(input)
                                            : std::nullopt;
}
Value helperArgument(Computation c, unsigned input) {
  auto *body = helperBody(c);
  unsigned position = c.states + itemCount(c) + input;
  if (input >= c.arguments + c.states)
    position -= c.states;
  return body && position < body->getNumArguments()
             ? body->getArgument(position)
             : Value();
}
std::optional<unsigned> itemArgument(Computation c, Value value) {
  auto arg = dyn_cast<BlockArgument>(value);
  if (!arg || arg.getOwner() != helperBody(c) ||
      arg.getArgNumber() < c.states ||
      arg.getArgNumber() >= c.states + itemCount(c))
    return std::nullopt;
  return arg.getArgNumber() - c.states;
}

// Neutral field expressions are read directly from SSA. This bounded walk
// does not manufacture a normalized expression graph or discard the original
// instruction inventory (checked separately below).
Value transparent(Value value) {
  for (unsigned remaining = 64; remaining; --remaining) {
    auto *op = value.getDefiningOp();
    auto *facet = semantics(op);
    if (!facet || op->getNumOperands() != 2 ||
        facet->law.algebra != protocol::ComputationAlgebra::FieldRing)
      break;
    auto left = fieldConstant(op->getOperand(0).getDefiningOp());
    auto right = fieldConstant(op->getOperand(1).getDefiningOp());
    using I = MathematicalIdentity;
    if ((facet->identity == I::FieldAdd ||
         facet->identity == I::FieldSubtract) &&
        right == "0")
      value = op->getOperand(0);
    else if (facet->identity == I::FieldAdd && left == "0")
      value = op->getOperand(1);
    else if (facet->identity == I::FieldMultiply && right == "1")
      value = op->getOperand(0);
    else if (facet->identity == I::FieldMultiply && left == "1")
      value = op->getOperand(1);
    else
      break;
  }
  return value;
}
struct Combine {
  Operation *operation;
  Value term;
  const protocol::ComputationContract *facet;
};
std::optional<Combine> combine(Computation c) {
  auto *body = helperBody(c);
  if (!body || c.collect || c.states != 1 || c.predicate)
    return std::nullopt;
  auto *op = transparent(body->back().getOperand(0)).getDefiningOp();
  auto *facet = semantics(op);
  if (!facet || !facet->reduction || !facet->law.associative ||
      op->getNumOperands() != 2)
    return std::nullopt;
  Value accumulator = body->getArgument(0);
  Value left = transparent(op->getOperand(0));
  Value right = transparent(op->getOperand(1));
  if (left == accumulator && right != accumulator)
    return Combine{op, right, facet};
  if (facet->law.commutative && right == accumulator && left != accumulator)
    return Combine{op, left, facet};
  return std::nullopt;
}
unsigned extentAxis(Operation *factor) {
  if (auto indices = dyn_cast<data::DomainIndicesOp>(factor))
    return indices.getAxis();
  return isa<data::DomainMatrixRowOp>(factor) ? 1 : 0;
}
bool hasExtent(Operation *factor) {
  return isa_and_nonnull<data::DomainElementsOp, data::DomainIndicesOp,
                         data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
      factor);
}
// The caller passes only a flat zip. All its factors are admitted with equal
// cardinality before traversal; this grants extent equality, not value
// identity.
bool equalIterationExtent(Computation c, ArrayRef<Operation *> factors,
                          unsigned input, unsigned axis) {
  for (auto *factor : factors) {
    if (!hasExtent(factor))
      continue;
    auto domain = domainInput(c, factor->getOperand(0));
    if (!domain)
      continue;
    auto factorAxis = extentAxis(factor);
    if ((*domain == input && factorAxis == axis) ||
        provesEqualExtent(helperArgument(c, *domain), factorAxis,
                          helperArgument(c, input), axis))
      return true;
    if (c.total &&
        provesEqualExtent(c.operation->getOperand(*domain), factorAxis,
                          c.operation->getOperand(input), axis))
      return true;
  }
  return false;
}
std::optional<Access> access(Computation c, ArrayRef<Operation *> factors,
                             Value value) {
  value = transparent(value);
  if (auto item = itemArgument(c, value)) {
    if (*item >= factors.size())
      return std::nullopt;
    auto *factor = factors[*item];
    if (!isa<data::DomainElementsOp, data::DomainMatrixRowOp,
             data::DomainMatrixColumnOp>(factor))
      return std::nullopt;
    auto input = domainInput(c, factor->getOperand(0));
    if (!input)
      return std::nullopt;
    Access result{AccessKind::Element, *input, *item,
                  std::nullopt,        value,  factor};
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(factor)) {
      result.kind = isa<data::DomainMatrixRowOp>(factor)
                        ? AccessKind::MatrixRow
                        : AccessKind::MatrixColumn;
      result.selectedIndex = domainInput(c, factor->getOperand(1));
      if (!result.selectedIndex)
        return std::nullopt;
    }
    return result;
  }
  auto *op = value.getDefiningOp();
  auto *facet = semantics(op);
  if (!facet || !facet->access)
    return std::nullopt;
  auto input = helperInput(c, op->getOperand(0));
  if (!input)
    return std::nullopt;
  unsigned varying = 1, selected = 0, axis = 0;
  if (*facet->access == protocol::AccessRule::MatrixCell) {
    // Matrix row: column index varies. Matrix column: row index varies.
    if (itemArgument(c, op->getOperand(2))) {
      varying = 2;
      selected = 1;
      axis = 1;
    } else
      selected = 2;
  }
  auto item = itemArgument(c, op->getOperand(varying));
  if (!item || *item >= factors.size() ||
      !isa<data::DomainIndicesOp>(factors[*item]) ||
      !equalIterationExtent(c, factors, *input, axis))
    return std::nullopt;
  Access result{AccessKind::Indexed, *input, *item, std::nullopt, value, op};
  if (selected) {
    result.kind =
        varying == 2 ? AccessKind::MatrixRow : AccessKind::MatrixColumn;
    result.selectedIndex = helperInput(c, op->getOperand(selected));
    // Unlike a view constructor, an indexed access executes only on nonempty
    // iterations. Require a bound before introducing eager row admission.
    if (!result.selectedIndex ||
        !provesBound(op->getOperand(selected), op->getOperand(0), 1 - axis))
      return std::nullopt;
  }
  return result;
}
bool supportedInventory(Computation c, ArrayRef<Operation *> factors,
                        bool bilinear = false) {
  auto *body = helperBody(c);
  if (!body || body->getOperations().size() > 100000)
    return false;
  llvm::DenseSet<Value> live;
  live.insert(body->back().getOperand(0));
  for (auto &op : llvm::reverse(body->without_terminator())) {
    auto *facet = semantics(&op);
    if (!facet)
      return false;
    bool used = live.contains(op.getResult(0));
    // Ordered helper instructions, including unused successful arithmetic,
    // are not discarded by optional reduction recognition.
    if (!used && !isa<func::FuncOp>(c.helper))
      return false;
    if (facet->access) {
      if (bilinear) {
        if (!used)
          return false;
      } else if (!access(c, factors, op.getResult(0)))
        return false;
    } else if (!facet->law.total)
      return false;
    if (used)
      live.insert(op.getOperands().begin(), op.getOperands().end());
  }
  return true;
}
} // namespace

std::optional<Reduction> recognizeReduction(Computation c) {
  auto combined = combine(c);
  if (!combined)
    return std::nullopt;
  SmallVector<Operation *> factors;
  domainLeaves(domainResult(c), factors);
  if (!llvm::all_of(factors, hasExtent) || factors.size() != itemCount(c))
    return std::nullopt;
  const auto &rule = *combined->facet->reduction;
  Reduction result;
  result.combine = combined->facet->key.str();
  result.accumulator = helperBody(c)->getArgument(0);
  result.term = combined->term;
  result.combiner = combined->operation;
  if (auto direct = access(c, factors, combined->term);
      direct && !rule.direct.empty()) {
    result.kernel = rule.direct.str();
    result.accesses.push_back(*direct);
  } else {
    auto *term = transparent(combined->term).getDefiningOp();
    auto *facet = semantics(term);
    if (!facet || !rule.term || facet->identity != *rule.term ||
        term->getNumOperands() != 2)
      return std::nullopt;
    auto first = access(c, factors, term->getOperand(rule.first));
    auto second = access(c, factors, term->getOperand(rule.second));
    if (!first || !second)
      return std::nullopt;
    result.kernel = rule.contraction.str();
    result.accesses = {*first, *second};
  }
  if (!supportedInventory(c, factors))
    return std::nullopt;
  for (unsigned i = 0; i < result.accesses.size(); ++i) {
    const auto &at = result.accesses[i];
    bool matrix =
        at.kind == AccessKind::MatrixRow || at.kind == AccessKind::MatrixColumn;
    auto container = collection(c.signature.getInput(at.input));
    if (!matrix) {
      if (container.family != "vector" && container.family != "curve")
        return std::nullopt;
      continue;
    }
    if (rule.matrixRow.empty() || result.accesses.size() != 2 ||
        collection(c.signature.getInput(result.accesses[1 - i].input)).family !=
            "vector")
      return std::nullopt;
    result.demand = at.kind == AccessKind::MatrixRow ? DemandKind::MatrixRow
                                                     : DemandKind::MatrixColumn;
    result.kernel = (result.demand == DemandKind::MatrixRow ? rule.matrixRow
                                                            : rule.matrixColumn)
                        .str();
    result.selectedIndex = at.selectedIndex;
    if (i != 0)
      std::swap(result.accesses[0], result.accesses[1]);
    break;
  }
  for (const auto &at : result.accesses) {
    result.inputs.push_back(at.input);
  }
  return result;
}

std::optional<Elementwise>
recognizeFormula(Block &body, Type field,
                 llvm::DenseMap<Value, FormulaMode> modes,
                 const llvm::DenseMap<Value, Value> &indices) {
  if (!isa<algebra::FieldType>(field) || body.empty() ||
      !isa<func::ReturnOp, local::ReturnOp>(body.back()) ||
      body.back().getNumOperands() != 1 ||
      body.back().getOperand(0).getType() != field)
    return std::nullopt;
  if (isa<local::FuncOp>(body.getParentOp())) {
    llvm::DenseSet<Value> live{body.back().getOperand(0)};
    for (auto &op : llvm::reverse(body.without_terminator())) {
      if (op.getNumResults() != 1 || !live.contains(op.getResult(0)))
        return std::nullopt;
      live.insert(op.getOperands().begin(), op.getOperands().end());
    }
  }
  Elementwise plan;
  plan.modes = std::move(modes);
  auto mode = [&](Value value) {
    auto found = plan.modes.find(value);
    return found == plan.modes.end() ? FormulaMode::Unused : found->second;
  };
  for (auto &op : body.without_terminator()) {
    auto *facet = semantics(&op);
    if (!facet || op.getResult(0).getType() != field)
      return std::nullopt;
    if (facet->identity == MathematicalIdentity::FieldConstant) {
      plan.modes[op.getResult(0)] = FormulaMode::Scalar;
      continue;
    }
    if (op.getNumOperands() != 2)
      return std::nullopt;
    auto left = mode(op.getOperand(0)), right = mode(op.getOperand(1));
    if (facet->access == protocol::AccessRule::Element &&
        left == FormulaMode::Container && right == FormulaMode::Index &&
        indices.lookup(op.getOperand(1)) == op.getOperand(0)) {
      plan.modes[op.getResult(0)] = FormulaMode::Rows;
      plan.lookups[op.getResult(0)] = op.getOperand(0);
      continue;
    }
    if (!facet->lanes ||
        facet->law.algebra != protocol::ComputationAlgebra::FieldRing ||
        (left != FormulaMode::Scalar && left != FormulaMode::Rows) ||
        (right != FormulaMode::Scalar && right != FormulaMode::Rows))
      return std::nullopt;
    plan.modes[op.getResult(0)] =
        left == FormulaMode::Rows || right == FormulaMode::Rows
            ? FormulaMode::Rows
            : FormulaMode::Scalar;
  }
  auto result = mode(body.back().getOperand(0));
  if (result != FormulaMode::Rows && result != FormulaMode::Scalar)
    return std::nullopt;
  return plan;
}
std::optional<Elementwise> recognizeElementwise(Computation c) {
  if (!c.collect || c.predicate || !helperBody(c) ||
      collection(c.signature.getResult(0)).family != "vector")
    return std::nullopt;
  Type field = elementType(c.signature.getResult(0));
  SmallVector<Operation *> factors;
  domainLeaves(domainResult(c), factors);
  auto &body = *helperBody(c);
  llvm::DenseMap<Value, FormulaMode> modes;
  llvm::DenseMap<Value, Value> indices;
  for (auto [i, factor] : enumerate(factors)) {
    if (!isa_and_nonnull<data::DomainElementsOp, data::DomainIndicesOp>(
            factor) ||
        collection(factor->getOperand(0).getType()).family != "vector")
      return std::nullopt;
    Value item = body.getArgument(i);
    if (isa<data::DomainIndicesOp>(factor)) {
      auto input = domainInput(c, factor->getOperand(0));
      if (!input)
        return std::nullopt;
      modes[item] = FormulaMode::Index;
      indices[item] = helperArgument(c, *input);
    } else {
      if (item.getType() != field)
        return std::nullopt;
      modes[item] = FormulaMode::Rows;
    }
  }
  for (auto argument : body.getArguments().drop_front(factors.size()))
    modes[argument] = argument.getType() == field ? FormulaMode::Scalar
                      : collection(argument.getType()).family == "vector"
                          ? FormulaMode::Container
                          : FormulaMode::Unused;
  return recognizeFormula(body, field, std::move(modes), indices);
}

std::optional<Bilinear> recognizeBilinear(Computation c) {
  auto combined = combine(c);
  if (!combined || combined->facet->identity != MathematicalIdentity::FieldAdd)
    return std::nullopt;
  auto product = domainResult(c).getDefiningOp<data::DomainProductOp>();
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
  auto &body = *helperBody(c);
  SmallVector<Value> terms, pending{combined->term};
  unsigned remaining = 100000;
  while (!pending.empty() && remaining--) {
    Value value = transparent(pending.pop_back_val());
    auto *definition = value.getDefiningOp();
    auto *facet = semantics(definition);
    if (facet && facet->identity == MathematicalIdentity::FieldMultiply)
      append_range(pending, definition->getOperands());
    else
      terms.push_back(value);
    if (terms.size() > 3)
      return std::nullopt;
  }
  if (!pending.empty() || terms.size() != 3 ||
      !is_contained(terms, body.getArgument(2)) ||
      !is_contained(terms, body.getArgument(4)))
    return std::nullopt;
  Value cell;
  for (Value term : terms)
    if (term != body.getArgument(2) && term != body.getArgument(4))
      cell = term;
  auto *lookup = cell ? cell.getDefiningOp() : nullptr;
  auto *facet = semantics(lookup);
  auto input = domainInput(c, matrix);
  if (!facet || facet->access != protocol::AccessRule::MatrixCell || !input ||
      lookup->getOperand(0) != helperArgument(c, *input) ||
      lookup->getOperand(1) != body.getArgument(1) ||
      lookup->getOperand(2) != body.getArgument(3) ||
      !supportedInventory(c, {}, true))
    return std::nullopt;
  // No other live indexed access may be erased under the product identity.
  for (auto &op : body.without_terminator())
    if (semantics(&op)->access && &op != lookup)
      return std::nullopt;
  return Bilinear{matrix, left, right};
}

namespace {
std::optional<IterationKind> iterationKind(Operation *op) {
  if (isa<data::DomainElementsOp>(op))
    return IterationKind::Elements;
  if (isa<data::DomainIndicesOp>(op))
    return IterationKind::Indices;
  if (isa<data::DomainMatrixRowOp>(op))
    return IterationKind::MatrixRow;
  if (isa<data::DomainMatrixColumnOp>(op))
    return IterationKind::MatrixColumn;
  if (isa<data::DomainMatrixCoordinatesOp>(op))
    return IterationKind::Coordinates;
  if (isa<data::DomainRangeOp>(op))
    return IterationKind::Range;
  if (isa<data::DomainZipOp>(op))
    return IterationKind::Zip;
  if (isa<data::DomainProductOp>(op))
    return IterationKind::Product;
  return std::nullopt;
}
class ComputationAnalysis {
  unsigned remaining;
  llvm::DenseSet<Operation *> active;

public:
  explicit ComputationAnalysis(unsigned budget) : remaining(budget) {}
  std::optional<ComputationView> read(Computation c, Operation *occurrence) {
    if (!remaining || active.size() >= 64 || !active.insert(c.helper).second ||
        !c.helper || c.helper->getNumRegions() != 1 ||
        !c.helper->getRegion(0).hasOneBlock())
      return std::nullopt;
    --remaining;
    auto &body = c.helper->getRegion(0).front();
    if (body.empty() || !isa<func::ReturnOp, local::ReturnOp>(body.back()))
      return std::nullopt;
    ComputationView result;
    result.computation = c;
    result.occurrence = occurrence;
    result.demand = c.collect ? DemandKind::Collection : DemandKind::Scalar;
    llvm::DenseMap<Value, unsigned> iterations;
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      if (!remaining)
        return std::nullopt;
      --remaining;
      auto kind = iterationKind(&op);
      if (!kind || op.getNumResults() != 1)
        return std::nullopt;
      Iteration iteration{&op, op.getResult(0), *kind, {}};
      if (*kind == IterationKind::Zip || *kind == IterationKind::Product)
        for (Value child : op.getOperands()) {
          auto found = iterations.find(child);
          if (found == iterations.end())
            return std::nullopt;
          iteration.children.push_back(found->second);
        }
      iterations[op.getResult(0)] = result.iteration.size();
      result.iteration.push_back(std::move(iteration));
      result.admission.push_back(&op);
    }
    auto root = iterations.find(domainResult(c));
    if (root == iterations.end())
      return std::nullopt;
    result.root = root->second;
    auto actual = [&](unsigned input) -> Value {
      return occurrence && input < occurrence->getNumOperands()
                 ? occurrence->getOperand(input)
                 : Value();
    };
    for (unsigned i = 0; i < c.states; ++i)
      result.seeds.push_back(
          {c.arguments + i, body.getArgument(i), actual(c.arguments + i)});
    unsigned base = c.states + itemCount(c);
    for (unsigned input = 0; input < c.signature.getNumInputs(); ++input) {
      if (input >= c.arguments && input < c.arguments + c.states)
        continue;
      unsigned formal = base + input - (input >= c.arguments ? c.states : 0);
      if (formal >= body.getNumArguments())
        return std::nullopt;
      result.captures.push_back(
          {input, body.getArgument(formal), actual(input)});
    }
    for (auto &op : body.without_terminator()) {
      if (!remaining)
        return std::nullopt;
      --remaining;
      result.payload.push_back(&op);
      Operation *definition = &op;
      if (isa<local::ApplyOp, func::CallOp>(op)) {
        auto reference = op.getAttrOfType<FlatSymbolRefAttr>("callee");
        definition = reference
                         ? SymbolTable::lookupNearestSymbolFrom(&op, reference)
                         : nullptr;
      }
      if (!definition || !isComputation(definition))
        continue;
      Computation child;
      if (failed(describe(definition, child)))
        return std::nullopt;
      auto nested = read(child, &op);
      if (!nested)
        return std::nullopt;
      result.nested.push_back(std::move(*nested));
    }
    append_range(result.results, body.back().getOperands());
    if (result.results.size() == 1)
      result.result = result.results.front();
    result.reduction = recognizeReduction(c);
    result.elementwise = recognizeElementwise(c);
    if (result.reduction) {
      result.demand = result.reduction->demand;
      result.accesses = result.reduction->accesses;
    } else if (helperBody(c)) {
      SmallVector<Operation *> factors;
      domainLeaves(domainResult(c), factors);
      if (llvm::all_of(factors, hasExtent) && factors.size() == itemCount(c)) {
        for (unsigned i = 0; i < itemCount(c); ++i)
          if (auto item = access(c, factors, body.getArgument(c.states + i)))
            result.accesses.push_back(*item);
        for (auto &op : body.without_terminator())
          if (op.getNumResults() == 1)
            if (auto item = access(c, factors, op.getResult(0)))
              result.accesses.push_back(*item);
      }
    }
    active.erase(c.helper);
    return result;
  }
};
} // namespace
std::optional<ComputationView> analyzeComputation(Computation c,
                                                  unsigned budget) {
  return ComputationAnalysis(budget).read(c, c.operation);
}
} // namespace zkc::finite
