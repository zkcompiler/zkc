#include "zkc/Analysis/Computation.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Interfaces/Mathematical.h"
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
namespace {
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

// Admit each payload instruction once, including dead work. The temporary
// inventory is shared by the concrete equations, never exported as an AST.
struct PayloadAnalysis {
  ArrayRef<Operation *> operations;
  llvm::DenseMap<Operation *, const protocol::ComputationContract *> contracts;
  bool supported = true;

  PayloadAnalysis(ArrayRef<Operation *> operations, ValueRange results,
                  bool ordered)
      : operations(operations) {
    llvm::DenseSet<Value> live;
    live.insert(results.begin(), results.end());
    for (Operation *op : llvm::reverse(operations)) {
      auto *facet = semantics(op);
      contracts[op] = facet;
      if (!facet) {
        supported = false;
        continue;
      }
      bool used = live.contains(op->getResult(0));
      if ((ordered && !used) || (!facet->access && !facet->law.total))
        supported = false;
      if (used)
        live.insert(op->getOperands().begin(), op->getOperands().end());
    }
  }
  const protocol::ComputationContract *contract(Value value) const {
    return contracts.lookup(value.getDefiningOp());
  }
  std::optional<StringRef> constant(Value value) const {
    auto *facet = contract(value);
    if (!facet || facet->identity != MathematicalIdentity::FieldConstant)
      return std::nullopt;
    auto *op = value.getDefiningOp();
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
      return constant.getValue();
    return cast<StringAttr>(op->getAttrOfType<ArrayAttr>("parameters")[0])
        .getValue();
  }
  // Neutral expressions are followed directly in the admitted SSA. No
  // normalized graph is manufactured and the inventory remains intact.
  Value transparent(Value value) const {
    for (unsigned remaining = 64; remaining; --remaining) {
      auto *op = value.getDefiningOp();
      auto *facet = contract(value);
      if (!facet || op->getNumOperands() != 2 ||
          facet->law.algebra != protocol::ComputationAlgebra::FieldRing)
        break;
      auto left = constant(op->getOperand(0));
      auto right = constant(op->getOperand(1));
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
};
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
struct ComputationFacts {
  ComputationView &view;
  PayloadAnalysis payload;
  SmallVector<Value> inputs;
  llvm::DenseMap<Value, unsigned> inputPositions, itemPositions,
      accessPositions;
  bool aligned, extentIteration, completeAccesses = true;

  ComputationFacts(ComputationView &view, bool aligned)
      : view(view), payload(view.payload, view.results,
                            !isa<func::FuncOp>(view.computation.helper)),
        inputs(view.computation.signature.getNumInputs()), aligned(aligned),
        extentIteration(
            aligned && llvm::all_of(view.items, [&](const auto &item) {
              return hasExtent(view.iteration[item.iteration].operation);
            })) {
    for (const auto &capture : view.captures) {
      inputs[capture.input] = capture.formal;
      inputPositions[capture.formal] = capture.input;
    }
    for (auto [i, item] : enumerate(view.items))
      itemPositions[item.formal] = i;
    for (const auto &item : view.items)
      if (auto access = readAccess(item.formal))
        addAccess(*access);
    for (Operation *op : view.payload) {
      auto *facet = payload.contracts.lookup(op);
      if (!facet || !facet->access)
        continue;
      if (auto access = readAccess(op->getResult(0)))
        addAccess(*access);
      else
        completeAccesses = false;
    }
  }
  Operation *factor(unsigned item) const {
    return view.iteration[view.items[item].iteration].operation;
  }
  std::optional<unsigned> input(Value value) const {
    auto found = inputPositions.find(value);
    return found == inputPositions.end()
               ? std::nullopt
               : std::optional<unsigned>(found->second);
  }
  std::optional<unsigned> item(Value value) const {
    auto found = itemPositions.find(value);
    return found == itemPositions.end()
               ? std::nullopt
               : std::optional<unsigned>(found->second);
  }
  const Access *access(Value value) const {
    auto found = accessPositions.find(payload.transparent(value));
    return found == accessPositions.end() ? nullptr
                                          : &view.accesses[found->second];
  }

private:
  void addAccess(const Access &access) {
    accessPositions[access.value] = view.accesses.size();
    view.accesses.push_back(access);
  }
  // A flat zip admits equal cardinalities before traversal. Only helper
  // premises and source-domain identity are shared with the independent reader;
  // facts known solely on a total operation's actual operands are insufficient.
  bool equalIterationExtent(unsigned input, unsigned axis) const {
    for (const auto &item : view.items) {
      auto *factor = view.iteration[item.iteration].operation;
      if (!hasExtent(factor))
        continue;
      auto domain = domainInput(view.computation, factor->getOperand(0));
      if (!domain)
        continue;
      auto factorAxis = extentAxis(factor);
      if ((*domain == input && factorAxis == axis) ||
          provesEqualExtent(inputs[*domain], factorAxis, inputs[input], axis))
        return true;
    }
    return false;
  }
  std::optional<Access> readAccess(Value value) const {
    auto c = view.computation;
    if (auto position = item(value)) {
      auto *leaf = factor(*position);
      if (!isa<data::DomainElementsOp, data::DomainMatrixRowOp,
               data::DomainMatrixColumnOp>(leaf))
        return std::nullopt;
      auto input = domainInput(c, leaf->getOperand(0));
      if (!input)
        return std::nullopt;
      Access result{AccessKind::Element, *input, *position,
                    std::nullopt,        value,  leaf,
                    std::nullopt};
      if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(leaf)) {
        result.kind = isa<data::DomainMatrixRowOp>(leaf)
                          ? AccessKind::MatrixRow
                          : AccessKind::MatrixColumn;
        result.selectedIndex = domainInput(c, leaf->getOperand(1));
        if (!result.selectedIndex)
          return std::nullopt;
      }
      return result;
    }
    auto *op = value.getDefiningOp();
    auto *facet = payload.contract(value);
    if (!facet || !facet->access)
      return std::nullopt;
    auto container = input(op->getOperand(0));
    if (!container)
      return std::nullopt;
    unsigned varying = 1, selected = 0, axis = 0;
    if (*facet->access == protocol::AccessRule::MatrixCell) {
      auto row = item(op->getOperand(1)), column = item(op->getOperand(2));
      if (row && column) {
        // Two enumerated coordinates retain their exact axes.
        // The bilinear equation below additionally requires a root product.
        for (auto [position, axis] :
             {std::pair{*row, 0u}, std::pair{*column, 1u}}) {
          auto indices = dyn_cast<data::DomainIndicesOp>(factor(position));
          if (!indices || indices.getAxis() != axis ||
              domainInput(c, indices.getInput()) != container)
            return std::nullopt;
        }
        return Access{AccessKind::MatrixCell,
                      *container,
                      *row,
                      std::nullopt,
                      value,
                      op,
                      *column};
      }
      if (column) {
        varying = 2;
        selected = 1;
        axis = 1;
      } else
        selected = 2;
    }
    auto position = item(op->getOperand(varying));
    if (!extentIteration || !position ||
        !isa<data::DomainIndicesOp>(factor(*position)) ||
        !equalIterationExtent(*container, axis))
      return std::nullopt;
    Access result{AccessKind::Indexed, *container, *position,
                  std::nullopt,        value,      op,
                  std::nullopt};
    if (selected) {
      result.kind =
          varying == 2 ? AccessKind::MatrixRow : AccessKind::MatrixColumn;
      result.selectedIndex = input(op->getOperand(selected));
      // Indexed access runs only on nonempty iterations. A bound is required
      // before introducing eager selected-row/column admission.
      if (!result.selectedIndex ||
          !provesBound(op->getOperand(selected), op->getOperand(0), 1 - axis))
        return std::nullopt;
    }
    return result;
  }
};
struct Combine {
  Operation *operation;
  Value term;
  const protocol::ComputationContract *facet;
};
std::optional<Combine> combine(const ComputationFacts &facts) {
  const auto &view = facts.view;
  auto c = view.computation;
  if (!view.result || c.collect || view.seeds.size() != 1 || c.predicate)
    return std::nullopt;
  Value result = facts.payload.transparent(view.result);
  auto *facet = facts.payload.contract(result);
  auto *op = result.getDefiningOp();
  if (!facet || !facet->reduction || !facet->law.associative ||
      op->getNumOperands() != 2)
    return std::nullopt;
  Value accumulator = view.seeds.front().formal;
  Value left = facts.payload.transparent(op->getOperand(0));
  Value right = facts.payload.transparent(op->getOperand(1));
  if (left == accumulator && right != accumulator)
    return Combine{op, right, facet};
  if (facet->law.commutative && right == accumulator && left != accumulator)
    return Combine{op, left, facet};
  return std::nullopt;
}
std::optional<Reduction> analyzeReduction(const ComputationFacts &facts,
                                          const Combine &combined) {
  if (!facts.extentIteration || !facts.payload.supported ||
      !facts.completeAccesses ||
      llvm::any_of(facts.view.accesses, [](const Access &access) {
        return access.kind == AccessKind::MatrixCell;
      }))
    return std::nullopt;
  auto c = facts.view.computation;
  const auto &rule = *combined.facet->reduction;
  Reduction result;
  result.combine = combined.facet->key.str();
  result.accumulator = facts.view.seeds.front().formal;
  result.term = combined.term;
  result.combiner = combined.operation;
  if (auto *direct = facts.access(combined.term);
      direct && !rule.direct.empty()) {
    result.kernel = rule.direct.str();
    result.accesses.push_back(*direct);
  } else {
    Value term = facts.payload.transparent(combined.term);
    auto *facet = facts.payload.contract(term);
    auto *op = term.getDefiningOp();
    if (!facet || !rule.term || facet->identity != *rule.term ||
        op->getNumOperands() != 2)
      return std::nullopt;
    auto *first = facts.access(op->getOperand(rule.first));
    auto *second = facts.access(op->getOperand(rule.second));
    if (!first || !second)
      return std::nullopt;
    result.kernel = rule.contraction.str();
    result.accesses = {*first, *second};
  }
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
  for (const auto &at : result.accesses)
    result.inputs.push_back(at.input);
  return result;
}

std::optional<Elementwise>
analyzeLanes(Block &body, Type field, ValueRange laneArguments,
             const llvm::DenseMap<Value, Value> &lookups,
             const PayloadAnalysis &payload) {
  if (!isa<algebra::FieldType>(field) || body.empty() || !payload.supported ||
      !isa<func::ReturnOp, local::ReturnOp>(body.back()) ||
      body.back().getNumOperands() != 1 ||
      body.back().getOperand(0).getType() != field)
    return std::nullopt;
  llvm::DenseSet<Value> scalars, lanes;
  for (Value argument : body.getArguments())
    if (argument.getType() == field)
      scalars.insert(argument);
  for (Value value : laneArguments) {
    auto argument = dyn_cast<BlockArgument>(value);
    if (!argument || argument.getOwner() != &body || value.getType() != field)
      return std::nullopt;
    scalars.erase(value);
    lanes.insert(value);
  }
  Elementwise result;
  for (Operation *op : payload.operations) {
    auto *facet = payload.contracts.lookup(op);
    Value value = op->getResult(0);
    if (value.getType() != field)
      return std::nullopt;
    if (facet->identity == MathematicalIdentity::FieldConstant) {
      scalars.insert(value);
      continue;
    }
    if (auto found = lookups.find(value); found != lookups.end()) {
      lanes.insert(value);
      result.lookups[value] = found->second;
      continue;
    }
    if (op->getNumOperands() != 2 || !facet->lanes ||
        facet->law.algebra != protocol::ComputationAlgebra::FieldRing)
      return std::nullopt;
    Value left = op->getOperand(0), right = op->getOperand(1);
    if ((!scalars.contains(left) && !lanes.contains(left)) ||
        (!scalars.contains(right) && !lanes.contains(right)))
      return std::nullopt;
    (lanes.contains(left) || lanes.contains(right) ? lanes : scalars)
        .insert(value);
  }
  Value returned = body.back().getOperand(0);
  if (!lanes.contains(returned) && !scalars.contains(returned))
    return std::nullopt;
  return result;
}
std::optional<Elementwise> analyzeElementwise(const ComputationFacts &facts) {
  const auto &view = facts.view;
  auto c = view.computation;
  if (!c.collect || c.predicate || !facts.aligned || !view.result ||
      collection(c.signature.getResult(0)).family != "vector")
    return std::nullopt;
  Type field = elementType(c.signature.getResult(0));
  SmallVector<Value> lanes;
  for (auto [i, item] : enumerate(view.items)) {
    auto *factor = facts.factor(i);
    if (!isa<data::DomainElementsOp, data::DomainIndicesOp>(factor) ||
        collection(factor->getOperand(0).getType()).family != "vector")
      return std::nullopt;
    if (isa<data::DomainElementsOp>(factor))
      lanes.push_back(item.formal);
  }
  llvm::DenseMap<Value, Value> lookups;
  for (const auto &access : view.accesses)
    if (access.kind == AccessKind::Indexed &&
        domainInput(c, facts.factor(access.item)->getOperand(0)) ==
            access.input)
      lookups[access.value] = facts.inputs[access.input];
  return analyzeLanes(c.helper->getRegion(0).front(), field, lanes, lookups,
                      facts.payload);
}
std::optional<Bilinear> analyzeBilinear(const ComputationFacts &facts,
                                        const Combine &combined) {
  const auto &view = facts.view;
  const auto &product = view.iteration[view.root];
  if (combined.facet->identity != MathematicalIdentity::FieldAdd ||
      !facts.payload.supported || !facts.completeAccesses ||
      product.kind != IterationKind::Product || product.children.size() != 2 ||
      view.items.size() != 4)
    return std::nullopt;
  Value matrix, left, right;
  for (unsigned axis = 0; axis < 2; ++axis) {
    const auto &zip = view.iteration[product.children[axis]];
    if (zip.kind != IterationKind::Zip || zip.children.size() != 2)
      return std::nullopt;
    auto indices = dyn_cast<data::DomainIndicesOp>(
        view.iteration[zip.children[0]].operation);
    auto elements = dyn_cast<data::DomainElementsOp>(
        view.iteration[zip.children[1]].operation);
    if (!indices || !elements || indices.getAxis() != axis ||
        collection(indices.getInput().getType()).family != "matrix" ||
        collection(elements.getInput().getType()).family != "vector")
      return std::nullopt;
    if (matrix && matrix != indices.getInput())
      return std::nullopt;
    matrix = indices.getInput();
    (axis ? right : left) = elements.getInput();
  }
  SmallVector<Value> terms, pending{combined.term};
  unsigned remaining = 100000;
  while (!pending.empty() && remaining--) {
    Value value = facts.payload.transparent(pending.pop_back_val());
    auto *facet = facts.payload.contract(value);
    if (facet && facet->identity == MathematicalIdentity::FieldMultiply)
      append_range(pending, value.getDefiningOp()->getOperands());
    else
      terms.push_back(value);
    if (terms.size() > 3)
      return std::nullopt;
  }
  Value leftItem = view.items[1].formal, rightItem = view.items[3].formal;
  if (!pending.empty() || terms.size() != 3 || !is_contained(terms, leftItem) ||
      !is_contained(terms, rightItem))
    return std::nullopt;
  Value cell;
  for (Value term : terms)
    if (term != leftItem && term != rightItem)
      cell = term;
  const auto *access = cell ? facts.access(cell) : nullptr;
  if (!access || access->kind != AccessKind::MatrixCell || access->item != 0 ||
      access->columnItem != 2 ||
      domainInput(view.computation, matrix) != access->input)
    return std::nullopt;
  // No other indexed access, including dead access, may disappear under the
  // product identity. Enumerated element arguments remain in the shared view.
  for (Operation *op : view.payload)
    if (facts.payload.contracts.lookup(op)->access && op != access->operation)
      return std::nullopt;
  return Bilinear{matrix, left, right};
}

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
    if (!remaining || !c.helper || active.size() >= 64 ||
        !active.insert(c.helper).second || c.helper->getNumRegions() != 1 ||
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
    if (root == iterations.end() ||
        body.getNumArguments() != c.signature.getNumInputs() + itemCount(c))
      return std::nullopt;
    result.root = root->second;
    bool aligned = true;
    SmallVector<unsigned> pending{result.root};
    while (!pending.empty()) {
      if (!remaining)
        return std::nullopt;
      --remaining;
      unsigned position = pending.pop_back_val();
      const auto &iteration = result.iteration[position];
      if (iteration.kind == IterationKind::Zip ||
          iteration.kind == IterationKind::Product) {
        aligned &= iteration.kind != IterationKind::Product;
        append_range(pending, llvm::reverse(iteration.children));
      } else {
        unsigned count = cast<data::DomainType>(iteration.descriptor.getType())
                             .getItemTypes()
                             .size();
        for (unsigned i = 0; i < count; ++i) {
          if (result.items.size() >= itemCount(c))
            return std::nullopt;
          result.items.push_back(
              {position, body.getArgument(c.states + result.items.size())});
        }
      }
    }
    if (result.items.size() != itemCount(c))
      return std::nullopt;
    auto actual = [&](unsigned input) -> Value {
      return occurrence && input < occurrence->getNumOperands()
                 ? occurrence->getOperand(input)
                 : Value();
    };
    for (unsigned i = 0; i < c.states; ++i)
      result.seeds.push_back(
          {c.arguments + i, body.getArgument(i), actual(c.arguments + i)});
    unsigned base = c.states + result.items.size();
    for (unsigned input = 0; input < c.signature.getNumInputs(); ++input) {
      if (input >= c.arguments && input < c.arguments + c.states)
        continue;
      unsigned formal = base + input - (input >= c.arguments ? c.states : 0);
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
    ComputationFacts facts(result, aligned);
    if (auto combined = combine(facts)) {
      result.reduction = analyzeReduction(facts, *combined);
      result.bilinear = analyzeBilinear(facts, *combined);
    }
    result.elementwise = analyzeElementwise(facts);
    if (result.reduction)
      result.demand = result.reduction->demand;
    active.erase(c.helper);
    return result;
  }
};
} // namespace
std::optional<Elementwise>
analyzeLaneFormula(Block &body, Type field, ValueRange laneArguments,
                   const llvm::DenseMap<Value, Value> &indices) {
  if (body.empty())
    return std::nullopt;
  SmallVector<Operation *> operations;
  for (auto &op : body.without_terminator())
    operations.push_back(&op);
  PayloadAnalysis payload(operations, body.back().getOperands(),
                          isa<local::FuncOp>(body.getParentOp()));
  llvm::DenseMap<Value, Value> lookups;
  for (Operation *op : operations) {
    auto *facet = payload.contracts.lookup(op);
    if (facet && facet->access == protocol::AccessRule::Element &&
        op->getNumOperands() == 2 &&
        indices.lookup(op->getOperand(1)) == op->getOperand(0) &&
        collection(op->getOperand(0).getType()).family == "vector")
      lookups[op->getResult(0)] = op->getOperand(0);
  }
  return analyzeLanes(body, field, laneArguments, lookups, payload);
}
std::optional<ComputationView> analyzeComputation(Computation c,
                                                  unsigned budget) {
  return ComputationAnalysis(budget).read(c, c.operation);
}
} // namespace zkc::finite
