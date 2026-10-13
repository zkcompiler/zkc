#include "ComputationEquations.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"
#include <limits>

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
using namespace finite;
namespace {
struct EquationWork {
  ComputationWork &remaining;
  bool exhausted = false;
  ComputationDiagnostic *diagnostic = nullptr;
  bool take(uint64_t amount = 1) {
    if (exhausted)
      return false;
    OptimizationOutcome outcome;
    if (!consumeComputationWork(remaining.equations, amount,
                                WorkOwner::Equations, &outcome)) {
      exhausted = true;
      if (diagnostic)
        diagnostic->outcome = outcome;
      return false;
    }
    return true;
  }
};
// Admit each payload instruction once, including dead work. The temporary
// inventory is shared by the concrete equations, never exported as an AST.
struct PayloadAnalysis {
  ArrayRef<Operation *> operations;
  llvm::DenseMap<Operation *, const protocol::ComputationContract *> contracts;
  bool supported = true;
  Operation *nonFieldOperation = nullptr, *nonModuleOperation = nullptr;
  EquationWork &work;

  PayloadAnalysis(ArrayRef<Operation *> operations, ValueRange results,
                  bool ordered, EquationWork &work,
                  Operation *nestedCall = nullptr)
      : operations(operations), work(work) {
    llvm::DenseSet<Value> live;
    if (!work.take(results.size())) {
      supported = false;
      return;
    }
    live.insert(results.begin(), results.end());
    for (Operation *op : llvm::reverse(operations)) {
      if (!work.take(1 + op->getNumOperands())) {
        supported = false;
        return;
      }
      auto *facet = semantics(op);
      contracts[op] = facet;
      if (!facet && op != nestedCall) {
        supported = false;
        continue;
      }
      // These are the closed fragments interpreted by the independent readers.
      // A new total algebra law does not automatically extend either reader.
      if (facet) {
        using I = MathematicalIdentity;
        bool scalar = facet->identity == I::FieldConstant ||
                      facet->identity == I::FieldAdd ||
                      facet->identity == I::FieldSubtract ||
                      facet->identity == I::FieldMultiply;
        if (!nonFieldOperation && !scalar &&
            !(facet->access &&
              isa<algebra::FieldType>(op->getResult(0).getType())))
          nonFieldOperation = op;
        if (!nonModuleOperation && !scalar && facet->identity != I::GroupAdd &&
            facet->identity != I::GroupScale)
          nonModuleOperation = op;
      }
      bool used = live.contains(op->getResult(0));
      if ((ordered && !used) || (facet && !facet->access && !facet->law.total))
        supported = false;
      if (used)
        live.insert(op->getOperands().begin(), op->getOperands().end());
    }
  }
  bool formula(Operation *unsupported) const {
    if (unsupported && work.diagnostic)
      *work.diagnostic = {{OptimizationStatus::Unsupported,
                           OptimizationReason::ImplementationRestriction},
                          unsupported,
                          {},
                          work.diagnostic->occurrencePath};
    return !unsupported;
  }
  bool fieldFormula() const { return formula(nonFieldOperation); }
  bool moduleFormula() const { return formula(nonModuleOperation); }
  const protocol::ComputationContract *contract(Value value) const {
    return value ? contracts.lookup(value.getDefiningOp()) : nullptr;
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
    for (unsigned remaining = 64; value && remaining; --remaining) {
      if (!work.take())
        return {};
      auto *op = value.getDefiningOp();
      auto *facet = contract(value);
      if (!facet || op->getNumOperands() != 2 ||
          facet->law.algebra != protocol::ComputationAlgebra::FieldRing)
        break;
      auto left = constant(op->getOperand(0));
      auto right = constant(op->getOperand(1));
      auto identity = [](std::optional<StringRef> value,
                         protocol::ScalarIdentity identity) {
        return (identity == protocol::ScalarIdentity::Zero && value == "0") ||
               (identity == protocol::ScalarIdentity::One && value == "1");
      };
      if (identity(right, facet->law.rightIdentity))
        value = op->getOperand(0);
      else if (identity(left, facet->law.leftIdentity))
        value = op->getOperand(1);
      else
        break;
    }
    return value;
  }
};
bool hasExtent(Operation *factor) {
  return isa_and_nonnull<data::DomainElementsOp, data::DomainIndicesOp,
                         data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
      factor);
}
struct ComputationFacts {
  const ComputationView &view;
  PayloadAnalysis payload;
  SmallVector<Value> inputs;
  llvm::DenseMap<Value, unsigned> accessPositions;
  bool aligned = true, extentIteration = false;
  Value missingAccess;

  ComputationFacts(const ComputationView &view, EquationWork &work)
      : view(view), payload(view.payload, view.results,
                            !isa<func::FuncOp>(view.computation.helper), work),
        inputs(view.computation.signature.getNumInputs()) {
    if (!work.take(view.items.size() + view.captures.size() +
                   view.accesses.size() + view.payload.size() + inputs.size() +
                   view.axes.size() + view.admission.size() +
                   view.occurrencePath.size() + view.environment.inputs.size()))
      return;
    SmallVector<unsigned> pending{view.root};
    while (!pending.empty()) {
      if (!work.take())
        return;
      const auto &iteration = view.iteration[pending.pop_back_val()];
      aligned &= iteration.kind != IterationKind::Product;
      append_range(pending, iteration.children);
    }
    extentIteration =
        aligned && llvm::all_of(view.items, [&](const auto &item) {
          return hasExtent(view.iteration[item.iteration].operation);
        });
    for (const auto &capture : view.captures)
      inputs[capture.input] = capture.formal;
    for (auto [i, access] : enumerate(view.accesses))
      accessPositions[access.value] = i;
    for (Operation *op : view.payload) {
      auto *facet = payload.contracts.lookup(op);
      if (!missingAccess && facet && facet->access &&
          !accessPositions.contains(op->getResult(0)))
        missingAccess = op->getResult(0);
    }
  }
  void reportMissingAccess() const {
    if (!payload.work.diagnostic)
      return;
    auto found = llvm::find_if(view.accessDeclines, [&](const auto &decline) {
      return decline.access == missingAccess;
    });
    *payload.work.diagnostic =
        found != view.accessDeclines.end()
            ? *found
            : ComputationDiagnostic{{OptimizationStatus::Unsupported,
                                     OptimizationReason::Structure},
                                    missingAccess.getDefiningOp(),
                                    missingAccess,
                                    view.occurrencePath};
  }
  Operation *factor(unsigned item) const {
    return view.iteration[view.items[item].iteration].operation;
  }
  const Access *access(Value value) const {
    auto found = accessPositions.find(payload.transparent(value));
    return found == accessPositions.end() ? nullptr
                                          : &view.accesses[found->second];
  }
};
EquationWitness witness(const ComputationView &view,
                        ArrayRef<Access> accesses) {
  EquationWitness result;
  result.occurrencePath = view.occurrencePath;
  for (const auto &axis : view.axes)
    result.reducedAxes.push_back(axis.identity);
  append_range(result.accesses, accesses);
  if (view.seeds.size() == 1)
    result.seed = view.seeds.front();
  result.yielded = view.result;
  result.admission = view.admission;
  for (const auto &input : view.environment.inputs)
    result.environment.push_back({input.formal, input.actual});
  return result;
}
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
  auto *op = result ? result.getDefiningOp() : nullptr;
  if (!facet || !facet->law.associative || op->getNumOperands() != 2)
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
      llvm::any_of(facts.view.accesses, [](const Access &access) {
        return access.kind == AccessKind::MatrixCell;
      }))
    return std::nullopt;
  if (facts.missingAccess) {
    facts.reportMissingAccess();
    return std::nullopt;
  }
  if (combined.facet->law.algebra == protocol::ComputationAlgebra::FieldRing) {
    if (!facts.payload.fieldFormula())
      return std::nullopt;
    // The field reader admits indices and matrix slices, but element domains
    // must carry field vectors. An unused zipped item still belongs to the
    // source domain and cannot disappear from independent comparison.
    for (const auto &item : facts.view.items) {
      auto *factor = facts.view.iteration[item.iteration].operation;
      if (isa<data::DomainElementsOp>(factor) &&
          !isa<algebra::FieldVectorType>(factor->getOperand(0).getType())) {
        facts.payload.formula(factor);
        return std::nullopt;
      }
    }
  }
  if (combined.facet->law.algebra ==
      protocol::ComputationAlgebra::GroupModule) {
    if (!facts.payload.moduleFormula())
      return std::nullopt;
    // The module reader currently interprets element domains and their zips.
    // Even an unused extra factor must remain within that source fragment.
    for (const auto &item : facts.view.items) {
      auto *factor = facts.view.iteration[item.iteration].operation;
      if (!isa<data::DomainElementsOp>(factor) ||
          !isa<algebra::FieldVectorType, algebra::GroupVectorType>(
              factor->getOperand(0).getType())) {
        facts.payload.formula(factor);
        return std::nullopt;
      }
    }
  }
  auto c = facts.view.computation;
  Reduction result;
  result.combine = combined.facet->identity;
  result.accumulator = facts.view.seeds.front().formal;
  result.term = combined.term;
  result.combiner = combined.operation;
  if (auto *direct = facts.access(combined.term)) {
    result.accesses.push_back(*direct);
  } else {
    Value term = facts.payload.transparent(combined.term);
    auto *facet = facts.payload.contract(term);
    auto *op = term ? term.getDefiningOp() : nullptr;
    if (!facet || op->getNumOperands() != 2)
      return std::nullopt;
    // This bounded matcher recognizes two maintained term equations. Their
    // recognition is independent of whether a realization is installed.
    using I = MathematicalIdentity;
    if (!((result.combine == I::FieldAdd &&
           facet->identity == I::FieldMultiply) ||
          (result.combine == I::GroupAdd && facet->identity == I::GroupScale)))
      return std::nullopt;
    auto *first = facts.access(op->getOperand(0));
    auto *second = facts.access(op->getOperand(1));
    if (!first || !second)
      return std::nullopt;
    result.termIdentity = facet->identity;
    result.accesses = {*first, *second};
  }
  for (unsigned i = 0; i < result.accesses.size(); ++i) {
    const auto &at = result.accesses[i];
    bool matrix =
        at.kind == AccessKind::MatrixRow || at.kind == AccessKind::MatrixColumn;
    Type container = c.signature.getInput(at.input);
    if (!matrix) {
      if (!isa<algebra::FieldVectorType, algebra::GroupVectorType>(container))
        return std::nullopt;
      continue;
    }
    if (result.combine != MathematicalIdentity::FieldAdd ||
        result.termIdentity != MathematicalIdentity::FieldMultiply ||
        result.accesses.size() != 2 ||
        !isa<algebra::FieldVectorType>(
            c.signature.getInput(result.accesses[1 - i].input)))
      return std::nullopt;
    result.matrixAccess = at.kind;
    result.selectedIndex = at.selectedIndex;
    result.matrixOperand = i;
    break;
  }
  for (const auto &at : result.accesses)
    result.inputs.push_back(at.input);
  result.witness = witness(facts.view, result.accesses);
  return result;
}

std::optional<Elementwise>
analyzeLanes(Block &body, Type field, ValueRange laneArguments,
             const llvm::DenseMap<Value, Value> &lookups,
             const PayloadAnalysis &payload,
             ArrayRef<ComputationDiagnostic> accessDeclines = {}) {
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
    if (!payload.work.take())
      return std::nullopt;
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
    if (facet->access && payload.work.diagnostic)
      for (const auto &decline : accessDeclines)
        if (decline.access == value) {
          *payload.work.diagnostic = decline;
          break;
        }
    if (op->getNumOperands() != 2 ||
        facet->law.algebra != protocol::ComputationAlgebra::FieldRing ||
        !is_contained(
            ArrayRef<MathematicalIdentity>{MathematicalIdentity::FieldAdd,
                                           MathematicalIdentity::FieldSubtract,
                                           MathematicalIdentity::FieldMultiply},
            facet->identity))
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
      !isa<algebra::FieldVectorType>(c.signature.getResult(0)))
    return std::nullopt;
  Type field = elementType(c.signature.getResult(0));
  SmallVector<Value> lanes;
  for (auto [i, item] : enumerate(view.items)) {
    auto *factor = facts.factor(i);
    if (!isa<data::DomainElementsOp, data::DomainIndicesOp>(factor) ||
        !isa<algebra::FieldVectorType>(factor->getOperand(0).getType()))
      return std::nullopt;
    if (isa<data::DomainElementsOp>(factor))
      lanes.push_back(item.formal);
  }
  llvm::DenseMap<Value, Value> lookups;
  for (const auto &access : view.accesses)
    if (access.kind == AccessKind::Indexed &&
        view.environment.inputPosition(
            facts.factor(access.item)->getOperand(0)) == access.input)
      lookups[access.value] = facts.inputs[access.input];
  return analyzeLanes(c.helper->getRegion(0).front(), field, lanes, lookups,
                      facts.payload, view.accessDeclines);
}
std::optional<Bilinear> analyzeBilinear(const ComputationFacts &facts,
                                        const Combine &combined) {
  const auto &view = facts.view;
  const auto &product = view.iteration[view.root];
  if (combined.facet->identity != MathematicalIdentity::FieldAdd ||
      !facts.payload.supported || product.kind != IterationKind::Product ||
      product.children.size() != 2 || view.items.size() != 4)
    return std::nullopt;
  if (!facts.payload.fieldFormula())
    return std::nullopt;
  if (facts.missingAccess) {
    facts.reportMissingAccess();
    return std::nullopt;
  }
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
        !isa<algebra::FieldMatrixType>(indices.getInput().getType()) ||
        !isa<algebra::FieldVectorType>(elements.getInput().getType()))
      return std::nullopt;
    if (matrix && matrix != indices.getInput())
      return std::nullopt;
    matrix = indices.getInput();
    (axis ? right : left) = elements.getInput();
  }
  SmallVector<Value> terms, pending{combined.term};
  while (!pending.empty()) {
    if (!facts.payload.work.take())
      return std::nullopt;
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
      view.environment.inputPosition(matrix) != access->input)
    return std::nullopt;
  // No other indexed access, including dead access, may disappear under the
  // product identity. Enumerated element arguments remain in the shared view.
  for (Operation *op : view.payload)
    if (facts.payload.contracts.lookup(op)->access && op != access->operation)
      return std::nullopt;
  return Bilinear{witness(view, view.accesses), matrix, left, right};
}

} // namespace
std::optional<Elementwise>
matchLaneFormula(Block &body, Type field, ValueRange laneArguments,
                 const llvm::DenseMap<Value, Value> &indices) {
  if (body.empty())
    return std::nullopt;
  SmallVector<Operation *> operations;
  for (auto &op : body.without_terminator())
    operations.push_back(&op);
  // Explicit maps are required realizations whose helper expansion already
  // has a cumulative capacity check. This compatibility entry must not spend
  // the optional finite-recognition reserve or add a second admission limit.
  ComputationWork remaining;
  remaining.equations = std::numeric_limits<uint64_t>::max();
  EquationWork work{remaining};
  PayloadAnalysis payload(operations, body.back().getOperands(),
                          isa<local::FuncOp>(body.getParentOp()), work);
  llvm::DenseMap<Value, Value> lookups;
  for (Operation *op : operations) {
    auto *facet = payload.contracts.lookup(op);
    if (facet && facet->access == protocol::AccessRule::Element &&
        op->getNumOperands() == 2 &&
        indices.lookup(op->getOperand(1)) == op->getOperand(0) &&
        isa<algebra::FieldVectorType>(op->getOperand(0).getType()))
      lookups[op->getResult(0)] = op->getOperand(0);
  }
  auto result = analyzeLanes(body, field, laneArguments, lookups, payload);
  return work.exhausted ? std::nullopt : result;
}

std::optional<std::pair<unsigned, unsigned>>
matchMapProduct(Block &formula, ArrayRef<bool> rowwise) {
  if (formula.empty() || formula.getNumArguments() != rowwise.size() ||
      formula.back().getNumOperands() != 1)
    return std::nullopt;
  SmallVector<Value> lanes;
  for (auto [i, argument] : enumerate(formula.getArguments()))
    if (rowwise[i])
      lanes.push_back(argument);
  if (!matchLaneFormula(formula, formula.back().getOperand(0).getType(), lanes))
    return std::nullopt;
  auto *product = formula.back().getOperand(0).getDefiningOp();
  auto *contract = product ? finite::semantics(product) : nullptr;
  if (!contract || contract->identity != MathematicalIdentity::FieldMultiply ||
      product->getNumOperands() != 2)
    return std::nullopt;
  auto left = dyn_cast<BlockArgument>(product->getOperand(0));
  auto right = dyn_cast<BlockArgument>(product->getOperand(1));
  if (!left || !right || left.getOwner() != &formula ||
      right.getOwner() != &formula || !rowwise[left.getArgNumber()] ||
      !rowwise[right.getArgNumber()])
    return std::nullopt;
  return std::make_pair(left.getArgNumber(), right.getArgNumber());
}
ComputationEquations matchComputation(const ComputationView &view) {
  ComputationWork work;
  return matchComputation(view, work);
}
ComputationEquations matchComputation(const ComputationView &view,
                                      ComputationWork &remaining,
                                      ComputationDiagnostic *diagnostic) {
  ComputationDiagnostic observed{
      {OptimizationStatus::Unsupported, OptimizationReason::Equation},
      view.occurrence,
      {},
      view.occurrencePath};
  auto report = llvm::scope_exit([&] {
    if (diagnostic)
      *diagnostic = observed;
  });
  ComputationEquations result;
  EquationWork work{remaining, false, &observed};
  if (!work.take())
    return result;
  ComputationFacts facts(view, work);
  if (work.exhausted)
    return result;
  if (auto combined = combine(facts)) {
    result.reduction = analyzeReduction(facts, *combined);
    result.bilinear = analyzeBilinear(facts, *combined);
  }
  result.elementwise = analyzeElementwise(facts);
  if (work.exhausted)
    return {};
  if (result.reduction || result.bilinear || result.elementwise)
    observed = {OptimizationOutcome::success(),
                view.occurrence,
                {},
                view.occurrencePath};
  return result;
}
namespace {
bool nativeVector(Type type, Type field) {
  auto vector = dyn_cast<algebra::FieldVectorType>(type);
  return vector && vector.getElementType() == field;
}
bool nativeMatrix(Type type, Type field) {
  auto matrix = dyn_cast<algebra::FieldMatrixType>(type);
  return matrix && matrix.getElementType() == field;
}
} // namespace
std::optional<NestedContraction>
matchNestedContraction(const ComputationView &structure) {
  ComputationWork work;
  return matchNestedContraction(structure, work);
}
std::optional<NestedContraction>
matchNestedContraction(const ComputationView &structure,
                       ComputationWork &remaining,
                       ComputationDiagnostic *diagnostic) {
  ComputationDiagnostic observed{
      {OptimizationStatus::Unsupported, OptimizationReason::Equation},
      structure.occurrence,
      {},
      structure.occurrencePath};
  auto report = llvm::scope_exit([&] {
    if (diagnostic)
      *diagnostic = observed;
  });
  EquationWork work{remaining, false, &observed};
  if (!work.take())
    return std::nullopt;
  if (!isa<local::FiniteCollectOp>(structure.computation.operation))
    return std::nullopt;
  NestedContraction selected;
  selected.outer = structure.computation;
  if (selected.outer.predicate || !isa<local::FuncOp>(selected.outer.helper))
    return std::nullopt;
  const auto *view = &structure;
  if (view->nested.size() != 1 || view->iteration.size() != 1 ||
      view->iteration[0].kind != finite::IterationKind::Indices)
    return std::nullopt;
  auto indices = dyn_cast<data::DomainIndicesOp>(view->iteration[0].operation);
  auto matrix = view->environment.inputPosition(indices.getInput());
  const auto &child = view->nested.front();
  ComputationDiagnostic childDiagnostic;
  auto equations = matchComputation(child, remaining, &childDiagnostic);
  if (!equations.reduction && !equations.bilinear && !equations.elementwise)
    observed = childDiagnostic;
  auto call = dyn_cast_or_null<local::ApplyOp>(child.occurrence);
  if (!matrix || !call || child.computation.collect ||
      child.computation.predicate || child.computation.states != 1 ||
      !isa<local::FiniteFoldOp>(child.computation.operation) ||
      !isa<local::FuncOp>(child.computation.helper) || !equations.reduction ||
      equations.reduction->inputs.size() != 2 ||
      !equations.reduction->matrixOperand ||
      !equations.reduction->selectedIndex)
    return std::nullopt;
  PayloadAnalysis outerPayload(view->payload, view->results, true, work, call);
  if (!outerPayload.supported ||
      outerPayload.transparent(view->result) != call->getResult(0))
    return std::nullopt;
  unsigned axis = indices.getAxis();
  if (axis > 1 || equations.reduction->matrixAccess !=
                      (axis ? AccessKind::MatrixColumn : AccessKind::MatrixRow))
    return std::nullopt;
  Type field = child.computation.signature.getResult(0);
  if (!isa<algebra::FieldType>(field) ||
      !nativeMatrix(selected.outer.signature.getInput(*matrix), field) ||
      !nativeVector(selected.outer.signature.getResult(0), field))
    return std::nullopt;
  auto mapInput = [&](unsigned input) -> std::optional<unsigned> {
    return view->environment.inputPosition(
        child.environment.actualInput(input));
  };
  auto innerMatrix = mapInput(
      equations.reduction->inputs[*equations.reduction->matrixOperand]);
  auto vector = mapInput(
      equations.reduction->inputs[1 - *equations.reduction->matrixOperand]);
  if (!innerMatrix || *innerMatrix != *matrix || !vector ||
      !nativeVector(selected.outer.signature.getInput(*vector), field) ||
      child.environment.actualInput(*equations.reduction->selectedIndex) !=
          view->items.front().formal)
    return std::nullopt;
  // Even unused descriptor inputs must have a direct environment mapping in
  // this bounded equation. More general uniform expressions keep the fallback.
  if (!work.take(child.computation.arguments + view->axes.size()))
    return std::nullopt;
  for (Value operand :
       call->getOperands().take_front(child.computation.arguments))
    if (!view->environment.inputPosition(operand) &&
        operand != view->items.front().formal)
      return std::nullopt;
  Value seed = child.seeds.front().actual;
  if (auto input = view->environment.inputPosition(seed)) {
    selected.seed.input = *input;
  } else {
    auto constant = finite::fieldConstant(seed.getDefiningOp());
    if (!constant || seed.getType() != field)
      return std::nullopt;
    selected.seed.constant = *constant;
  }
  // Reuse the inner reduction equation through the actual environment. Extra
  // scalar instructions may establish neutral identities; they must all be
  // live and total. Indexed accesses are outside this nested reader's slice.
  for (Operation *op : child.payload) {
    if (!work.take())
      return std::nullopt;
    auto *facet = finite::semantics(op);
    if (!facet || facet->access || !facet->law.total)
      return std::nullopt;
  }
  // This bounded composition supports strict zip, including ignored lanes and
  // unused zip constructors. Every constructor still contributes admission.
  auto &domain = child.computation.domain->getRegion(0).front();
  for (auto &op : domain.without_terminator()) {
    if (!work.take())
      return std::nullopt;
    if (isa<data::DomainZipOp>(op))
      continue;
    auto formal = child.environment.inputPosition(op.getOperand(0));
    if (!formal)
      return std::nullopt;
    auto mapped = mapInput(*formal);
    if (!mapped)
      return std::nullopt;
    if (isa<data::DomainElementsOp>(op)) {
      if (!nativeVector(selected.outer.signature.getInput(*mapped), field))
        return std::nullopt;
    } else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      auto index = child.environment.inputPosition(op.getOperand(1));
      if (*mapped != *matrix || !index ||
          child.environment.actualInput(*index) != view->items.front().formal ||
          isa<data::DomainMatrixColumnOp>(op) != bool(axis))
        return std::nullopt;
    } else
      return std::nullopt;
  }
  selected.witness = equations.reduction->witness;
  for (const auto &axis : view->axes)
    selected.witness.freeAxes.push_back(axis.identity);
  selected.inner = child.computation;
  selected.call = call.getOperation();
  selected.matrix = *matrix;
  selected.vector = *vector;
  selected.axis = axis;
  if (work.exhausted)
    return std::nullopt;
  observed = {OptimizationOutcome::success(),
              structure.occurrence,
              {},
              structure.occurrencePath};
  return selected;
}

} // namespace zkc::mathematical
