#include "zkc/Analysis/Computation.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"

using namespace mlir;
using namespace llvm;
namespace zkc::finite {
std::optional<unsigned>
ComputationEnvironment::inputPosition(Value formal) const {
  if (!formal)
    return std::nullopt;
  for (const auto &input : inputs)
    if (input.formal == formal || input.domainFormal == formal)
      return input.input;
  return std::nullopt;
}
Value ComputationEnvironment::actualInput(unsigned input) const {
  return input < inputs.size() ? inputs[input].actual : Value();
}
Value ComputationEnvironment::resolveCapture(Value value) const {
  auto position = inputPosition(value);
  if (!position || inputs[*position].state)
    return value;
  const auto &input = inputs[*position];
  return input.resolved ? input.resolved : input.formal;
}
namespace {
Value domainResult(Computation c) {
  return c.domain.getBody().front().back().getOperand(0);
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
struct AccessAnalysis {
  ComputationView &view;
  ComputationWork &work;
  MathematicalFactAnalysis &factAnalysis;
  facts::Work &evidence;
  mutable bool complete = true;
  SmallVector<Value> inputs;
  llvm::DenseMap<Value, unsigned> inputPositions, itemPositions;
  bool extentIteration;

  AccessAnalysis(ComputationView &view, bool aligned, ComputationWork &work,
                 MathematicalFactAnalysis &factAnalysis, facts::Work &evidence)
      : view(view), work(work), factAnalysis(factAnalysis), evidence(evidence),
        inputs(view.computation.signature.getNumInputs()),
        extentIteration(
            aligned && llvm::all_of(view.items, [&](const auto &item) {
              return hasExtent(view.iteration[item.iteration].operation);
            })) {
    if (!charge(inputs.size() + view.captures.size() + 2 * view.items.size() +
                view.payload.size()))
      return;
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
      auto *facet = semantics(op);
      if (!facet || !facet->access)
        continue;
      if (auto access = readAccess(op->getResult(0)))
        addAccess(*access);
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

private:
  bool charge(uint64_t count = 1) const {
    complete &= consumeComputationWork(work.structural, count);
    return complete;
  }
  void addAccess(Access access) {
    access.container = inputs[access.input];
    access.axes.push_back(view.items[access.item].axis);
    if (access.columnItem)
      access.axes.push_back(view.items[*access.columnItem].axis);
    if (auto *facet = semantics(access.operation); facet && facet->access)
      append_range(access.indices,
                   access.operation->getOperands().drop_front());
    else if (access.selectedIndex)
      access.indices.push_back(inputs[*access.selectedIndex]);
    view.accesses.push_back(std::move(access));
  }
  // A flat zip admits equal cardinalities before traversal. Only helper
  // premises and source-domain identity are shared with the independent reader;
  // facts known solely on a total operation's actual operands are insufficient.
  bool equalIterationExtent(unsigned input, unsigned axis) const {
    for (const auto &item : view.items) {
      if (!charge())
        return false;
      auto *factor = view.iteration[item.iteration].operation;
      if (!hasExtent(factor))
        continue;
      auto domain = view.environment.inputPosition(factor->getOperand(0));
      if (!domain)
        continue;
      auto factorAxis = extentAxis(factor);
      if ((*domain == input && factorAxis == axis) ||
          factAnalysis.equalExtent(inputs[*domain], factorAxis, inputs[input],
                                   axis, evidence) == facts::Status::Proven)
        return true;
    }
    return false;
  }
  std::optional<Access> readAccess(Value value) const {
    if (auto position = item(value)) {
      auto *leaf = factor(*position);
      if (!isa<data::DomainElementsOp, data::DomainMatrixRowOp,
               data::DomainMatrixColumnOp>(leaf))
        return std::nullopt;
      auto input = view.environment.inputPosition(leaf->getOperand(0));
      if (!input)
        return std::nullopt;
      Access result{AccessKind::Element,
                    *input,
                    *position,
                    std::nullopt,
                    value,
                    leaf,
                    std::nullopt,
                    {},
                    {},
                    {}};
      if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(leaf)) {
        result.kind = isa<data::DomainMatrixRowOp>(leaf)
                          ? AccessKind::MatrixRow
                          : AccessKind::MatrixColumn;
        result.selectedIndex =
            view.environment.inputPosition(leaf->getOperand(1));
        if (!result.selectedIndex)
          return std::nullopt;
      }
      return result;
    }
    auto *op = value.getDefiningOp();
    auto *facet = semantics(op);
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
        for (auto [position, axis] :
             {std::pair{*row, 0u}, std::pair{*column, 1u}}) {
          auto indices = dyn_cast<data::DomainIndicesOp>(factor(position));
          if (!indices || indices.getAxis() != axis ||
              view.environment.inputPosition(indices.getInput()) != container)
            return std::nullopt;
        }
        return Access{AccessKind::MatrixCell,
                      *container,
                      *row,
                      std::nullopt,
                      value,
                      op,
                      *column,
                      {},
                      {},
                      {}};
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
    Access result{AccessKind::Indexed,
                  *container,
                  *position,
                  std::nullopt,
                  value,
                  op,
                  std::nullopt,
                  {},
                  {},
                  {}};
    if (selected) {
      result.kind =
          varying == 2 ? AccessKind::MatrixRow : AccessKind::MatrixColumn;
      result.selectedIndex = input(op->getOperand(selected));
      // Indexed access runs only on nonempty iterations. A bound is required
      // before introducing eager selected-row/column admission.
      if (!result.selectedIndex ||
          factAnalysis.bound(op->getOperand(selected), op->getOperand(0),
                             1 - axis, evidence) != facts::Status::Proven)
        return std::nullopt;
    }
    return result;
  }
};
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
  ComputationWork &work;
  MathematicalFactAnalysis factAnalysis;
  facts::Work evidence;
  llvm::DenseSet<Operation *> active;
  SymbolTableCollection symbols;

public:
  ComputationAnalysis(ComputationWork &work, Operation *subject)
      : work(work), factAnalysis(MathematicalFactAnalysis::rootFor(subject)),
        evidence(work.evidence) {}
  std::optional<ComputationView>
  read(Computation c, Operation *occurrence,
       ArrayRef<Operation *> parentPath = {},
       const llvm::DenseMap<Value, Value> &enclosing =
           llvm::DenseMap<Value, Value>()) {
    if (!c.helper || active.size() >= 64 || c.helper->getNumRegions() != 1 ||
        !c.helper->getRegion(0).hasOneBlock() ||
        !consumeComputationWork(
            work.structural,
            1 + c.signature.getNumInputs() + c.signature.getNumResults() +
                c.helper->getRegion(0).front().getNumArguments()))
      return std::nullopt;
    auto callback =
        readCallback(c, c.collect ? CallbackRole::Body : CallbackRole::Step);
    if (failed(callback))
      return std::nullopt;
    auto &body = *callback->body;
    ComputationView result;
    result.computation = c;
    result.occurrence = occurrence;
    result.terminator = callback->terminator;
    append_range(result.occurrencePath, parentPath);
    result.occurrencePath.push_back(occurrence);
    llvm::DenseMap<Value, unsigned> iterations;
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      if (!consumeComputationWork(work.structural, 1 + op.getNumOperands()))
        return std::nullopt;
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
    bool aligned = true;
    struct PendingAxis {
      unsigned iteration;
      SmallVector<unsigned> path;
    };
    SmallVector<PendingAxis> pending{{result.root, {}}};
    while (!pending.empty()) {
      if (!consumeComputationWork(work.structural))
        return std::nullopt;
      auto pendingAxis = pending.pop_back_val();
      unsigned position = pendingAxis.iteration;
      const auto &iteration = result.iteration[position];
      if (iteration.kind == IterationKind::Zip ||
          iteration.kind == IterationKind::Product) {
        aligned &= iteration.kind != IterationKind::Product;
        for (unsigned child = iteration.children.size(); child; --child) {
          if (!consumeComputationWork(work.structural,
                                      1 + pendingAxis.path.size()))
            return std::nullopt;
          auto path = pendingAxis.path;
          path.push_back(child - 1);
          pending.push_back({iteration.children[child - 1], std::move(path)});
        }
      } else {
        unsigned count = cast<data::DomainType>(iteration.descriptor.getType())
                             .getItemTypes()
                             .size();
        for (unsigned i = 0; i < count; ++i) {
          if (!consumeComputationWork(work.structural,
                                      1 + pendingAxis.path.size()) ||
              result.items.size() >= callback->formals.items.size())
            return std::nullopt;
          Axis axis;
          axis.identity = {result.occurrencePath, iteration.operation,
                           pendingAxis.path, i};
          if (hasExtent(iteration.operation) ||
              iteration.kind == IterationKind::Coordinates) {
            axis.container = iteration.operation->getOperand(0);
            axis.containerAxis = iteration.kind == IterationKind::Coordinates
                                     ? i
                                     : extentAxis(iteration.operation);
          }
          result.items.push_back({position,
                                  callback->formals.items[result.items.size()],
                                  static_cast<unsigned>(result.axes.size())});
          result.axes.push_back(std::move(axis));
        }
      }
    }
    if (result.items.size() != callback->formals.items.size())
      return std::nullopt;
    auto actual = [&](unsigned input) -> Value {
      return occurrence && input < occurrence->getNumOperands()
                 ? occurrence->getOperand(input)
                 : Value();
    };
    // Reorder checked callback formals into the entry ABI. Positions remain
    // distinct even when an occurrence passes one actual more than once.
    SmallVector<Value> entryFormals;
    append_range(entryFormals, callback->formals.domain);
    append_range(entryFormals, callback->formals.state);
    append_range(entryFormals, callback->formals.captures);
    auto entry = partitionEntry(c, entryFormals);
    if (failed(entry) || (occurrence && !isDeclaration(occurrence) &&
                          failed(partitionEntry(c, occurrence->getOperands()))))
      return std::nullopt;
    for (auto [input, formal] : enumerate(entryFormals)) {
      bool state = input >= entry->domain.size() &&
                   input < entry->domain.size() + entry->initialState.size();
      Value operand = actual(input);
      Value resolved = enclosing.lookup(operand);
      InputReference binding{static_cast<unsigned>(input),
                             formal,
                             operand,
                             input < entry->domain.size()
                                 ? c.domain.getBody().front().getArgument(input)
                                 : Value(),
                             resolved ? resolved : operand,
                             state};
      result.environment.inputs.push_back(binding);
      (state ? result.seeds : result.captures).push_back(binding);
    }
    // Map invariant captures only. A step's state is a recurrence variable,
    // not an alias for its seed; an item is local to this iteration occurrence.
    llvm::DenseMap<Value, Value> bindings;
    for (const auto &capture : result.captures)
      bindings[capture.formal] =
          result.environment.resolveCapture(capture.formal);
    auto readPayload = [&](Block &block, SmallVectorImpl<Operation *> &payload,
                           const llvm::DenseMap<Value, Value> &environment) {
      // A helper is active only while its own callback is being traversed.
      // A predicate may invoke an acyclic fold that shares this step helper.
      Operation *callback = block.getParentOp();
      if (active.size() >= 64 || !active.insert(callback).second)
        return false;
      auto release = llvm::scope_exit([&] { active.erase(callback); });
      for (auto &op : block.without_terminator()) {
        if (!consumeComputationWork(work.structural, 1 + op.getNumOperands()))
          return false;
        payload.push_back(&op);
        Operation *definition = &op;
        if (isa<local::ApplyOp, func::CallOp>(op)) {
          auto reference = op.getAttrOfType<FlatSymbolRefAttr>("callee");
          definition = reference
                           ? symbols.lookupNearestSymbolFrom(&op, reference)
                           : nullptr;
        }
        if (!definition || !isComputation(definition))
          continue;
        Computation child;
        if (failed(describe(definition, child, nullptr, &symbols)))
          return false;
        auto nested = read(child, &op, result.occurrencePath, environment);
        if (!nested)
          return false;
        result.nested.push_back(std::move(*nested));
      }
      return true;
    };
    if (c.predicate) {
      if (!consumeComputationWork(work.structural,
                                  1 + callback->signature.getNumInputs()))
        return std::nullopt;
      auto predicate = readCallback(c, CallbackRole::Predicate);
      if (failed(predicate))
        return std::nullopt;
      auto environment = bindCallback(*predicate, {{},
                                                   callback->formals.items,
                                                   callback->formals.domain,
                                                   callback->formals.captures});
      if (failed(environment))
        return std::nullopt;
      result.predicateTerminator = predicate->terminator;
      llvm::DenseMap<Value, Value> predicateBindings;
      for (auto [formal, source] :
           zip(predicate->body->getArguments(), environment->actuals)) {
        result.predicateArguments.push_back({formal, source});
        Value resolved = bindings.lookup(source);
        predicateBindings[formal] = resolved ? resolved : source;
      }
      if (!readPayload(*predicate->body, result.predicatePayload,
                       predicateBindings))
        return std::nullopt;
      append_range(result.predicateResults, predicate->returned);
    }
    if (!readPayload(body, result.payload, bindings))
      return std::nullopt;
    append_range(result.results, callback->returned);
    for (auto [i, yielded] : enumerate(result.results))
      result.resultMappings.push_back(
          {static_cast<unsigned>(i), yielded,
           occurrence && i < occurrence->getNumResults()
               ? occurrence->getResult(i)
               : Value(),
           !c.collect && i < result.seeds.size() ? result.seeds[i].actual
                                                 : Value(),
           !c.collect ? std::optional<unsigned>(result.seeds[i].input)
                      : std::nullopt,
           c.signature.getResult(i),
           c.collect && !c.predicate ? std::optional<unsigned>(result.root)
                                     : std::nullopt});
    if (result.results.size() == 1)
      result.result = result.results.front();
    AccessAnalysis accesses(result, aligned, work, factAnalysis, evidence);
    if (!accesses.complete)
      return std::nullopt;
    return result;
  }
};
} // namespace
std::optional<ComputationView> analyzeComputation(Computation c,
                                                  unsigned budget) {
  ComputationWork work;
  work.structural = budget;
  return analyzeComputation(c, work);
}
std::optional<ComputationView> analyzeComputation(Computation c,
                                                  ComputationWork &work) {
  return ComputationAnalysis(work, c.operation).read(c, c.operation);
}
} // namespace zkc::finite
