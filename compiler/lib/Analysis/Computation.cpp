#include "zkc/Analysis/Computation.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/IRMapping.h"
#include "zkc/Analysis/MathematicalFacts.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/ScopeExit.h"

using namespace mlir;
using namespace llvm;
namespace zkc::finite {
struct ComputationBody {
  OwningOpRef<mlir::ModuleOp> storage;
  func::FuncOp helper;
  llvm::DenseMap<Operation *, Operation *> sources;
  llvm::DenseMap<Value, Value> callbackValues;
  SmallVector<Operation *> numericalCalls;
};
Operation *ComputationView::sourceOperation(Operation *operation) const {
  if (numericalBody)
    if (auto *source = numericalBody->sources.lookup(operation))
      return source;
  return operation;
}
ArrayRef<Operation *> ComputationView::numericalCalls() const {
  return numericalBody ? ArrayRef<Operation *>(numericalBody->numericalCalls)
                       : ArrayRef<Operation *>();
}
Value ComputationView::callbackValue(Value source) const {
  return numericalBody ? numericalBody->callbackValues.lookup(source) : source;
}
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
// An invocation-local standard SSA view, not a normalizer. Call arguments and
// every returned coordinate are substituted exactly. In particular, dead
// arithmetic, pins and opaque Local control remain visible to recognition.
class NumericalBodyReader {
  ComputationBody &result;
  ComputationWork &work;
  ComputationDiagnostic &diagnostic;
  SymbolTableCollection symbols;
  llvm::DenseSet<Operation *> active;
  llvm::DenseMap<Operation *, runtime::BindingOp> bindings;
  OpBuilder builder;
  SymbolTable targetSymbols;
  const protocol::SourceExecutionClosure *scopedSource;
  bool charge(Operation *op) {
    return consumeComputationWork(
        work.structural, 1 + op->getNumOperands() + op->getNumResults(),
        WorkOwner::Structural, &diagnostic.outcome);
  }
  FailureOr<SmallVector<Value>> copy(Block &source, ValueRange arguments,
                                     Block &target, bool numerical) {
    if (auto function = dyn_cast<func::FuncOp>(source.getParentOp());
        function && protocol::isScopedExecutionFunction(function))
      return copyScoped(function, arguments, target);
    auto *owner = source.getParentOp();
    if (active.size() >= 64) {
      diagnostic.outcome = {OptimizationStatus::Unsupported,
                            OptimizationReason::Depth};
      return failure();
    }
    if (!active.insert(owner).second) {
      diagnostic.outcome = {OptimizationStatus::Unsupported,
                            OptimizationReason::Cycle};
      return failure();
    }
    auto leave = llvm::scope_exit([&] { active.erase(owner); });
    if (source.getNumArguments() != arguments.size() || !charge(owner))
      return failure();
    IRMapping values;
    for (auto [formal, actual] : zip(source.getArguments(), arguments)) {
      if (formal.getType() != actual.getType())
        return failure();
      values.map(formal, actual);
    }
    for (auto &op : source.without_terminator()) {
      if (!charge(&op))
        return failure();
      SmallVector<Value> inputs;
      for (Value operand : op.getOperands()) {
        Value actual = values.lookupOrNull(operand);
        if (!actual)
          return failure();
        inputs.push_back(actual);
      }
      func::FuncOp callee;
      if (auto call = dyn_cast<kernel::CallOp>(op)) {
        // Structural substitution does not choose a realization. Preserve each
        // original occurrence so selection can inspect its actual constraints.
        // The visit was charged above, including calls with no scalar output.
        result.numericalCalls.push_back(&op);
        callee = kernel::resolve(call, symbols);
      } else if (auto call = dyn_cast<func::CallOp>(op)) {
        callee = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
      }
      if (isa<kernel::CallOp, func::CallOp>(op)) {
        if (!callee || !callee.getBody().hasOneBlock() ||
            callee.front().empty())
          return failure();
        auto outputs = copy(callee.front(), inputs, target, true);
        if (failed(outputs) || outputs->size() != op.getNumResults())
          return failure();
        for (auto [expected, actual] : zip(op.getResultTypes(), *outputs))
          if (expected != actual.getType())
            return failure();
        values.map(op.getResults(), *outputs);
        continue;
      }
      // Keep opaque straight-line payloads intact. Region control cannot be
      // substituted by this bounded view and conservatively keeps fallback.
      // Nested finite invocations inside standard numerical helpers also need
      // their own call-occurrence axes; this scalar view does not flatten them.
      if (op.getNumRegions() || (numerical && isComputation(&op)))
        return failure();
      // Exact pack projection is descriptor substitution, not arithmetic
      // simplification. Keep every scalar producer and its occurrence order.
      if (auto projection = dyn_cast<algebra::ArrayAtOp>(op)) {
        auto pack =
            inputs.front().getDefiningOp<algebra::ArrayFromElementsOp>();
        auto coordinate = projection.getIndexAttr().getInt();
        if (pack && coordinate >= 0 &&
            uint64_t(coordinate) < pack.getNumOperands()) {
          values.map(projection.getResult(), pack.getOperand(coordinate));
          continue;
        }
      }
      builder.setInsertionPointToEnd(&target);
      auto *copy = builder.clone(op, values);
      result.sources[copy] = &op;
      if (auto reference = op.getAttrOfType<FlatSymbolRefAttr>("binding")) {
        auto binding =
            symbols.lookupNearestSymbolFrom<runtime::BindingOp>(&op, reference);
        if (!binding)
          return failure();
        auto &retained = bindings[binding];
        if (!retained) {
          if (!charge(binding))
            return failure();
          auto *declaration = binding->clone();
          targetSymbols.insert(declaration);
          retained = cast<runtime::BindingOp>(declaration);
        }
        copy->setAttr("binding",
                      FlatSymbolRefAttr::get(retained.getSymNameAttr()));
      }
    }
    auto &end = source.back();
    if (!charge(&end) ||
        (numerical ? !isa<func::ReturnOp>(end) : !isa<local::ReturnOp>(end)))
      return failure();
    SmallVector<Value> outputs;
    for (Value operand : end.getOperands()) {
      Value actual = values.lookupOrNull(operand);
      if (!actual)
        return failure();
      outputs.push_back(actual);
    }
    if (!numerical) {
      for (Value argument : source.getArguments())
        result.callbackValues[argument] = values.lookup(argument);
      for (auto &op : source.without_terminator())
        for (Value value : op.getResults())
          result.callbackValues[value] = values.lookup(value);
    }
    return outputs;
  }

  // This is optional recognition storage. Only laws with an explicit total
  // mathematical counterpart may cross the scoped boundary. Every source
  // operation is visited; an unused guard, pin or stop still declines it.
  FailureOr<SmallVector<Value>>
  copyScoped(func::FuncOp source, ValueRange arguments, Block &target) {
    if (!scopedSource || active.size() >= 64 || !active.insert(source).second)
      return failure();
    auto leave = llvm::scope_exit([&] { active.erase(source); });
    auto found = scopedSource->bodies.find(source.getSymName().str());
    if (found == scopedSource->bodies.end() || found->second.empty() ||
        source.getNumArguments() != arguments.size() + 1 || !charge(source))
      return failure();
    IRMapping values;
    for (auto [formal, actual] :
         zip(source.getArguments().drop_front(), arguments)) {
      if (formal.getType() != actual.getType())
        return failure();
      values.map(formal, actual);
    }
    for (const auto &step : found->second) {
      auto *op = step.operation;
      if (op->getParentOp() != source || !charge(op) || !step.regions.empty())
        return failure();
      SmallVector<Value> inputs;
      for (Value input : step.inputs) {
        auto actual = values.lookupOrNull(input);
        if (!actual)
          return failure();
        inputs.push_back(actual);
      }
      if (isa<exec::ReturnOp>(op)) {
        if (&step != &found->second.back())
          return failure();
        for (Block &block : source.getBody())
          for (Value value : block.getArguments())
            if (auto mapped = values.lookupOrNull(value))
              result.callbackValues[value] = mapped;
        return inputs;
      }
      func::FuncOp callee;
      if (auto call = dyn_cast<func::CallOp>(op))
        callee = symbols.lookupNearestSymbolFrom<func::FuncOp>(
            call, call.getCalleeAttr());
      else if (auto call = dyn_cast<exec::ComputeOp>(op)) {
        result.numericalCalls.push_back(op);
        callee = call.resolveCallee(symbols);
      }
      if (isa<func::CallOp, exec::ComputeOp>(op)) {
        if (!callee || callee.empty())
          return failure();
        auto outputs = copy(callee.front(), inputs, target, true);
        if (failed(outputs) || outputs->size() != step.outputs.size() ||
            ValueRange(*outputs).getTypes() !=
                ValueRange(step.outputs).getTypes())
          return failure();
        values.map(step.outputs, *outputs);
        continue;
      }
      if (isComputation(op)) {
        // An uninterpreted typed call retains the nested occurrence in this
        // private SSA view. Its source association, not its temporary symbol,
        // supplies the descriptor, callback and scoped execution contract.
        OpBuilder::InsertionGuard restore(builder);
        builder.setInsertionPointToEnd(result.storage->getBody());
        auto declaration = func::FuncOp::create(
            op->getLoc(), "_nested_computation",
            builder.getFunctionType(ValueRange(inputs).getTypes(),
                                    ValueRange(step.outputs).getTypes()));
        declaration.setPrivate();
        targetSymbols.insert(declaration);
        builder.setInsertionPointToEnd(&target);
        auto call =
            func::CallOp::create(builder, op->getLoc(), declaration, inputs);
        result.sources[call] = op;
        values.map(step.outputs, call.getResults());
        continue;
      }
      auto apply = dyn_cast<exec::ApplyOp>(op);
      if (!apply || step.outputs.size() != 1)
        return failure();
      auto binding = symbols.lookupNearestSymbolFrom<runtime::BindingOp>(
          apply, apply.getBindingAttr());
      auto decoded =
          binding ? protocol::readBinding(binding)
                  : llvm::Expected<protocol::OperationBinding>(
                        llvm::createStringError(llvm::inconvertibleErrorCode(),
                                                "missing source binding"));
      if (!decoded) {
        llvm::consumeError(decoded.takeError());
        return failure();
      }
      SmallVector<protocol::BoundType> inputTypes, outputTypes;
      for (auto [ports, types] :
           {std::pair{ValueRange(step.inputs), &inputTypes},
            std::pair{ValueRange(step.outputs), &outputTypes}})
        for (Type type : ports.getTypes()) {
          auto encoded = protocol::encodeBoundType(type, false);
          if (!encoded) {
            llvm::consumeError(encoded.takeError());
            return failure();
          }
          types->push_back(std::move(*encoded));
        }
      SmallVector<std::string> parameters;
      for (Attribute attr : apply.getParameters()) {
        auto text = dyn_cast<StringAttr>(attr);
        if (!text)
          return failure();
        parameters.push_back(text.getValue().str());
      }
      if (!protocol::admitMathematicalMeaning(decoded->application, inputTypes,
                                              outputTypes, parameters))
        return failure();
      StringRef contract = decoded->application.contract;
      StringRef name =
          contract == "field.constant"
              ? algebra::ConstantFieldOp::getOperationName()
          : contract == "field.add" ? algebra::FieldAddOp::getOperationName()
          : contract == "field.sub"
              ? algebra::SubtractFieldOp::getOperationName()
          : contract == "field.mul"
              ? algebra::FieldMultiplyOp::getOperationName()
          : contract == "curve.add" ? algebra::GroupAddOp::getOperationName()
          : contract == "curve.scale"
              ? algebra::GroupScaleOp::getOperationName()
          : contract == "vector.get" ? data::BoundedAtOp::getOperationName()
          : contract == "matrix.get"
              ? data::BoundedMatrixAtOp::getOperationName()
              : StringRef();
      if (name.empty() || (contract == "field.constant" ? parameters.size() != 1
                                                        : !parameters.empty()))
        return failure();
      builder.setInsertionPointToEnd(&target);
      OperationState state(op->getLoc(), name);
      state.addOperands(inputs);
      state.addTypes(ValueRange(step.outputs).getTypes());
      if (contract == "field.constant")
        state.addAttribute("value", builder.getStringAttr(parameters.front()));
      auto *projected = builder.create(state);
      result.sources[projected] = op;
      values.map(step.outputs, projected->getResults());
    }
    return failure();
  }

public:
  NumericalBodyReader(ComputationBody &result, ComputationWork &work,
                      ComputationDiagnostic &diagnostic,
                      const protocol::SourceExecutionClosure *source = nullptr)
      : result(result), work(work), diagnostic(diagnostic),
        builder(result.helper.getContext()), targetSymbols(*result.storage),
        scopedSource(source) {}
  LogicalResult read(func::FuncOp source) {
    auto *body = result.helper.addEntryBlock();
    auto outputs = copyScoped(source, body->getArguments(), *body);
    if (failed(outputs))
      return failure();
    builder.setInsertionPointToEnd(body);
    func::ReturnOp::create(builder, source.getLoc(), *outputs);
    return success();
  }
  LogicalResult read(local::FuncOp source) {
    auto *body = result.helper.addEntryBlock();
    auto outputs =
        copy(source.getBody().front(), body->getArguments(), *body, false);
    if (failed(outputs))
      return failure();
    builder.setInsertionPointToEnd(body);
    auto end = func::ReturnOp::create(builder, source.getLoc(), *outputs);
    result.sources[end] = &source.getBody().front().back();
    for (auto &op : llvm::make_early_inc_range(body->without_terminator())) {
      if (!charge(&op))
        return failure();
      if (!isa<algebra::ArrayFromElementsOp>(op) || !op.use_empty())
        continue;
      for (auto iterator = result.callbackValues.begin();
           iterator != result.callbackValues.end();) {
        if (!charge(&op))
          return failure();
        auto current = iterator++;
        if (current->second == op.getResult(0))
          result.callbackValues.erase(current);
      }
      result.sources.erase(&op);
      op.erase();
    }
    return success();
  }
};

std::shared_ptr<ComputationBody>
readNumericalBody(CallbackView &callback, ComputationWork &work,
                  ComputationDiagnostic &diagnostic,
                  const protocol::SourceExecutionClosure *source = nullptr) {
  // The original ABI has already been checked. This standard function is only
  // owned SSA storage; it does not change the partial callback's contract.
  auto *helper = callback.abi.symbol;
  bool scoped = bool(callback.abi.scope);
  if ((!isa<local::FuncOp>(helper) && !scoped) ||
      callback.exit != CallbackExit::Return)
    return {};
  auto result = std::make_shared<ComputationBody>();
  result->storage = mlir::ModuleOp::create(helper->getLoc());
  auto signature =
      scoped ? protocol::scopedDataSignature(cast<func::FuncOp>(helper))
             : callback.abi.signature;
  if (!signature)
    return {};
  result->helper = func::FuncOp::create(
      helper->getLoc(), SymbolTable::getSymbolName(helper).getValue(),
      signature);
  result->helper.setPrivate();
  if (auto premises = helper->getAttrOfType<ArrayAttr>("data.preconditions")) {
    SmallVector<Attribute> translated;
    for (Attribute premise : premises) {
      if (!consumeComputationWork(work.structural, 1, WorkOwner::Structural,
                                  &diagnostic.outcome))
        return {};
      if (!scoped)
        translated.push_back(premise);
      else if (auto bound = dyn_cast<data::IndexBoundAttr>(premise)) {
        if (!bound.getIndexArg() || !bound.getContainerArg())
          return {};
        translated.push_back(data::IndexBoundAttr::get(
            helper->getContext(), bound.getIndexArg() - 1,
            bound.getContainerArg() - 1, bound.getAxis()));
      } else if (auto equal = dyn_cast<data::EqualExtentAttr>(premise)) {
        if (!equal.getLeftArg() || !equal.getRightArg())
          return {};
        translated.push_back(data::EqualExtentAttr::get(
            helper->getContext(), equal.getLeftArg() - 1, equal.getLeftAxis(),
            equal.getRightArg() - 1, equal.getRightAxis()));
      } else
        return {};
    }
    result->helper->setAttr("data.preconditions",
                            ArrayAttr::get(helper->getContext(), translated));
  }
  result->storage->getBody()->push_back(result->helper);
  NumericalBodyReader reader(*result, work, diagnostic, source);
  if (failed(scoped ? reader.read(cast<func::FuncOp>(helper))
                    : reader.read(cast<local::FuncOp>(helper))))
    return {};
  auto &body = result->helper.front();
  auto *terminator = &body.back();
  ValueRange arguments = body.getArguments();
  if (arguments.size() + unsigned(scoped) !=
          callback.abi.entry->getNumArguments() ||
      !isa<func::ReturnOp>(terminator) ||
      terminator->getNumOperands() != callback.returned.size())
    return {};
  unsigned position = 0;
  for (ValueRange segment :
       {callback.abi.formals.state, callback.abi.formals.items,
        callback.abi.formals.domain, callback.abi.formals.captures})
    for (Value original : segment) {
      if (!consumeComputationWork(work.structural, 1, WorkOwner::Structural,
                                  &diagnostic.outcome))
        return {};
      auto formal = dyn_cast<BlockArgument>(original);
      if (!formal || formal.getOwner() != callback.abi.entry ||
          formal.getArgNumber() != position + unsigned(scoped) ||
          position >= arguments.size() ||
          original.getType() != arguments[position].getType() ||
          result->callbackValues.lookup(original) != arguments[position])
        return {};
      ++position;
    }
  if (position != arguments.size())
    return {};
  for (auto [original, substituted] :
       zip(callback.returned, terminator->getOperands())) {
    if (!consumeComputationWork(work.structural, 1, WorkOwner::Structural,
                                &diagnostic.outcome) ||
        original.getType() != substituted.getType() ||
        result->callbackValues.lookup(original) != substituted)
      return {};
  }
  // Preserve symbol/signature/role/exit as observations of the source callback.
  // Only body-relative references move to the checked positional SSA view.
  auto formals = callback.abi.formals;
  callback.abi.entry = &body;
  callback.abi.formals = {
      arguments.take_front(formals.state.size()),
      arguments.slice(formals.state.size(), formals.items.size()),
      arguments.slice(formals.state.size() + formals.items.size(),
                      formals.domain.size()),
      arguments.drop_front(formals.state.size() + formals.items.size() +
                           formals.domain.size())};
  callback.terminator = terminator;
  callback.returned = terminator->getOperands();
  return result;
}

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
  ComputationDiagnostic &diagnostic;
  const std::optional<CapacityCause> &evidenceDebit;
  mutable bool complete = true;
  SmallVector<Value> inputs;
  llvm::DenseMap<Value, unsigned> inputPositions, itemPositions;
  bool extentIteration;

  AccessAnalysis(ComputationView &view, bool aligned, ComputationWork &work,
                 MathematicalFactAnalysis &factAnalysis, facts::Work &evidence,
                 ComputationDiagnostic &diagnostic,
                 const std::optional<CapacityCause> &evidenceDebit)
      : view(view), work(work), factAnalysis(factAnalysis), evidence(evidence),
        diagnostic(diagnostic), evidenceDebit(evidenceDebit),
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
    OptimizationOutcome outcome;
    bool accepted = consumeComputationWork(work.structural, count,
                                           WorkOwner::Structural, &outcome);
    if (!accepted && complete)
      diagnostic = {outcome, view.occurrence, {}, view.occurrencePath};
    complete &= accepted;
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
  bool equalIterationExtent(Value access, unsigned input, unsigned axis) const {
    std::optional<ComputationDiagnostic> decline;
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
      if (*domain == input && factorAxis == axis)
        return true;
      auto status = factAnalysis.equalExtent(inputs[*domain], factorAxis,
                                             inputs[input], axis, evidence);
      if (status == facts::Status::Proven)
        return true;
      auto outcome = evidenceOutcome(status, OptimizationReason::EqualExtent);
      outcome.input = *domain;
      outcome.otherInput = input;
      outcome.axis = factorAxis;
      outcome.otherAxis = axis;
      // A later successful probe discharges this access. Preserve an actual
      // failed query only when no probe proves the required equality.
      if (!decline || status == facts::Status::Capacity)
        decline =
            ComputationDiagnostic{outcome, access.getDefiningOp(), access};
    }
    if (decline) {
      decline->occurrencePath = view.occurrencePath;
      view.accessDeclines.push_back(*decline);
    }
    return false;
  }
  OptimizationOutcome evidenceOutcome(facts::Status status,
                                      OptimizationReason reason) const {
    OptimizationOutcome result{OptimizationStatus::MissingEvidence, reason};
    if (status == facts::Status::Capacity) {
      result.status = OptimizationStatus::Capacity;
      result.capacity =
          evidenceDebit.value_or(CapacityCause{WorkOwner::Evidence, {}, {}});
    }
    return result;
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
        !equalIterationExtent(value, *container, axis))
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
      if (!result.selectedIndex)
        return std::nullopt;
      auto status = factAnalysis.bound(op->getOperand(selected),
                                       op->getOperand(0), 1 - axis, evidence);
      if (status != facts::Status::Proven) {
        auto outcome = evidenceOutcome(status, OptimizationReason::StrictBound);
        outcome.input = *container;
        outcome.otherInput = result.selectedIndex;
        outcome.axis = 1 - axis;
        view.accessDeclines.push_back(
            {outcome, op, value, view.occurrencePath});
        return std::nullopt;
      }
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
  std::optional<CapacityCause> evidenceDebit;
  facts::Work evidence;
  ComputationDiagnostic &diagnostic;
  Operation *subject = nullptr;
  SmallVector<Operation *> occurrencePath;
  bool charge(uint64_t amount = 1) {
    OptimizationOutcome outcome;
    if (consumeComputationWork(work.structural, amount, WorkOwner::Structural,
                               &outcome))
      return true;
    diagnostic = {outcome, subject, {}, occurrencePath};
    return false;
  }
  llvm::DenseSet<Operation *> active;
  SymbolTableCollection symbols;

public:
  ComputationAnalysis(ComputationWork &work, Operation *subject,
                      ComputationDiagnostic &diagnostic)
      : work(work), factAnalysis(MathematicalFactAnalysis::rootFor(subject)),
        evidence([this](uint64_t amount) {
          uint64_t available = this->work.evidence;
          if (consumeComputationWork(this->work.evidence, amount))
            return true;
          evidenceDebit = CapacityCause{WorkOwner::Evidence, amount, available};
          return false;
        }),
        diagnostic(diagnostic) {}
  std::optional<ComputationView>
  read(Computation c, Operation *occurrence,
       ArrayRef<Operation *> parentPath = {},
       const llvm::DenseMap<Value, Value> &enclosing =
           llvm::DenseMap<Value, Value>(),
       Operation *sourceOccurrence = nullptr) {
    if (!sourceOccurrence)
      sourceOccurrence = occurrence;
    Operation *previousSubject = subject;
    auto previousPath = std::move(occurrencePath);
    occurrencePath.assign(parentPath.begin(), parentPath.end());
    occurrencePath.push_back(sourceOccurrence);
    subject = sourceOccurrence;
    auto restore = llvm::scope_exit([&] {
      subject = previousSubject;
      occurrencePath = std::move(previousPath);
    });
    diagnostic = {
        {OptimizationStatus::Unsupported, OptimizationReason::Structure},
        occurrence,
        {},
        occurrencePath};
    if (active.size() >= 64) {
      diagnostic.outcome = {OptimizationStatus::Unsupported,
                            OptimizationReason::Depth};
      return std::nullopt;
    }
    if (!c.helper || c.helper->getNumRegions() != 1 ||
        (!c.scoped && !c.helper->getRegion(0).hasOneBlock()) ||
        !charge(1 + c.signature.getNumInputs() + c.signature.getNumResults() +
                c.helper->getRegion(0).front().getNumArguments()))
      return std::nullopt;
    auto role = c.collect ? CallbackRole::Body : CallbackRole::Step;
    FailureOr<CallbackView> callback = failure();
    if (c.scoped && c.scopedSource) {
      auto abi = readCallbackABI(c, role);
      auto found = c.scopedSource->bodies.find(
          SymbolTable::getSymbolName(c.helper).getValue().str());
      if (succeeded(abi) && found != c.scopedSource->bodies.end() &&
          !found->second.empty()) {
        auto *end = found->second.back().operation;
        if (isa<exec::ReturnOp>(end))
          callback =
              CallbackView{*abi, end, CallbackExit::Return, end->getOperands()};
      }
    } else
      callback = readCallback(c, role);
    if (failed(callback))
      return std::nullopt;
    SmallVector<Value> originalReturned(callback->returned);
    std::shared_ptr<ComputationBody> numericalBody;
    if (c.scoped) {
      numericalBody =
          readNumericalBody(*callback, work, diagnostic, c.scopedSource);
      if (!numericalBody)
        return std::nullopt;
    } else if (auto helper = dyn_cast<local::FuncOp>(c.helper)) {
      bool calls = false;
      for (auto &op : helper.getBody().front().without_terminator()) {
        if (!charge())
          return std::nullopt;
        calls |= isa<kernel::CallOp, func::CallOp>(op);
      }
      if (calls) {
        numericalBody = readNumericalBody(*callback, work, diagnostic);
        if (!numericalBody)
          return std::nullopt;
      }
    }
    auto &body = *callback->abi.entry;
    ComputationView result;
    result.computation = c;
    result.numericalBody = std::move(numericalBody);
    result.callbackBody = &body;
    result.occurrence = occurrence;
    result.terminator = callback->terminator;
    append_range(result.occurrencePath, parentPath);
    result.occurrencePath.push_back(sourceOccurrence);
    llvm::DenseMap<Value, unsigned> iterations;
    for (auto &op : c.domain.getBody().front().without_terminator()) {
      if (!charge(1 + op.getNumOperands()))
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
      if (!charge())
        return std::nullopt;
      auto pendingAxis = pending.pop_back_val();
      unsigned position = pendingAxis.iteration;
      const auto &iteration = result.iteration[position];
      if (iteration.kind == IterationKind::Zip ||
          iteration.kind == IterationKind::Product) {
        aligned &= iteration.kind != IterationKind::Product;
        for (unsigned child = iteration.children.size(); child; --child) {
          if (!charge(1 + pendingAxis.path.size()))
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
          if (!charge(1 + pendingAxis.path.size()) ||
              result.items.size() >= callback->abi.formals.items.size())
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
          result.items.push_back(
              {position, callback->abi.formals.items[result.items.size()],
               static_cast<unsigned>(result.axes.size())});
          result.axes.push_back(std::move(axis));
        }
      }
    }
    if (result.items.size() != callback->abi.formals.items.size())
      return std::nullopt;
    ValueRange actualOperands =
        occurrence ? occurrence->getOperands() : ValueRange{};
    ValueRange actualResults =
        occurrence ? occurrence->getResults() : ValueRange{};
    if (c.scoped && occurrence == sourceOccurrence) {
      auto function = occurrence
                          ? dyn_cast<func::FuncOp>(occurrence->getParentOp())
                          : func::FuncOp();
      if (!function || !c.scopedSource)
        return std::nullopt;
      auto found = c.scopedSource->bodies.find(function.getSymName().str());
      if (found == c.scopedSource->bodies.end())
        return std::nullopt;
      const protocol::SourceExecutionStep *invocation = nullptr;
      for (const auto &step : found->second) {
        if (!charge())
          return std::nullopt;
        if (step.operation == occurrence) {
          invocation = &step;
          break;
        }
      }
      if (!invocation)
        return std::nullopt;
      actualOperands = invocation->inputs;
      actualResults = invocation->outputs;
    }
    auto actual = [&](unsigned input) -> Value {
      return input < actualOperands.size() ? actualOperands[input] : Value();
    };
    // Reorder checked callback formals into the entry ABI. Positions remain
    // distinct even when an occurrence passes one actual more than once.
    SmallVector<Value> entryFormals;
    append_range(entryFormals, callback->abi.formals.domain);
    append_range(entryFormals, callback->abi.formals.state);
    append_range(entryFormals, callback->abi.formals.captures);
    auto entry = partitionEntry(c, entryFormals);
    if (failed(entry) || (occurrence && !isDeclaration(occurrence) &&
                          failed(partitionEntry(c, actualOperands))))
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
      if (!active.insert(callback).second) {
        diagnostic.outcome = {OptimizationStatus::Unsupported,
                              OptimizationReason::Cycle};
        return false;
      }
      auto release = llvm::scope_exit([&] { active.erase(callback); });
      for (auto &op : block.without_terminator()) {
        if (!charge(1 + op.getNumOperands()))
          return false;
        payload.push_back(&op);
        Operation *source = result.sourceOperation(&op);
        Operation *definition = source;
        if (!isComputation(source) && isa<local::ApplyOp, func::CallOp>(op)) {
          auto reference = op.getAttrOfType<FlatSymbolRefAttr>("callee");
          definition = reference
                           ? symbols.lookupNearestSymbolFrom(source, reference)
                           : nullptr;
        }
        if (!definition || !isComputation(definition))
          continue;
        Computation child;
        if (failed(describe(definition, child, nullptr, &symbols)))
          return false;
        child.scopedSource = c.scopedSource;
        child.fixedBindings = c.fixedBindings;
        auto nested =
            read(child, &op, result.occurrencePath, environment, source);
        if (!nested)
          return false;
        result.nested.push_back(std::move(*nested));
        diagnostic = {
            {OptimizationStatus::Unsupported, OptimizationReason::Structure},
            occurrence,
            {},
            occurrencePath};
      }
      return true;
    };
    if (c.predicate) {
      if (!charge(1 + callback->abi.signature.getNumInputs()))
        return std::nullopt;
      auto predicate = readCallback(c, CallbackRole::Predicate);
      if (failed(predicate))
        return std::nullopt;
      auto environment =
          bindCallback(predicate->abi, {{},
                                        callback->abi.formals.items,
                                        callback->abi.formals.domain,
                                        callback->abi.formals.captures});
      if (failed(environment))
        return std::nullopt;
      result.predicateTerminator = predicate->terminator;
      llvm::DenseMap<Value, Value> predicateBindings;
      for (auto [formal, source] :
           zip(predicate->abi.entry->getArguments(), environment->actuals)) {
        result.predicateArguments.push_back({formal, source});
        Value resolved = bindings.lookup(source);
        predicateBindings[formal] = resolved ? resolved : source;
      }
      if (!readPayload(*predicate->abi.entry, result.predicatePayload,
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
           i < actualResults.size() ? actualResults[i] : Value(),
           !c.collect && i < result.seeds.size() ? result.seeds[i].actual
                                                 : Value(),
           !c.collect ? std::optional<unsigned>(result.seeds[i].input)
                      : std::nullopt,
           c.signature.getResult(i),
           c.collect && !c.predicate ? std::optional<unsigned>(result.root)
                                     : std::nullopt,
           originalReturned[i]});
    if (result.results.size() == 1)
      result.result = result.results.front();
    AccessAnalysis accesses(result, aligned, work, factAnalysis, evidence,
                            diagnostic, evidenceDebit);
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
std::optional<ComputationView>
analyzeComputation(Computation c, ComputationWork &work,
                   ComputationDiagnostic *diagnostic) {
  ComputationDiagnostic observed;
  auto result =
      ComputationAnalysis(work, c.operation, observed).read(c, c.operation);
  if (result)
    observed = {OptimizationOutcome::success(),
                c.operation,
                {},
                result->occurrencePath};
  else {
    // Failed temporary views have already been destroyed. Preserve the refusal
    // and its debit without exporting references into their transient SSA.
    observed.subject = c.operation;
    observed.access = {};
  }
  if (diagnostic)
    *diagnostic = observed;
  return result;
}
} // namespace zkc::finite
