#include "CollectFold.h"
#include "CollectionRealization.h"
#include "ComputationSelection.h"
#include "FinitePreparation.h"
#include "FiniteVerification.h"
#include "HelperNormalization.h"
#include "LaneRealization.h"
#include "MathematicalSupport.h"
#include "NumericalSelection.h"
#include "RealizationEmission.h"
#include "RealizationTrace.h"
#include "ScopedFinite.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Analysis/Computation.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "zkc/Transforms/Finite.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include <algorithm>
#include <limits>
using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
mathematical::RealizationChoice
observedChoice(mathematical::RealizationKind kind) {
  using Kind = mathematical::RealizationKind;
  using Choice = mathematical::RealizationChoice;
  switch (kind) {
  case Kind::Ordered:
    return Choice::Ordered;
  case Kind::Bilinear:
    return Choice::Bilinear;
  case Kind::NestedContraction:
    return Choice::NestedContraction;
  case Kind::CollectionSum:
    return Choice::MapSum;
  case Kind::Reduction:
  case Kind::PointwiseReduction:
    return Choice::Reduction;
  case Kind::Elementwise:
    return Choice::Elementwise;
  }
  llvm_unreachable("unknown finite realization");
}
// This is a producer-only selection view. The original callback remains the
// source for ordered emission and for the independent actual-payload reader.
OwningOpRef<ModuleOp> normalizeSelectionCallback(Computation &computation,
                                                 Operation *root,
                                                 uint64_t &structural,
                                                 OptimizationOutcome &outcome) {
  auto size = sizeCallbackPreparation(computation, root, structural, outcome);
  if (!size)
    return {};
  if (size->work > structural) {
    // This predicts insufficient room without spending unperformed copying.
    // A saturated estimate is a lower bound, not an exact failed debit.
    outcome = {OptimizationStatus::Capacity, OptimizationReason::ExpansionSize,
               CapacityCause{WorkOwner::Structural,
                             size->work > callbackStructuralLimit
                                 ? std::nullopt
                                 : std::optional<uint64_t>(size->work),
                             structural}};
    return {};
  }
  // The helper APIs also require operation/slot counters. Bound these adapters
  // by the same remaining optional work; every copy debits the callback view,
  // which settles into the shared counter when its scope ends. Neither another
  // callback nor a retry can refill it.
  unsigned operations = static_cast<unsigned>(
      std::min<uint64_t>(structural, std::numeric_limits<unsigned>::max()));
  uint64_t slots = structural;
  OwningOpRef<func::FuncOp> scratch;
  {
    // Required helper expansion diagnoses failure. Here failure only declines
    // an optional proposal; the untouched ordered path owns any real refusal.
    ScopedDiagnosticHandler quiet(root->getContext(),
                                  [](Diagnostic &) { return success(); });
    if (succeeded(mathematical::chargeHelperOperations(
            computation.helper, operations, slots, &structural, &outcome))) {
      scratch = cast<func::FuncOp>(computation.helper->clone());
      SymbolTableCollection symbols;
      if (failed(mathematical::inlineHelpers(*scratch, operations, slots,
                                             symbols, root, &structural,
                                             &outcome)))
        scratch = {};
    }
  }
  if (!scratch) {
    if (outcome.capacity) {
      auto &capacity = *outcome.capacity;
      if (capacity.owner == WorkOwner::HelperSlots && capacity.requested)
        ++*capacity.requested; // Structural work also charges the operation.
      capacity.owner = WorkOwner::Structural;
      capacity.available = structural;
    }
    return {};
  }
  // The private scope below does not clone nested finite symbol closures. Keep
  // such payloads ordered, including dead nested computations: erasing one
  // would erase its conditional domain admission. Indexed accesses may use
  // the callback's original premises: the independent reader retains that
  // exact argument environment while interpreting the original helper calls.
  for (auto &op :
       llvm::make_early_inc_range(scratch->front().without_terminator())) {
    if (!consumeComputationWork(structural, 1, WorkOwner::Structural, &outcome))
      return {};
    if (isComputation(&op)) {
      outcome = {OptimizationStatus::Unsupported,
                 OptimizationReason::ImplementationRestriction};
      return {};
    }
  }
  if (size->arrayProjections && failed(mathematical::foldArrayProjections(
                                    scratch->front(), structural, &outcome)))
    return {};
  // Facts only admit premises inside the occurrence's symbol root. Retain the
  // helper's own signature/preconditions in a private symbol scope together
  // with a typed occurrence. Fresh entry formals deliberately carry no
  // caller-only extent assumptions. The domain view still borrows the original
  // domain SSA, which admission and the emitter use as their shared identity.
  auto signature = computation.signature;
  if (!consumeComputationWork(structural,
                              4 + 2 * signature.getNumInputs() +
                                  2 * signature.getNumResults(),
                              WorkOwner::Structural, &outcome))
    return {};
  OwningOpRef<ModuleOp> context(ModuleOp::create(root->getLoc()));
  auto helper = scratch.release();
  context->getBody()->push_back(helper);
  OpBuilder builder(context->getBody(), context->getBody()->end());
  auto subject = func::FuncOp::create(
      builder, computation.operation->getLoc(),
      (helper.getSymName() + "_selection").str(), signature);
  subject.setPrivate();
  builder.setInsertionPointToEnd(subject.addEntryBlock());
  auto *occurrence = builder.clone(*computation.operation);
  occurrence->setOperands(subject.getArguments());
  func::ReturnOp::create(builder, occurrence->getLoc(),
                         occurrence->getResults());
  computation.helper = helper;
  computation.operation = occurrence;
  return context;
}
class Realizer {
  Operation *unit;
  Operation *sourceRoot = nullptr;
  const protocol::SourceExecutionClosure *sourceClosure;
  const llvm::DenseSet<Operation *> *fixedBindings;
  OpBuilder &builder;
  SymbolTableCollection symbols;
  Location loc;
  Type index, boolean;
  mathematical::RealizationEmitter emitter;
  unsigned occurrence = 0;
  std::optional<protocol::Assignments> admissionPath;
  unsigned admissionOccurrence = 0;
  llvm::DenseMap<Value, Value> values, sizes, lowers;
  Computation computation;
  const CollectFold *composition = nullptr;
  SmallVector<Value> consumerEnvironment;
  Value substitutedElement, substitutedPosition;
  mathematical::RealizationWork &work;
  const mathematical::MathematicalRecipes &recipes;
  mathematical::RealizationScope *observation;
  bool retryOrdered;
  NumericalExpressionMode expressionMode;
  bool failedHelper = false;
  ScopedCallbackEmitter scopedCallback;
  TotalRecipeEmitter totalCallback;
  ScopedEmissionBudget *budget;
  StringRef scopedOccurrence;
  bool stoppedCallback = false;
  enum class ControlKind { Loop, Branch };
  struct Control {
    SmallVector<Value> outputs;
    SmallVector<func::FuncOp> bodies;
    OpBuilder::InsertPoint continuation;
  };
  llvm::DenseMap<Operation *, unsigned> regionReturns;
  llvm::DenseMap<Operation *, std::unique_ptr<exec::ScopedExecutionBuilder>>
      controls;
  exec::ScopedExecutionBuilder &entryControl;
  func::FuncOp scopedEntry;
  func::FuncOp function() {
    return cast<func::FuncOp>(builder.getInsertionBlock()->getParentOp());
  }
  exec::ScopedExecutionBuilder &scopeControl() {
    auto current = function();
    if (current == scopedEntry)
      return entryControl;
    auto &control = controls[current];
    if (!control)
      control = std::make_unique<exec::ScopedExecutionBuilder>(
          builder, current, entryControl.getLoopForm());
    return *control;
  }
  std::string sitePrefix = "finite_";
  bool reserve(uint64_t amount) {
    if (failedHelper)
      return false;
    if (!budget)
      return true;
    if (amount > budget->work) {
      budget->capacity =
          CapacityCause{WorkOwner::AlgorithmExpansion, amount, budget->work};
      failedHelper = true;
      return false;
    }
    budget->work -= amount;
    return true;
  }
  std::string site() {
    auto suffix = std::to_string(occurrence++);
    auto size = sitePrefix.size() + suffix.size();
    if (size > 128) {
      uint64_t standaloneBytes = 16 * 1024 * 1024;
      auto &bytes = budget ? budget->siteBytes : standaloneBytes;
      auto encoded = protocol::algorithmSite({}, sitePrefix + suffix, bytes);
      if (!encoded) {
        llvm::consumeError(encoded.takeError());
        if (budget)
          budget->capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes};
        failedHelper = true;
        return {};
      }
      return std::move(*encoded);
    }
    if (budget) {
      if (size > budget->siteBytes) {
        budget->capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes, size,
                                         budget->siteBytes};
        failedHelper = true;
        return {};
      }
      budget->siteBytes -= size;
    }
    return sitePrefix + suffix;
  }
  Value emit(const protocol::BindingApplication &application, ValueRange inputs,
             Type output, ArrayRef<Attribute> params = {},
             StringRef explicitSite = {}) {
    // A fixed envelope covers the invoke/dispatch/success block, binding and
    // operands. Debit before creating any CFG or declaration. Callback copies
    // and nested traversal spend the same enclosing transaction account.
    if (!reserve(32 + 8 * (inputs.size() + bool(output) + params.size() +
                           application.arguments.size())) ||
        llvm::any_of(inputs, [](Value value) { return !value; })) {
      failedHelper = true;
      return {};
    }
    std::string occurrence;
    if (admissionPath && application.contract == "control.require") {
      ++this->occurrence;
      uint64_t standaloneBytes = 16 * 1024 * 1024;
      auto &bytes = budget ? budget->siteBytes : standaloneBytes;
      auto encoded = protocol::algorithmSite(
          *admissionPath, "finite_" + std::to_string(admissionOccurrence),
          bytes);
      if (!encoded) {
        llvm::consumeError(encoded.takeError());
        if (budget)
          budget->capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes};
        failedHelper = true;
        return {};
      }
      occurrence = std::move(*encoded);
    } else
      occurrence = explicitSite.empty() ? site() : explicitSite.str();
    if (admissionPath)
      ++admissionOccurrence;
    if (failedHelper)
      return {};
    SmallVector<Type> outputs;
    if (output)
      outputs.push_back(output);

    auto reference = emitter.binding(builder, loc, application);
    auto &control = scopeControl();
    auto previousLocation = control.getLocation();
    control.setLocation(loc);
    auto restoreLocation =
        llvm::scope_exit([&] { control.setLocation(previousLocation); });
    auto values = control.invoke(
        "exec.apply", outputs, control.scoped(inputs),
        {builder.getNamedAttr("binding", reference),
         builder.getNamedAttr("site", builder.getStringAttr(occurrence)),
         builder.getNamedAttr("parameters", builder.getArrayAttr(params))});
    return output ? values.front() : Value();
  }
  Value emit(StringRef contract, ValueRange inputs, Type output,
             ArrayRef<std::string> args = {}, ArrayRef<Attribute> params = {}) {
    return emit({contract.str(), {args.begin(), args.end()}, ""}, inputs,
                output, params);
  }
  Value number(uint64_t n) {
    return emit("index.constant", {}, index, {},
                {builder.getIntegerAttr(index, n)});
  }
  Value length(Value input, unsigned axis = 0) {
    if (failedHelper || !input)
      return {};
    auto col = mathematical::collectionRealization(input.getType());
    assert(col && axis < col->rank && "admitted collection axis required");
    if (col->staticExtent)
      return number(*col->staticExtent);
    return emit(*col->length, input, index,
                col->rank == 2
                    ? ArrayRef<Attribute>{builder.getIntegerAttr(index, axis)}
                    : ArrayRef<Attribute>{});
  }
  void require(Value condition) { emit("control.require", condition, {}, {}); }
  Control control(ControlKind kind, ValueRange inputs, TypeRange outputs,
                  unsigned regions) {
    if (!reserve(64 + 16 * (inputs.size() + outputs.size() + regions)) ||
        llvm::any_of(inputs, [](Value value) { return !value; })) {
      failedHelper = true;
      return {};
    }
    auto occurrence = site();
    if (failedHelper)
      return {};

    Control result;
    bool loop = kind == ControlKind::Loop;
    unsigned prefix = loop ? 2 + outputs.size() : 1;
    auto captures = inputs.drop_front(prefix);
    auto parent = function().getSymName();
    if (!reserve(parent.size() + occurrence.size()))
      return {};
    // Names identify actual control occurrences, not allocation order. A
    // different finite recipe must not renumber unrelated numerical calls.
    // This bounded private spelling has no semantic or proof authority.
    auto coordinate = (Twine(parent.size()) + ":" + parent + occurrence).str();
    auto stem = "_finite_region_" +
                toHex(SHA256::hash(arrayRefFromStringRef(coordinate)), true);
    auto outline = [&](unsigned arm) {
      OpBuilder::InsertionGuard restore(builder);
      builder.setInsertionPointToEnd(&unit->getRegion(0).front());
      SmallVector<Type> arguments{
          runtime::ScopeType::get(builder.getContext())};
      if (loop) {
        arguments.push_back(index);
        append_range(arguments, outputs);
      }
      append_range(arguments, captures.getTypes());
      auto base = stem + "_" + std::to_string(arm);
      std::string name = base;
      unsigned collision = 0;
      while (SymbolTable::lookupSymbolIn(unit, name) ||
             SymbolTable::lookupSymbolIn(sourceRoot, name))
        name = base + "_" + std::to_string(collision++);
      auto body = func::FuncOp::create(
          builder, loc, name,
          builder.getFunctionType(
              arguments, {exec::OutcomeType::get(builder.getContext(),
                                                 SmallVector<Type>(outputs))}));
      body.setPrivate();
      body.setNoInline(true);
      body->setAttr("runtime.region", builder.getUnitAttr());
      builder.createBlock(&body.getBody(), body.getBody().end(), arguments,
                          SmallVector<Location>(arguments.size(), loc));
      regionReturns[body] = outputs.size();
      result.bodies.push_back(body);
      return body;
    };
    auto &control = scopeControl();
    result.outputs =
        loop ? control.loop(inputs[0], inputs[1],
                            inputs.slice(2, outputs.size()), captures, outputs,
                            false, occurrence, outline)
             : control.conditional(inputs[0], captures, outputs, occurrence,
                                   outline);
    result.continuation = builder.saveInsertionPoint();
    return result;
  }
  SmallVector<Value> region(Control &control, unsigned i, TypeRange types) {
    if (failedHelper)
      return {};

    auto body = control.bodies[i];
    if (!llvm::equal(body.getArgumentTypes().drop_front(), types)) {
      failedHelper = true;
      return {};
    }
    builder.setInsertionPointToEnd(&body.front());
    stoppedCallback = false;
    return SmallVector<Value>(body.getArguments().drop_front());
  }
  void resume(const Control &control) {
    if (failedHelper)
      return;

    builder.restoreInsertionPoint(control.continuation);
    stoppedCallback = false;
  }
  void yield(ValueRange values) {
    if (!reserve(8 + 2 * values.size()))
      return;

    if (!stoppedCallback) {
      auto current = function();
      auto &control = scopeControl();
      control.complete(values.take_front(regionReturns.lookup(current)));
    }
    return;
  }
  // A zero-trip loop applies the existing executable bound admission without
  // inventing a second limit contract or evaluating a helper.
  void validateBound(Value bound) {
    auto loop = control(ControlKind::Loop, {bound, bound}, {}, 1);
    region(loop, 0, {index});
    yield({});
    resume(loop);
  }
  Value reversedRange(Value lower, Value upper) {
    Value less = emit("index.less", {lower, upper}, boolean);
    SmallVector<Value> inputs{less, lower};
    if (upper != lower)
      inputs.push_back(upper);
    SmallVector<Type> types(inputs.size() - 1, index);
    auto branch = control(ControlKind::Branch, inputs, {index}, 2);
    auto yes = region(branch, 0, types);
    if (failedHelper)
      return {};
    yield(emit("index.sub", {yes[upper == lower ? 0 : 1], yes[0]}, index));
    region(branch, 1, types);
    yield(number(0));
    resume(branch);
    return failedHelper ? Value() : branch.outputs[0];
  }
  Value cardinalityProduct(Value left, Value right) {
    validateBound(left);
    validateBound(right);
    Value result = emit("index.mul", {left, right}, index);
    validateBound(result);
    return result;
  }
  void admit(ArrayRef<Operation *> admission) {
    // Visit all constructors in descriptor order, including dead intermediates.
    for (Operation *constructor : admission) {
      if (!reserve(1 + constructor->getNumOperands()))
        return;
      auto &op = *constructor;
      Value size;
      if (isa<data::DomainElementsOp, data::DomainIndicesOp>(op)) {
        unsigned axis =
            isa<data::DomainIndicesOp>(op)
                ? unsigned(cast<data::DomainIndicesOp>(op).getAxis())
                : 0;
        size = length(values.lookup(op.getOperand(0)), axis);
      } else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
        bool row = isa<data::DomainMatrixRowOp>(op);
        Value matrix = values.lookup(op.getOperand(0));
        Value selected = values.lookup(op.getOperand(1));
        Value bound = length(matrix, row ? 0 : 1);
        require(emit("index.less", {selected, bound}, boolean));
        size = length(matrix, row ? 1 : 0);
      } else if (isa<data::DomainRangeOp>(op)) {
        Value lower = values.lookup(op.getOperand(0)),
              upper = values.lookup(op.getOperand(1));
        validateBound(lower);
        validateBound(upper);
        lowers[op.getResult(0)] = lower;
        size = reversedRange(lower, upper);
      } else if (isa<data::DomainZipOp>(op)) {
        size = sizes.lookup(op.getOperand(0));
        for (Value child : op.getOperands().drop_front())
          require(emit("index.equal", {size, sizes.lookup(child)}, boolean));
      } else if (isa<data::DomainProductOp>(op)) {
        size = sizes.lookup(op.getOperand(0));
        for (Value child : op.getOperands().drop_front())
          size = cardinalityProduct(size, sizes.lookup(child));
      } else if (isa<data::DomainMatrixCoordinatesOp>(op)) {
        Value matrix = values.lookup(op.getOperand(0));
        Value rows = length(matrix, 0), columns = length(matrix, 1);
        // The second radix is retained as an ordinary SSA capture.
        lowers[op.getResult(0)] =
            cast<data::DomainMatrixCoordinatesOp>(op).getOrder() == "row_major"
                ? columns
                : rows;
        size = cardinalityProduct(rows, columns);
      }
      sizes[op.getResult(0)] = size;
    }
  }
  SmallVector<Value> items(Value descriptor, Value position,
                           IRMapping &mapping) {
    if (!reserve(1))
      return {};
    auto *op = descriptor.getDefiningOp();
    auto actual = [&](Value v) { return mapping.lookup(values.lookup(v)); };
    if (isa<data::DomainZipOp>(op)) {
      SmallVector<Value> result;
      for (Value child : op->getOperands())
        append_range(result, items(child, position, mapping));
      return result;
    }
    if (isa<data::DomainProductOp>(op)) {
      SmallVector<SmallVector<Value>> factors;
      Value quotient = position;
      for (Value child : reverse(op->getOperands())) {
        Value divisor = mapping.lookup(sizes.lookup(child));
        Value remainder = emit("index.mod", {quotient, divisor}, index);
        factors.push_back(items(child, remainder, mapping));
        quotient = emit("index.div", {quotient, divisor}, index);
      }
      SmallVector<Value> result;
      for (auto &factor : reverse(factors))
        append_range(result, factor);
      return result;
    }
    if (isa<data::DomainIndicesOp>(op))
      return {position};
    if (isa<data::DomainRangeOp>(op))
      return {emit("index.add",
                   {mapping.lookup(lowers.lookup(descriptor)), position},
                   index)};
    if (isa<data::DomainMatrixCoordinatesOp>(op)) {
      Value radix = mapping.lookup(lowers.lookup(descriptor));
      Value major = emit("index.div", {position, radix}, index),
            minor = emit("index.mod", {position, radix}, index);
      return cast<data::DomainMatrixCoordinatesOp>(op).getOrder() == "row_major"
                 ? SmallVector<Value>{major, minor}
                 : SmallVector<Value>{minor, major};
    }
    Value container = actual(op->getOperand(0));
    auto col = mathematical::collectionRealization(container.getType());
    assert(col && col->get && "admitted collection read required");
    if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(op)) {
      Value selected = actual(op->getOperand(1));
      bool row = isa<data::DomainMatrixRowOp>(op);
      return {emit(
          *col->get,
          {container, row ? selected : position, row ? position : selected},
          col->element)};
    }
    return {emit(*col->get, {container, position}, col->element)};
  }
  Expected<mathematical::LaneRealizationResult> elementwise(
      Block &body, const ComputationView &view,
      const mathematical::Elementwise &equation, ValueRange entry, Type vector,
      Value output = {},
      mathematical::LaneResultMode mode = mathematical::LaneResultMode::Map,
      ValueRange additionalTerms = {},
      MathematicalIdentity combine = MathematicalIdentity::FieldAdd,
      Operation *sumConsumer = nullptr, StringRef sumOccurrence = {}) {
    Value root = view.iteration[view.root].descriptor;
    llvm::DenseMap<Value, mathematical::LaneInput> inputs;
    for (const auto &access : view.accesses)
      if (access.kind == AccessKind::Element)
        inputs[access.value] = {entry[access.input], true};
    for (const auto &capture : view.captures)
      inputs[capture.formal] = {entry[capture.input], false};
    for (auto [lookup, container] : equation.lookups)
      inputs[lookup] = {inputs.lookup(container).value, true};
    SmallVector<std::string> args{
        cast<algebra::FieldType>(elementType(vector)).getDomain().str()};
    auto admitted = mathematical::admitLaneFormula(body, inputs, vector,
                                                   &work.lanes, recipes, output,
                                                   additionalTerms, combine);
    if (!admitted)
      return admitted.takeError();
    if (!admitted->formula)
      return mathematical::LaneRealizationResult{
          admitted->status, {}, admitted->reason, admitted->outcome};
    if (expressionMode == NumericalExpressionMode::PreferNative) {
      auto result = mathematical::emitNumericalLanes(
          *admitted->formula, vector, sizes.lookup(root), mode,
          [&](const protocol::BindingApplication &binding, ValueRange operands,
              Type result, ArrayRef<Attribute> parameters) {
            auto previousLocation = loc;
            if (sumConsumer)
              loc = sumConsumer->getLoc();
            auto value = emit(binding, operands, result, parameters,
                              sumConsumer ? sumOccurrence : StringRef());
            loc = previousLocation;
            return value;
          },
          &work.lanes);
      if (!result || sumConsumer ||
          result->status == mathematical::LaneRealizationStatus::Realized)
        return result;
      // Body/port capacity is optional and has emitted nothing. Reuse the
      // admitted formula; never replenish optional work for this alternative.
      if (observation)
        observation->selection(
            computation.operation, mathematical::DecisionFamily::Lanes,
            mathematical::RealizationChoice::Elementwise, result->outcome);
    }
    return mathematical::emitVectorLanes(
        *admitted->formula, vector, sizes.lookup(root), recipes,
        [&](StringRef contract, ValueRange operands, Type result,
            ArrayRef<Attribute> parameters) {
          return emit(contract, operands, result, args, parameters);
        });
  }

  SmallVector<Value> apply(CallbackRole role, CallbackValues actuals) {
    if (!reserve(1))
      return {};
    auto callback = readCallbackABI(computation, role);
    if (failed(callback)) {
      failedHelper = true;
      return {};
    }
    auto environment =
        bindCallback(*callback, actuals,
                     callback->scope ? scopeControl().getScope() : Value());
    if (failed(environment)) {
      failedHelper = true;
      return {};
    }
    auto *helper = callback->symbol;
    auto type = callback->signature;
    ValueRange arguments = environment->actuals;
    if (computation.total) {
      auto math = cast<func::FuncOp>(helper);
      OptimizationOutcome outcome;
      if (failed(mathematical::chargeHelperOperations(
              math, work.helperOperations, work.helperSlots, nullptr,
              &outcome))) {
        if (observation)
          observation->failure(mathematical::RequiredFailure{
              "finite helper expansion", outcome.capacity});
        failedHelper = true;
        return {};
      }
      // Detached normalization subject, separate from body emission. Expansion
      // and polynomial elimination remain fallible and consume shared work.
      OwningOpRef<func::FuncOp> scratch(cast<func::FuncOp>(math->clone()));
      SymbolTableCollection tables;
      if (failed(mathematical::inlineHelpers(*scratch, work.helperOperations,
                                             work.helperSlots, tables,
                                             sourceRoot, nullptr, &outcome)) ||
          failed(poly::eliminatePolynomials(scratch->front(), work.polynomial,
                                            &outcome))) {
        if (observation)
          observation->failure(mathematical::RequiredFailure{
              "finite helper normalization", outcome.capacity});
        failedHelper = true;
        return {};
      }
      IRMapping mapping;
      for (auto [a, b] : zip(scratch->getArguments(), arguments))
        mapping.map(a, b);
      for (auto &op : scratch->front().without_terminator()) {
        if (composition &&
            computation.operation == composition->consumer.operation) {
          if (auto read = dyn_cast<data::BoundedAtOp>(op);
              read &&
              mapping.lookup(read.getInput()) == composition->collected &&
              mapping.lookup(read.getIndex()) == substitutedPosition) {
            mapping.map(op.getResult(0), substitutedElement);
            continue;
          }
          for (Value operand : op.getOperands())
            if (mapping.lookup(operand) == composition->collected) {
              failedHelper = true;
              return {};
            }
        }
        auto occurrence = site();
        if (failedHelper)
          return {};

        op.setAttr("site", builder.getStringAttr(occurrence));
        SmallVector<Value> inputs;
        for (Value operand : op.getOperands())
          inputs.push_back(mapping.lookup(operand));
        auto result = totalCallback(&op, inputs, scopeControl());
        if (failed(result) || result->size() != op.getNumResults()) {
          failedHelper = true;
          return {};
        }
        mapping.map(op.getResults(), *result);
      }
      SmallVector<Value> results;
      for (Value v : scratch->front().back().getOperands())
        results.push_back(mapping.lookup(v));
      return results;
    }

    auto occurrence = site();
    if (failedHelper)
      return {};
    auto result =
        scopedCallback(cast<func::FuncOp>(helper), arguments.drop_front(),
                       occurrence, scopeControl());
    if (failed(result)) {
      failedHelper = true;
      return {};
    }
    stoppedCallback = result->stopped;
    if ((stoppedCallback && !result->values.empty()) ||
        (!stoppedCallback &&
         !llvm::equal(
             ValueRange(result->values).getTypes(),
             cast<exec::OutcomeType>(type.getResult(0)).getPayload()))) {
      failedHelper = true;
      return {};
    }
    return result->values;
  }
  SmallVector<Value> transition(ValueRange state, ValueRange item,
                                ValueRange environment, Value position = {}) {
    if (composition) {
      auto producer = computation;
      auto producerEnvironment =
          environment.take_front(producer.arguments + producer.captures);
      auto element =
          apply(CallbackRole::Body,
                {{},
                 item,
                 producerEnvironment.take_front(producer.arguments),
                 producerEnvironment.drop_front(producer.arguments)});
      if (failedHelper || element.size() != 1) {
        failedHelper = true;
        return {};
      }
      auto env = environment.drop_front(producer.arguments + producer.captures);
      SmallVector<Value> consumerEnv;
      unsigned next = 0;
      for (Value value : consumerEnvironment)
        consumerEnv.push_back(value == composition->collected ? value
                                                              : env[next++]);
      computation = composition->consumer;
      substitutedElement = element[0];
      substitutedPosition = position;
      SmallVector<Value> consumerItem{composition->indexed ? position
                                                           : element[0]};
      auto result =
          apply(CallbackRole::Step,
                {state, consumerItem,
                 ValueRange(consumerEnv).take_front(computation.arguments),
                 ValueRange(consumerEnv).drop_front(computation.arguments)});
      computation = producer;
      return result;
    }
    auto result =
        apply(computation.collect ? CallbackRole::Body : CallbackRole::Step,
              {computation.collect ? ValueRange{} : state, item,
               environment.take_front(computation.arguments),
               environment.drop_front(computation.arguments)});
    if (failedHelper || stoppedCallback)
      return {};
    if (!computation.collect)
      return result;
    auto col = mathematical::collectionRealization(state[0].getType());
    assert(col && col->append && "admitted collection append required");
    return {emit(*col->append, {state[0], result[0]}, state[0].getType())};
  }

public:
  Realizer(Operation *unit, OpBuilder &builder,
           exec::ScopedExecutionBuilder &entryControl,
           mathematical::RealizationWork &work,
           const mathematical::MathematicalRecipes &recipes =
               mathematical::mathematicalRecipes(),
           mathematical::RealizationScope *observation = nullptr,
           bool retryOrdered = false,
           NumericalExpressionMode expressionMode =
               NumericalExpressionMode::PreferNative,
           ScopedCallbackEmitter scopedCallback = {},
           StringRef scopedOccurrence = {},
           ScopedEmissionBudget *budget = nullptr,
           const protocol::SourceExecutionClosure *sourceClosure = nullptr,
           const llvm::DenseSet<Operation *> *fixedBindings = nullptr,
           TotalRecipeEmitter totalCallback = {})
      : unit(unit), sourceClosure(sourceClosure), fixedBindings(fixedBindings),
        builder(builder), loc(unit->getLoc()),
        index(IntegerType::get(unit->getContext(), 64, IntegerType::Unsigned)),
        boolean(builder.getI1Type()), emitter(unit, "_finite_binding_"),
        work(work), recipes(recipes), observation(observation),
        retryOrdered(retryOrdered), expressionMode(expressionMode),
        scopedCallback(scopedCallback), totalCallback(totalCallback),
        budget(budget), scopedOccurrence(scopedOccurrence),
        entryControl(entryControl), scopedEntry(function()) {}
  FailureOr<SmallVector<Value>>
  emitBody(Operation *source, ValueRange entry, bool optimize,
           const CollectFold *pair = nullptr, ValueRange consumerInputs = {},
           Operation *sumConsumer = nullptr, StringRef sumOccurrence = {},
           Operation *explicitSourceRoot = nullptr) {
    composition = pair;
    // The source closure may be separate from the table receiving bindings.
    // Detached helper copies keep resolving through this original owner.
    sourceRoot = explicitSourceRoot
                     ? explicitSourceRoot
                     : SymbolTable::getNearestSymbolTable(source);
    if (!sourceRoot ||
        failed(describe(source, computation, sourceRoot, &symbols)))
      return failure();
    computation.scopedSource = sourceClosure;
    computation.fixedBindings = fixedBindings;
    emitter.reserveNames(sourceRoot);
    auto partitions = partitionEntry(computation, entry);
    if (failed(partitions))
      return failure();
    // Ordered emission reads the domain directly. It needs no optional
    // structural/equation work, including when retrying a discarded proposal.
    // Keep the owned body alive through every borrowed view/equation and lane
    // emission. Never replace computation or a source symbol with this copy.
    OwningOpRef<ModuleOp> normalized;
    Computation selectionComputation = computation;
    mathematical::ComputationSelection selection;
    if (optimize || sumConsumer) {
      CallbackStructuralWork callbackWork(work.matching,
                                          selection.diagnostic.outcome);
      bool ready = true;
      if (computation.total && !computation.predicate) {
        // Helpers without calls or pack projections retain their admitted
        // context. Bound the discovery scan too; exhaustion only declines
        // selection.
        bool needsNormalization = false;
        for (auto &op : computation.helper->getRegion(0).front()) {
          if (!consumeComputationWork(callbackWork.remaining.structural, 1,
                                      WorkOwner::Structural,
                                      &selection.diagnostic.outcome)) {
            ready = false;
            break;
          }
          if (isa<func::CallOp, algebra::ArrayAtOp>(op)) {
            needsNormalization = true;
            break;
          }
        }
        if (ready && needsNormalization) {
          normalized = normalizeSelectionCallback(
              selectionComputation, sourceRoot,
              callbackWork.remaining.structural, selection.diagnostic.outcome);
          ready = bool(normalized);
        }
      }
      if (ready)
        selection =
            mathematical::selectComputation(selectionComputation, {true, false},
                                            callbackWork.remaining, recipes);
      // A collection and its sole adjacent native sum have a separate policy
      // from ordinary finite bulk lowering. Recognition reads the admitted
      // scalar callback; no candidate or structural pair supplies its equation.
      if (sumConsumer &&
          selection.kind == mathematical::RealizationKind::Elementwise &&
          selection.view && selection.view->results.size() == 1) {
        selection.sumCollection = true;
        auto &view = *selection.view;
        auto *product = view.results[0].getDefiningOp();
        auto *meaning = product ? finite::semantics(product) : nullptr;
        SmallVector<unsigned> inputs;
        if (meaning &&
            meaning->identity == MathematicalIdentity::FieldMultiply &&
            product->getNumOperands() == 2) {
          for (Value operand : product->getOperands()) {
            std::optional<unsigned> input;
            for (const auto &access : view.accesses) {
              if (!consumeComputationWork(callbackWork.remaining.structural, 1,
                                          WorkOwner::Structural,
                                          &selection.diagnostic.outcome))
                break;
              if (access.value == operand &&
                  access.kind == AccessKind::Element &&
                  isa<algebra::FieldVectorType>(
                      computation.signature.getInput(access.input)))
                input = access.input;
            }
            if (!input || selection.diagnostic.outcome.status ==
                              OptimizationStatus::Capacity)
              break;
            inputs.push_back(*input);
          }
        }
        if (inputs.size() == 2) {
          selection.collectionSum =
              mathematical::selectMapSum({inputs[0], inputs[1]}, recipes);
          if (selection.collectionSum)
            selection.kind = mathematical::RealizationKind::CollectionSum;
        }
      }
      if (!optimize) {
        // An independently enabled contraction does not enable the ordinary
        // map alternatives. Its required endpoint remains the ordered source.
        selection.allowCollectionMap = false;
        if (!selection.collectionSum &&
            !(selection.sumCollection &&
              expressionMode == NumericalExpressionMode::PreferNative))
          selection.kind = mathematical::RealizationKind::Ordered;
      }
      mathematical::applyNumericalSelection(work, selection, recipes);
      // A normalized helper's positions are not source positions. Attribute
      // queries inside that private view to the original finite occurrence.
      auto prepared = [&](Operation *op) {
        return normalized && op && normalized->getOperation()->isAncestor(op);
      };
      if (!selection.diagnostic.subject ||
          selection.diagnostic.subject == selectionComputation.operation ||
          prepared(selection.diagnostic.subject))
        selection.diagnostic.subject = source;
      for (auto *&occurrence : selection.diagnostic.occurrencePath)
        if (occurrence == selectionComputation.operation ||
            prepared(occurrence))
          occurrence = source;
    }
    if (!optimize && !sumConsumer)
      selection.diagnostic.outcome = {
          retryOrdered ? OptimizationStatus::Succeeded
                       : OptimizationStatus::PolicyDisabled,
          retryOrdered ? OptimizationReason::OrderedRetry
                       : OptimizationReason::Policy};
    if (observation)
      observation->selectionDiagnostic(
          source, mathematical::DecisionFamily::Finite,
          observedChoice(selection.kind), selection.diagnostic);
    const ComputationView *view = selection.view ? &*selection.view : nullptr;
    SmallVector<Operation *> admission;
    for (auto &op : computation.domain.getBody().front().without_terminator())
      admission.push_back(&op);
    values.clear();
    sizes.clear();
    lowers.clear();
    occurrence = 0;
    failedHelper = false;
    loc = source->getLoc();
    sitePrefix =
        (scopedOccurrence.empty()
             ? source->getAttrOfType<StringAttr>("site").getValue().str()
             : scopedOccurrence.str()) +
        "_finite_";
    for (auto [formal, actual] :
         zip(computation.domain.getBody().front().getArguments(),
             partitions->domain))
      values[formal] = actual;
    admit(admission);
    if (failedHelper)
      return failure();
    SmallVector<Value> initial(partitions->initialState), environment;
    append_range(environment, partitions->domain);
    append_range(environment, partitions->captures);
    if (selection.kind == mathematical::RealizationKind::NestedContraction) {
      const auto &nested = *selection.nested;
      const auto &recipe = *selection.matrix;
      auto output = computation.signature.getResult(0);
      auto field = cast<algebra::FieldVectorType>(output).getElementType();
      SmallVector<std::string> arguments{
          cast<algebra::FieldType>(field).getDomain().str()};
      auto root = computation.domain.getBody().front().back().getOperand(0);
      Value size = sizes.lookup(root), zero = number(0);
      Value nonempty = emit("index.less", {zero, size}, boolean);
      SmallVector<Value> inputs{nonempty};
      append_range(inputs, entry);
      inputs.push_back(size);
      inputs.push_back(zero);
      auto branch = control(ControlKind::Branch, inputs, output, 2);
      auto captureTypes = ValueRange(inputs).drop_front().getTypes();
      for (unsigned arm = 0; arm < 2 && !failedHelper; ++arm) {
        auto captures = region(branch, arm, captureTypes);
        if (failedHelper)
          break;
        if (arm) {
          yield(emit("vector.empty", {}, output, arguments));
          continue;
        }
        // Only the entered arm admits inner domains. Inspect every constructor
        // in source order, including unused lanes and strict zip comparisons.
        // The outer indices guarantee the same selector bounds on later rows.
        auto &domain = nested.inner.domain->getRegion(0).front();
        auto mapped = [&](Value formal) {
          auto position = cast<BlockArgument>(formal).getArgNumber();
          auto input = nested.domainInputs[position];
          return input ? captures[input - 1] : captures.back();
        };
        llvm::DenseMap<Value, Value> extents;
        loc = nested.inner.operation->getLoc();
        admissionPath = protocol::Assignments{
            {scopedOccurrence.str(),
             SymbolTable::getSymbolName(computation.helper).str()},
            {nested.call->getAttrOfType<StringAttr>("site").str(),
             SymbolTable::getSymbolName(nested.inner.helper).str()}};
        admissionOccurrence = 0;
        for (auto &op : domain.without_terminator()) {
          if (failedHelper)
            break;
          Value extent;
          if (isa<data::DomainElementsOp>(op))
            extent = length(mapped(op.getOperand(0)));
          else if (isa<data::DomainMatrixRowOp, data::DomainMatrixColumnOp>(
                       op)) {
            Value matrix = mapped(op.getOperand(0));
            Value limit = length(matrix, nested.axis);
            require(
                emit("index.less", {mapped(op.getOperand(1)), limit}, boolean));
            extent = length(matrix, 1 - nested.axis);
          } else {
            extent = extents.lookup(op.getOperand(0));
            for (Value child : op.getOperands().drop_front())
              require(emit("index.equal", {extent, extents.lookup(child)},
                           boolean));
          }
          extents[op.getResult(0)] = extent;
        }
        admissionPath.reset();
        loc = source->getLoc();
        Value seed = nested.seed.input
                         ? captures[*nested.seed.input]
                         : emit("field.constant", {}, field, arguments,
                                {cantFail(algebra::decodeFieldLiteral(
                                    cast<algebra::FieldType>(field),
                                    nested.seed.constant))});
        SmallVector<Value> roles{captures[nested.matrix],
                                 captures[nested.vector]};
        SmallVector<Value> operands;
        for (unsigned i = 0; i < recipe.arity; ++i)
          operands.push_back(roles[recipe.operands[i]]);
        Value result = emit(recipe.target, operands, output, arguments);
        Value initial = emit("vector.fill", {seed, captures[entry.size()]},
                             output, arguments);
        yield(emit(recipe.seedCombiner, {initial, result}, output, arguments));
      }
      resume(branch);
      return failedHelper ? FailureOr<SmallVector<Value>>(failure())
                          : FailureOr<SmallVector<Value>>(branch.outputs);
    }
    if (selection.kind == mathematical::RealizationKind::CollectionSum) {
      const auto &reduction = *selection.collectionSum;
      SmallVector<Value> operands;
      for (unsigned input : reduction.inputs)
        operands.push_back(entry[input]);
      auto vector =
          cast<algebra::FieldVectorType>(computation.signature.getResult(0));
      loc = sumConsumer->getLoc();
      auto result =
          emit({reduction.recipe->target.str(), {vector.getDomain().str()}, ""},
               operands, vector.getElementType(), {}, sumOccurrence);
      return failedHelper
                 ? FailureOr<SmallVector<Value>>(failure())
                 : FailureOr<SmallVector<Value>>(SmallVector<Value>{result});
    }
    if (selection.kind == mathematical::RealizationKind::Bilinear) {
      const auto &plan = selection.equations.bilinear;
      auto type = computation.signature.getResult(0);
      auto col = mathematical::collectionRealization(
          values.lookup(plan->matrix).getType());
      const auto &recipe = *selection.matrix;
      SmallVector<Value> roles{values.lookup(plan->matrix),
                               values.lookup(plan->left),
                               values.lookup(plan->right)};
      SmallVector<Value> inputs;
      for (unsigned i = 0; i < recipe.arity; ++i)
        inputs.push_back(roles[recipe.operands[i]]);
      Value result = emit(recipe.target, inputs, type, col->get->arguments);
      result = emit(recipe.seedCombiner, {initial.front(), result}, type,
                    col->get->arguments);
      return SmallVector<Value>{result};
    }
    if (selection.kind == mathematical::RealizationKind::Reduction) {
      const auto &reduction = selection.reduction;
      SmallVector<Value> inputs;
      for (unsigned position : reduction->inputs)
        inputs.push_back(entry[position]);
      if (reduction->selectedIndex)
        inputs.push_back(entry[*reduction->selectedIndex]);
      auto resultType = computation.signature.getResult(0);
      auto col = mathematical::collectionRealization(
          entry[reduction->staticSourceInput].getType());
      Value reduced = emit(reduction->recipe->target, inputs, resultType,
                           col->get->arguments);
      Value result =
          emit(reduction->recipe->combiner, {initial.front(), reduced},
               resultType, col->get->arguments);
      return SmallVector<Value>{result};
    }
    if (selection.kind == mathematical::RealizationKind::Elementwise ||
        selection.kind == mathematical::RealizationKind::PointwiseReduction) {
      const auto *reduction = selection.pointwiseReduction;
      Type resultType = computation.signature.getResult(0);
      Type vector = reduction
                        ? Type(algebra::FieldVectorType::get(
                              resultType.getContext(),
                              cast<algebra::FieldType>(resultType).getDomain()))
                        : resultType;
      const auto &formula =
          reduction ? selection.equations.pointwiseReduction->formula
                    : *selection.equations.elementwise;
      Value term =
          reduction ? selection.equations.pointwiseReduction->term : Value();
      const auto *equation =
          reduction ? &*selection.equations.pointwiseReduction : nullptr;
      auto mode = selection.sumCollection ? mathematical::LaneResultMode::Sum
                  : !reduction            ? mathematical::LaneResultMode::Map
                  : equation->combine == MathematicalIdentity::FieldMultiply
                      ? mathematical::LaneResultMode::Product
                      : mathematical::LaneResultMode::Sum;
      auto result = elementwise(
          *view->callbackBody, *view, formula, entry, vector, term, mode,
          equation ? ValueRange(equation->additionalTerms) : ValueRange{},
          equation ? equation->combine : MathematicalIdentity::FieldAdd,
          selection.sumCollection ? sumConsumer : nullptr, sumOccurrence);
      if (!result) {
        diagnostics::emit(source->emitOpError(), result.takeError());
        return failure();
      }
      if (result->status == mathematical::LaneRealizationStatus::Realized) {
        Value value = result->value;
        if (reduction) {
          SmallVector<std::string> args{
              cast<algebra::FieldType>(resultType).getDomain().str()};
          if (value.getType() == vector)
            value = emit(reduction->target, value, resultType, args);
          value = emit(reduction->combiner, {initial.front(), value},
                       resultType, args);
        }
        return SmallVector<Value>{value};
      }
      if (observation)
        observation->selection(source, mathematical::DecisionFamily::Lanes,
                               mathematical::RealizationChoice::Ordered,
                               result->outcome);
      // A declined optional formula has emitted no payload or bindings. Keep
      // the complete admission above and continue with the ordinary loop.
    }
    if (composition) {
      auto consumer = partitionEntry(composition->consumer, consumerInputs);
      if (failed(consumer))
        return failure();
      initial.assign(consumer->initialState.begin(),
                     consumer->initialState.end());
      consumerEnvironment.clear();
      append_range(consumerEnvironment, consumer->domain);
      append_range(consumerEnvironment, consumer->captures);
      for (Value value : consumerEnvironment)
        if (value != composition->collected)
          environment.push_back(value);
    } else if (computation.collect) {
      auto result = computation.signature.getResult(0);
      auto col = mathematical::collectionRealization(result);
      assert(col && col->empty && "admitted collection construction required");
      initial.push_back(emit(*col->empty, {}, col->storage));
    }
    if (failedHelper)
      return failure();
    Value root = computation.domain.getBody().front().back().getOperand(0);
    Value zero = number(0), upper = sizes.lookup(root);
    // Capture only Copy/Drop values; each affine state is in the carried
    // prefix.
    SmallVector<Value> captures(environment);
    for (Operation *op : admission) {
      captures.push_back(sizes.lookup(op->getResult(0)));
      if (auto v = lowers.lookup(op->getResult(0)))
        captures.push_back(v);
    }
    SmallVector<Value> unique;
    for (Value value : captures)
      if (!is_contained(unique, value))
        unique.push_back(value);
    captures = std::move(unique);
    SmallVector<Value> loopInputs{zero, upper};
    append_range(loopInputs, initial);
    append_range(loopInputs, captures);
    SmallVector<Type> stateTypes;
    for (Value v : initial)
      stateTypes.push_back(v.getType());
    auto loop = control(ControlKind::Loop, loopInputs, stateTypes, 1);
    SmallVector<Type> arguments{index};
    append_range(arguments, stateTypes);
    for (Value v : captures)
      arguments.push_back(v.getType());
    auto body = region(loop, 0, arguments);
    if (failedHelper)
      return failure();
    IRMapping mapping;
    auto state = ValueRange(body).slice(1, initial.size());
    auto captured = ValueRange(body).drop_front(1 + initial.size());
    for (auto [a, b] : zip(captures, captured))
      mapping.map(a, b);
    auto item = items(root, body[0], mapping);
    if (failedHelper)
      return failure();
    SmallVector<Value> env;
    for (Value v : environment)
      env.push_back(mapping.lookup(v));
    SmallVector<Value> next;
    if (computation.predicate) {
      auto predicate =
          apply(CallbackRole::Predicate,
                {{},
                 item,
                 ValueRange(env).take_front(computation.arguments),
                 ValueRange(env).drop_front(computation.arguments)});
      if (failedHelper)
        return failure();
      if (!stoppedCallback) {
        Value condition = predicate[0];
        SmallVector<Value> branchCaptures;
        auto capture = [&](ValueRange operands) {
          for (Value value : operands)
            if (!is_contained(branchCaptures, value))
              branchCaptures.push_back(value);
        };
        capture(state);
        capture(item);
        capture(env);
        SmallVector<Value> branchInputs{condition};
        append_range(branchInputs, branchCaptures);
        auto branch = control(ControlKind::Branch, branchInputs, stateTypes, 2);
        SmallVector<Type> branchTypes;
        for (Value v : branchCaptures)
          branchTypes.push_back(v.getType());
        auto yes = region(branch, 0, branchTypes);
        if (failedHelper)
          return failure();
        IRMapping branchMapping;
        for (auto [a, b] : zip(branchCaptures, yes))
          branchMapping.map(a, b);
        auto remap = [&](ValueRange operands) {
          SmallVector<Value> result;
          for (Value value : operands)
            result.push_back(branchMapping.lookup(value));
          return result;
        };
        auto transitionResults =
            transition(remap(state), remap(item), remap(env));
        if (failedHelper)
          return failure();
        yield(transitionResults);
        auto no = region(branch, 1, branchTypes);
        for (auto [a, b] : zip(branchCaptures, no))
          branchMapping.map(a, b);
        yield(remap(state));
        resume(branch);
        append_range(next, branch.outputs);
      }
    } else
      next = transition(state, item, env, body[0]);
    if (failedHelper)
      return failure();
    append_range(next, captured);
    yield(next);
    resume(loop);
    if (failedHelper)
      return failure();
    SmallVector<Value> results(loop.outputs);
    if (!composition && computation.collect &&
        computation.signature.getResult(0) != results[0].getType()) {
      auto col = mathematical::collectionRealization(
          computation.signature.getResult(0));
      assert(col && col->wrap && "admitted collection wrapper required");
      results[0] =
          emit(*col->wrap, results, computation.signature.getResult(0));
    }
    if (failedHelper)
      return failure();
    return results;
  }
};
} // namespace
FailureOr<SmallVector<Value>> realizeScopedTotalExpression(
    Operation *source, Operation *sourceRoot, ValueRange inputs,
    OpBuilder &builder, exec::ScopedExecutionBuilder &control,
    TotalRecipeEmitter callback, mathematical::RealizationWork &work,
    MathematicalSelectionPolicy policy, mathematical::RealizationTrace *trace,
    ScopedEmissionBudget &budget, bool orderedRetry, const CollectFold *pair,
    ValueRange consumerInputs) {
  auto function = control.getFunction();
  auto *owner = SymbolTable::getNearestSymbolTable(function);
  auto occurrence = source->getAttrOfType<StringAttr>("site");
  if (!callback || !sourceRoot || !owner || !occurrence ||
      occurrence.getValue().empty() || !isComputation(source) ||
      !mathematical::isTotal(source))
    return failure();
  mathematical::RealizationScope scope(trace, "finite-expression", source,
                                       policy, &work);
  Realizer realizer(owner, builder, control, work,
                    mathematical::mathematicalRecipes(), &scope, orderedRetry,
                    policy.numericalExpressions, {}, occurrence.getValue(),
                    &budget, nullptr, nullptr, callback);
  auto result =
      realizer.emitBody(source, inputs, pair ? false : policy.finiteBulk, pair,
                        consumerInputs, nullptr, {}, sourceRoot);
  if (succeeded(result))
    scope.complete();
  return result;
}

FailureOr<SmallVector<Value>> realizeScopedExpression(
    Operation *source, ValueRange inputs, OpBuilder &builder,
    exec::ScopedExecutionBuilder &control, ScopedCallbackEmitter callback,
    mathematical::RealizationWork &work, MathematicalSelectionPolicy policy,
    mathematical::RealizationTrace *trace, StringRef occurrenceName,
    ScopedEmissionBudget *budget,
    const protocol::SourceExecutionClosure *sourceClosure,
    const llvm::DenseSet<Operation *> *fixedBindings,
    const mathematical::MathematicalRecipes &recipes, Operation *sumConsumer,
    StringRef sumOccurrence, bool orderedRetry) {
  auto *block = builder.getInsertionBlock();
  auto function =
      block ? dyn_cast<func::FuncOp>(block->getParentOp()) : func::FuncOp();
  auto *owner =
      function ? SymbolTable::getNearestSymbolTable(function) : nullptr;
  auto occurrence = source->getAttrOfType<StringAttr>("site");
  if (!callback || !owner || owner->getNumRegions() != 1 ||
      !owner->getRegion(0).hasOneBlock() || !occurrence ||
      occurrence.getValue().empty() || function.getNumArguments() == 0 ||
      !isa<runtime::ScopeType>(function.getArgument(0).getType()) ||
      !isa<exec::FoldOp, exec::CollectOp>(source))
    return failure();
  mathematical::RealizationScope scope(trace, "finite-expression", source,
                                       policy, &work);
  Realizer realizer(owner, builder, control, work, recipes, &scope,
                    orderedRetry, policy.numericalExpressions, callback,
                    occurrenceName, budget, sourceClosure, fixedBindings);
  auto result = realizer.emitBody(source, inputs, policy.finiteBulk, nullptr,
                                  {}, sumConsumer, sumOccurrence);
  if (succeeded(result))
    scope.complete();
  return result;
}

} // namespace zkc::finite
