#include "Computation/Support.h"
#include "NumericalSelection.h"
#include "RealizationSubject.h"
#include "RealizationTrace.h"
#include "ScopedCollectionSum.h"
#include "ScopedFinite.h"
#include "ScopedPreparation.h"
#include "ScopedSubstitution.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/TimeProfiler.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
using Values = SmallVector<Value>;
using Types = SmallVector<Type>;
using Environment = llvm::DenseMap<Value, Value>;
struct Result {
  Values values;
  bool stopped = false;
};

// Source admission consumes the actual CFG and associates each ordered step
// with its logical SSA ports and closed bodies. Reconstruct only that checked
// control profile. No Local IR or native-program body is used for production.
class ScopedExpander : private OpBuilder::Listener {
  const SourceExecutionClosure &source;
  SymbolTable symbols;
  protocol_ir::ProtocolModuleOp target;
  OpBuilder builder;
  llvm::StringSet<> names;
  unsigned nextRegion = 0;
  unsigned definitions = 0, bindings = 0;
  // Substitution charges logical operations and every data port across the
  // complete closure. Numerical materialization has a separate transaction
  // allowance for its additional snapshots and correspondence reads.
  uint64_t defaultRemaining = 1000000, defaultBytes = 16 * 1024 * 1024;
  uint64_t &remaining, &remainingBytes;
  const llvm::DenseMap<Operation *, func::FuncOp> *replacements;
  mathematical::NumericalSelection *selection;
  std::optional<CapacityCause> *capacity;
  mathematical::RealizationWork *finiteWork;
  MathematicalSelectionPolicy finitePolicy;
  const llvm::DenseSet<Operation *> *fixedBindings;
  const mathematical::MathematicalRecipes &recipes;
  mathematical::RealizationTrace *trace;
  bool orderedRetry;
  llvm::DenseSet<Operation *> replacedDefinitions;
  SmallVector<mathematical::NumericalOccurrence> finiteOwners;
  void notifyOperationInserted(Operation *op, OpBuilder::InsertPoint) override {
    if (selection)
      for (auto owner : finiteOwners)
        selection->record(op, owner);
  }

  void record(Operation *before, Operation *after) {
    if (selection)
      for (auto owner : selection->owners(before))
        selection->record(after, owner);
  }
  bool valid = true;
  std::string root;

  bool charge(Operation *op, uint64_t work) {
    if (!valid)
      return false;
    if (work > remaining) {
      if (capacity)
        *capacity =
            CapacityCause{WorkOwner::AlgorithmExpansion, work, remaining};
      diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit");
      valid = false;
      return false;
    }
    remaining -= work;
    return true;
  }
  bool declaration(Operation *op) {
    // Binding and Func/domain inventories have separate carrier limits.
    // Outlined bodies become control inside a callable, not extra Program
    // definitions. Their construction still consumes operation/port work.
    if (isa<func::FuncOp>(op) && op->hasAttr("runtime.region"))
      return true;
    // Profile metadata shares the symbol namespace, not either inventory.
    auto *inventory = isa<runtime::BindingOp>(op)             ? &bindings
                      : isa<func::FuncOp, data::DomainOp>(op) ? &definitions
                                                              : nullptr;
    if (!inventory || ++*inventory <= 4096)
      return true;
    if (capacity)
      *capacity = CapacityCause{WorkOwner::AlgorithmExpansion, 1, 0};
    diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit",
                      isa<runtime::BindingOp>(op)
                          ? "expanded binding limit"
                          : "expanded definition limit");
    valid = false;
    return false;
  }
  Values values(ValueRange inputs, const Environment &env) {
    Values result;
    for (Value input : inputs)
      result.push_back(env.lookup(input));
    return result;
  }
  Types types(ValueRange values) { return Types(values.getTypes()); }
  std::string site(Operation *op, const Assignments &path) {
    auto original = op->getAttrOfType<StringAttr>("site");
    if (!original)
      return {};
    if ((replacements || finiteWork) && path.empty()) {
      if (original.getValue().size() > remainingBytes) {
        if (capacity)
          *capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes,
                                    original.getValue().size(), remainingBytes};
        valid = false;
        return {};
      }
      remainingBytes -= original.getValue().size();
      return original.getValue().str();
    }
    auto encoded = algorithmSite(path, original.getValue(), remainingBytes);
    if (!encoded) {
      if (capacity)
        *capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes};
      diagnostics::emit(op->emitOpError(), encoded.takeError());
      valid = false;
      return {};
    }
    return *encoded;
  }
  // Inlining can identify distinct immutable capture bindings. Keep the first
  // actual value and substitute every old formal position at the same time.
  SmallVector<unsigned> captures(ValueRange inputs, Values &unique) {
    llvm::DenseMap<Value, unsigned> positions;
    SmallVector<unsigned> indices;
    for (Value input : inputs) {
      auto [found, inserted] = positions.try_emplace(input, unique.size());
      if (inserted)
        unique.push_back(input);
      indices.push_back(found->second);
    }
    return indices;
  }
  func::FuncOp region(func::FuncOp original, ArrayRef<unsigned> indices,
                      ValueRange captured, const Assignments &path,
                      unsigned depth, bool &stopped) {
    OpBuilder::InsertionGuard guard(builder);
    std::string name;
    do {
      name = "_execution_region_" + std::to_string(nextRegion++);
    } while (!names.insert(name).second);
    unsigned prefix = original.getNumArguments() - 1 - indices.size();
    Types inputs(original.getArgumentTypes().take_front(1 + prefix));
    append_range(inputs, captured.getTypes());
    if (!declaration(original) || !charge(original, 1 + inputs.size()))
      return {};
    builder.setInsertionPointToEnd(&target.getBody().front());
    auto function = func::FuncOp::create(
        builder, original.getLoc(), name,
        builder.getFunctionType(inputs, original.getResultTypes()));
    NamedAttrList attributes(original->getAttrs());
    attributes.set("sym_name", function->getAttr("sym_name"));
    attributes.set("function_type", function->getAttr("function_type"));
    function->setAttrs(attributes.getDictionary(builder.getContext()));
    if (auto conditions =
            original->getAttrOfType<ArrayAttr>("data.preconditions")) {
      if (!charge(original, conditions.size()))
        return {};
      auto position = [&](unsigned argument) {
        return argument <= prefix ? argument
                                  : 1 + prefix + indices[argument - 1 - prefix];
      };
      SmallVector<Attribute> transported;
      for (Attribute condition : conditions) {
        if (auto bound = dyn_cast<data::IndexBoundAttr>(condition))
          transported.push_back(data::IndexBoundAttr::get(
              builder.getContext(), position(bound.getIndexArg()),
              position(bound.getContainerArg()), bound.getAxis()));
        else {
          auto equal = cast<data::EqualExtentAttr>(condition);
          transported.push_back(data::EqualExtentAttr::get(
              builder.getContext(), position(equal.getLeftArg()),
              equal.getLeftAxis(), position(equal.getRightArg()),
              equal.getRightAxis()));
        }
      }
      function->setAttr("data.preconditions",
                        builder.getArrayAttr(transported));
    }
    builder.createBlock(
        &function.getBody(), function.getBody().end(), inputs,
        SmallVector<Location>(inputs.size(), original.getLoc()));
    builder.setInsertionPointToEnd(&function.front());
    Environment env;
    for (unsigned i = 0; i < prefix; ++i)
      env[original.getArgument(1 + i)] = function.getArgument(1 + i);
    for (auto [i, index] : enumerate(indices))
      env[original.getArgument(1 + prefix + i)] =
          function.getArgument(1 + prefix + index);
    exec::ScopedExecutionBuilder control(builder, function);
    stopped =
        body(original, std::move(env), control, path, depth, false).stopped;
    return valid ? function : func::FuncOp();
  }
  bool discardStoppedPayload(func::FuncOp function) {
    // Only a proved stopping outline may lose its result payload. Its actual
    // returns must all package failures; intermediate outcomes keep their ABI.
    auto outcome = exec::OutcomeType::get(builder.getContext(), {});
    auto checked = function.walk([&](func::ReturnOp returned) {
      if (!charge(returned, 1) || returned.getNumOperands() != 1 ||
          !returned.getOperand(0).getDefiningOp<exec::FailureOp>())
        return WalkResult::interrupt();
      return WalkResult::advance();
    });
    if (checked.wasInterrupted()) {
      valid = false;
      return false;
    }
    function.walk(
        [&](exec::FailureOp failed) { failed.getOutcome().setType(outcome); });
    function.setFunctionType(
        builder.getFunctionType(function.getArgumentTypes(), {outcome}));
    return true;
  }
  void unreachable(exec::ScopedExecutionBuilder &control) {
    auto function =
        cast<func::FuncOp>(builder.getInsertionBlock()->getParentOp());
    llvm::StringSet<> sites;
    function.walk([&](Operation *op) {
      if (auto name = op->getAttrOfType<StringAttr>("site")) {
        if (charge(op, 1 + name.getValue().size()))
          sites.insert(name.getValue());
      }
    });
    unsigned index = 0;
    std::string name;
    do {
      name = "unreachable_" + std::to_string(index++);
    } while (sites.contains(name));
    if (!charge(function, 8) || name.size() > remainingBytes) {
      if (capacity && valid)
        *capacity = CapacityCause{WorkOwner::AlgorithmOriginBytes, name.size(),
                                  remainingBytes};
      valid = false;
      return;
    }
    remainingBytes -= name.size();
    control.reject("abort", name);
  }
  Result body(func::FuncOp function, Environment env,
              exec::ScopedExecutionBuilder &control, const Assignments &path,
              unsigned depth, bool inlineReturn) {
    if (depth > 64) {
      if (capacity)
        *capacity = CapacityCause{WorkOwner::AlgorithmExpansion};
      diagnostics::emit(function.emitOpError(), "algorithm-expansion-limit");
      valid = false;
      return {};
    }
    const auto &steps = source.bodies.at(function.getSymName().str());
    for (unsigned index = 0; index < steps.size(); ++index) {
      const auto &step = steps[index];
      auto *op = step.operation;
      auto previousLocation = control.getLocation();
      control.setLocation(op->getLoc());
      auto restoreLocation =
          llvm::scope_exit([&] { control.setLocation(previousLocation); });
      if (!charge(op, 1 + step.inputs.size() + step.outputs.size()))
        return {};
      auto inputs = values(step.inputs, env);
      if (replacements) {
        auto selected = replacements->find(op);
        if (selected != replacements->end()) {
          auto callee = selected->second;
          Environment arguments;
          for (auto [formal, actual] :
               zip(callee.getArguments().drop_front(), inputs))
            arguments[formal] = actual;
          auto result =
              body(callee, std::move(arguments), control, {}, depth + 1, true);
          if (!valid || result.stopped)
            return result;
          if (result.values.size() != step.outputs.size()) {
            valid = false;
            return {};
          }
          for (auto [before, after] : zip(step.outputs, result.values))
            env[before] = after;
          continue;
        }
      }
      if (finiteWork && isa<exec::FoldOp, exec::CollectOp>(op)) {
        auto occurrence = site(op, path);
        if (!valid)
          return {};
        if (!finiteWork->finiteExpressions) {
          if (capacity)
            *capacity = CapacityCause{WorkOwner::AlgorithmExpansion, 1, 0};
          valid = false;
          return {};
        }
        --finiteWork->finiteExpressions;
        auto callback = [&](func::FuncOp callee, ValueRange actuals,
                            StringRef callSite,
                            exec::ScopedExecutionBuilder &scope)
            -> FailureOr<finite::ScopedCallbackResult> {
          Environment arguments;
          for (auto [formal, actual] :
               zip(callee.getArguments().drop_front(), actuals))
            arguments[formal] = actual;
          Assignments nested(path);
          nested.emplace_back(callSite.str(), callee.getSymName().str());
          auto result = body(callee, std::move(arguments), scope, nested,
                             depth + 1, true);
          if (!valid)
            return failure();
          return finite::ScopedCallbackResult{std::move(result.values),
                                              result.stopped};
        };
        std::optional<CapacityCause> cause;
        finite::ScopedEmissionBudget budget{remaining, remainingBytes, cause};

        auto *sumConsumer =
            finitePolicy.vectorReductionFusion
                ? finite::collectionSumConsumer(
                      step,
                      index + 1 < steps.size() ? &steps[index + 1] : nullptr,
                      fixedBindings)
                : nullptr;
        auto sumOccurrence =
            sumConsumer ? site(sumConsumer, path) : std::string();
        if (!valid)
          return {};
        auto effective = finitePolicy;
        auto previousSelection = finiteWork->numericalSelection;
        auto previousOccurrence = finiteWork->numericalOccurrence;
        auto previousOwners = finiteOwners.size();
        auto restoreSelection = llvm::scope_exit([&] {
          finiteWork->numericalSelection = previousSelection;
          finiteWork->numericalOccurrence = previousOccurrence;
          finiteOwners.resize(previousOwners);
        });
        if (selection) {
          // Root plus qualified site identifies this actual substitution, even
          // when a different recipe changes the number of numerical calls.
          auto subject = mathematical::realizationSubject(op);
          subject.definition = subject.declaration;
          subject.originalSite = subject.site;
          subject.declaration = root;
          subject.site = occurrence;
          subject.occurrence = path;
          selection->enterInvocation({});
          auto id = selection->discover(subject,
                                        finitePolicy.finiteBulk || sumConsumer,
                                        finitePolicy.numericalExpressions);
          if (!id) {
            diagnostics::emit(op->emitOpError(), id.takeError());
            valid = false;
            return {};
          }
          finiteOwners.push_back(*id);
          finiteWork->numericalSelection = selection;
          finiteWork->numericalOccurrence = *id;
          effective = selection->policy(*id, finitePolicy);
        }
        auto result = finite::realizeScopedExpression(
            op, inputs, builder, control, callback, *finiteWork, effective,
            trace, occurrence, &budget, &source, fixedBindings, recipes,
            effective.vectorReductionFusion ? sumConsumer : nullptr,
            sumOccurrence, orderedRetry);
        if (failed(result) || result->size() != step.outputs.size()) {
          if (capacity && cause)
            *capacity = cause;
          valid = false;
          return {};
        }
        bool fused =
            sumConsumer && result->size() == 1 &&
            (*result)[0].getType() == steps[index + 1].outputs[0].getType();
        const auto &outputs = fused ? steps[index + 1].outputs : step.outputs;
        if (ValueRange(outputs).getTypes() != ValueRange(*result).getTypes()) {
          valid = false;
          return {};
        }
        for (auto [before, after] : zip(outputs, *result))
          env[before] = after;
        if (fused) {
          const auto &sum = steps[++index];
          if (!charge(sum.operation,
                      1 + sum.inputs.size() + sum.outputs.size()))
            return {};
        }
        continue;
      }
      if (auto call = dyn_cast<func::CallOp>(op)) {
        auto callee = symbols.lookup<func::FuncOp>(call.getCallee());
        Assignments nested(path);
        nested.emplace_back(
            call->getAttrOfType<StringAttr>("runtime.site").getValue().str(),
            call.getCallee().str());
        Environment arguments;
        for (auto [formal, actual] :
             zip(callee.getArguments().drop_front(), inputs))
          arguments[formal] = actual;
        auto returned = body(callee, std::move(arguments), control, nested,
                             depth + 1, true);
        if (!valid || returned.stopped)
          return returned;
        for (auto [before, after] : zip(step.outputs, returned.values))
          env[before] = after;
        continue;
      }
      if (isa<exec::ReturnOp>(op)) {
        if (!inlineReturn)
          control.returned(inputs);
        return {std::move(inputs), false};
      }
      if (isa<exec::CompleteOp>(op)) {
        control.complete(inputs);
        return {std::move(inputs), false};
      }
      if (isa<runtime::ReleaseBindingsOp>(op)) {
        control.release(inputs);
        continue;
      }
      auto occurrence = site(op, path);
      if (!valid)
        return {};
      if (auto reject = dyn_cast<exec::RejectOp>(op)) {
        control.reject(reject.getReason(), occurrence);
        return {{}, true};
      }
      auto *insertion = builder.getInsertionBlock();
      auto *previous = insertion->empty() ? nullptr : &insertion->back();
      Values outputs;
      auto outputTypes = types(step.outputs);
      bool terminal = false;
      if (!step.regions.empty()) {
        unsigned prefix = isa<exec::RangeOp>(op) ? 2 + step.outputs.size() : 1;
        Values unique;
        auto indices = captures(ArrayRef(inputs).drop_front(prefix), unique);
        SmallVector<func::FuncOp> regions;
        bool allStopped = true;
        for (auto original : step.regions) {
          bool stopped = false;
          auto generated =
              region(original, indices, unique, path, depth + 1, stopped);
          if (!generated)
            return {};
          regions.push_back(generated);
          allStopped &= stopped;
        }
        // A range can execute zero iterations. Only exhaustive branch/match
        // controls with no continuing arm eliminate the caller continuation.
        terminal = !isa<exec::RangeOp>(op) && allStopped;
        if (terminal) {
          outputTypes.clear();
          for (auto generated : regions)
            if (!discardStoppedPayload(generated))
              return {};
        }
        auto outline = [&](unsigned index) { return regions[index]; };
        if (isa<exec::TestOp>(op)) {
          outputs = control.conditional(inputs.front(), unique, outputTypes,
                                        occurrence, outline);
        } else if (auto match = dyn_cast<exec::MatchOp>(op)) {
          SmallVector<std::string> alternatives;
          for (Attribute value : match.getAlternatives())
            alternatives.push_back(cast<StringAttr>(value).str());
          outputs = control.match(inputs.front(), unique, outputTypes,
                                  alternatives, occurrence, outline);
        } else {
          outputs = control.loop(inputs[0], inputs[1],
                                 ArrayRef(inputs).slice(2, step.outputs.size()),
                                 unique, outputTypes, step.conditional,
                                 occurrence, outline);
        }
      } else {
        NamedAttrList attributes(op->getAttrs());
        attributes.set("site", builder.getStringAttr(occurrence));
        outputs = control.invoke(op->getName().getStringRef(), outputTypes,
                                 control.scoped(inputs), attributes.getAttrs());
      }
      if (!valid || (!terminal && outputs.size() != step.outputs.size())) {
        valid = false;
        return {};
      }
      record(op, previous ? previous->getNextNode() : &insertion->front());
      if (terminal) {
        // Required CFG terminator, unreachable after either stopped arm. It
        // is not attributed to a source occurrence or treated as a new effect.
        unreachable(control);
        return {{}, true};
      }
      for (auto [before, after] : zip(step.outputs, outputs))
        env[before] = after;
    }
    valid = false;
    return {};
  }

public:
  ScopedExpander(
      const SourceExecutionClosure &source, Operation *original,
      protocol_ir::ProtocolModuleOp target,
      const llvm::DenseMap<Operation *, func::FuncOp> *replacements = nullptr,
      mathematical::NumericalSelection *selection = nullptr,
      std::optional<CapacityCause> *capacity = nullptr,
      mathematical::RealizationWork *finiteWork = nullptr,
      MathematicalSelectionPolicy finitePolicy = {},
      const llvm::DenseSet<Operation *> *fixedBindings = nullptr,
      const mathematical::MathematicalRecipes &recipes =
          mathematical::mathematicalRecipes(),
      mathematical::RealizationTrace *trace = nullptr,
      bool orderedRetry = false)
      : source(source), symbols(original), target(target),
        builder(target.getContext(), this),
        remaining(selection ? selection->remainingCopy : defaultRemaining),
        remainingBytes(selection ? selection->remainingSiteBytes
                                 : defaultBytes),
        replacements(replacements), selection(selection), capacity(capacity),
        finiteWork(finiteWork), finitePolicy(finitePolicy),
        fixedBindings(fixedBindings), recipes(recipes), trace(trace),
        orderedRetry(orderedRetry) {
    if (replacements)
      for (const auto &replacement : *replacements)
        replacedDefinitions.insert(replacement.second);
    for (Operation &op : original->getRegion(0).front())
      if (auto name = SymbolTable::getSymbolName(&op))
        names.insert(name.getValue());
  }
  LogicalResult run(Operation *original) {
    // The input is independently admitted before any cloning or substitution.
    // Its non-execution declarations remain exact and in their original order.
    for (Operation &op : original->getRegion(0).front()) {
      auto function = dyn_cast<func::FuncOp>(op);
      if (replacedDefinitions.contains(&op))
        continue;
      if (!function || !isScopedExecutionFunction(function)) {
        if (!declaration(&op))
          return failure();
        builder.setInsertionPointToEnd(&target.getBody().front());
        IRMapping mapping;
        auto *copy = builder.clone(op, mapping);
        record(&op, copy);
        op.walk([&](Operation *nested) {
          if (nested != &op)
            record(nested, mapping.lookup(nested));
        });
        continue;
      }
      if (function->hasAttr("runtime.region"))
        continue;
      if (!declaration(function) ||
          !charge(function, function.getNumArguments()))
        return failure();
      root = function.getSymName().str();
      builder.setInsertionPointToEnd(&target.getBody().front());
      auto copied = func::FuncOp::create(builder, function.getLoc(), root,
                                         function.getFunctionType());
      copied->setAttrs(function->getAttrs());
      copied.addEntryBlock();
      builder.setInsertionPointToEnd(&copied.front());
      Environment env;
      for (auto [before, after] : zip(function.getArguments().drop_front(),
                                      copied.getArguments().drop_front()))
        env[before] = after;
      exec::ScopedExecutionBuilder control(builder, copied);
      body(function, std::move(env), control, {}, 0, false);
      if (!valid)
        return failure();
    }
    return success();
  }
};
} // namespace

OwningOpRef<ModuleOp>
expandScopedHelpers(ModuleOp source, std::vector<AlgorithmOrigin> *origins) {
  if (failed(zkc::admitStage(source)) || !hasSingleElement(*source.getBody()))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner)
    return {};
  auto closure = readSourceExecutionClosure(owner);
  if (!closure) {
    diagnostics::emit(owner.emitOpError(), closure.takeError());
    return {};
  }
  OwningOpRef<ModuleOp> candidate(ModuleOp::create(source.getLoc()));
  candidate->getOperation()->setAttrs(source->getAttrs());
  OpBuilder builder(candidate->getBodyRegion());
  auto target = protocol_ir::ProtocolModuleOp::create(
      builder, owner.getLoc(), owner.getProfileAttr(), mlir::ArrayAttr{});
  target->setAttrs(owner->getAttrs());
  target.getBody().push_back(new Block);
  if (failed(ScopedExpander(*closure, owner, target).run(owner)) ||
      failed(zkc::admitStage(*candidate)) ||
      failed(verifyScopedHelperExpansionPreserved(source, *candidate, origins)))
    return {};
  return candidate;
}
OwningOpRef<ModuleOp> substituteNumericalBodies(
    ModuleOp source,
    const llvm::DenseMap<Operation *, func::FuncOp> &replacements,
    mathematical::NumericalSelection &selection,
    std::optional<CapacityCause> *capacity) {
  llvm::TimeTraceScope timing("zkc.numerical-substitution");
  if (!hasSingleElement(*source.getBody()) ||
      !computation::chargeCopy(source, selection.remainingCopy, capacity))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner)
    return {};
  auto closure = readSourceExecutionClosure(owner);
  if (!closure) {
    diagnostics::emit(owner.emitOpError(), closure.takeError());
    return {};
  }
  for (const auto &[operation, function] : replacements) {
    if (!isa<exec::ComputeOp>(operation) ||
        operation->getParentOfType<protocol_ir::ProtocolModuleOp>() != owner ||
        function->getParentOp() != owner.getOperation() ||
        !isScopedExecutionFunction(function) ||
        function->hasAttr("runtime.region"))
      return {};
    auto compute = cast<exec::ComputeOp>(operation);
    auto selected = function;
    auto found = closure->bodies.find(selected.getSymName().str());
    if (!llvm::equal(selected.getArgumentTypes().drop_front(),
                     compute.getInputs().getTypes()) ||
        !llvm::equal(selected.getResultTypes(),
                     TypeRange{compute.getOutcome().getType()}) ||
        found == closure->bodies.end() || found->second.empty() ||
        !isa<exec::ReturnOp>(found->second.back().operation))
      return {};
  }
  OwningOpRef<ModuleOp> candidate(ModuleOp::create(source.getLoc()));
  candidate->getOperation()->setAttrs(source->getAttrs());
  OpBuilder builder(candidate->getBodyRegion());
  auto target = protocol_ir::ProtocolModuleOp::create(
      builder, owner.getLoc(), owner.getProfileAttr(), mlir::ArrayAttr{});
  target->setAttrs(owner->getAttrs());
  target.getBody().push_back(new Block);
  if (failed(ScopedExpander(*closure, owner, target, &replacements, &selection,
                            capacity)
                 .run(owner)))
    return {};
  return candidate;
}

OwningOpRef<ModuleOp>
prepareScopedFinite(ModuleOp source, mathematical::RealizationWork &work,
                    uint64_t &copy, uint64_t &siteBytes,
                    std::optional<CapacityCause> &capacity,
                    MathematicalSelectionPolicy policy,
                    const llvm::DenseSet<Operation *> *fixedBindings,
                    mathematical::NumericalSelection *selection,
                    mathematical::VerificationDecision *reported,
                    const mathematical::MathematicalRecipes &recipes,
                    mathematical::RealizationTrace *trace) {
  llvm::TimeTraceScope timing("zkc.finite-preparation");
  mathematical::RealizationScope scope(trace, "scoped-finite-preparation",
                                       source, policy, &work);
  if (failed(zkc::admitStage(source)) || !hasSingleElement(*source.getBody()))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  if (!owner)
    return {};
  auto closure = readSourceExecutionClosure(owner);
  if (!closure) {
    diagnostics::emit(owner.emitOpError(), closure.takeError());
    return {};
  }
  mathematical::NumericalSelection standalone(&work);
  auto &choices = selection ? *selection : standalone;
  bool orderedRetry = false;
  for (;;) {
    mathematical::RecipeConstructionWork construction(work);
    bool speculative = (policy.finiteBulk || policy.vectorReductionFusion) &&
                       choices.canSpeculate() && work.discardedRecipeCopy &&
                       work.discardedRecipeSiteBytes &&
                       construction.canDiscard(work);
    if (!speculative) {
      policy.finiteBulk = false;
      policy.vectorReductionFusion = false;
    }
    mathematical::RealizationScope attempt(trace, "scoped-finite-attempt",
                                           source, policy);
    attempt.propose(policy);
    auto incomingCopy = copy, incomingBytes = siteBytes;
    auto copyCeiling =
        speculative ? std::min(copy, work.discardedRecipeCopy) : copy;
    auto byteCeiling = speculative
                           ? std::min(siteBytes, work.discardedRecipeSiteBytes)
                           : siteBytes;
    copy = copyCeiling;
    siteBytes = byteCeiling;
    auto settle = llvm::scope_exit([&] {
      copy += incomingCopy - copyCeiling;
      siteBytes += incomingBytes - byteCeiling;
    });
    capacity.reset();
    mathematical::VerificationDecision outcome;
    auto propose = [&]() -> OwningOpRef<ModuleOp> {
      if (!computation::chargeCopy(source, copy, &capacity))
        return {};
      OwningOpRef<ModuleOp> candidate(ModuleOp::create(source.getLoc()));
      candidate->getOperation()->setAttrs(source->getAttrs());
      OpBuilder builder(candidate->getBodyRegion());
      auto target = protocol_ir::ProtocolModuleOp::create(
          builder, owner.getLoc(), owner.getProfileAttr(), mlir::ArrayAttr{});
      target->setAttrs(owner->getAttrs());
      target.getBody().push_back(new Block);
      choices.remainingCopy = copy;
      choices.remainingSiteBytes = siteBytes;
      auto result = ScopedExpander(*closure, owner, target, nullptr, &choices,
                                   &capacity, &work, policy, fixedBindings,
                                   recipes, trace, orderedRetry)
                        .run(owner);
      copy = choices.remainingCopy;
      siteBytes = choices.remainingSiteBytes;
      if (failed(result) || failed(zkc::admitStage(*candidate)) ||
          failed(verifyScopedFinitePreparation(source, *candidate, work, policy,
                                               &outcome, fixedBindings))) {
        choices.origins.clear();
        return {};
      }
      return candidate;
    };
    OwningOpRef<ModuleOp> candidate;
    if (speculative) {
      zkc::diagnostics::ScopedThreadDiagnosticHandler quiet(
          source.getContext(), [](Diagnostic &) { return success(); });
      candidate = propose();
    } else
      candidate = propose();
    if (reported)
      *reported = outcome;
    if (candidate) {
      attempt.publish();
      scope.publish(mathematical::PublicationBoundary::ReturnedCandidate);
      return candidate;
    }
    mathematical::DecisionCause cause = outcome;
    if (capacity)
      cause =
          mathematical::RequiredFailure{"scoped finite construction", capacity};
    attempt.discard(cause);
    scope.failure(cause);
    // A containing physical attempt owns its complete discard envelope. Do
    // not retry or transfer the same construction to a second reserve here.
    if (selection)
      return {};
    bool optionalCapacity =
        outcome.outcome ==
        mathematical::VerificationObservation::OptionalCapacity;
    if (!speculative || (!capacity && !optionalCapacity)) {
      if (speculative)
        diagnostics::emit(source.emitOpError(), "finite-preparation",
                          outcome.detail.empty()
                              ? "candidate construction refused"
                              : outcome.detail);
      return {};
    }
    // The optional proposal was not published. Transfer only its performed
    // construction to the discard reserve; matching and checking remain spent.
    auto copied = copyCeiling - copy, bytes = byteCeiling - siteBytes;
    if (copied > work.discardedRecipeCopy ||
        bytes > work.discardedRecipeSiteBytes || !construction.discard(work))
      return {};
    work.discardedRecipeCopy -= copied;
    work.discardedRecipeSiteBytes -= bytes;
    copy = copyCeiling;
    siteBytes = byteCeiling;
    policy.finiteBulk = false;
    policy.vectorReductionFusion = false;
    orderedRetry = true;
    attempt.retry(policy);
  }
}

} // namespace zkc::protocol

namespace zkc::mathematical {
OwningOpRef<ModuleOp> substituteScopedComputations(
    ModuleOp source,
    const llvm::DenseMap<Operation *, func::FuncOp> &replacements,
    NumericalSelection &selection, std::optional<CapacityCause> *capacity) {
  return protocol::substituteNumericalBodies(source, replacements, selection,
                                             capacity);
}
} // namespace zkc::mathematical
