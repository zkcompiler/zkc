#include "Kernel/Support.h"
#include "NumericalSelection.h"
#include "ScopedFinite.h"
#include "ScopedPreparation.h"
#include "ScopedSubstitution.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Data/IR/DataAttrs.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringSet.h"

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
class ScopedExpander {
  const SourceExecutionClosure &source;
  SymbolTable symbols;
  protocol_ir::ProtocolModuleOp target;
  OpBuilder builder;
  llvm::StringSet<> names;
  unsigned nextRegion = 0;
  unsigned definitions = 0;
  uint64_t defaultRemaining = 100000, defaultBytes = 16 * 1024 * 1024;
  uint64_t &remaining, &remainingBytes;
  const llvm::DenseMap<Operation *, func::FuncOp> *replacements;
  mathematical::NumericalSelection *selection;
  std::optional<CapacityCause> *capacity;
  mathematical::RealizationWork *finiteWork;
  llvm::DenseSet<Operation *> replacedDefinitions;

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
    if (++definitions <= 4096)
      return true;
    if (capacity)
      *capacity = CapacityCause{WorkOwner::AlgorithmExpansion, 1, 0};
    diagnostics::emit(op->emitOpError(), "algorithm-expansion-limit",
                      "expanded definition limit");
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
    for (const auto &step : steps) {
      auto *op = step.operation;
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
        MathematicalSelectionPolicy ordered;
        ordered.finiteBulk = false;
        auto result = finite::realizeScopedExpression(
            op, inputs, builder, control, callback, *finiteWork, ordered,
            nullptr, occurrence, &budget);
        if (failed(result) || result->size() != step.outputs.size()) {
          if (capacity && cause)
            *capacity = cause;
          valid = false;
          return {};
        }
        for (auto [before, after] : zip(step.outputs, *result))
          env[before] = after;
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
      mathematical::RealizationWork *finiteWork = nullptr)
      : source(source), symbols(original), target(target),
        builder(target.getContext()),
        remaining(selection ? selection->remainingCopy : defaultRemaining),
        remainingBytes(selection ? selection->remainingSiteBytes
                                 : defaultBytes),
        replacements(replacements), selection(selection), capacity(capacity),
        finiteWork(finiteWork) {
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
  if (failed(verify(source)) || !hasSingleElement(*source.getBody()))
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
  auto target = protocol_ir::ProtocolModuleOp::create(builder, owner.getLoc(),
                                                      owner.getProfileAttr());
  target->setAttrs(owner->getAttrs());
  target.getBody().push_back(new Block);
  if (failed(ScopedExpander(*closure, owner, target).run(owner)) ||
      failed(verify(*candidate)) ||
      failed(verifyScopedHelperExpansionPreserved(source, *candidate, origins)))
    return {};
  return candidate;
}
OwningOpRef<ModuleOp> substituteNumericalBodies(
    ModuleOp source,
    const llvm::DenseMap<Operation *, func::FuncOp> &replacements,
    mathematical::NumericalSelection &selection,
    std::optional<CapacityCause> *capacity) {
  if (!hasSingleElement(*source.getBody()) ||
      !kernel::chargeCopy(source, selection.remainingCopy, capacity))
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
  auto target = protocol_ir::ProtocolModuleOp::create(builder, owner.getLoc(),
                                                      owner.getProfileAttr());
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
                    std::optional<CapacityCause> &capacity) {
  if (failed(verify(source)) || !hasSingleElement(*source.getBody()) ||
      !kernel::chargeCopy(source, copy, &capacity))
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
  auto target = protocol_ir::ProtocolModuleOp::create(builder, owner.getLoc(),
                                                      owner.getProfileAttr());
  target->setAttrs(owner->getAttrs());
  target.getBody().push_back(new Block);
  mathematical::NumericalSelection budgets;
  budgets.remainingCopy = copy;
  budgets.remainingSiteBytes = siteBytes;
  auto result = ScopedExpander(*closure, owner, target, nullptr, &budgets,
                               &capacity, &work)
                    .run(owner);
  copy = budgets.remainingCopy;
  siteBytes = budgets.remainingSiteBytes;
  if (failed(result) || failed(verify(*candidate)) ||
      failed(verifyScopedFinitePreparation(source, *candidate, work)))
    return {};
  return candidate;
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
