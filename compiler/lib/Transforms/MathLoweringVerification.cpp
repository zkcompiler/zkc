#include "Kernel/Support.h"
#include "MathematicalSupport.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Mathematical.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::mathematical {
namespace {
// Match participant demand cuts and their unchanged ordered context. Numerical
// realization is independently checked at the Kernel boundary.
class LoweringVerifier {
  protocol_ir::ProtocolModuleOp before, after;
  llvm::DenseSet<Operation *> generated, invoked, generatedKernels;
  SymbolTableCollection kernelSymbols;
  SymbolTable sourceSymbols, symbols;
  size_t remaining = 1000000;
  bool batching = true;
  std::optional<protocol::SourceExecutionClosure> closure;
  llvm::DenseSet<Operation *> generatedRegions;
  LogicalResult refuse(Operation *op, StringRef detail) {
    return diagnostics::emit(op->emitOpError(),
                             "mathematical-lowering-preservation", detail);
  }
  bool charge(size_t amount = 1) {
    if (amount > remaining)
      return false;
    remaining -= amount;
    return true;
  }
  bool guard(local::GuardOp source, const protocol::SourceExecutionStep &step,
             Value condition) {
    if (!isa<exec::TestOp>(step.operation) || !step.outputs.empty() ||
        ValueRange(step.inputs) != ValueRange{condition} ||
        step.regions.size() != 2)
      return false;
    func::FuncOp yesRegion = step.regions[0], noRegion = step.regions[1];
    for (auto function : {yesRegion, noRegion}) {
      if (sourceSymbols.lookup(function.getSymName()) ||
          !generatedRegions.insert(function).second)
        return false;
    }
    const auto &yes = closure->bodies.at(yesRegion.getSymName().str());
    const auto &no = closure->bodies.at(noRegion.getSymName().str());
    if (yes.size() != 1 || no.size() != 1 ||
        !isa<exec::CompleteOp>(yes[0].operation) || !yes[0].inputs.empty())
      return false;
    auto stop = dyn_cast<exec::RejectOp>(no[0].operation);
    return stop && stop.getReason() == "reject" &&
           stop.getSite() == source.getSite();
  }

  LogicalResult participant(protocol_ir::ParticipantOp source,
                            protocol_ir::ParticipantOp target) {
    if (source->getAttrDictionary() != target->getAttrDictionary())
      return refuse(target, "lowering changed the participant interface");
    return block(source.getBody().front(), target.getBody().front(), target);
  }
  LogicalResult block(Block &original, Block &candidate, Operation *target) {
    if (original.getArgumentTypes() != candidate.getArgumentTypes() ||
        original.empty() || candidate.empty())
      return refuse(target, "lowering changed a region interface");
    llvm::DenseMap<Value, Value> participantValues;
    llvm::DenseMap<Value, Value> sourceValues;
    for (auto [a, b] : zip(original.getArguments(), candidate.getArguments())) {
      participantValues[a] = b;
      sourceValues[b] = a;
    }
    llvm::DenseMap<Operation *, unsigned> order;
    llvm::DenseSet<Value> realized;
    unsigned index = 0;
    for (auto &op : original)
      order[&op] = index++;
    // Without batching, every operation some action demands is expected
    // before the first action that follows it.
    llvm::DenseSet<Operation *> demanded;
    if (!batching) {
      SmallVector<Value> pending;
      for (auto &action : original)
        if (!isTotal(&action))
          append_range(pending, action.getOperands());
      while (!pending.empty()) {
        auto value = pending.pop_back_val();
        if (!charge())
          return refuse(target, "lowering comparison work limit exceeded");
        auto *definition = value.getDefiningOp();
        if (!definition || !isTotal(definition) ||
            !demanded.insert(definition).second)
          continue;
        append_range(pending, definition->getOperands());
      }
    }
    auto *cursor = &candidate.front();
    for (auto &action : original) {
      if (isTotal(&action))
        continue;
      SmallVector<Operation *> needed;
      SmallVector<Value> pending;
      if (batching) {
        append_range(pending, action.getOperands());
      } else {
        for (auto &op : original) {
          if (&op == &action)
            break;
          if (!charge())
            return refuse(target, "lowering comparison work limit exceeded");
          if (demanded.contains(&op))
            for (auto value : op.getResults())
              if (!mathematical::isFormalType(value.getType()) &&
                  !realized.contains(value))
                pending.push_back(value);
        }
      }
      // Concrete values are computed once; formal descriptors may be rebuilt
      // for later consumers without introducing physical ports or work.
      llvm::DenseSet<Operation *> visited;
      while (!pending.empty()) {
        auto value = pending.pop_back_val();
        if (!charge())
          return refuse(target, "lowering comparison work limit exceeded");
        auto *definition = value.getDefiningOp();
        if (!definition || !isTotal(definition) ||
            (!mathematical::isFormalType(value.getType()) &&
             realized.contains(value)) ||
            !visited.insert(definition).second)
          continue;
        needed.push_back(definition);
        append_range(pending, definition->getOperands());
      }
      llvm::sort(needed, [&](Operation *a, Operation *b) {
        return order[a] < order[b];
      });
      auto sourceGuard = dyn_cast<local::GuardOp>(action);
      if (!needed.empty() || sourceGuard) {
        auto call = dyn_cast_or_null<protocol_ir::LocalCallOp>(cursor);
        auto function = call ? dyn_cast_or_null<func::FuncOp>(
                                   symbols.lookup(call.getCallee()))
                             : func::FuncOp();
        if (!function || !generated.contains(function) ||
            !invoked.insert(function).second)
          return refuse(target,
                        "missing or reused calculation at its first demand");
        // Diagnose the existing one-calculation policy at the demand boundary.
        // Splitting a valid calculation changes local invocations and finite
        // costs.
        if (!sourceGuard) {
          auto next =
              dyn_cast_or_null<protocol_ir::LocalCallOp>(call->getNextNode());
          auto nextFunction = next ? dyn_cast_or_null<func::FuncOp>(
                                         symbols.lookup(next.getCallee()))
                                   : func::FuncOp();
          if (nextFunction && generated.contains(nextFunction))
            return refuse(call, "multiple calculations at one cut");
        }
        if (sourceGuard && call.getSite() != sourceGuard.getSite())
          return refuse(call, "guard invocation changed its occurrence");
        llvm::DenseMap<Value, Value> localValues;
        llvm::DenseSet<Value> usedCaptures;
        llvm::DenseSet<Value> captureArguments;
        for (auto [input, argument] :
             zip(call.getInputs(), function.getArguments().drop_front())) {
          auto value = sourceValues.lookup(input);
          if (!value || !localValues.try_emplace(value, argument).second)
            return refuse(call, "calculation changed or duplicated a capture");
          captureArguments.insert(argument);
        }
        auto lookup = [&](Value value) -> Value {
          auto mapped = localValues.lookup(value);
          if (mapped && captureArguments.contains(mapped))
            usedCaptures.insert(mapped);
          return mapped;
        };
        const auto &steps = closure->bodies.at(function.getSymName().str());
        unsigned instruction = 0;
        if (!needed.empty()) {
          if (steps.empty())
            return refuse(call, "missing mathematical invocation");
          const auto &step = steps[instruction];
          auto kernelCall = dyn_cast<exec::ComputeOp>(step.operation);
          auto entry = kernelCall ? kernelCall.resolveCallee(kernelSymbols)
                                  : func::FuncOp();
          auto unit = entry ? dyn_cast<mlir::ModuleOp>(entry->getParentOp())
                            : mlir::ModuleOp();
          if (!unit || !generatedKernels.insert(unit).second ||
              sourceSymbols.lookup(SymbolTable::getSymbolName(unit)) ||
              kernelCall.getInputs() != function.getArguments().drop_front() ||
              failed(kernel::verifyDependencies(before, unit)))
            return refuse(call, "missing or changed actual numerical closure");
          for (auto &value : localValues) {
            auto argument = dyn_cast<BlockArgument>(value.second);
            if (!argument || argument.getOwner() != &function.getBody().front())
              return refuse(call, "invalid capture mapping");
            value.second = entry.getArgument(argument.getArgNumber() - 1);
          }
          captureArguments.clear();
          captureArguments.insert(entry.getArguments().begin(),
                                  entry.getArguments().end());
          auto *mathematics = &entry.front().front();
          for (auto *op : needed) {
            if (!charge(1 + op->getNumOperands() + op->getNumResults()))
              return refuse(call, "logical comparison work limit");
            auto dependencies = operandDependencies(op, 0);
            if (failed(dependencies) ||
                dependencies->size() != op->getNumOperands())
              return refuse(call, "incomplete numerical operand dependencies");
            for (auto [index, operand] : enumerate(*dependencies))
              if (index != operand)
                return refuse(call, "numerical dependency ordering changed");
            SmallVector<Value> inputs;
            for (auto operand : op->getOperands()) {
              auto value = lookup(operand);
              if (!value)
                return refuse(call,
                              "calculation lost a mathematical dependency");
              inputs.push_back(value);
            }
            NamedAttrList sourceAttrs(op->getAttrs());
            sourceAttrs.erase("site");
            if (!mathematics || mathematics->getName() != op->getName() ||
                mathematics->getAttrDictionary() !=
                    sourceAttrs.getDictionary(after.getContext()) ||
                mathematics->getOperands() != ValueRange(inputs) ||
                mathematics->getResultTypes() != op->getResultTypes() ||
                mathematics->getNumRegions())
              return refuse(
                  call,
                  "actual numerical operation, operands or attributes differ");
            for (auto [source, actual] :
                 zip(op->getResults(), mathematics->getResults())) {
              localValues[source] = actual;
              if (!mathematical::isFormalType(source.getType()))
                realized.insert(source);
            }
            mathematics = mathematics->getNextNode();
          }
          if (any_of(step.outputs,
                     [](Value value) { return value.use_empty(); }))
            return refuse(call, "unused extra numerical output");
          auto returned = dyn_cast_or_null<func::ReturnOp>(mathematics);
          if (!returned || returned->getNextNode() ||
              returned.getNumOperands() != step.outputs.size())
            return refuse(
                call, "numerical entry contains extra work or changed outputs");
          // The entry's actual return operands determine the wrapper values.
          // This detects same-typed result permutations and hidden/lost
          // escapes.
          llvm::DenseMap<Value, Value> returnedValues;
          for (auto [value, result] : zip(returned.getOperands(), step.outputs))
            if (!returnedValues.try_emplace(value, result).second)
              return refuse(call, "duplicated numerical return coordinate");
          if (sourceGuard) {
            auto value = localValues.lookup(sourceGuard.getCondition());
            if (isa_and_nonnull<BlockArgument>(value))
              usedCaptures.insert(value);
          }
          for (auto &value : localValues)
            if (auto actual = returnedValues.lookup(value.second))
              value.second = actual;
          ++instruction;
        }
        if (sourceGuard) {
          if (instruction >= steps.size() ||
              !guard(sourceGuard, steps[instruction++],
                     lookup(sourceGuard.getCondition())))
            return refuse(
                call, "calculation changed the guard condition or rejection");
        }
        if (instruction >= steps.size() ||
            !isa<exec::ReturnOp>(steps[instruction].operation) ||
            instruction + 1 != steps.size() ||
            usedCaptures.size() != call.getNumOperands())
          return refuse(call,
                        "calculation contains extra work or unused captures");
        auto returned = cast<exec::ReturnOp>(steps[instruction].operation);
        llvm::DenseMap<Value, Value> results;
        for (auto *op : needed)
          for (Value result : op->getResults())
            if (!mathematical::isFormalType(result.getType()))
              results[localValues.lookup(result)] = result;
        llvm::DenseSet<Value> exported;
        for (auto [value, output] :
             zip(returned.getValues(), call.getResults())) {
          auto originalValue = results.lookup(value);
          if (!originalValue || !exported.insert(originalValue).second ||
              output.use_empty())
            return refuse(call, "calculation changed or duplicated a result");
          participantValues[originalValue] = output;
          sourceValues[output] = originalValue;
        }
        cursor = cursor->getNextNode();
      }
      if (sourceGuard)
        continue;
      if (!cursor || cursor->getName() != action.getName() ||
          cursor->getAttrDictionary() != action.getAttrDictionary() ||
          cursor->getOperandTypes() != action.getOperandTypes() ||
          cursor->getResultTypes() != action.getResultTypes())
        return refuse(target, "lowering changed ordered participant actions");
      for (auto [a, b] : zip(action.getOperands(), cursor->getOperands()))
        if (participantValues.lookup(a) != b)
          return refuse(cursor, "lowering changed an action operand");
      if (auto loop = dyn_cast<protocol_ir::ProtocolLoopOp>(action)) {
        auto lowered = cast<protocol_ir::ProtocolLoopOp>(cursor);
        if (failed(block(loop.getBody().front(), lowered.getBody().front(),
                         cursor)))
          return failure();
      }
      for (auto [a, b] : zip(action.getResults(), cursor->getResults())) {
        participantValues[a] = b;
        sourceValues[b] = a;
      }
      cursor = cursor->getNextNode();
    }
    return cursor ? refuse(target, "lowering added a participant action")
                  : success();
  }

public:
  LoweringVerifier(protocol_ir::ProtocolModuleOp before,
                   protocol_ir::ProtocolModuleOp after, bool batching)
      : before(before), after(after), sourceSymbols(before), symbols(after),
        batching(batching) {}
  LogicalResult run() {
    if (before.getProfile() != protocol_ir::Profile::Participant ||
        after.getProfile() != protocol_ir::Profile::Exec)
      return refuse(after, "expected 'participant' to 'exec' profiles");
    // Formation already bounded types, attributes and regions. Account for
    // operations and operand edges across the whole pair before inspecting it.
    for (auto unit : {before, after}) {
      auto walk = unit.walk([&](Operation *op) {
        return charge(1 + op->getNumOperands() + op->getNumResults())
                   ? WalkResult::advance()
                   : WalkResult::interrupt();
      });
      if (walk.wasInterrupted())
        return refuse(after, "lowering comparison work limit exceeded");
    }
    auto admitted = protocol::readSourceExecutionClosure(after);
    if (!admitted)
      return diagnostics::emit(after.emitOpError(), admitted.takeError());
    closure = std::move(*admitted);
    auto records = after.getBody().front().getOps<protocol_ir::ProjectionOp>();
    if (!hasSingleElement(records))
      return refuse(after, "lowering requires one projection record");
    auto record = *records.begin();
    // Module verification already ties every (participant, callee, site) record
    // to exactly one invocation. This check owns the frozen-source recipe.
    for (auto item : record.getCalculations()) {
      auto ref = cast<DictionaryAttr>(item).getAs<FlatSymbolRefAttr>("callee");
      auto *function = symbols.lookup(ref.getValue());
      if (!function || !generated.insert(function).second)
        return refuse(record, "calculation callee is not unique");
      if (sourceSymbols.lookup(ref.getValue()))
        return refuse(record, "calculation callee must be fresh");
      auto local = dyn_cast<func::FuncOp>(function);
      if (!local || !protocol::isScopedExecutionFunction(local))
        return refuse(record, "calculation must have an admitted scoped body");
      Builder builder(after.getContext());
      auto origin = builder.getArrayAttr(
          {builder.getStringAttr(ref.getValue()), builder.getArrayAttr({})});
      const StringRef identityAttributes[] = {"sym_name", "function_type",
                                              "runtime.origin", "no_inline"};
      if (function->getAttrs().size() != std::size(identityAttributes) ||
          !all_of(function->getAttrs(),
                  [&](NamedAttribute attribute) {
                    return is_contained(identityAttributes,
                                        attribute.getName().getValue());
                  }) ||
          function->getAttr("runtime.origin") != origin)
        return refuse(function, "calculation changed its generated identity");
    }
    unsigned count = 0;
    for (auto original :
         before.getBody().front().getOps<protocol_ir::ParticipantOp>()) {
      auto candidate = dyn_cast_or_null<protocol_ir::ParticipantOp>(
          symbols.lookup(original.getSymName()));
      if (!candidate)
        return refuse(after, "lowering lost a participant");
      if (failed(participant(original, candidate)))
        return failure();
      ++count;
    }
    if (count !=
            llvm::range_size(
                after.getBody().front().getOps<protocol_ir::ParticipantOp>()) ||
        generated.size() != invoked.size())
      return refuse(after,
                    "lowering added participants or unused calculations");
    // Only outlined functions and bindings used by their recipes may extend
    // the frozen symbol table. Even unused executable declarations affect
    // later admission and exported artifacts.
    llvm::DenseSet<Operation *> recipeBindings;
    for (auto *function : generated)
      function->walk([&](Operation *op) {
        if (auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding"))
          recipeBindings.insert(symbols.lookup(reference.getValue()));
      });
    for (auto &definition : after.getBody().front()) {
      auto name = SymbolTable::getSymbolName(&definition);
      if (name && !sourceSymbols.lookup(name) &&
          !generated.contains(&definition) &&
          !recipeBindings.contains(&definition) &&
          !generatedKernels.contains(&definition) &&
          !generatedRegions.contains(&definition))
        return refuse(&definition, "lowering added an untracked declaration");
    }
    llvm::DenseMap<Operation *, unsigned> uses;
    after.walk([&](protocol_ir::LocalCallOp call) {
      auto *callee = symbols.lookup(call.getCallee());
      if (generated.contains(callee))
        ++uses[callee];
    });
    for (auto *function : generated)
      if (uses.lookup(function) != 1)
        return refuse(function, "calculation must have exactly one invocation");
    return success();
  }
};
} // namespace
LogicalResult verifyMathLowering(protocol_ir::ProtocolModuleOp original,
                                 protocol_ir::ProtocolModuleOp candidate,
                                 bool batching) {
  return LoweringVerifier(original, candidate, batching).run();
}
} // namespace zkc::mathematical
