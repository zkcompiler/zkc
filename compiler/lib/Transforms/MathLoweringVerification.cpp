#include "Kernel/Support.h"
#include "MathematicalSupport.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
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
  bool guard(local::GuardOp source, Operation *&cursor, Value condition) {
    auto branch = dyn_cast_or_null<local::LocalIfOp>(cursor);
    if (!branch || branch.getNumResults() ||
        branch.getInputs() != ValueRange{condition})
      return false;
    if (!hasSingleElement(branch.getThenRegion()) ||
        !hasSingleElement(branch.getElseRegion()))
      return false;
    auto &yes = branch.getThenRegion().front();
    auto &no = branch.getElseRegion().front();
    if (!hasSingleElement(yes) || !hasSingleElement(no))
      return false;
    auto yield = dyn_cast<local::LocalYieldOp>(yes.back());
    auto stop = dyn_cast<local::StopOp>(no.back());
    if (!yield || yield.getNumOperands() || !stop ||
        stop.getReason() != "reject" || stop.getSite() != source.getSite())
      return false;
    cursor = cursor->getNextNode();
    return true;
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
        auto call = dyn_cast_or_null<local::CallOp>(cursor);
        auto function = call ? dyn_cast_or_null<local::FuncOp>(
                                   symbols.lookup(call.getCallee()))
                             : local::FuncOp();
        if (!function || !generated.contains(function) ||
            !invoked.insert(function).second)
          return refuse(target,
                        "missing or reused calculation at its first demand");
        // Diagnose the existing one-calculation policy at the demand boundary.
        // Splitting a valid calculation changes local invocations and finite
        // costs.
        if (!sourceGuard) {
          auto next = dyn_cast_or_null<local::CallOp>(call->getNextNode());
          auto nextFunction = next ? dyn_cast_or_null<local::FuncOp>(
                                         symbols.lookup(next.getCallee()))
                                   : local::FuncOp();
          if (nextFunction && generated.contains(nextFunction))
            return refuse(call, "multiple calculations at one cut");
        }
        if (sourceGuard && call.getSite() != sourceGuard.getSite())
          return refuse(call, "guard invocation changed its occurrence");
        llvm::DenseMap<Value, Value> localValues;
        llvm::DenseSet<Value> usedCaptures;
        for (auto [input, argument] :
             zip(call.getInputs(), function.getArguments())) {
          auto value = sourceValues.lookup(input);
          if (!value || !localValues.try_emplace(value, argument).second)
            return refuse(call, "calculation changed or duplicated a capture");
        }
        auto lookup = [&](Value value) -> Value {
          auto mapped = localValues.lookup(value);
          if (mapped && isa<BlockArgument>(mapped))
            usedCaptures.insert(mapped);
          return mapped;
        };
        auto *instruction = &function.getBody().front().front();
        if (!needed.empty()) {
          auto kernelCall = dyn_cast<kernel::CallOp>(instruction);
          auto entry = kernelCall ? kernel::resolve(kernelCall, kernelSymbols)
                                  : func::FuncOp();
          auto unit = entry ? dyn_cast<kernel::ModuleOp>(entry->getParentOp())
                            : kernel::ModuleOp();
          if (!unit || !generatedKernels.insert(unit).second ||
              sourceSymbols.lookup(unit.getSymName()) ||
              kernelCall.getInputs() != function.getArguments() ||
              failed(kernel::verifyDependencies(before, unit)))
            return refuse(call, "missing or changed actual numerical closure");
          for (auto &value : localValues) {
            auto argument = dyn_cast<BlockArgument>(value.second);
            if (!argument || argument.getOwner() != &function.getBody().front())
              return refuse(call, "invalid capture mapping");
            value.second = entry.getArgument(argument.getArgNumber());
          }
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
          if (any_of(kernelCall.getResults(),
                     [](Value value) { return value.use_empty(); }))
            return refuse(call, "unused extra numerical output");
          auto returned = dyn_cast_or_null<func::ReturnOp>(mathematics);
          if (!returned || returned->getNextNode() ||
              returned.getNumOperands() != kernelCall.getNumResults())
            return refuse(
                call, "numerical entry contains extra work or changed outputs");
          // The entry's actual return operands determine the wrapper values.
          // This detects same-typed result permutations and hidden/lost
          // escapes.
          llvm::DenseMap<Value, Value> returnedValues;
          for (auto [value, result] :
               zip(returned.getOperands(), kernelCall.getResults()))
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
          instruction = kernelCall->getNextNode();
        }
        if (sourceGuard && !guard(sourceGuard, instruction,
                                  lookup(sourceGuard.getCondition())))
          return refuse(call,
                        "calculation changed the guard condition or rejection");
        auto returned = dyn_cast_or_null<local::ReturnOp>(instruction);
        if (!returned || instruction->getNextNode() ||
            usedCaptures.size() != call.getNumOperands())
          return refuse(call,
                        "calculation contains extra work or unused captures");
        llvm::DenseMap<Value, Value> results;
        for (auto *op : needed)
          for (Value result : op->getResults())
            if (!mathematical::isFormalType(result.getType()))
              results[localValues.lookup(result)] = result;
        llvm::DenseSet<Value> exported;
        for (auto [value, output] :
             zip(returned.getInputs(), call.getResults())) {
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
      auto local = dyn_cast<local::FuncOp>(function);
      if (!local || !hasSingleElement(local.getBody()))
        return refuse(record, "calculation must have one local body");
      Builder builder(after.getContext());
      auto origin = builder.getArrayAttr(
          {builder.getStringAttr(ref.getValue()), builder.getArrayAttr({})});
      const StringRef identityAttributes[] = {"sym_name", "function_type",
                                              "logical_origin"};
      if (function->getAttrs().size() != std::size(identityAttributes) ||
          !all_of(function->getAttrs(),
                  [&](NamedAttribute attribute) {
                    return is_contained(identityAttributes,
                                        attribute.getName().getValue());
                  }) ||
          function->getAttr("logical_origin") != origin)
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
          !generatedKernels.contains(&definition))
        return refuse(&definition, "lowering added an untracked declaration");
    }
    llvm::DenseMap<Operation *, unsigned> uses;
    after.walk([&](local::CallOp call) {
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
