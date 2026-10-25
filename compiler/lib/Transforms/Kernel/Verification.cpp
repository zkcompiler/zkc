#include "../NumericalLowering.h"
#include "../RealizationTrace.h"
#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Transforms/Mathematical.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include <limits>

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
class Checker {
  protocol_ir::ProtocolModuleOp original, candidate;
  SymbolTable sourceSymbols, targetSymbols, originalDeclarations;
  MathematicalSelectionPolicy fallback;
  ArrayRef<std::pair<std::string, std::string>> selections;
  mathematical::RealizationWork &work;
  mathematical::VerificationDecision &outcome;
  bool maps;
  SymbolTableCollection symbols;
  llvm::DenseSet<Operation *> generatedBindings, consumedHelpers;
  llvm::DenseMap<Operation *, size_t> invocations;
  uint64_t &remaining, &remainingBytes;

  LogicalResult refuse(Operation *op, StringRef reason) {
    if (outcome.outcome !=
            mathematical::VerificationObservation::OptionalCapacity &&
        outcome.outcome !=
            mathematical::VerificationObservation::RequiredCapacity)
      outcome = {mathematical::VerificationObservation::Mismatch, reason.str()};
    return diagnostics::emit(op->emitOpError(),
                             maps ? "numerical-lowering-correspondence"
                                  : "kernel-lowering-correspondence",
                             reason);
  }
  bool charge(Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining) {
      remaining = 0;
      outcome = {mathematical::VerificationObservation::RequiredCapacity,
                 "numerical context comparison capacity"};
      return false;
    }
    remaining -= cost;
    return true;
  }
  LogicalResult mapCall(local::ApplyOp call, ValueRange inputs,
                        Operation *&cursor, IRMapping &values,
                        bool &consumedSum) {
    using namespace mathematical;
    auto map = sourceSymbols.lookup<algebra::MapRealizeOp>(call.getCallee());
    if (!map)
      return refuse(candidate, "unknown retained map declaration");
    auto policy = mapSelectionPolicy(map, fallback);
    auto eligible = eligibleMapSum(call, sourceSymbols, policy, selections);
    Operation *begin = cursor, *end = cursor, *last = nullptr;
    unsigned count = 0;
    // The concrete source call site owns this exact bounded generated path.
    // This determines the complete span independently of producer records.
    while (end) {
      if (!charge(end))
        return failure();
      auto expected = mapPayloadSite(map, call.getSite(), count,
                                     work.numericalCheckSiteBytes);
      if (!expected) {
        consumeError(expected.takeError());
        outcome = {VerificationObservation::RequiredCapacity,
                   "numerical site comparison capacity",
                   {},
                   realizationSubject(call)};
        return failure();
      }
      auto site = end->getAttrOfType<StringAttr>("site");
      if (!site || site.getValue() != *expected)
        break;
      auto reference = end->getAttrOfType<FlatSymbolRefAttr>("binding");
      auto binding =
          reference
              ? targetSymbols.lookup<runtime::BindingOp>(reference.getValue())
              : runtime::BindingOp();
      if (!binding ||
          (policy.numericalExpressions == NumericalExpressionMode::VectorOnly &&
           protocol::numericalContract(binding.getContract())))
        return refuse(candidate,
                      "native map expression is disabled or unbound");
      last = end;
      end = end->getNextNode();
      ++count;
    }
    unsigned guards = 0;
    for (bool row : map.getRowwise())
      if (row)
        guards += guards ? 3 : 1;
    if (count < guards)
      return refuse(candidate, "missing ordered map shape guards");
    Value output;
    if (count > guards) {
      if (!last || last->getNumResults() != 1)
        return refuse(candidate, "missing map payload result");
      output = last->getResult(0);
    }
    consumedSum = output && isa<algebra::FieldType>(output.getType());
    if (consumedSum && !eligible)
      return refuse(candidate,
                    "map/sum fusion is disabled or replacement is fixed");
    auto result =
        readMapPayload(map, inputs, consumedSum, begin, end, {}, targetSymbols,
                       generatedBindings, work.requiredMapChecking,
                       work.optionalMapChecking, outcome);
    outcome.subject = realizationSubject(call);
    outcome.invocation = std::numeric_limits<size_t>::max();
    if (failed(result)) {
      if (outcome.outcome == VerificationObservation::OptionalCapacity ||
          outcome.outcome == VerificationObservation::RequiredCapacity)
        return failure();
      return refuse(candidate, "map guards or actual formula differ");
    }
    auto *replaced = consumedSum ? call->getNextNode() : call.getOperation();
    if (replaced->getNumResults() != 1 ||
        replaced->getResult(0).getType() != (*result).getType())
      return refuse(candidate, "map result coordinate changed");
    values.map(replaced->getResult(0), *result);
    cursor = end;
    return success();
  }
  LogicalResult block(Block &before, Block &after, IRMapping values,
                      ArrayRef<unsigned> ports = {},
                      std::optional<unsigned> forwarded = {},
                      unsigned depth = 0) {
    if (depth > 64)
      return refuse(candidate, "Local block depth changed");
    if (ports.empty()) {
      if (before.getArgumentTypes() != after.getArgumentTypes())
        return refuse(candidate, "Local block interface changed");
      values.map(before.getArguments(), after.getArguments());
    } else {
      if (ports.size() != before.getNumArguments())
        return refuse(candidate, "Local capture layout changed");
      unsigned width = 0;
      for (auto [argument, port] : zip(before.getArguments(), ports)) {
        if (port >= after.getNumArguments() ||
            argument.getType() != after.getArgument(port).getType())
          return refuse(candidate, "Local capture type changed");
        values.map(argument, after.getArgument(port));
        width = std::max(width, port + 1);
      }
      if (width != after.getNumArguments())
        return refuse(candidate, "extra Local capture argument");
    }
    auto *cursor = after.empty() ? nullptr : &after.front();
    for (auto it = before.begin(); it != before.end(); ++it) {
      auto &op = *it;
      if (!charge(&op))
        return failure();
      SmallVector<Value> inputs;
      for (auto value : op.getOperands()) {
        auto actual = values.lookupOrNull(value);
        if (!actual)
          return refuse(candidate, "lost an actual Local operand");
        inputs.push_back(actual);
      }
      if (maps)
        if (auto call = dyn_cast<local::ApplyOp>(op)) {
          if (depth >= 64)
            return refuse(candidate, "retained map occurrence depth");
          bool consumedSum = false;
          if (failed(mapCall(call, inputs, cursor, values, consumedSum)))
            return failure();
          if (consumedSum)
            ++it;
          continue;
        }
      if (auto call = dyn_cast<CallOp>(op)) {
        auto entry = resolve(call, symbols);
        auto policy = effectiveSelectionPolicy(call, fallback);
        if (!entry || failed(policy))
          return refuse(&op, "invalid original numerical invocation");
        auto *begin = cursor;
        finite::VerificationResult result{finite::VerificationStatus::Mismatch,
                                          {}};
        finite::VerificationLimits limits;
        limits.sharedReader = &work.requiredFiniteChecking;
        limits.sharedComparison = &work.optionalFiniteChecking;
        auto outputs = verifyKernelRecipes(
            entry, candidate, call.getSite(), inputs, cursor, remaining,
            remainingBytes, *policy, limits, result);
        if (failed(outputs)) {
          outcome = mathematical::verificationDecision(result);
          outcome.invocation = invocations.lookup(call);
          if (outcome.outcome ==
                  mathematical::VerificationObservation::OptionalCapacity ||
              outcome.outcome ==
                  mathematical::VerificationObservation::RequiredCapacity)
            return failure();
          return refuse(candidate, "actual Kernel recipes differ");
        }
        if (outputs->size() != call.getNumResults())
          return refuse(candidate, "Kernel return arity changed");
        for (auto [source, actual] : zip(call.getResults(), *outputs)) {
          if (source.getType() != actual.getType())
            return refuse(candidate, "Kernel return coordinate changed type");
          values.map(source, actual);
        }
        for (auto *at = begin; at != cursor; at = at->getNextNode()) {
          if (!at)
            return refuse(candidate, "invalid recipe cursor");
          auto walk = at->walk([&](Operation *nested) {
            if (!charge(nested))
              return WalkResult::interrupt();
            if (auto reference =
                    nested->getAttrOfType<FlatSymbolRefAttr>("binding")) {
              auto *binding = targetSymbols.lookup(reference.getValue());
              if (!binding)
                return WalkResult::interrupt();
              if (!sourceSymbols.lookup(reference.getValue()))
                generatedBindings.insert(binding);
            }
            return WalkResult::advance();
          });
          if (walk.wasInterrupted())
            return refuse(candidate,
                          "recipe binding lookup or comparison limit");
        }
        continue;
      }
      bool control =
          isa<local::LocalIfOp, local::LocalForOp, local::LocalMatchOp>(op);
      bool loop = isa<local::LocalForOp>(op);
      unsigned prefix = loop ? 2 + op.getNumResults() : 1;
      SmallVector<unsigned> capturePorts;
      if (control || (forwarded &&
                      isa<local::LocalYieldOp, local::LocalConditionOp>(op))) {
        unsigned start = control ? prefix : inputs.size() - *forwarded;
        SmallVector<Value> canonical(inputs.begin(), inputs.begin() + start);
        llvm::DenseMap<Value, unsigned> seen;
        for (auto value : ArrayRef<Value>(inputs).drop_front(start)) {
          auto [found, inserted] = seen.try_emplace(value, canonical.size());
          if (inserted)
            canonical.push_back(value);
          capturePorts.push_back(found->second - start);
        }
        inputs = std::move(canonical);
      }
      if (!cursor || cursor->getName() != op.getName() ||
          cursor->getAttrDictionary() != op.getAttrDictionary() ||
          cursor->getResultTypes() != op.getResultTypes() ||
          cursor->getOperands() != ValueRange(inputs) ||
          cursor->getNumRegions() != op.getNumRegions())
        return refuse(candidate,
                      "ordered Local context, pin, site or operand changed");
      for (auto [a, b] : zip(op.getRegions(), cursor->getRegions())) {
        if (!hasSingleElement(a) || !hasSingleElement(b))
          return refuse(candidate, "structured Local control changed");
        SmallVector<unsigned> innerPorts;
        if (control) {
          unsigned start = a.front().getNumArguments() - capturePorts.size();
          for (unsigned i = 0; i < start; ++i)
            innerPorts.push_back(i);
          for (auto port : capturePorts)
            innerPorts.push_back(start + port);
        }
        if (failed(block(a.front(), b.front(), values, innerPorts,
                         loop ? std::optional<unsigned>(capturePorts.size())
                              : std::nullopt,
                         depth + 1)))
          return refuse(candidate, "structured Local control changed");
      }
      values.map(op.getResults(), cursor->getResults());
      cursor = cursor->getNextNode();
    }
    return cursor ? refuse(candidate, "candidate added Local work") : success();
  }

public:
  Checker(protocol_ir::ProtocolModuleOp original,
          protocol_ir::ProtocolModuleOp candidate,
          protocol_ir::ProtocolModuleOp unprepared,
          MathematicalSelectionPolicy fallback,
          ArrayRef<std::pair<std::string, std::string>> selections,
          mathematical::RealizationWork &work,
          mathematical::VerificationDecision &outcome, bool maps)
      : original(original), candidate(candidate), sourceSymbols(original),
        targetSymbols(candidate), originalDeclarations(unprepared),
        fallback(fallback), selections(selections), work(work),
        outcome(outcome), maps(maps), remaining(work.numericalContextChecking),
        remainingBytes(work.numericalCheckSiteBytes) {
    size_t invocation = 0;
    original.walk([&](CallOp call) { invocations[call] = invocation++; });
  }
  LogicalResult run() {
    if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
        original.getProfile() != protocol_ir::Profile::Exec)
      return refuse(candidate, "expected unchanged exec module contract");
    if (maps) {
      uint64_t expanded = 0;
      if (failed(
              algebra::collectMapHelpers(original, consumedHelpers, expanded)))
        return failure();
      if (expanded > remaining) {
        remaining = 0;
        outcome = {mathematical::VerificationObservation::RequiredCapacity,
                   "original map closure admission capacity"};
        return failure();
      }
      remaining -= expanded;
    }
    auto next = candidate.getBody().front().begin();
    for (auto &op : original.getBody().front()) {
      if (isa<mlir::ModuleOp>(op) || (maps && (isa<algebra::MapRealizeOp>(op) ||
                                               consumedHelpers.contains(&op))))
        continue;
      while (next != candidate.getBody().front().end()) {
        auto binding = dyn_cast<runtime::BindingOp>(*next);
        if (!binding || sourceSymbols.lookup(binding.getSymName()))
          break;
        ++next;
      }
      if (next == candidate.getBody().front().end())
        return refuse(candidate, "missing original declaration");
      auto *target = &*next++;
      if (auto function = dyn_cast<local::FuncOp>(op)) {
        auto after = dyn_cast<local::FuncOp>(target);
        if (!after ||
            function->getAttrDictionary() != after->getAttrDictionary() ||
            !function.getBody().hasOneBlock() || !after.getBody().hasOneBlock())
          return refuse(candidate, "Local declaration interface changed");
        if (failed(
                block(function.getBody().front(), after.getBody().front(), {})))
          return failure();
      } else {
        // Requests constrain replacement in the pinned mathematical subject;
        // the retained final Local declaration keeps the original attributes.
        Operation *expected = &op;
        if (auto binding = dyn_cast<runtime::BindingOp>(op))
          expected = originalDeclarations.lookup(binding.getSymName());
        if (!expected ||
            !OperationEquivalence::isEquivalentTo(
                expected, target, OperationEquivalence::IgnoreLocations))
          return refuse(candidate, "retained declaration or its order changed");
      }
    }
    while (next != candidate.getBody().front().end()) {
      auto binding = dyn_cast<runtime::BindingOp>(*next++);
      if (!binding || sourceSymbols.lookup(binding.getSymName()))
        return refuse(candidate, "unexpected extra declaration");
    }
    for (auto &op : candidate.getBody().front()) {
      auto name = SymbolTable::getSymbolName(&op);
      auto *source = name ? sourceSymbols.lookup(name) : nullptr;
      if (isa<mlir::ModuleOp>(op) ||
          (maps && (isa<algebra::MapRealizeOp>(op) ||
                    (source && consumedHelpers.contains(source)))))
        return refuse(candidate, "residual numerical declaration");
      if (name && !source && !generatedBindings.contains(&op))
        return refuse(&op, "unused or unaccounted generated declaration");
    }
    outcome = {mathematical::VerificationObservation::Verified, {}};
    return success();
  }
};

LogicalResult
checkLowering(mlir::ModuleOp original, mlir::ModuleOp candidate,
              MathematicalSelectionPolicy policy,
              ArrayRef<std::pair<std::string, std::string>> selections,
              mathematical::RealizationWork &work,
              mathematical::VerificationDecision &outcome, bool maps) {
  outcome = {mathematical::VerificationObservation::Mismatch,
             "numerical lowering differs"};
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return diagnostics::emit(candidate.emitError(),
                             maps ? "numerical-lowering-correspondence"
                                  : "kernel-lowering-correspondence",
                             "module shape changed");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after)
    return failure();
  OwningOpRef<mlir::ModuleOp> pinned, normalized;
  mlir::ModuleOp source = original;
  if (!selections.empty()) {
    if (!chargeCopy(original, work.numericalCheckCopy)) {
      outcome = {mathematical::VerificationObservation::RequiredCapacity,
                 "numerical source pinning copy capacity"};
      return failure();
    }
    pinned = cast<mlir::ModuleOp>(original->clone());
    auto root = cast<protocol_ir::ProtocolModuleOp>(pinned->getBody()->front());
    for (auto binding : root.getBody().front().getOps<runtime::BindingOp>())
      for (const auto &[name, implementation] : selections)
        if (binding.getSymName() == name)
          binding.setImplementation(implementation);
    source = *pinned;
  }
  bool hasKernels = false;
  source.walk([&](Operation *op) {
    hasKernels |= (mathematical::isComputationUnit(op) || isa<CallOp>(op));
  });
  if (hasKernels) {
    // Reconstruct and check mathematical normalization/frontier only. No
    // executable emitter, selected menu or producer receipt enters this edge.
    std::optional<CapacityCause> capacity;
    normalized =
        prepareKernelLowering(source, &work.numericalCheckCopy, &capacity);
    if (!normalized) {
      if (capacity)
        outcome = {mathematical::VerificationObservation::RequiredCapacity,
                   "numerical normalization copy capacity", capacity};
      return failure();
    }
    source = *normalized;
  }
  auto subject = cast<protocol_ir::ProtocolModuleOp>(source.getBody()->front());
  return Checker(subject, after, before, policy, selections, work, outcome,
                 maps)
      .run();
}
} // namespace
LogicalResult verifyKernelLowering(mlir::ModuleOp original,
                                   mlir::ModuleOp candidate,
                                   MathematicalSelectionPolicy policy) {
  mathematical::RealizationWork work;
  mathematical::VerificationDecision outcome;
  return checkLowering(original, candidate, policy, {}, work, outcome, false);
}
} // namespace zkc::kernel

namespace zkc::mathematical {
LogicalResult verifyNumericalLowering(
    mlir::ModuleOp original, mlir::ModuleOp candidate,
    MathematicalSelectionPolicy policy,
    ArrayRef<std::pair<std::string, std::string>> selections,
    RealizationWork *shared, VerificationDecision *reported) {
  RealizationWork standalone;
  VerificationDecision outcome;
  auto result =
      kernel::checkLowering(original, candidate, policy, selections,
                            shared ? *shared : standalone, outcome, true);
  if (reported)
    *reported = outcome;
  return result;
}
} // namespace zkc::mathematical
