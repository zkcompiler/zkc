#include "Support.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::kernel {
namespace {
class Checker {
  protocol_ir::ProtocolModuleOp original, candidate;
  SymbolTable sourceSymbols, targetSymbols;
  MathematicalSelectionPolicy fallback;
  SymbolTableCollection symbols;
  llvm::DenseSet<Operation *> generatedBindings;
  uint64_t remaining = 1000000, remainingBytes = 16 * 1024 * 1024;
  LogicalResult refuse(Operation *op, StringRef reason) {
    return diagnostics::emit(op->emitOpError(),
                             "kernel-lowering-correspondence", reason);
  }
  bool charge(Operation *op) {
    uint64_t cost = 1 + op->getNumOperands() + op->getNumResults();
    if (cost > remaining)
      return false;
    remaining -= cost;
    return true;
  }
  LogicalResult block(Block &before, Block &after, IRMapping values,
                      ArrayRef<unsigned> ports = {},
                      std::optional<unsigned> forwarded = {}) {
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
    for (auto &op : before) {
      if (!charge(&op))
        return refuse(candidate, "comparison work limit");
      SmallVector<Value> inputs;
      for (auto value : op.getOperands()) {
        auto actual = values.lookupOrNull(value);
        if (!actual)
          return refuse(candidate, "lost an actual Local operand");
        inputs.push_back(actual);
      }
      if (auto call = dyn_cast<CallOp>(op)) {
        auto entry = resolve(call, symbols);
        auto policy = selectionPolicy(call, fallback);
        if (!entry || failed(policy))
          return refuse(&op, "invalid original numerical invocation");
        auto *begin = cursor;
        finite::VerificationResult outcome{finite::VerificationStatus::Mismatch,
                                           {}};
        auto outputs = verifyKernelRecipes(
            entry, candidate, call.getSite(), inputs, cursor, remaining,
            remainingBytes, *policy, {}, outcome);
        if (failed(outputs) || outputs->size() != call.getNumResults())
          return refuse(
              candidate,
              "actual Local recipes differ from the numerical closure");
        for (auto [source, actual] : zip(call.getResults(), *outputs)) {
          if (source.getType() != actual.getType())
            return refuse(candidate,
                          "numerical return coordinate changed type");
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
                              : std::nullopt)))
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
          MathematicalSelectionPolicy fallback)
      : original(original), candidate(candidate), sourceSymbols(original),
        targetSymbols(candidate), fallback(fallback) {}
  LogicalResult run() {
    if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
        original.getProfile() != protocol_ir::Profile::Exec)
      return refuse(candidate, "expected unchanged exec module contract");
    auto next = candidate.getBody().front().begin();
    for (auto &op : original.getBody().front()) {
      if (isa<ModuleOp>(op))
        continue;
      while (next != candidate.getBody().front().end()) {
        auto binding = dyn_cast<local::OperationBindingOp>(*next);
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
            !function.getBody().hasOneBlock() ||
            !after.getBody().hasOneBlock() ||
            failed(
                block(function.getBody().front(), after.getBody().front(), {})))
          return refuse(candidate, "Local function interface or body changed");
      } else if (!OperationEquivalence::isEquivalentTo(
                     &op, target, OperationEquivalence::IgnoreLocations))
        return refuse(candidate, "retained declaration or its order changed");
    }
    while (next != candidate.getBody().front().end()) {
      auto binding = dyn_cast<local::OperationBindingOp>(*next++);
      if (!binding || sourceSymbols.lookup(binding.getSymName()))
        return refuse(candidate, "unexpected extra declaration");
    }
    for (auto &op : candidate.getBody().front()) {
      if (isa<ModuleOp>(op))
        return refuse(candidate, "residual numerical unit");
      if (auto name = SymbolTable::getSymbolName(&op);
          name && !sourceSymbols.lookup(name) &&
          !generatedBindings.contains(&op))
        return refuse(&op, "unused or unaccounted generated declaration");
    }
    return success();
  }
};
} // namespace
LogicalResult verifyKernelLowering(mlir::ModuleOp original,
                                   mlir::ModuleOp candidate,
                                   MathematicalSelectionPolicy policy) {
  if (failed(verify(original)) || failed(verify(candidate)))
    return failure();
  if (original->getAttrDictionary() != candidate->getAttrDictionary() ||
      !hasSingleElement(*original.getBody()) ||
      !hasSingleElement(*candidate.getBody()))
    return diagnostics::emit(candidate.emitError(),
                             "kernel-lowering-correspondence",
                             "module shape changed");
  auto before =
      dyn_cast<protocol_ir::ProtocolModuleOp>(original.getBody()->front());
  auto after =
      dyn_cast<protocol_ir::ProtocolModuleOp>(candidate.getBody()->front());
  if (!before || !after)
    return failure();
  // Reconstruct a mathematical proposal, check its original helper/polynomial
  // meaning and frontier coordinates independently, then read the *actual*
  // candidate with the existing recipe checker. No executable emitter is run.
  auto normalized = prepareKernelLowering(original);
  if (!normalized)
    return diagnostics::emit(
        candidate.emitError(), "kernel-lowering-correspondence",
        "original normalization/frontier could not be checked");
  auto subject =
      cast<protocol_ir::ProtocolModuleOp>(normalized->getBody()->front());
  return Checker(subject, after, policy).run();
}
} // namespace zkc::kernel
