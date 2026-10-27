#include "../HelperNormalization.h"
#include "Support.h"
#include "mlir/IR/OperationSupport.h"
#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::computation {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(),
                           "computation-closure-correspondence", detail);
}
bool charge(Operation *op, uint64_t &remaining) {
  auto walk = op->walk([&](Operation *nested) {
    uint64_t cost = 1 + nested->getNumOperands() + nested->getNumResults();
    if (cost > remaining)
      return WalkResult::interrupt();
    remaining -= cost;
    return WalkResult::advance();
  });
  return !walk.wasInterrupted();
}
} // namespace
LogicalResult verifyDependencies(Operation *sourceOwner,
                                 mlir::ModuleOp candidate) {
  SymbolTable source(sourceOwner), target(candidate);
  auto entry = mathematical::getComputationEntry(candidate);
  if (!entry)
    return refuse(candidate, "missing public entry");
  uint64_t remaining = 1000000;
  llvm::DenseSet<Operation *> reachable;
  SmallVector<Operation *> pending{entry};
  while (!pending.empty()) {
    auto *current = pending.pop_back_val();
    if (!reachable.insert(current).second)
      continue;
    if (!charge(current, remaining))
      return refuse(candidate, "closure comparison work limit");
    auto uses = SymbolTable::getSymbolUses(current);
    if (!uses)
      return refuse(candidate, "cannot inspect dependency symbol uses");
    for (const auto &use : *uses) {
      auto reference = dyn_cast<FlatSymbolRefAttr>(use.getSymbolRef());
      if (!remaining || !reference)
        return refuse(candidate, "dependency reference or comparison limit");
      --remaining;
      auto *definition = target.lookup(reference.getValue());
      auto *original = source.lookup(reference.getValue());
      if (!definition || !original || definition == entry.getOperation() ||
          original->getName() != definition->getName())
        return refuse(candidate,
                      "symbol remapping changed a dependency identity");
      pending.push_back(definition);
    }
    if (current == entry.getOperation())
      continue;
    auto name = SymbolTable::getSymbolName(current);
    auto *original = name ? source.lookup(name.getValue()) : nullptr;
    if (!original || !charge(original, remaining) ||
        original->getAttrDictionary() != current->getAttrDictionary())
      return refuse(current, "dependency interface or preconditions changed");
    if (!OperationEquivalence::isEquivalentTo(
            original, current, OperationEquivalence::IgnoreLocations))
      return refuse(current, "actual helper computation differs");
  }
  for (auto &definition : *candidate.getBody())
    if (!reachable.contains(&definition))
      return refuse(&definition, "unit contains an unrelated dependency");
  return success();
}
LogicalResult verifyComputationClosure(Operation *sourceOwner,
                                       func::FuncOp sourceEntry,
                                       mlir::ModuleOp candidate) {
  auto target = mathematical::getComputationEntry(candidate);
  if (!target || !sourceEntry ||
      sourceEntry.getFunctionType() != target.getFunctionType())
    return refuse(candidate, "entry interface changed");
  uint64_t remaining = 1000000;
  if (!charge(sourceEntry, remaining) || !charge(target, remaining))
    return refuse(candidate, "entry comparison work limit");
  // Compare regions under actual positional SSA mapping. Name and visibility
  // belong to the moved entry carrier; every other attribute remains exact.
  NamedAttrList before(sourceEntry->getAttrs()), after(target->getAttrs());
  before.erase("sym_name");
  before.erase("sym_visibility");
  after.erase("sym_name");
  after.erase("sym_visibility");
  if (before.getDictionary(sourceEntry.getContext()) !=
          after.getDictionary(target.getContext()) ||
      !OperationEquivalence::isRegionEquivalentTo(
          &sourceEntry.getBody(), &target.getBody(),
          OperationEquivalence::IgnoreLocations))
    return refuse(candidate,
                  "entry operands, result coordinates or attributes changed");
  return verifyDependencies(sourceOwner, candidate);
}
} // namespace zkc::computation
