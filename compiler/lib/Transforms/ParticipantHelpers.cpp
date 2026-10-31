#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/Execution.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Transforms/Algorithms.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol {
namespace {
protocol_ir::ProtocolModuleOp participantUnit(ModuleOp module) {
  if (!module || failed(admitStage(module)) ||
      !hasSingleElement(*module.getBody()))
    return {};
  auto owner =
      dyn_cast<protocol_ir::ProtocolModuleOp>(module.getBody()->front());
  return owner && owner.getProfile() == protocol_ir::Profile::Participant
             ? owner
             : protocol_ir::ProtocolModuleOp{};
}
bool helper(Operation *op) {
  auto function = dyn_cast<func::FuncOp>(op);
  return function && isScopedExecutionFunction(function);
}
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "algorithm-correspondence",
                           detail);
}
} // namespace

LogicalResult verifyParticipantHelperPruningPreserved(ModuleOp source,
                                                      ModuleOp candidate) {
  auto before = participantUnit(source), after = participantUnit(candidate);
  if (!before || !after ||
      source->getAttrDictionary() != candidate->getAttrDictionary() ||
      before->getAttrDictionary() != after->getAttrDictionary())
    return refuse(candidate, "helper pruning changed the participant context");
  // Admission checks every actual symbol use in the retained subject. Thus a
  // deleted helper cannot be invoked or named by a remaining declaration. No
  // producer liveness cache, chosen root set or claimed deletion is evidence.
  auto actual = after.getBody().front().begin();
  auto end = after.getBody().front().end();
  for (Operation &original : before.getBody().front()) {
    if (actual != end &&
        OperationEquivalence::isEquivalentTo(
            &original, &*actual, OperationEquivalence::IgnoreLocations)) {
      ++actual;
      continue;
    }
    if (!helper(&original))
      return refuse(after, "helper pruning changed a retained declaration");
  }
  if (actual != end)
    return refuse(after, "helper pruning added or changed a declaration");
  return success();
}

OwningOpRef<ModuleOp> pruneParticipantHelpers(ModuleOp source) {
  auto owner = participantUnit(source);
  if (!owner)
    return {};
  // The protocol unit is not a generic linker's export table. Its entries,
  // relations, bindings and projection records are all retained roots. Apply
  // the standard MLIR symbol-use graph only to scoped helper definitions.
  auto uses = SymbolTable::getSymbolUses(&owner.getBody());
  if (!uses) {
    (void)refuse(owner, "helper pruning cannot resolve all symbol uses");
    return {};
  }
  SymbolTableCollection symbols;
  llvm::DenseMap<Operation *, SmallVector<Operation *>> edges;
  uint64_t remaining = 1000000;
  for (const auto &use : *uses) {
    if (!remaining--) {
      (void)refuse(owner, "helper pruning exceeds the symbol-use work limit");
      return {};
    }
    auto *target =
        symbols.lookupNearestSymbolFrom(use.getUser(), use.getSymbolRef());
    if (!target) {
      (void)refuse(owner, "helper pruning encountered an unresolved symbol");
      return {};
    }
    auto *user = use.getUser();
    while (user->getParentOp() != owner)
      user = user->getParentOp();
    // Nested symbols live inside a retained declaration, never independently
    // in this elimination set.
    while (target->getParentOp() != owner)
      target = target->getParentOp();
    edges[user].push_back(target);
  }
  llvm::DenseSet<Operation *> live;
  SmallVector<Operation *> pending;
  for (Operation &op : owner.getBody().front())
    if (!helper(&op)) {
      live.insert(&op);
      pending.push_back(&op);
    }
  while (!pending.empty()) {
    auto *op = pending.pop_back_val();
    for (auto *used : edges[op])
      if (live.insert(used).second)
        pending.push_back(used);
  }
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  auto target =
      cast<protocol_ir::ProtocolModuleOp>(candidate->getBody()->front());
  SmallVector<Operation *> dead;
  for (auto [before, after] :
       zip(owner.getBody().front(), target.getBody().front()))
    if (helper(&before) && !live.contains(&before))
      dead.push_back(&after);
  for (auto *op : dead)
    op->erase();
  if (failed(verifyParticipantHelperPruningPreserved(source, *candidate)))
    return {};
  return candidate;
}
} // namespace zkc::protocol
