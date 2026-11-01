#include "zkc/Transforms/EndpointClosure.h"
#include "mlir/IR/OperationSupport.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Admission.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
using namespace llvm;
using namespace mlir;
namespace zkc {
namespace {
namespace pir = protocol_ir;
constexpr unsigned workLimit = 1000000;
// This inventory is an ephemeral read of the actual source, never a supplied
// certificate or a mutable graph. A shell is retained solely for a nested path.
struct Inventory {
  llvm::DenseSet<Operation *> definitions, shells;
  SmallVector<Operation *> pending;
  unsigned work = 0;
  bool charge() { return ++work <= workLimit; }
  void demand(Operation *op, Operation *root) {
    if (definitions.insert(op).second)
      pending.push_back(op);
    for (auto *parent = op->getParentOp(); parent && parent != root;
         parent = parent->getParentOp())
      shells.insert(parent);
  }
};
Expected<pir::ProtocolModuleOp> sourceRoot(ModuleOp source) {
  if (!source || source->getNumRegions() != 1 ||
      !hasSingleElement(source.getBodyRegion()) ||
      !hasSingleElement(*source.getBody()))
    return error("endpoint-source", "expected one closed Exec module");
  auto root = dyn_cast<pir::ProtocolModuleOp>(&source.getBody()->front());
  if (!root || failed(admitStage(source)) ||
      root.getProfile() != pir::Profile::Exec)
    return error("endpoint-source", "source is not admitted closed Exec");
  return root;
}
SmallVector<Attribute> selectedTargets(pir::ProtocolEntryOp entry,
                                       StringRef role) {
  SmallVector<Attribute> targets;
  for (auto item : entry.getTargets()) {
    auto pair = cast<ArrayAttr>(item);
    if (cast<StringAttr>(pair[0]).getValue() == role)
      targets.push_back(pair);
  }
  return targets;
}
Expected<Inventory> readInventory(pir::ProtocolModuleOp root, StringRef role) {
  if (role.empty() || role.size() > 4096)
    return error("endpoint-role", "expected a bounded selected role");
  Inventory inventory;
  unsigned count = 0;
  for (auto endpoint : root.getBody().front().getOps<pir::ParticipantOp>())
    if (endpoint.getRole() == role) {
      inventory.demand(endpoint, root);
      ++count;
    }
  if (count != 1)
    return error("endpoint-role",
                 "selected role must have exactly one endpoint");
  SymbolTableCollection tables;
  for (auto entry : root.getBody().front().getOps<pir::ProtocolEntryOp>()) {
    auto targets = selectedTargets(entry, role);
    if (targets.empty())
      continue;
    inventory.definitions.insert(entry);
    for (auto item : targets) {
      auto ref = cast<SymbolRefAttr>(cast<ArrayAttr>(item)[1]);
      auto *target = tables.lookupNearestSymbolFrom(entry, ref);
      if (!target)
        return error("endpoint-reference", "unresolved selected entry target");
      inventory.demand(target, root);
    }
  }
  while (!inventory.pending.empty()) {
    auto *definition = inventory.pending.pop_back_val();
    if (!inventory.charge())
      return error("endpoint-limit");
    // A reference to a symbol table itself conservatively demands its full
    // body. A nested reference demands only the resolved leaf and its shells.
    if (definition->hasTrait<OpTrait::SymbolTable>())
      for (auto &region : definition->getRegions())
        for (auto &block : region)
          for (auto &child : block)
            inventory.demand(&child, root);
    auto uses = SymbolTable::getSymbolUses(definition);
    if (!uses)
      return error("endpoint-reference", "unknown symbol-table boundary");
    for (const auto &use : *uses) {
      if (!inventory.charge())
        return error("endpoint-limit");
      auto *target =
          tables.lookupNearestSymbolFrom(use.getUser(), use.getSymbolRef());
      if (!target)
        return error("endpoint-reference",
                     "unresolved executable symbol reference");
      inventory.demand(target, root);
    }
  }
  return inventory;
}
void prune(Block &block, const Inventory &inventory, StringRef role) {
  for (auto &op : make_early_inc_range(block)) {
    if (auto entry = dyn_cast<pir::ProtocolEntryOp>(op)) {
      auto targets = selectedTargets(entry, role);
      if (targets.empty())
        op.erase();
      else
        entry.setTargetsAttr(ArrayAttr::get(op.getContext(), targets));
    } else if (inventory.definitions.contains(&op)) {
      continue;
    } else if (inventory.shells.contains(&op)) {
      for (auto &region : op.getRegions())
        for (auto &child : region)
          prune(child, inventory, role);
    } else {
      op.erase();
    }
  }
}
// The reader compares actual retained source definitions directly, rather than
// trusting a producer match list, serialized digest or a generic DCE result.
Error compareBlock(Block &source, Block &candidate, const Inventory &inventory,
                   StringRef role, unsigned &work) {
  auto actual = candidate.begin();
  for (auto &op : source) {
    if (++work > workLimit)
      return error("endpoint-limit");
    if (!inventory.definitions.contains(&op) && !inventory.shells.contains(&op))
      continue;
    if (actual == candidate.end())
      return error("endpoint-correspondence", "missing executable definition");
    auto *other = &*actual++;
    if (auto entry = dyn_cast<pir::ProtocolEntryOp>(op)) {
      OwningOpRef<Operation *> expected(op.clone());
      cast<pir::ProtocolEntryOp>(*expected).setTargetsAttr(
          ArrayAttr::get(op.getContext(), selectedTargets(entry, role)));
      if (!OperationEquivalence::isEquivalentTo(
              *expected, other, OperationEquivalence::IgnoreLocations))
        return error("endpoint-correspondence", "selected entry changed");
    } else if (inventory.definitions.contains(&op)) {
      if (!OperationEquivalence::isEquivalentTo(
              &op, other, OperationEquivalence::IgnoreLocations))
        return error("endpoint-correspondence",
                     "retained executable definition changed");
    } else {
      // Symbol-table shells may lose children, but their contract is exact.
      if (op.getName() != other->getName() ||
          op.getAttrDictionary() != other->getAttrDictionary() ||
          op.getPropertiesAsAttribute() != other->getPropertiesAsAttribute() ||
          op.getNumRegions() != other->getNumRegions() || op.getNumOperands() ||
          other->getNumOperands() || op.getNumResults() ||
          other->getNumResults())
        return error("endpoint-correspondence",
                     "nested symbol-table shell changed");
      for (auto [left, right] : zip(op.getRegions(), other->getRegions())) {
        if (!hasSingleElement(left) || !hasSingleElement(right) ||
            left.front().getNumArguments() || right.front().getNumArguments())
          return error("endpoint-correspondence",
                       "unsupported symbol-table shell");
        if (auto e = compareBlock(left.front(), right.front(), inventory, role,
                                  work))
          return e;
      }
    }
  }
  if (actual != candidate.end())
    return error("endpoint-correspondence", "extra executable definition");
  return Error::success();
}
struct SelectEndpointPass
    : PassWrapper<SelectEndpointPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SelectEndpointPass)
  SelectEndpointPass() = default;
  explicit SelectEndpointPass(StringRef selected) { role = selected.str(); }
  SelectEndpointPass(const SelectEndpointPass &other) : PassWrapper(other) {}
  Option<std::string> role{*this, "role",
                           llvm::cl::desc("Selected participant role")};
  StringRef getArgument() const final { return "zkc-select-endpoint"; }
  StringRef getDescription() const final {
    return "Check and select a closed Exec endpoint";
  }
  void runOnOperation() final {
    auto closed = closeEndpoint(getOperation(), role);
    if (!closed) {
      diagnostics::emit(getOperation().emitError(), closed.takeError());
      return signalPassFailure();
    }
    auto candidate = closed->candidateSnapshot();
    getOperation().getBodyRegion().takeBody(candidate->getBodyRegion());
  }
};
} // namespace
Error checkEndpointClosure(ModuleOp source, ModuleOp candidate,
                           StringRef role) {
  auto root = sourceRoot(source);
  if (!root)
    return root.takeError();
  if (!candidate || candidate.getContext() != source.getContext() ||
      candidate->getNumRegions() != 1 ||
      !hasSingleElement(candidate.getBodyRegion()) ||
      !hasSingleElement(*candidate.getBody()) || failed(admitStage(candidate)))
    return error("endpoint-candidate");
  auto target = dyn_cast<pir::ProtocolModuleOp>(&candidate.getBody()->front());
  if (!target ||
      source->getAttrDictionary() != candidate->getAttrDictionary() ||
      source->getPropertiesAsAttribute() !=
          candidate->getPropertiesAsAttribute() ||
      (*root)->getAttrDictionary() != target->getAttrDictionary() ||
      (*root)->getPropertiesAsAttribute() != target->getPropertiesAsAttribute())
    return error("endpoint-correspondence", "module contract changed");
  auto inventory = readInventory(*root, role);
  if (!inventory)
    return inventory.takeError();
  unsigned work = 0;
  return compareBlock((*root).getBody().front(), target.getBody().front(),
                      *inventory, role, work);
}
Expected<CheckedEndpoint> closeEndpoint(ModuleOp source, StringRef role) {
  auto root = sourceRoot(source);
  if (!root)
    return root.takeError();
  OwningOpRef<ModuleOp> retained(cast<ModuleOp>(source->clone()));
  OwningOpRef<ModuleOp> candidate(cast<ModuleOp>(source->clone()));
  auto candidateRoot =
      cast<pir::ProtocolModuleOp>(&candidate->getBody()->front());
  auto inventory = readInventory(candidateRoot, role);
  if (!inventory)
    return inventory.takeError();
  prune(candidateRoot.getBody().front(), *inventory, role);
  if (auto e = checkEndpointClosure(*retained, *candidate, role))
    return std::move(e);
  return CheckedEndpoint(std::move(retained), std::move(candidate), role.str());
}
OwningOpRef<ModuleOp> CheckedEndpoint::sourceSnapshot() const {
  return source ? OwningOpRef<ModuleOp>(cast<ModuleOp>(source.get()->clone()))
                : OwningOpRef<ModuleOp>();
}
OwningOpRef<ModuleOp> CheckedEndpoint::candidateSnapshot() const {
  return candidate
             ? OwningOpRef<ModuleOp>(cast<ModuleOp>(candidate.get()->clone()))
             : OwningOpRef<ModuleOp>();
}
std::unique_ptr<Pass> createSelectEndpointPass(StringRef role) {
  return std::make_unique<SelectEndpointPass>(role);
}
} // namespace zkc
