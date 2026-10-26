#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"

using namespace mlir;
namespace zkc::kernel {
namespace {
LogicalResult refuse(Operation *op, StringRef code, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), code, detail);
}
Operation *localOwner(CallOp call) {
  auto *owner = call->getParentOp();
  while (owner &&
         isa<local::LocalIfOp, local::LocalForOp, local::LocalMatchOp>(owner))
    owner = owner->getParentOp();
  return isa_and_nonnull<local::FuncOp>(owner) ? owner : nullptr;
}
} // namespace

func::FuncOp resolve(CallOp call, SymbolTableCollection &symbols) {
  auto reference = call->getAttrOfType<SymbolRefAttr>("callee");
  if (!reference || reference.getNestedReferences().size() != 1)
    return {};
  // Inspect the entry safely before constructing a symbol table over possibly
  // malformed nested declarations.
  auto unit = symbols.lookupNearestSymbolFrom<mlir::ModuleOp>(
      call, reference.getRootReference());
  auto *owner = localOwner(call);
  if (!unit || !owner || unit->getParentOp() != owner->getParentOp())
    return {};
  auto entry = mathematical::getComputationEntry(unit);
  if (!entry || entry->getAttrOfType<StringAttr>("sym_name") !=
                    reference.getNestedReferences().front().getAttr())
    return {};
  return entry;
}

LogicalResult CallOp::verify() {
  if (!localOwner(*this))
    return refuse(*this, "kernel-call-context",
                  "expected local.func or its structured Local control");
  auto reference = (*this)->getAttrOfType<SymbolRefAttr>("callee");
  if (!reference || reference.getNestedReferences().size() != 1)
    return refuse(*this, "kernel-call-symbol", "expected @unit::@entry");
  for (auto attribute : (*this)->getAttrs())
    if (!llvm::is_contained(getAttributeNames(),
                            attribute.getName().getValue()))
      return refuse(*this, "kernel-call-attribute",
                    "unsupported call attribute");
  for (auto [attributes, count] :
       {std::pair{getArgAttrsAttr(), getNumOperands()},
        std::pair{getResAttrsAttr(), getNumResults()}})
    if (attributes && (attributes.size() != count ||
                       !llvm::all_of(attributes, [](Attribute value) {
                         auto dictionary = dyn_cast<DictionaryAttr>(value);
                         return dictionary && dictionary.empty();
                       })))
      return refuse(*this, "kernel-call-attribute",
                    "port attributes must be empty dictionaries matching the "
                    "argument or result count");
  if (auto raw = (*this)->getAttr("policy")) {
    auto policy = dyn_cast<ArrayAttr>(raw);
    if (!policy || policy.size() != 3 ||
        !llvm::all_of(policy,
                      [](Attribute value) { return isa<BoolAttr>(value); }))
      return refuse(*this, "kernel-call-policy",
                    "expected [BoolAttr finiteBulk, BoolAttr "
                    "vectorReductionFusion, BoolAttr collectFoldFusion]");
  }
  return success();
}

LogicalResult CallOp::verifySymbolUses(SymbolTableCollection &symbols) {
  auto entry = resolve(*this, symbols);
  if (!entry)
    return refuse(*this, "kernel-call-symbol",
                  "expected the public entry of a sibling computation module");
  auto attribute = entry->getAttrOfType<TypeAttr>("function_type");
  auto type =
      attribute ? dyn_cast<FunctionType>(attribute.getValue()) : FunctionType();
  if (!type || getOperandTypes() != type.getInputs() ||
      getResultTypes() != type.getResults())
    return refuse(*this, "kernel-call-signature",
                  "entry signature does not match");
  // Region admission has not necessarily run yet. Check shape before reading
  // the entry block.
  if (entry->getNumRegions() != 1 ||
      !llvm::hasSingleElement(entry->getRegion(0)) ||
      entry->getRegion(0).front().empty() ||
      !isa<func::ReturnOp>(entry->getRegion(0).front().back()))
    return refuse(
        *this, "kernel-call-symbol",
        "expected a defined single-block entry ending in func.return");
  return success();
}
} // namespace zkc::kernel
