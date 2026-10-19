#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Kernel/IR/KernelOps.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"

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

func::FuncOp getEntry(ModuleOp unit) {
  if (!unit || unit->getNumRegions() != 1 ||
      !llvm::hasSingleElement(unit->getRegion(0)))
    return {};
  func::FuncOp entry;
  for (auto function : unit.getBody().front().getOps<func::FuncOp>()) {
    // Symbol uses may be checked before nested declaration invariants. Avoid
    // SymbolOpInterface visibility accessors on an unverified attribute.
    if (!function->getAttrOfType<StringAttr>("sym_name"))
      return {};
    auto raw = function->getAttr("sym_visibility");
    auto visibility = dyn_cast_if_present<StringAttr>(raw);
    if (raw && (!visibility || (visibility.getValue() != "public" &&
                                visibility.getValue() != "private" &&
                                visibility.getValue() != "nested")))
      return {};
    if (visibility && visibility.getValue() != "public")
      continue;
    if (entry)
      return {};
    entry = function;
  }
  return entry;
}

func::FuncOp resolve(CallOp call, SymbolTableCollection &symbols) {
  auto reference = call->getAttrOfType<SymbolRefAttr>("callee");
  if (!reference || reference.getNestedReferences().size() != 1)
    return {};
  // Inspect the entry safely before constructing a symbol table over possibly
  // malformed nested declarations.
  auto unit = symbols.lookupNearestSymbolFrom<ModuleOp>(
      call, reference.getRootReference());
  auto *owner = localOwner(call);
  if (!unit || !owner || unit->getParentOp() != owner->getParentOp())
    return {};
  auto entry = getEntry(unit);
  if (!entry || entry->getAttrOfType<StringAttr>("sym_name") !=
                    reference.getNestedReferences().front().getAttr())
    return {};
  return entry;
}

LogicalResult ModuleOp::verifyRegions() {
  for (auto attribute : (*this)->getAttrs())
    if (attribute.getName() != "sym_name")
      return refuse(*this, "kernel-formation", "unsupported unit attribute");
  if (!llvm::hasSingleElement(getBody()) || getBody().front().getNumArguments())
    return refuse(*this, "kernel-formation",
                  "expected one symbol-table block without arguments");
  auto entry = getEntry(*this);
  if (!entry)
    return refuse(*this, "kernel-entry",
                  "expected exactly one public func.func entry");
  for (auto &declaration : getBody().front())
    if (!isa<func::FuncOp, data::DomainOp>(declaration))
      return refuse(
          &declaration, "kernel-formation",
          "unit admits only standard functions and data.domain dependencies");
  // An executable entry must discharge all premises itself. Private helper
  // premises are checked against actual mathematical operands by TotalClosure.
  if (auto raw = entry->getAttr("data.preconditions")) {
    auto assumptions = dyn_cast<ArrayAttr>(raw);
    if (!assumptions || !assumptions.empty())
      return refuse(entry, "kernel-entry", "entry must be unconditional");
  }
  mathematical::NativeTypePolicies types(*this);
  auto port = [&](Type type) {
    auto policy = types.get(type);
    return !isa<poly::PolynomialType>(type) && policy && policy->total &&
           !policy->affine;
  };
  if (!llvm::all_of(entry.getArgumentTypes(), port) ||
      !llvm::all_of(entry.getResultTypes(), port))
    return refuse(entry, "kernel-entry",
                  "entry requires total non-affine native data ports without "
                  "formal polynomials");

  for (auto domain : getBody().front().getOps<data::DomainOp>()) {
    auto signature = domain.getFunctionType();
    auto result = dyn_cast<data::DomainType>(signature.getResult(0));
    if (!result || !llvm::all_of(signature.getInputs(), port) ||
        !llvm::all_of(result.getItemTypes(), port))
      return refuse(domain, "kernel-formation",
                    "domain dependencies require total non-affine native data");
  }
  // Verify every retained definition, including unused helpers and descriptors.
  // The entry has no formal polynomial ports, so its inlined observations must
  // have known fitting bounds; a conditional generic summary is insufficient.
  SymbolTableCollection symbols;
  return mathematical::TotalClosure(*this, symbols, entry).verify();
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
                  "expected the public entry of a sibling kernel.module");
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
