#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialTypes.h"

using namespace mlir;
namespace zkc::mathematical {
namespace {
LogicalResult refuse(Operation *op, StringRef code, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), code, detail);
}
} // namespace

bool isComputationUnit(Operation *operation) {
  return isa_and_nonnull<mlir::ModuleOp>(operation) &&
         operation->getAttrOfType<UnitAttr>("exec.computation");
}

func::FuncOp getComputationEntry(mlir::ModuleOp unit) {
  if (!unit || !isComputationUnit(unit) ||
      !unit->getAttrOfType<StringAttr>("sym_name") ||
      unit->getNumRegions() != 1 || !llvm::hasSingleElement(unit->getRegion(0)))
    return {};
  func::FuncOp entry;
  for (auto function : unit.getBody()->getOps<func::FuncOp>()) {
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

LogicalResult verifyComputationUnit(mlir::ModuleOp unit) {
  if (!unit)
    return failure();
  if (!isComputationUnit(unit))
    return refuse(unit, "computation-profile",
                  "expected the exec.computation unit profile");
  for (auto attribute : unit->getAttrs())
    if (attribute.getName() != "sym_name" &&
        attribute.getName() != "exec.computation")
      return refuse(unit, "computation-formation",
                    "unsupported unit attribute");
  if (!llvm::hasSingleElement(unit.getBodyRegion()) ||
      unit.getBody()->getNumArguments())
    return refuse(unit, "computation-formation",
                  "expected one symbol-table block without arguments");
  auto entry = getComputationEntry(unit);
  if (!entry)
    return refuse(unit, "computation-entry",
                  "expected exactly one public func.func entry");
  for (auto &declaration : *unit.getBody())
    if (!isa<func::FuncOp, data::DomainOp>(declaration))
      return refuse(
          &declaration, "computation-formation",
          "unit admits only standard functions and data.domain dependencies");
  // Public selects the entry of this isolated mathematical closure. Its
  // explicit premises remain part of the function contract and are discharged
  // at each actual scoped invocation, just as for a private helper.
  NativeTypePolicies types(unit);
  auto port = [&](Type type) {
    auto policy = types.get(type);
    return !isFormalType(type) && policy && policy->total && !policy->affine;
  };
  if (!llvm::all_of(entry.getArgumentTypes(), port) ||
      !llvm::all_of(entry.getResultTypes(), port))
    return refuse(entry, "computation-entry",
                  "entry requires total non-affine native data ports without "
                  "formal polynomials");
  for (auto domain : unit.getBody()->getOps<data::DomainOp>()) {
    auto signature = domain.getFunctionType();
    auto result = dyn_cast<data::DomainType>(signature.getResult(0));
    if (!result || !llvm::all_of(signature.getInputs(), port) ||
        !llvm::all_of(result.getItemTypes(), port))
      return refuse(domain, "computation-formation",
                    "domain dependencies require total non-affine native data");
  }
  // Do not reduce this inventory to the entry's live dependency closure.
  SymbolTableCollection symbols;
  return TotalClosure(unit, symbols, entry).verify();
}
} // namespace zkc::mathematical
