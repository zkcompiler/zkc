#include "zkc/Analysis/ComputationUnit.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"

using namespace mlir;
namespace zkc::exec {
namespace {
LogicalResult refuse(Operation *op, StringRef code, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), code, detail);
}
func::FuncOp owner(ComputeOp call) {
  auto function = dyn_cast_or_null<func::FuncOp>(call->getParentOp());
  if (!function || function->getNumRegions() != 1 ||
      function->getRegion(0).empty() || !function->getParentOp() ||
      !function->getParentOp()->hasTrait<OpTrait::SymbolTable>())
    return {};
  auto &entry = function->getRegion(0).front();
  if (entry.getNumArguments() == 0 ||
      !isa<runtime::ScopeType>(entry.getArgument(0).getType()) ||
      call.getScope() != entry.getArgument(0))
    return {};
  return function;
}
} // namespace

func::FuncOp ComputeOp::resolveCallee(SymbolTableCollection &symbols) {
  auto function = owner(*this);
  auto reference = getCalleeAttr();
  if (!function || !reference || reference.getNestedReferences().size() > 1)
    return {};
  auto *table = function->getParentOp();
  if (reference.getNestedReferences().empty()) {
    auto helper = dyn_cast_or_null<func::FuncOp>(
        symbols.lookupSymbolIn(table, reference.getRootReference()));
    if (!helper ||
        helper->getAttrOfType<StringAttr>("sym_visibility") !=
            StringAttr::get(getContext(), "private") ||
        helper->hasAttr("runtime.origin") || helper->hasAttr("runtime.region"))
      return {};
    return helper;
  }
  auto unit = dyn_cast_or_null<ModuleOp>(
      symbols.lookupSymbolIn(table, reference.getRootReference()));
  auto entry = mathematical::getComputationEntry(unit);
  if (!entry || entry.getSymNameAttr() !=
                    reference.getNestedReferences().front().getAttr())
    return {};
  return entry;
}

LogicalResult ComputeOp::verify() {
  if (!owner(*this))
    return refuse(*this, "execution-computation-context",
                  "expected the containing function's borrowed scope");
  if (getSite().empty())
    return refuse(*this, "execution-formation",
                  "mathematical invocation requires an occurrence");
  for (auto attribute : (*this)->getAttrs())
    if (!llvm::is_contained(getAttributeNames(),
                            attribute.getName().getValue()))
      return refuse(*this, "execution-computation-attribute",
                    "unsupported invocation attribute");
  if (auto policy = getPolicyAttr())
    if (policy.size() != 3 || !llvm::all_of(policy, [](Attribute item) {
          return isa<BoolAttr>(item);
        }))
      return refuse(*this, "execution-computation-policy",
                    "expected three Boolean selection choices");
  mathematical::NativeTypePolicies types(*this);
  for (TypeRange ports : {TypeRange(getInputs().getTypes()),
                          TypeRange(getOutcome().getType().getPayload())})
    for (Type type : ports) {
      auto policy = types.get(type);
      if (!policy || !policy->total || policy->affine)
        return refuse(*this, "execution-computation-signature",
                      "expected total non-affine mathematical data ports");
    }
  return success();
}

LogicalResult ComputeOp::verifySymbolUses(SymbolTableCollection &symbols) {
  auto helper = resolveCallee(symbols);
  if (!helper)
    return refuse(*this, "execution-computation-symbol",
                  "expected an actual private source helper or a sibling "
                  "computation unit's public entry");
  // A sibling's region verifier may not have run yet. Check shape before
  // accessing its body. This does not recursively admit mathematical meaning.
  auto raw = helper->getAttrOfType<TypeAttr>("function_type");
  auto signature =
      raw ? dyn_cast<FunctionType>(raw.getValue()) : FunctionType();
  if (!signature || getInputs().getTypes() != signature.getInputs() ||
      TypeRange(getOutcome().getType().getPayload()) != signature.getResults())
    return refuse(*this, "execution-computation-signature",
                  "actual mathematical ports differ from invocation ports");
  if (helper->getNumRegions() != 1 ||
      !llvm::hasSingleElement(helper->getRegion(0)) ||
      helper->getRegion(0).front().empty() ||
      !isa<func::ReturnOp>(helper->getRegion(0).front().back()))
    return refuse(*this, "execution-computation-symbol",
                  "expected a defined mathematical body ending in func.return");
  return success();
}
} // namespace zkc::exec
