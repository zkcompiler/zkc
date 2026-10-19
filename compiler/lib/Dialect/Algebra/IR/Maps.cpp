#include "zkc/Analysis/TotalClosure.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Mathematical.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;

namespace zkc::algebra {
Type mapField(FunctionType type, ArrayRef<bool> rowwise) {
  if (!type || type.getNumInputs() != rowwise.size() ||
      type.getNumResults() != 1 || !llvm::is_contained(rowwise, true))
    return {};
  auto vector = dyn_cast<FieldVectorType>(type.getResult(0));
  if (!vector)
    return {};
  auto field = dyn_cast<FieldType>(vector.getElementType());
  if (!field ||
      protocol::installedDomains().identitySort(field.getDomain()) != "Field")
    return {};
  for (auto [input, mapped] : llvm::zip(type.getInputs(), rowwise))
    if (input != (mapped ? Type(vector) : Type(field)))
      return {};
  return field;
}

LogicalResult MapRealizeOp::verify() {
  for (auto attribute : (*this)->getAttrs())
    if (!llvm::is_contained(ArrayRef<StringRef>{"sym_name", "helper",
                                                "function_type", "rowwise",
                                                "policy"},
                            attribute.getName().getValue()))
      return diagnostics::emit(emitOpError(), "algebra-map-signature",
                               "unsupported map request attribute");
  if (!mapField(getFunctionType(), getRowwise()))
    return diagnostics::emit(
        emitOpError(), "algebra-map-signature",
        "expected one scalar field, a vector result and at least one rowwise "
        "vector input");
  if (auto raw = (*this)->getAttr("policy")) {
    auto policy = dyn_cast<ArrayAttr>(raw);
    if (!policy || policy.size() != 3 ||
        !llvm::all_of(policy,
                      [](Attribute value) { return isa<BoolAttr>(value); }))
      return diagnostics::emit(
          emitOpError(), "algebra-map-policy",
          "expected [BoolAttr finiteBulk, BoolAttr vectorReductionFusion, "
          "BoolAttr collectFoldFusion]");
  }
  return success();
}

LogicalResult MapRealizeOp::verifySymbolUses(SymbolTableCollection &tables) {
  // Only an existing private sibling helper is mapped. The admitting profile
  // checks its helper closure with MapFormulas once per helper; a walk here
  // would repeat it for every map.
  auto helper =
      tables.lookupNearestSymbolFrom<func::FuncOp>(*this, getHelperAttr());
  if (!helper || failed(helper->getName().verifyInvariants(helper)) ||
      helper.isExternal() || !helper.isPrivate() ||
      helper->getParentOp() != (*this)->getParentOp())
    return diagnostics::emit(emitOpError(), "algebra-map-helper",
                             "expected a private sibling helper body");
  auto field = mapField(getFunctionType(), getRowwise());
  auto attribute = helper->getAttrOfType<TypeAttr>("function_type");
  SmallVector<Type> scalars(getRowwise().size(), field);
  if (!field || !attribute ||
      attribute.getValue() != FunctionType::get(getContext(), scalars, {field}))
    return diagnostics::emit(emitOpError(), "algebra-map-signature",
                             "helper ports must be the mapped scalar field");
  return success();
}

LogicalResult MapFormulas::verify(MapRealizeOp map) {
  auto field = mapField(map.getFunctionType(), map.getRowwise());
  if (!field)
    return diagnostics::emit(map.emitOpError(), "algebra-map-signature");
  auto helper =
      tables.lookupNearestSymbolFrom<func::FuncOp>(map, map.getHelperAttr());
  if (!helper)
    return diagnostics::emit(map.emitOpError(), "algebra-map-helper",
                             "expected a private sibling helper body");
  auto refuse = [&](func::FuncOp owner, Operation &at, const Twine &detail) {
    admitted.clear();
    auto diagnostic =
        diagnostics::emit(map.emitOpError(), "algebra-map-formula",
                          "helper @" + owner.getSymName() + " " + detail);
    diagnostic.attachNote(at.getLoc()) << "refused operation";
    return diagnostic;
  };
  auto outside = [](Operation &op) {
    return ("uses '" + op.getName().getStringRef() +
            "' outside the map field's ring formula")
        .str();
  };
  auto inField = [&](TypeRange types) {
    return llvm::all_of(types, [&](Type type) { return type == field; });
  };
  // Helpers are cached when queued and a refusal clears the cache, so after a
  // successful map every cached helper's closure has been read in its field.
  SmallVector<func::FuncOp> pending;
  if (admitted.insert({helper, field}).second)
    pending.push_back(helper);
  while (!pending.empty()) {
    auto current = pending.pop_back_val();
    if (current.isExternal() || !current.getBody().hasOneBlock())
      return refuse(current, *current, "has no single-block body");
    for (auto &op : current.getBody().front().without_terminator()) {
      auto call = dyn_cast<func::CallOp>(op);
      if (!call) {
        if (!isRingOperation(op) || op.getResult(0).getType() != field)
          return refuse(current, op, outside(op));
        continue;
      }
      auto callee = tables.lookupNearestSymbolFrom<func::FuncOp>(
          call, call.getCalleeAttr());
      if (!callee ||
          !llvm::equal(callee.getFunctionType().getInputs(),
                       call.getOperandTypes()) ||
          !llvm::equal(callee.getFunctionType().getResults(),
                       call.getResultTypes()) ||
          !inField(call.getOperandTypes()) || !inField(call.getResultTypes()))
        return refuse(current, op, outside(op));
      if (admitted.insert({callee, field}).second)
        pending.push_back(callee);
    }
  }
  return success();
}

// Internal requests carry the exact original scalar closure. This reader is
// shared by preparation, projection and logical execution admission; it never
// substitutes a runtime length guard for a total-mathematics premise.
LogicalResult collectMapHelpers(Operation *owner,
                                llvm::DenseSet<Operation *> &helpers,
                                uint64_t &expandedOperations) {
  helpers.clear();
  expandedOperations = 0;
  if (!owner || owner->getNumRegions() != 1 ||
      !owner->getRegion(0).hasOneBlock())
    return failure();
  auto maps = owner->getRegion(0).front().getOps<MapRealizeOp>();
  if (maps.empty())
    return success();
  SymbolTableCollection symbols;
  mathematical::TotalClosure closure(owner, symbols);
  if (failed(closure.verify()))
    return failure();
  MapFormulas formulas(symbols);
  unsigned remaining = mathematical::realizedHelperOperationLimit;
  SmallVector<func::FuncOp> pending;
  for (auto map : maps) {
    if (failed(map->getName().verifyInvariants(map)) ||
        failed(map.verifySymbolUses(symbols)) || failed(formulas.verify(map)))
      return failure();
    auto helper =
        symbols.lookupNearestSymbolFrom<func::FuncOp>(map, map.getHelperAttr());
    const mathematical::TotalSummary *summary;
    if (failed(closure.get(helper, summary)))
      return failure();
    if (summary->expandedOperations > remaining)
      return diagnostics::emit(
          map.emitOpError(), "mathematical-analysis-limit",
          "map helpers exceed the shared expansion budget");
    remaining -= summary->expandedOperations;
    expandedOperations += summary->expandedOperations;
    if (helpers.insert(helper).second)
      pending.push_back(helper);
  }
  // TotalClosure checked the entire source, including private sibling scope,
  // domains, unused work, signatures and cycles before this bounded traversal.
  while (!pending.empty()) {
    auto helper = pending.pop_back_val();
    for (auto call : helper.getBody().front().getOps<func::CallOp>()) {
      auto callee = symbols.lookupNearestSymbolFrom<func::FuncOp>(
          call, call.getCalleeAttr());
      if (helpers.insert(callee).second)
        pending.push_back(callee);
    }
  }
  return success();
}

LogicalResult collectMapHelpers(Operation *owner,
                                llvm::DenseSet<Operation *> &helpers) {
  uint64_t expandedOperations;
  return collectMapHelpers(owner, helpers, expandedOperations);
}
} // namespace zkc::algebra
