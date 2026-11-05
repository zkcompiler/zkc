#include "zkc/Dialect/SelectedControl.h"
#include "mlir/IR/SymbolTable.h"
#include "zkc/Analysis/NativeTypes.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Data/Variant.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/MathematicalSemantics.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeTypes.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc {
bool isSelectedControl(Operation *op) {
  return isa_and_nonnull<protocol_ir::BranchOp,
                         protocol_ir::ParticipantBranchOp, data::BranchOp>(op);
}
Error requireUnconditionalProtocolControl(ArrayRef<Operation *> roots,
                                          StringRef diagnostic) {
  if (roots.empty() || is_contained(roots, nullptr))
    return error(diagnostic);
  // One allowance covers visited operations and followed symbol uses.
  unsigned remaining = 100000;
  SymbolTableCollection symbols;
  llvm::DenseSet<Operation *> reached(roots.begin(), roots.end());
  SmallVector<Operation *> definitions(roots.begin(), roots.end());
  while (!definitions.empty()) {
    Operation *definition = definitions.pop_back_val();
    // Every arm and nested region of a reached definition is reached, whether
    // or not a selector can take it.
    SmallVector<Operation *> pending{definition};
    while (!pending.empty()) {
      Operation *op = pending.pop_back_val();
      // Total Math selection has no protocol events. Still traverse its arms
      // and references: this is not a selector-based reachability shortcut.
      if (!remaining-- ||
          isa<protocol_ir::BranchOp, protocol_ir::ParticipantBranchOp>(op))
        return error(diagnostic);
      for (Region &region : op->getRegions())
        for (Block &block : region)
          for (Operation &child : block)
            pending.push_back(&child);
    }
    // Applications, helper and local calls, oracle and relation declarations
    // and every other static reference extend the closure.
    auto uses = SymbolTable::getSymbolUses(definition);
    if (!uses)
      return error(diagnostic);
    for (const SymbolTable::SymbolUse &use : *uses) {
      if (!remaining--)
        return error(diagnostic);
      Operation *callee =
          symbols.lookupNearestSymbolFrom(use.getUser(), use.getSymbolRef());
      if (callee && reached.insert(callee).second)
        definitions.push_back(callee);
    }
  }
  return Error::success();
}
Expected<SmallVector<Type>> selectedPayloadTypes(Operation *op, unsigned arm) {
  if (!op || !isSelectedControl(op))
    return error("selected-control-shape");
  auto alternatives = op->getAttrOfType<ArrayAttr>("alternatives");
  if (!isSelectedControl(op) || !op->getNumOperands() || !alternatives ||
      arm >= alternatives.size() || !isa<StringAttr>(alternatives[arm]))
    return error("selected-control-shape");
  Type type = op->getOperand(0).getType();
  if (auto represented = dyn_cast<runtime::RepresentedType>(type))
    type = represented.getLogical();
  if (type.isSignlessInteger(1))
    return SmallVector<Type>{};
  return data::variantPayloadTypes(
      op->getOperand(0).getType(),
      cast<StringAttr>(alternatives[arm]).getValue());
}
Value selectedCapture(BlockArgument argument) {
  Operation *op = argument.getOwner()->getParentOp();
  if (!isSelectedControl(op))
    return {};
  unsigned arm = argument.getOwner()->getParent()->getRegionNumber();
  auto payload = selectedPayloadTypes(op, arm);
  if (!payload) {
    consumeError(payload.takeError());
    return {};
  }
  unsigned index = argument.getArgNumber();
  if (index < payload->size() ||
      index - payload->size() + 1 >= op->getNumOperands())
    return {};
  return op->getOperand(index - payload->size() + 1);
}
LogicalResult verifySelectedControl(Operation *op) {
  auto refuse = [&](StringRef detail) {
    return diagnostics::emit(op->emitOpError(), "selected-control-shape",
                             detail);
  };
  auto alternatives = op->getAttrOfType<ArrayAttr>("alternatives");
  if (alternatives && (alternatives.size() > selectedRegionArmLimit ||
                       op->getNumRegions() > selectedRegionArmLimit))
    return diagnostics::emit(op->emitOpError(), "selected-control-limit",
                             "selected region exceeds " +
                                 Twine(uint64_t(selectedRegionArmLimit)) +
                                 " arms");
  if (!isSelectedControl(op) || !op->getNumOperands() || !alternatives ||
      alternatives.empty() || alternatives.size() != op->getNumRegions())
    return refuse("expected selector and exactly one region per alternative");
  Type type = op->getOperand(0).getType();
  if (auto represented = dyn_cast<runtime::RepresentedType>(type))
    type = represented.getLogical();
  SmallVector<StringRef> labels;
  if (type.isSignlessInteger(1))
    labels = {"then", "else"};
  else if (auto variant = dyn_cast<data::VariantType>(type))
    for (auto alternative : variant.getAlternatives())
      labels.push_back(alternative.getLabel().getValue());
  else
    return refuse("selector must be Boolean or an ordinary nominal variant");
  if (labels.size() != alternatives.size())
    return refuse("selection must be exhaustive");
  for (auto [index, label] : enumerate(labels)) {
    auto actual = dyn_cast<StringAttr>(alternatives[index]);
    if (!actual || actual.getValue() != label)
      return refuse("alternatives must be unique and in declaration order");
    auto payload = selectedPayloadTypes(op, index);
    if (!payload)
      return diagnostics::emit(op->emitOpError(), payload.takeError());
    SmallVector<Type> arguments(*payload);
    append_range(arguments, op->getOperands().drop_front().getTypes());
    Region &arm = op->getRegion(index);
    if (!hasSingleElement(arm) || arm.front().empty() ||
        arm.front().getArgumentTypes() != TypeRange(arguments))
      return refuse("arm arguments must be payload followed by exact captures");
    auto *yield = &arm.front().back();
    if ((isa<data::BranchOp>(op) ? !isa<data::YieldOp>(yield)
                                 : !isa<protocol_ir::ProtocolYieldOp>(yield)) ||
        yield->getOperandTypes() != op->getResultTypes())
      return refuse("every arm must yield the exact ordered result types");
  }
  if (auto branch = dyn_cast<protocol_ir::BranchOp>(op)) {
    llvm::StringSet<> roles;
    for (Attribute role : branch.getRoles()) {
      auto name = dyn_cast<StringAttr>(role);
      if (!name || !roles.insert(name.getValue()).second)
        return refuse("branch roles must be distinct");
    }
    if (roles.empty() || branch.getOutputRoles().size() != op->getNumResults())
      return refuse("branch requires its roster and every result placement");
    for (Attribute placement : branch.getOutputRoles()) {
      auto set = dyn_cast<ArrayAttr>(placement);
      llvm::StringSet<> seen;
      if (!set || set.empty())
        return refuse("result placements must be nonempty role sets");
      for (Attribute role : set) {
        auto name = dyn_cast<StringAttr>(role);
        if (!name || !roles.contains(name.getValue()) ||
            !seen.insert(name.getValue()).second)
          return refuse("result roles must be distinct participating roles");
      }
    }
  }
  return success();
}
} // namespace zkc

LogicalResult zkc::protocol_ir::BranchOp::verifyRegions() {
  return verifySelectedControl(*this);
}
LogicalResult zkc::protocol_ir::ParticipantBranchOp::verifyRegions() {
  return verifySelectedControl(*this);
}
LogicalResult zkc::data::BranchOp::verifyRegions() {
  return verifySelectedControl(*this);
}
