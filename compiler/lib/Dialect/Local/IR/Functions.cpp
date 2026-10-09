#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Interfaces/FunctionImplementation.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalOps.h"

using namespace mlir;

namespace zkc::local {
void FuncOp::build(OpBuilder &builder, OperationState &state, StringRef name,
                   FunctionType type, ArrayRef<NamedAttribute> attrs) {
  state.addAttribute(getSymNameAttrName(state.name),
                     builder.getStringAttr(name));
  state.addAttribute(getFunctionTypeAttrName(state.name), TypeAttr::get(type));
  state.addAttributes(attrs);
  state.addRegion();
}

ParseResult FuncOp::parse(OpAsmParser &parser, OperationState &state) {
  auto functionType =
      [](Builder &builder, ArrayRef<Type> inputs, ArrayRef<Type> results,
         function_interface_impl::VariadicFlag, std::string &) -> Type {
    return builder.getFunctionType(inputs, results);
  };
  return function_interface_impl::parseFunctionOp(
      parser, state, false, getFunctionTypeAttrName(state.name), functionType,
      getArgAttrsAttrName(state.name), getResAttrsAttrName(state.name));
}

void FuncOp::print(OpAsmPrinter &printer) {
  function_interface_impl::printFunctionOp(
      printer, *this, false, getFunctionTypeAttrName(), getArgAttrsAttrName(),
      getResAttrsAttrName());
}

LogicalResult FuncOp::verifyRegions() {
  if (isExternal())
    return success();
  if (!llvm::hasSingleElement(getBody()) || getBody().front().empty())
    return diagnostics::emit(emitOpError(), "local-function-body");
  if (!isa<ReturnOp, StopOp>(getBody().front().back()))
    return diagnostics::emit(emitOpError(), "local-function-terminator");
  return success();
}

LogicalResult ReturnOp::verify() {
  auto function = cast<FuncOp>((*this)->getParentOp());
  if (getOperandTypes() != function.getResultTypes())
    return diagnostics::emit(emitOpError(), "interactive-return-signature");
  return success();
}

namespace {
LogicalResult verifyCall(Operation *op, FlatSymbolRefAttr reference,
                         SymbolTableCollection &tables) {
  auto *function = tables.lookupNearestSymbolFrom(op, reference);
  if (!isa_and_nonnull<FuncOp>(function) &&
      !(isa<ApplyOp>(op) && isa_and_nonnull<RealizeOp>(function)))
    return diagnostics::emit(
        op->emitOpError(), "interactive-symbol-kind",
        "expected a local.func or preparation-time realization");
  // A sibling's verifier may not have run yet.
  auto attribute = function->getAttrOfType<TypeAttr>("function_type");
  auto type =
      attribute ? dyn_cast<FunctionType>(attribute.getValue()) : FunctionType();
  if (!type || op->getOperandTypes() != type.getInputs() ||
      op->getResultTypes() != type.getResults())
    return diagnostics::emit(op->emitOpError(), "interactive-call-signature");
  return success();
}
} // namespace

LogicalResult ApplyOp::verify() {
  auto *owner = (*this)->getParentOp();
  while (owner && isa<LocalIfOp, LocalForOp, LocalMatchOp>(owner))
    owner = owner->getParentOp();
  if (!isa_and_nonnull<FuncOp>(owner))
    return diagnostics::emit(emitOpError(), "algorithm-call-context");
  return success();
}

LogicalResult ApplyOp::verifySymbolUses(SymbolTableCollection &tables) {
  if (failed(verifyCall(*this, getCalleeAttr(), tables)))
    return failure();
  auto function =
      tables.lookupNearestSymbolFrom<FuncOp>(*this, getCalleeAttr());
  if (function && function.isExternal())
    return diagnostics::emit(emitOpError(), "algorithm-call-symbol",
                             "local.apply requires an executable body");
  return success();
}

LogicalResult RealizeOp::verifySymbolUses(SymbolTableCollection &tables) {
  auto helper =
      tables.lookupNearestSymbolFrom<func::FuncOp>(*this, getHelperAttr());
  if (!helper || failed(helper->getName().verifyInvariants(helper)) ||
      helper.isExternal() || !helper.isPrivate() ||
      helper->getParentOp() != (*this)->getParentOp())
    return diagnostics::emit(emitOpError(), "local-realization-helper");
  auto attribute = helper->getAttrOfType<TypeAttr>("function_type");
  if (!attribute || attribute.getValue() != getFunctionType())
    return diagnostics::emit(emitOpError(), "local-realization-signature");
  return success();
}

LogicalResult CallOp::verifySymbolUses(SymbolTableCollection &tables) {
  return verifyCall(*this, getCalleeAttr(), tables);
}
} // namespace zkc::local
