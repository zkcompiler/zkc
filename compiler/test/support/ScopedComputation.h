#ifndef ZKC_TEST_SCOPEDCOMPUTATION_H
#define ZKC_TEST_SCOPEDCOMPUTATION_H

#include "NativeCases.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/IR/Verifier.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Exec/Builders.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"

namespace zkc::test::scopedComputation {
using namespace mlir;
inline func::FuncOp region(OpBuilder &builder, func::FuncOp parent,
                           StringRef name, TypeRange inputs,
                           TypeRange outputs) {
  builder.setInsertionPoint(parent);
  SmallVector<Type> arguments{runtime::ScopeType::get(builder.getContext())};
  llvm::append_range(arguments, inputs);
  auto type = builder.getFunctionType(
      arguments,
      exec::OutcomeType::get(builder.getContext(), llvm::to_vector(outputs)));
  auto helper = func::FuncOp::create(builder, parent.getLoc(), name, type);
  helper.setPrivate();
  helper->setAttr("no_inline", builder.getUnitAttr());
  helper->setAttr("runtime.region", builder.getUnitAttr());
  builder.setInsertionPointToEnd(helper.addEntryBlock());
  return helper;
}
inline SmallVector<Value> apply(exec::ScopedExecutionBuilder &control,
                                OpBuilder &builder, StringRef binding,
                                StringRef site, ValueRange inputs,
                                TypeRange outputs,
                                ArrayRef<StringRef> parameters = {}) {
  return control.invoke(
      "exec.apply", outputs, control.scoped(inputs),
      {builder.getNamedAttr(
           "binding", FlatSymbolRefAttr::get(builder.getContext(), binding)),
       builder.getNamedAttr("parameters", builder.getStrArrayAttr(parameters)),
       builder.getNamedAttr("site", builder.getStringAttr(site))});
}
inline func::FuncOp computation(func::FuncOp helper, StringRef name) {
  OpBuilder builder(helper);
  SmallVector<Type> inputs{runtime::ScopeType::get(helper.getContext())};
  llvm::append_range(inputs, helper.getArgumentTypes());
  auto outcome =
      exec::OutcomeType::get(helper.getContext(), helper.getResultTypes());
  auto caller = func::FuncOp::create(builder, helper.getLoc(), name,
                                     builder.getFunctionType(inputs, outcome));
  caller->setAttr("no_inline", builder.getUnitAttr());
  caller->setAttr("runtime.origin",
                  builder.getArrayAttr(
                      {builder.getStringAttr(name), builder.getArrayAttr({})}));
  builder.setInsertionPointToEnd(caller.addEntryBlock());
  exec::ScopedExecutionBuilder control(builder, caller);
  auto values = control.invoke(
      "exec.compute", helper.getResultTypes(), caller.getArguments(),
      {builder.getNamedAttr("callee",
                            FlatSymbolRefAttr::get(helper.getSymNameAttr())),
       builder.getNamedAttr("site", builder.getStringAttr(name))});
  control.returned(values);
  return caller;
}
inline void numericalAddition(ModuleOp module) {
  auto helper =
      SymbolTable(&module.getBody()->front()).lookup<func::FuncOp>("step");
  exec::ApplyOp addition;
  helper.walk([&](exec::ApplyOp op) {
    auto binding = SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
        op, op.getBindingAttr());
    if (binding.getContract() == "field.add")
      addition = op;
  });
  require(bool(addition), "missing callback addition");
  OpBuilder builder(helper);
  auto type =
      builder.getFunctionType(addition.getInputs().getTypes(),
                              addition.getOutcome().getType().getPayload());
  auto raw = func::FuncOp::create(builder, helper.getLoc(), "raw_add", type);
  raw.setPrivate();
  auto entry = func::FuncOp::create(builder, helper.getLoc(), "entry", type);
  entry.setPrivate();
  builder.setInsertionPointToEnd(raw.addEntryBlock());
  auto sum = algebra::FieldAddOp::create(builder, helper.getLoc(),
                                         type.getResult(0), raw.getArguments());
  func::ReturnOp::create(builder, helper.getLoc(), sum.getResult());
  builder.setInsertionPointToEnd(entry.addEntryBlock());
  auto call =
      func::CallOp::create(builder, helper.getLoc(), raw, entry.getArguments());
  func::ReturnOp::create(builder, helper.getLoc(), call.getResults());
  builder.setInsertionPoint(addition);
  OperationState state(addition.getLoc(), "exec.compute");
  state.addOperands(addition->getOperands());
  state.addTypes(addition->getResultTypes());
  state.addAttribute("callee", FlatSymbolRefAttr::get(entry.getSymNameAttr()));
  state.addAttribute("site", builder.getStringAttr("numerical"));
  state.addAttribute("policy", builder.getBoolArrayAttr({false, false, false}));
  auto *replacement = builder.create(state);
  addition.getOutcome().replaceAllUsesWith(replacement->getResult(0));
  addition.erase();
  require(succeeded(verify(module)), "numerical source fixture refused");
}
inline exec::ReturnOp returned(func::FuncOp function) {
  exec::ReturnOp result;
  function.walk([&](exec::ReturnOp op) { result = op; });
  require(bool(result), "missing scoped source return");
  return result;
}
inline ValueRange payload(Operation *call) {
  return cast<exec::DispatchOp>(call->getNextNode())
      .getReturned()
      ->getArguments();
}
inline Operation *duplicateInvocation(Operation *original, func::FuncOp helper,
                                      StringRef site) {
  auto end = returned(helper);
  auto stop = cast<exec::DispatchOp>(original->getNextNode()).getStopped();
  IRRewriter rewriter(helper.getContext());
  auto *before = end->getBlock();
  auto *tail = rewriter.splitBlock(before, end->getIterator());
  OpBuilder builder(helper.getContext());
  builder.setInsertionPointToEnd(before);
  exec::ScopedExecutionBuilder control(builder, helper);
  NamedAttrList attributes(original->getAttrs());
  attributes.set("site", builder.getStringAttr(site));
  auto outputs = control.invoke(
      original->getName().getStringRef(),
      cast<exec::OutcomeType>(original->getResult(0).getType()).getPayload(),
      original->getOperands(), attributes.getAttrs(), stop);
  require(!outputs.empty(), "missing duplicated invocation results");
  auto *call = before->getTerminator()->getPrevNode();
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
  return call;
}
inline Operation *appendApply(func::FuncOp helper, StringRef binding,
                              ValueRange inputs, TypeRange outputs,
                              StringRef site,
                              ArrayRef<StringRef> parameters = {}) {
  auto end = returned(helper);
  exec::DispatchOp first;
  helper.walk([&](exec::DispatchOp op) {
    if (!first)
      first = op;
  });
  require(bool(first), "missing failure continuation");
  IRRewriter rewriter(helper.getContext());
  auto *before = end->getBlock();
  auto *tail = rewriter.splitBlock(before, end->getIterator());
  OpBuilder builder(helper.getContext());
  builder.setInsertionPointToEnd(before);
  exec::ScopedExecutionBuilder control(builder, helper);
  control.invoke(
      "exec.apply", outputs, control.scoped(inputs),
      {builder.getNamedAttr(
           "binding", FlatSymbolRefAttr::get(helper.getContext(), binding)),
       builder.getNamedAttr("parameters", builder.getStrArrayAttr(parameters)),
       builder.getNamedAttr("site", builder.getStringAttr(site))},
      first.getStopped());
  auto *call = before->getTerminator()->getPrevNode();
  rewriter.mergeBlocks(tail, builder.getInsertionBlock());
  return call;
}
inline void omit(Operation *operation, ValueRange replacements = {}) {
  auto dispatch = cast<exec::DispatchOp>(operation->getNextNode());
  auto *next = dispatch.getReturned(), *before = operation->getBlock();
  IRRewriter rewriter(operation->getContext());
  dispatch.erase();
  operation->erase();
  rewriter.mergeBlocks(next, before, replacements);
}
} // namespace zkc::test::scopedComputation
#endif
