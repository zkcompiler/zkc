#include "zkc/Analysis/ComputationMeaning.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Parameters.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/InvocationParameters.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
runtime::BindingOp semanticBinding(Operation *op) {
  auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto declaration =
      reference ? SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                      op, reference)
                : runtime::BindingOp();
  if (!declaration || !declaration.getContractAttr() ||
      !declaration.getArgumentsAttr() || !declaration.getImplementationAttr())
    return {};
  auto checked = readLogicalBindingSignature(
      [&] {
        auto diagnostic = emitError(op->getLoc());
        diagnostic.abandon();
        return diagnostic;
      },
      declaration);
  return checked ? declaration : runtime::BindingOp{};
}
} // namespace
const protocol::ComputationContract *semantics(Operation *op) {
  if (!op || op->getNumRegions() || op->getNumResults() != 1)
    return nullptr;
  StringRef contract;
  SmallVector<Attribute> arguments, parameters;
  if (op->hasAttr("binding")) {
    for (auto attribute : op->getAttrs())
      if (!is_contained(ArrayRef<StringRef>{"binding", "parameters", "site"},
                        attribute.getName().getValue()))
        return nullptr;
    // Inspect the logical signature independently of provider availability.
    // The original implementation constraint still prohibits replacement;
    // meaning lookup never reconstructs a neutral binding application.
    auto binding = semanticBinding(op);
    if (!binding)
      return nullptr;
    contract = binding.getContract();
    append_range(arguments, binding.getArguments());
    if (!isa<exec::ApplyOp>(op))
      return nullptr;
    auto attrs = op->getAttrOfType<ArrayAttr>("parameters");
    if (!attrs)
      return nullptr;
    append_range(parameters, attrs);

  } else {
    // A mathematical interface alone is not a closed profile admission rule.
    if (!isa<algebra::ConstantFieldOp, algebra::FieldAddOp,
             algebra::SubtractFieldOp, algebra::FieldMultiplyOp,
             algebra::GroupAddOp, algebra::GroupScaleOp, data::BoundedAtOp,
             data::BoundedMatrixAtOp>(op))
      return nullptr;
    if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op)) {
      if (op->getAttrs().size() != 1 || !constant.getValueAttr())
        return nullptr;
      parameters.push_back(constant.getValue());
    } else if (!op->getAttrs().empty())
      return nullptr;
    // The admitted total syntax has explicit logical signature adapters. A
    // meaning lookup never chooses the first executable declaration sharing it.
    if (isa<algebra::ConstantFieldOp>(op))
      contract = "field.constant";
    else if (isa<algebra::FieldAddOp>(op))
      contract = "field.add";
    else if (isa<algebra::SubtractFieldOp>(op))
      contract = "field.sub";
    else if (isa<algebra::FieldMultiplyOp>(op))
      contract = "field.mul";
    else if (isa<algebra::GroupAddOp>(op))
      contract = "curve.add";
    else if (isa<algebra::GroupScaleOp>(op))
      contract = "curve.scale";
    else if (isa<data::BoundedAtOp>(op))
      contract = "vector.get";
    else
      contract = "matrix.get";
    auto type = op->getResult(0).getType();
    if (auto field = dyn_cast<algebra::FieldType>(type))
      arguments.push_back(StringAttr::get(op->getContext(), field.getDomain()));
    else if (auto group = dyn_cast<algebra::GroupType>(type))
      arguments.push_back(StringAttr::get(op->getContext(), group.getDomain()));
    else
      return nullptr;
  }
  auto silent = [&] {
    auto diagnostic = emitError(op->getLoc());
    diagnostic.abandon();
    return diagnostic;
  };
  auto signature =
      resolveLogicalSignature(silent, op->getContext(), contract, arguments);
  if (!signature ||
      failed(verifyInvocationParameters(
          silent, contract, ArrayAttr::get(op->getContext(), arguments),
          ArrayAttr::get(op->getContext(), parameters))))
    return nullptr;
  if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
    auto outcome = dyn_cast<exec::OutcomeType>(apply.getResult().getType());
    if (!outcome || op->getNumOperands() == 0 ||
        !isa<runtime::ScopeType>(op->getOperand(0).getType()) ||
        !equal(apply.getInputs().getTypes(), signature.getInputs()) ||
        !equal(outcome.getPayload(), signature.getResults()))
      return nullptr;
  } else if (!equal(op->getOperandTypes(), signature.getInputs()) ||
             !equal(op->getResultTypes(), signature.getResults()))
    return nullptr;
  return protocol::computationContract(contract);
}
bool replaceable(Operation *op) {
  if (!semantics(op))
    return false;
  if (!op->hasAttr("binding"))
    return true;
  auto binding = semanticBinding(op);
  return binding && binding.getImplementation().empty();
}
algebra::FieldLiteralAttr fieldConstant(Operation *op) {
  auto *facet = semantics(op);
  if (!facet || facet->identity != MathematicalIdentity::FieldConstant)
    return {};
  if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
    return constant.getValue();
  return cast<algebra::FieldLiteralAttr>(
      op->getAttrOfType<ArrayAttr>("parameters")[0]);
}
} // namespace zkc::finite
