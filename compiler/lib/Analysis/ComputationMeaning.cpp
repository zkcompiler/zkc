#include "zkc/Analysis/ComputationMeaning.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Bindings.h"
#include "zkc/Dialect/Data/IR/DataOps.h"
#include "zkc/Dialect/Exec/IR/ExecOps.h"
#include "zkc/Dialect/Runtime/IR/RuntimeOps.h"
#include "zkc/Interfaces/Mathematical.h"
#include "llvm/ADT/DenseSet.h"

using namespace mlir;
using namespace llvm;
namespace zkc::finite {
namespace {
std::optional<protocol::BindingApplication> semanticBinding(Operation *op) {
  auto reference = op->getAttrOfType<FlatSymbolRefAttr>("binding");
  auto declaration =
      reference ? SymbolTable::lookupNearestSymbolFrom<runtime::BindingOp>(
                      op, reference)
                : runtime::BindingOp();
  if (!declaration || !declaration.getContractAttr() ||
      !declaration.getArgumentsAttr() || !declaration.getImplementationAttr())
    return std::nullopt;
  protocol::BindingApplication application{
      declaration.getContract().str(),
      {},
      declaration.getImplementation().str()};
  for (auto attr : declaration.getArguments()) {
    auto value = dyn_cast<StringAttr>(attr);
    if (!value)
      return std::nullopt;
    application.arguments.push_back(value.getValue().str());
  }
  return application;
}
} // namespace
const protocol::ComputationContract *semantics(Operation *op) {
  if (!op || op->getNumRegions() || op->getNumResults() != 1)
    return nullptr;
  protocol::BindingApplication application;
  SmallVector<std::string> parameters;
  if (op->hasAttr("binding")) {
    for (auto attribute : op->getAttrs())
      if (!is_contained(ArrayRef<StringRef>{"binding", "parameters", "site"},
                        attribute.getName().getValue()))
        return nullptr;
    // Binding admission validates the original physical constraint separately.
    // Reading mathematical meaning must not re-enter physical resolution.
    auto binding = semanticBinding(op);
    if (!binding)
      return nullptr;
    application = std::move(*binding);
    if (!isa<exec::ApplyOp>(op))
      return nullptr;
    auto attrs = op->getAttrOfType<ArrayAttr>("parameters");
    if (!attrs)
      return nullptr;
    for (auto attr : attrs) {
      auto value = dyn_cast<StringAttr>(attr);
      if (!value)
        return nullptr;
      parameters.push_back(value.getValue().str());
    }
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
      parameters.push_back(constant.getValue().str());
    } else if (!op->getAttrs().empty())
      return nullptr;
    // The admitted total syntax has explicit logical signature adapters. A
    // meaning lookup never chooses the first executable declaration sharing it.
    if (isa<algebra::ConstantFieldOp>(op))
      application.contract = "field.constant";
    else if (isa<algebra::FieldAddOp>(op))
      application.contract = "field.add";
    else if (isa<algebra::SubtractFieldOp>(op))
      application.contract = "field.sub";
    else if (isa<algebra::FieldMultiplyOp>(op))
      application.contract = "field.mul";
    else if (isa<algebra::GroupAddOp>(op))
      application.contract = "curve.add";
    else if (isa<algebra::GroupScaleOp>(op))
      application.contract = "curve.scale";
    else if (isa<data::BoundedAtOp>(op))
      application.contract = "vector.get";
    else
      application.contract = "matrix.get";
    auto result = protocol::encodeBoundType(op->getResult(0).getType(), false);
    if (!result) {
      consumeError(result.takeError());
      return nullptr;
    }
    application.arguments.push_back(result->identity);
  }
  SmallVector<protocol::BoundType> inputs, outputs;
  auto read = [](TypeRange types, SmallVectorImpl<protocol::BoundType> &out) {
    for (Type type : types) {
      auto bound = protocol::encodeBoundType(type, false);
      if (!bound) {
        consumeError(bound.takeError());
        return false;
      }
      out.push_back(std::move(*bound));
    }
    return true;
  };
  if (auto apply = dyn_cast<exec::ApplyOp>(op)) {
    // Meaning observes the data ports of the scoped invocation. The enclosing
    // source reader owns scope/dispatch formation and reached-failure behavior.
    auto outcome = dyn_cast<exec::OutcomeType>(apply.getResult().getType());
    if (!outcome || op->getNumOperands() == 0 ||
        !isa<runtime::ScopeType>(op->getOperand(0).getType()) ||
        !read(apply.getInputs().getTypes(), inputs) ||
        !read(outcome.getPayload(), outputs))
      return nullptr;
  } else if (!read(op->getOperandTypes(), inputs) ||
             !read(op->getResultTypes(), outputs))
    return nullptr;
  return protocol::admitMathematicalMeaning(application, inputs, outputs,
                                            parameters);
}
bool replaceable(Operation *op) {
  if (!semantics(op))
    return false;
  if (!op->hasAttr("binding"))
    return true;
  auto binding = semanticBinding(op);
  return binding && binding->implementation.empty();
}
std::optional<std::string> fieldConstant(Operation *op) {
  auto *facet = semantics(op);
  if (!facet || facet->identity != MathematicalIdentity::FieldConstant)
    return std::nullopt;
  if (auto constant = dyn_cast<algebra::ConstantFieldOp>(op))
    return constant.getValue().str();
  return cast<StringAttr>(op->getAttrOfType<ArrayAttr>("parameters")[0])
      .getValue()
      .str();
}
} // namespace zkc::finite
