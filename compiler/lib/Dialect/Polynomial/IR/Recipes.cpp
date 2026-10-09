#include "zkc/Contracts/Variant.h"
#include "zkc/Dialect/Algebra/IR/AlgebraOps.h"
#include "zkc/Dialect/Algebra/Mathematical.h"
#include "zkc/Dialect/Algebra/RingExpression.h"
#include "zkc/Dialect/Diagnostics.h"
#include "zkc/Dialect/Local/IR/LocalTypes.h"
#include "zkc/Dialect/Polynomial/IR/PolynomialOps.h"
#include "zkc/Dialect/Polynomial/Mathematical.h"
#include "zkc/Dialect/Protocol/IR/ProtocolOps.h"
#include "llvm/ADT/StringExtras.h"
using namespace mlir;
using namespace llvm;
namespace zkc::poly {
namespace {
LogicalResult refuse(Operation *op, StringRef detail) {
  return diagnostics::emit(op->emitOpError(), "polynomial-formation", detail);
}
bool name(StringRef s) {
  return !s.empty() && s.size() <= 96 &&
         (isAlpha(s.front()) || s.front() == '_') && all_of(s, [](char c) {
           return isAlnum(c) || c == '_' || c == '.' || c == '-';
         });
}
} // namespace
FailureOr<unsigned> recipeDegree(RecipeOp recipe) {
  auto symbol = recipe->getAttrOfType<StringAttr>("sym_name");
  auto declared = recipe->getAttrOfType<IntegerAttr>("degree");
  if (!symbol || !name(symbol.getValue()) || !declared ||
      !declared.getType().isSignlessInteger(64) || declared.getInt() < 0 ||
      declared.getInt() > 16 || recipe->getNumRegions() != 1 ||
      recipe->getNumOperands() || recipe->getNumResults() ||
      recipe->getAttrs().size() != 2 || !hasSingleElement(recipe.getBody()))
    return failure();
  auto &body = recipe.getBody().front();
  if (body.getNumArguments() == 0 || body.getNumArguments() > 16 ||
      body.empty())
    return failure();
  Type field = body.getArgument(0).getType();
  if (!isa<algebra::FieldType>(field))
    return failure();
  if (!all_of(body.getArgumentTypes(),
              [&](Type type) { return type == field; }) ||
      std::distance(body.begin(), body.end()) > 129)
    return failure();
  auto result = dyn_cast<RecipeYieldOp>(body.back());
  if (!result || result->getNumOperands() != 1 || result->getNumResults() ||
      result->getNumRegions() || !result->getAttrs().empty() ||
      result.getValue().getType() != field)
    return failure();
  SmallVector<Value> observations;
  for (auto &op : body.without_terminator())
    observations.append(op.getResults().begin(), op.getResults().end());
  observations.push_back(result.getValue());
  auto expression = algebra::describeRingExpression(body, observations);
  if (!expression) {
    consumeError(expression.takeError());
    return failure();
  }
  // The Ring view owns arithmetic degree propagation. Polynomial recipes retain
  // their smaller realization ABI and declared (possibly loose) output bound.
  for (const auto &fact : expression->facts())
    if (fact.degree > 16)
      return failure();
  if (expression->facts()[expression->outputs().back()].degree >
      uint64_t(declared.getInt()))
    return failure();
  // This is an ABI bound, not a simplifier-dependent estimate.
  return unsigned(declared.getInt());
}
LogicalResult RecipeOp::verifyRegions() {
  auto owner = dyn_cast<protocol_ir::ProtocolModuleOp>((*this)->getParentOp());
  if (!owner || owner.getProfile() != protocol_ir::Profile::Protocol ||
      failed(recipeDegree(*this)))
    return refuse(*this, "recipe requires 1..16 field slots and a closed ring "
                         "expression of at most 128 operations and degree 16");
  return success();
}
Type residualStateType(RecipeOp recipe) {
  if (failed(recipeDegree(recipe)))
    return {};
  auto &body = recipe.getBody().front();
  auto field =
      cast<algebra::FieldType>(body.getArgument(0).getType()).getDomain();
  std::vector<std::string> payload{"point:" + field.str()};
  payload.resize(1 + body.getNumArguments(), "table:" + field.str());
  auto descriptor = protocol::encodeVariant(
      {"poly.residual." + recipe.getSymName().str(), {{"state", payload}}});
  return descriptor
             ? Type(local::VariantType::get(recipe.getContext(), *descriptor))
             : Type{};
}
FailureOr<FunctionType> realizationType(RealizeOp realization) {
  auto reference = realization->getAttrOfType<FlatSymbolRefAttr>("recipe");
  auto kindAttr = realization->getAttrOfType<StringAttr>("kind");
  if (!reference || !kindAttr)
    return failure();
  auto recipe =
      SymbolTable::lookupNearestSymbolFrom<RecipeOp>(realization, reference);
  if (!recipe || failed(recipeDegree(recipe)))
    return failure();
  auto field = cast<algebra::FieldType>(
      recipe.getBody().front().getArgument(0).getType());
  // The existing dynamically shaped MLE installation is BLS12-381 only.
  if (field.getDomain() != "bls12-381.fr")
    return failure();
  auto *context = realization.getContext();
  auto state = residualStateType(recipe);
  if (!state)
    return failure();
  auto table = MultilinearType::get(context, field.getDomain());
  auto point = PointType::get(context, field.getDomain());
  auto index = IntegerType::get(context, 64, IntegerType::Unsigned);
  SmallVector<Type> inputs, outputs;
  auto kind = realization.getKind();
  if (kind == "init" || kind == "evaluate") {
    inputs.push_back(kind == "init" ? Type(index) : Type(point));
    inputs.append(recipe.getBody().front().getNumArguments(), table);
    outputs.push_back(kind == "init" ? state : Type(field));
  } else if (kind == "bind") {
    inputs = {state, field};
    outputs = {state};
  } else if (kind == "round") {
    inputs = {state};
    outputs = {
        RankedTensorType::get({int64_t(*recipeDegree(recipe)) + 1}, field)};
  } else if (kind == "finish") {
    inputs = {state};
    outputs = {point, field};
  } else if (kind == "arity") {
    inputs = {state};
    outputs = {index};
  } else
    return failure();
  return FunctionType::get(context, inputs, outputs);
}
LogicalResult RealizeOp::verify() {
  auto owner = dyn_cast<protocol_ir::ProtocolModuleOp>((*this)->getParentOp());
  if (!owner || owner.getProfile() != protocol_ir::Profile::Protocol ||
      (*this)->getAttrs().size() != 4 || !name(getSymName()))
    return refuse(
        *this, "realization requires a recipe and its exact derived signature");
  return success();
}
LogicalResult RealizeOp::verifySymbolUses(SymbolTableCollection &) {
  auto expected = realizationType(*this);
  if (failed(expected) || *expected != getFunctionType())
    return refuse(
        *this, "realization requires a recipe and its exact derived signature");
  return success();
}
} // namespace zkc::poly
