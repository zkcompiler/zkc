#include "../ParameterSupport.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/RingExpression.h"
#include "zkc/Dialect/Diagnostics.h"
#include "llvm/ADT/SmallVector.h"

using namespace llvm;
using namespace mlir;
namespace zkc::algebra {
std::optional<LiteralPresentation> literalPresentation(FieldType field) {
  if (!field)
    return std::nullopt;
  auto spelling = protocol::fieldModulus(field.getDomain());
  APInt modulus;
  if (spelling.empty() || spelling.size() > 1234 ||
      spelling.getAsInteger(10, modulus) || modulus.ule(1) ||
      modulus.getActiveBits() > 4096)
    return std::nullopt;
  auto binaryWidth = protocol::fieldBitPatternWidth(field.getDomain());
  auto width = binaryWidth ? binaryWidth : (modulus - 1).getActiveBits();
  return LiteralPresentation{std::move(modulus), width, binaryWidth != 0};
}
bool isPrimeSubfieldLiteral(FieldLiteralAttr literal) {
  auto presentation =
      literal ? literalPresentation(literal.getField()) : std::nullopt;
  if (!presentation || !literal.getValue())
    return false;
  const auto &value = literal.getValue().getValue();
  unsigned width =
      std::max(value.getBitWidth(), presentation->modulus.getBitWidth());
  return value.zextOrTrunc(width).ult(presentation->modulus.zextOrTrunc(width));
}
LogicalResult
FieldLiteralAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                         FieldType field, IntegerAttr value) {
  auto presentation = literalPresentation(field);
  if (!presentation || !value ||
      !value.getType().isUnsignedInteger(presentation->width) ||
      (!presentation->binary &&
       value.getValue()
           .zextOrTrunc(presentation->modulus.getBitWidth())
           .uge(presentation->modulus)))
    return diagnostics::emit(
        emit(), "field-literal",
        "exact field presentation and canonical value required");
  return success();
}
LogicalResult
RingNodeAttr::verify(llvm::function_ref<InFlightDiagnostic()> emit,
                     RingNodeKind kind, DenseI32ArrayAttr indices,
                     FieldLiteralAttr literal, FieldType target) {
  auto refuse = [&] { return diagnostics::emit(emit(), "ring-node-shape"); };
  if (!indices || !symbolizeRingNodeKind(static_cast<uint32_t>(kind)) ||
      any_of(indices.asArrayRef(), [](int32_t i) { return i < 0; }) ||
      bool(literal) != (kind == RingNodeKind::Constant) ||
      bool(target) != (kind == RingNodeKind::Embed))
    return refuse();
  size_t arity = kind == RingNodeKind::Constant ? 0
                 : kind == RingNodeKind::Add || kind == RingNodeKind::Multiply
                     ? 2
                     : 1;
  if (static_cast<size_t>(indices.size()) != arity)
    return refuse();
  if (literal && (!isPrimeSubfieldLiteral(literal) ||
                  failed(FieldLiteralAttr::verify(emit, literal.getField(),
                                                  literal.getValue()))))
    return refuse();
  if (target && !literalPresentation(target))
    return refuse();
  return success();
}
LogicalResult RingExpressionAttr::verify(
    llvm::function_ref<InFlightDiagnostic()> emit, ArrayRef<FieldType> inputs,
    ArrayRef<RingNodeAttr> nodes, DenseI32ArrayAttr outputs) {
  auto refuse = [&](StringRef code) { return diagnostics::emit(emit(), code); };
  if (!outputs || inputs.size() > ring::Limits::inputs ||
      nodes.size() > ring::Limits::nodes ||
      static_cast<size_t>(outputs.size()) > ring::Limits::outputs)
    return refuse("ring-limit");
  for (auto input : inputs)
    if (!literalPresentation(input))
      return refuse("ring-field");
  SmallVector<FieldType> fields;
  SmallVector<uint32_t> depths;
  fields.reserve(nodes.size());
  depths.reserve(nodes.size());
  for (auto [position, node] : enumerate(nodes)) {
    if (!node)
      return refuse("ring-node-shape");
    if (failed(RingNodeAttr::verify(emit, node.getKind(), node.getIndices(),
                                    node.getLiteral(), node.getTarget())))
      return failure();
    auto kind = node.getKind();
    auto indices = node.getIndices().asArrayRef();
    if (kind == RingNodeKind::Constant) {
      fields.push_back(node.getLiteral().getField());
      depths.push_back(1);
      continue;
    }
    if (kind == RingNodeKind::Input) {
      if (static_cast<size_t>(indices.front()) >= inputs.size())
        return refuse("ring-input");
      fields.push_back(inputs[indices.front()]);
      depths.push_back(1);
      continue;
    }
    for (int32_t index : indices)
      if (size_t(index) >= position)
        return refuse("ring-edge");
    auto field = fields[indices.front()];
    auto depth = depths[indices.front()] + 1;
    if (kind == RingNodeKind::Add || kind == RingNodeKind::Multiply) {
      if (field != fields[indices.back()])
        return refuse("ring-field-mismatch");
      depth = std::max(depth, depths[indices.back()] + 1);
    } else if (kind == RingNodeKind::Embed) {
      auto target = node.getTarget();
      const auto &domains = protocol::installedDomains();
      if (!domains.hasFact("ExtensionField", {target.getDomain().str()}) ||
          domains.associatedIdentity(target.getDomain(), "BaseField") !=
              field.getDomain())
        return refuse("ring-embedding");
      field = target;
    }
    if (depth > ring::Limits::depth)
      return refuse("ring-depth");
    fields.push_back(field);
    depths.push_back(depth);
  }
  SmallVector<bool> live(nodes.size(), false);
  for (int32_t output : outputs.asArrayRef()) {
    if (output < 0 || static_cast<size_t>(output) >= nodes.size())
      return refuse("ring-output");
    live[output] = true;
  }
  for (size_t i = nodes.size(); i-- > 0;)
    if (live[i] && nodes[i].getKind() != RingNodeKind::Input)
      for (int32_t index : nodes[i].getIndices().asArrayRef())
        live[index] = true;
  if (!all_of(live, [](bool value) { return value; }))
    return refuse("ring-unreachable-node");
  return success();
}
} // namespace zkc::algebra
