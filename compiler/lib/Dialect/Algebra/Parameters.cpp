#include "zkc/Dialect/Algebra/Parameters.h"
#include "ParameterSupport.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/SmallString.h"

using namespace llvm;
using namespace mlir;
namespace zkc::algebra {
Expected<FieldLiteralAttr> decodeFieldLiteral(FieldType field, StringRef text) {
  auto presentation = literalPresentation(field);
  if (!presentation || text.empty() || text.size() > 1234)
    return zkc::error("field-literal");
  auto digits = text;
  bool bits = digits.consume_front("0x");
  if (digits.empty() || (digits.size() > 1 && digits.front() == '0') ||
      !all_of(digits, [&](char c) {
        return (c >= '0' && c <= '9') || (bits && c >= 'a' && c <= 'f');
      }))
    return zkc::error("field-literal");
  APInt value;
  if (digits.getAsInteger(bits ? 16 : 10, value) ||
      value.getActiveBits() > presentation->width ||
      (bits && (!presentation->binary || value.ule(1))) ||
      (!bits && (presentation->binary
                     ? value.ugt(1)
                     : value.zextOrTrunc(presentation->modulus.getBitWidth())
                           .uge(presentation->modulus))))
    return zkc::error("field-literal");
  auto integer =
      IntegerAttr::get(IntegerType::get(field.getContext(), presentation->width,
                                        IntegerType::Unsigned),
                       value.zextOrTrunc(presentation->width));
  return FieldLiteralAttr::get(field.getContext(), field, integer);
}
Expected<std::string> encodeFieldLiteral(FieldLiteralAttr literal) {
  if (!literal || failed(FieldLiteralAttr::verify(
                      [&] {
                        auto diagnostic =
                            emitError(UnknownLoc::get(literal.getContext()));
                        diagnostic.abandon();
                        return diagnostic;
                      },
                      literal.getField(), literal.getValue())))
    return zkc::error("field-literal");
  auto presentation = literalPresentation(literal.getField());
  const auto &value = literal.getValue().getValue();
  bool bits = presentation->binary && value.ugt(1);
  SmallString<128> digits;
  value.toString(digits, bits ? 16 : 10, false);
  return bits ? "0x" + StringRef(digits).lower() : digits.str().str();
}
Expected<RingExpressionAttr>
importRingExpression(MLIRContext *context, const ring::Expression &value) {
  if (!context || !context->getLoadedDialect<AlgebraDialect>())
    return zkc::error("ring-field");
  SmallVector<FieldType> inputs;
  for (const auto &input : value.inputs())
    inputs.push_back(FieldType::get(context, input.field));
  SmallVector<RingNodeAttr> nodes;
  for (const auto &node : value.nodes()) {
    RingNodeKind kind;
    SmallVector<int32_t> indices;
    FieldLiteralAttr literal;
    FieldType target;
    switch (node.kind) {
    case ring::Kind::Constant: {
      kind = RingNodeKind::Constant;
      auto decoded = decodeFieldLiteral(FieldType::get(context, node.field),
                                        node.constant);
      if (!decoded)
        return decoded.takeError();
      literal = *decoded;
      break;
    }
    case ring::Kind::Input:
      kind = RingNodeKind::Input;
      indices.push_back(node.input);
      break;
    case ring::Kind::Add:
    case ring::Kind::Mul:
      kind = node.kind == ring::Kind::Add ? RingNodeKind::Add
                                          : RingNodeKind::Multiply;
      indices = {int32_t(node.left), int32_t(node.right)};
      break;
    case ring::Kind::Neg:
    case ring::Kind::Embed:
      kind = node.kind == ring::Kind::Neg ? RingNodeKind::Negate
                                          : RingNodeKind::Embed;
      indices.push_back(node.left);
      if (node.kind == ring::Kind::Embed)
        target = FieldType::get(context, node.field);
      break;
    }
    nodes.push_back(RingNodeAttr::get(context, kind,
                                      DenseI32ArrayAttr::get(context, indices),
                                      literal, target));
  }
  SmallVector<int32_t> outputs(value.outputs().begin(), value.outputs().end());
  return RingExpressionAttr::get(context, inputs, nodes,
                                 DenseI32ArrayAttr::get(context, outputs));
}
Expected<ring::Expression> exportRingExpression(RingExpressionAttr value) {
  if (!value || failed(RingExpressionAttr::verify(
                    [&] {
                      // An empty diagnostic converts to success. Abandon only
                      // publication of this real diagnostic, retaining failure.
                      auto diagnostic =
                          emitError(UnknownLoc::get(value.getContext()));
                      diagnostic.abandon();
                      return diagnostic;
                    },
                    value.getInputs(), value.getNodes(), value.getOutputs())))
    return zkc::error("ring-attribute");
  std::vector<ring::Input> inputs;
  for (auto input : value.getInputs())
    inputs.push_back({input.getDomain().str()});
  std::vector<ring::Node> nodes;
  for (auto node : value.getNodes()) {
    auto indices = node.getIndices().asArrayRef();
    switch (node.getKind()) {
    case RingNodeKind::Constant: {
      auto literal = encodeFieldLiteral(node.getLiteral());
      if (!literal)
        return literal.takeError();
      nodes.push_back(ring::Node::literal(
          node.getLiteral().getField().getDomain().str(), std::move(*literal)));
      break;
    }
    case RingNodeKind::Input:
      nodes.push_back(ring::Node::slot(indices[0]));
      break;
    case RingNodeKind::Add:
      nodes.push_back(ring::Node::add(indices[0], indices[1]));
      break;
    case RingNodeKind::Multiply:
      nodes.push_back(ring::Node::mul(indices[0], indices[1]));
      break;
    case RingNodeKind::Negate:
      nodes.push_back(ring::Node::neg(indices[0]));
      break;
    case RingNodeKind::Embed:
      nodes.push_back(
          ring::Node::embed(node.getTarget().getDomain().str(), indices[0]));
      break;
    }
  }
  std::vector<uint32_t> outputs(value.getOutputs().asArrayRef().begin(),
                                value.getOutputs().asArrayRef().end());
  return ring::Expression::create(std::move(inputs), std::move(nodes),
                                  std::move(outputs));
}

namespace {
bool formed(RingExpressionAttr value) {
  return value && succeeded(RingExpressionAttr::verify(
                      [&] {
                        auto diagnostic =
                            emitError(UnknownLoc::get(value.getContext()));
                        diagnostic.abandon();
                        return diagnostic;
                      },
                      value.getInputs(), value.getNodes(), value.getOutputs()));
}
// The native encoder does not reconstruct a neutral graph. Its output is
// checked against the independent neutral writer in the boundary tests.
void writeRing(raw_ostream &out, RingExpressionAttr value) {
  out << "[\"zkc.ring/0\",[";
  interleave(
      value.getInputs(), out,
      [&](FieldType field) { out << json::Value(field.getDomain()); }, ",");
  out << "],[";
  interleave(
      value.getNodes(), out,
      [&](RingNodeAttr node) {
        out << '[';
        switch (node.getKind()) {
        case RingNodeKind::Constant: {
          SmallString<128> digits;
          node.getLiteral().getValue().getValue().toString(digits, 10, false);
          out << "\"constant\","
              << json::Value(node.getLiteral().getField().getDomain()) << ','
              << json::Value(StringRef(digits));
          break;
        }
        case RingNodeKind::Input:
          out << "\"input\"," << node.getIndices()[0];
          break;
        case RingNodeKind::Add:
        case RingNodeKind::Multiply:
          out << (node.getKind() == RingNodeKind::Add ? "\"add\"," : "\"mul\",")
              << node.getIndices()[0] << ',' << node.getIndices()[1];
          break;
        case RingNodeKind::Negate:
          out << "\"neg\"," << node.getIndices()[0];
          break;
        case RingNodeKind::Embed:
          out << "\"embed\"," << json::Value(node.getTarget().getDomain())
              << ',' << node.getIndices()[0];
          break;
        }
        out << ']';
      },
      ",");
  out << "],[";
  interleave(value.getOutputs().asArrayRef(), out, ",");
  out << "]]";
}
class ByteCounter : public raw_ostream {
  uint64_t count = 0;
  void write_impl(const char *, size_t bytes) override { count += bytes; }
  uint64_t current_pos() const override { return count; }

public:
  ByteCounter() : raw_ostream(/*unbuffered=*/true) {}
};
} // namespace
Expected<std::string> encodeRingExpression(RingExpressionAttr value) {
  if (!formed(value))
    return zkc::error("ring-attribute");
  std::string result;
  raw_string_ostream out(result);
  writeRing(out, value);
  if (result.size() > ring::Limits::bytes)
    return zkc::error("ring-limit");
  return result;
}
Expected<uint64_t> ringExpressionByteSize(RingExpressionAttr value) {
  if (!formed(value))
    return zkc::error("ring-attribute");
  ByteCounter out;
  writeRing(out, value);
  return out.tell();
}
} // namespace zkc::algebra
