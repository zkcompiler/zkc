#include "zkc/Dialect/Protocol/Origins.h"
#include "zkc/Contracts/SourceTerms.h"
#include "zkc/Support/Refusal.h"

using namespace mlir;
using namespace llvm;
namespace zkc::protocol_ir {
namespace {
Attribute encode(MLIRContext *context, const json::Value &value) {
  if (auto s = value.getAsString())
    return StringAttr::get(context, *s);
  SmallVector<Attribute> items;
  for (const auto &item : *value.getAsArray())
    items.push_back(encode(context, item));
  return ArrayAttr::get(context, items);
}
Expected<json::Value> decode(Attribute attr, unsigned &remaining,
                             unsigned depth = 0) {
  if (!remaining || depth > 132)
    return error("source.protocol-origin", "origin traversal limit exceeded");
  --remaining;
  if (auto s = dyn_cast_or_null<StringAttr>(attr)) {
    if (s.getValue().size() > 2048 || !json::isUTF8(s.getValue()))
      return error("source.protocol-origin", "invalid origin string");
    return s.getValue();
  }
  auto a = dyn_cast_or_null<ArrayAttr>(attr);
  if (!a || a.size() > remaining)
    return error("source.protocol-origin", "expected bounded origin array");
  json::Array items;
  for (Attribute item : a) {
    auto value = decode(item, remaining, depth + 1);
    if (!value)
      return value.takeError();
    items.push_back(std::move(*value));
  }
  return items;
}
} // namespace
ArrayAttr protocolOriginAttr(MLIRContext *context, const json::Value &value) {
  return cast<ArrayAttr>(encode(context, value));
}
Expected<json::Value> readProtocolOrigin(Attribute attr) {
  unsigned remaining = 32768;
  auto value = decode(attr, remaining);
  if (!value)
    return value.takeError();
  if (auto e = checkProtocolOrigin(*value))
    return std::move(e);
  return std::move(*value);
}
} // namespace zkc::protocol_ir
