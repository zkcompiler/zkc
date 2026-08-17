//===- AttributeJson.cpp - MLIR attributes as canonical JSON --------------===//
// The one part of the canonical byte layer that reads MLIR. It lives
// beside the encoder rather than with the JSON writer so that the
// writer, the domain rule, and the unique-key parser stay linkable
// without MLIR — which is what lets the registry library compute
// contract digests over them.
//===----------------------------------------------------------------------===//

#include "zkc/Encoding/CanonicalJson.h"

#include "zkc/Encoding/EncodingDomain.h"

#include "mlir/IR/BuiltinAttributes.h"
#include "llvm/Support/Error.h"

using namespace llvm;

llvm::Expected<json::Value>
zkc::encoding::attributeToCanonicalJson(mlir::Attribute attribute,
                                        unsigned depth) {
  if (depth > kMaxAttrDepth)
    return createStringError(
        "attribute nesting exceeds the canonical depth bound");
  if (auto string = mlir::dyn_cast<mlir::StringAttr>(attribute)) {
    if (!inEncodingDomain(string.getValue()))
      return createStringError(
          "string leaves the canonical encoding domain (printable ASCII)");
    return json::Value(string.getValue().str());
  }
  if (mlir::isa<mlir::BoolAttr>(attribute))
    return createStringError(
        "boolean leaves the canonical encoding domain (no boolean encoding)");
  if (auto integer = mlir::dyn_cast<mlir::IntegerAttr>(attribute)) {
    const bool isUnsigned = integer.getType().isUnsignedInteger();
    if (!inIntegerDomain(integer.getValue(), isUnsigned))
      return createStringError(
          "integer leaves the canonical encoding domain (signed 64-bit)");
    return json::Value(
        isUnsigned ? static_cast<int64_t>(integer.getValue().getZExtValue())
                   : integer.getValue().getSExtValue());
  }
  if (auto array = mlir::dyn_cast<mlir::ArrayAttr>(attribute)) {
    json::Array result;
    for (mlir::Attribute member : array) {
      auto converted = attributeToCanonicalJson(member, depth + 1);
      if (!converted)
        return converted.takeError();
      result.push_back(std::move(*converted));
    }
    return json::Value(std::move(result));
  }
  if (auto dictionary = mlir::dyn_cast<mlir::DictionaryAttr>(attribute)) {
    json::Object result;
    for (mlir::NamedAttribute named : dictionary) {
      if (!inEncodingDomain(named.getName().getValue()))
        return createStringError(
            "dictionary key leaves the canonical encoding domain "
            "(printable ASCII)");
      auto converted = attributeToCanonicalJson(named.getValue(), depth + 1);
      if (!converted)
        return converted.takeError();
      result[named.getName().getValue()] = std::move(*converted);
    }
    return json::Value(std::move(result));
  }
  return createStringError("attribute kind has no canonical encoding");
}
