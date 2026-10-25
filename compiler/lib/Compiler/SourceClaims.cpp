#include "zkc/Compiler/SourceClaims.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::language {
Expected<std::string> exportSourceClaims(const CheckedOriginal &original,
                                         const Limits &limits) {
  auto claims = inspectSourceClaims(original.entry(), limits);
  if (!claims)
    return claims.takeError();
  auto value = json::parse(*claims);
  if (!value)
    return value.takeError();
  auto sha256 = [](StringRef bytes) {
    return "sha256:" + toHex(SHA256::hash(arrayRefFromStringRef(bytes)), true);
  };
  auto &root = *value->getAsObject();
  root["admission"] = json::Object{
      {"format", "zkc.structured-source/0"},
      {"original_sha256", sha256(original.bytes())},
      {"protocol_symbol", original.entry().protocol().symbol},
      {"original_identity", original.identity()},
      {"interface_sha256", sha256(original.interfaceJson())},
      {"capture", original.entry().project().capture().identity()},
      {"installation", original.entry().project().installationIdentity()}};
  std::string bytes;
  BoundedStream out(bytes, limits.interfaceBytes);
  out << *value;
  if (out.overflow())
    return error("source.limit", "source claim export byte limit exceeded");
  return bytes;
}
Error checkSourceClaims(const CheckedOriginal &original, StringRef bytes,
                        const Limits &limits) {
  auto expected = exportSourceClaims(original, limits);
  if (!expected)
    return expected.takeError();
  auto actual = zkc::parseNaturalJson(bytes, limits.interfaceBytes,
                                      limits.expressionDepth * 4 + 16,
                                      "source.claim.export", "source.limit");
  if (!actual)
    return actual.takeError();
  auto canonical = json::parse(*expected);
  if (!canonical)
    return canonical.takeError();
  if (*actual != *canonical)
    return error("source.claim.export",
                 "claims differ from the checked original");
  return Error::success();
}
} // namespace zkc::language
