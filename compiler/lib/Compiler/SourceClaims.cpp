#include "zkc/Compiler/SourceClaims.h"
#include "ComponentContracts.h"
#include "zkc/Compiler/StructuredSource.h"
#include "zkc/Dialect/Registry.h"
#include "zkc/Language/Inspection.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"

using namespace llvm;
namespace zkc::language {
namespace {
Expected<json::Value> componentSnapshot(const CheckedOriginal &original) {
  mlir::DialectRegistry registry;
  zkc::registerDialects(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  auto structured = protocol::exportStructuredSource(
      original.bytes(), original.entry().protocol().symbol, context);
  if (!structured)
    return structured.takeError();
  return json::parse(*structured);
}
} // namespace
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
  root["proposals"] = json::Array{};
  root["seams"] = json::Array{};
  auto declarations = inspectComponentDeclarations(original.entry(), limits);
  if (!declarations)
    return declarations.takeError();
  if (*declarations != "[[],[]]") {
    auto snapshot = componentSnapshot(original);
    if (!snapshot)
      return snapshot.takeError();
    auto components = deriveComponentContracts(*snapshot);
    if (!components)
      return components.takeError();
    root["proposals"] = std::move(*components->getArray("proposals"));
    root["seams"] = std::move(*components->getArray("seams"));
  }
  root["admission"] = json::Object{
      {"format", "zkc.structured-source/0"},
      {"original_sha256", sha256(original.bytes())},
      {"protocol_symbol", original.entry().protocol().symbol},
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
  auto actualRoot = actual->getAsObject(),
       canonicalRoot = canonical->getAsObject();
  if (!actualRoot || !actualRoot->getArray("proposals") ||
      !actualRoot->getArray("seams"))
    return error("source.claim.export", "missing component export fields");
  auto proposed = *actualRoot->get("proposals"),
       seams = *actualRoot->get("seams");
  (*actualRoot)["proposals"] = *canonicalRoot->get("proposals");
  (*actualRoot)["seams"] = *canonicalRoot->get("seams");
  if (*actual != *canonical)
    return error("source.claim.export",
                 "claims differ from the checked original");
  (*actualRoot)["proposals"] = std::move(proposed);
  (*actualRoot)["seams"] = std::move(seams);
  if (!canonicalRoot->getArray("proposals")->empty() ||
      !canonicalRoot->getArray("seams")->empty()) {
    auto snapshot = componentSnapshot(original);
    if (!snapshot)
      return snapshot.takeError();
    return checkComponentContracts(*snapshot, *actualRoot);
  }
  if (*actual != *canonical)
    return error("source.claim.export",
                 "claims differ from the checked original");
  return Error::success();
}
} // namespace zkc::language
