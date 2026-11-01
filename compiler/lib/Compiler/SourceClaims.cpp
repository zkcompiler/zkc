#include "zkc/Compiler/SourceClaims.h"
#include "ComponentContracts.h"
#include "SourceArtifacts.h"
#include "SourceView.h"
#include "zkc/Language/InspectionData.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/Refusal.h"

using namespace llvm;
namespace zkc::language {
namespace {
struct ClaimData {
  json::Value value;
  std::optional<protocol::SourceView> native;
};
Expected<ClaimData> claimData(const CheckedOriginal &original,
                              const Limits &limits) {
  if (auto e = checkLimits(limits))
    return std::move(e);
  if (original.bytes().size() > limits.irBytes ||
      original.interfaceJson().size() > limits.interfaceBytes)
    return error("source.limit", "checked original exceeds export byte limits");
  auto value = sourceClaimsData(original.entry(), limits);
  if (!value)
    return value.takeError();
  auto &root = *value->getAsObject();
  auto declarations = componentDeclarationsData(original.entry(), limits);
  if (!declarations)
    return declarations.takeError();
  std::optional<protocol::SourceView> native;
  const auto &tables = *declarations->getAsArray();
  if (!tables[0].getAsArray()->empty() || !tables[1].getAsArray()->empty()) {
    auto snapshot = detail::OriginalAccess::read(original);
    if (!snapshot)
      return snapshot.takeError();
    native.emplace(std::move(*snapshot));
    auto components = deriveComponentContracts(*native);
    if (!components)
      return components.takeError();
    root["proposals"] = std::move(*components->getArray("proposals"));
    root["seams"] = std::move(*components->getArray("seams"));
  }
  root["admission"] = detail::sourceAdmission(original);
  if (!jsonWithinByteLimit(*value, limits.interfaceBytes))
    return error("source.limit", "source claim export byte limit exceeded");
  return ClaimData{std::move(*value), std::move(native)};
}
} // namespace
Expected<std::string> exportSourceClaims(const CheckedOriginal &original,
                                         const Limits &limits) {
  auto data = claimData(original, limits);
  if (!data)
    return data.takeError();
  return printJson(data->value);
}
Error checkSourceClaims(const CheckedOriginal &original, StringRef bytes,
                        const Limits &limits) {
  auto expected = claimData(original, limits);
  if (!expected)
    return expected.takeError();
  auto actual = zkc::parseNaturalJson(bytes, limits.interfaceBytes,
                                      limits.expressionDepth * 4 + 16,
                                      "source.claim.export", "source.limit");
  if (!actual)
    return actual.takeError();
  auto &canonical = expected->value;
  auto actualRoot = actual->getAsObject(),
       canonicalRoot = canonical.getAsObject();
  if (!actualRoot || !actualRoot->getArray("proposals") ||
      !actualRoot->getArray("seams"))
    return error("source.claim.export", "missing component export fields");
  auto proposed = *actualRoot->get("proposals"),
       seams = *actualRoot->get("seams");
  (*actualRoot)["proposals"] = *canonicalRoot->get("proposals");
  (*actualRoot)["seams"] = *canonicalRoot->get("seams");
  if (!zkc::equalNaturalJson(*actual, canonical))
    return error("source.claim.export",
                 "claims differ from the checked original");
  (*actualRoot)["proposals"] = std::move(proposed);
  (*actualRoot)["seams"] = std::move(seams);
  if (!canonicalRoot->getArray("proposals")->empty() ||
      !canonicalRoot->getArray("seams")->empty()) {
    return checkComponentContracts(*expected->native, *actualRoot);
  }
  if (!zkc::equalNaturalJson(*actual, canonical))
    return error("source.claim.export",
                 "claims differ from the checked original");
  return Error::success();
}
} // namespace zkc::language
