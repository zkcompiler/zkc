#ifndef ZKC_TEST_SUPPORT_VARIANT_SPELLING_H
#define ZKC_TEST_SUPPORT_VARIANT_SPELLING_H
#include "zkc/Contracts/Variant.h"

namespace zkc::test {
// Concise wire fixtures belong to tests. Production variants own typed
// payloads; no implicit string-to-type construction is provided there.
struct VariantFixtureAlternative {
  std::string label;
  std::vector<std::string> payload;
};
struct VariantFixtureDescriptor {
  llvm::json::Value nominal;
  std::vector<VariantFixtureAlternative> alternatives;
};
inline std::optional<std::string>
encodeVariantFixture(const VariantFixtureDescriptor &fixture) {
  protocol::TypeParseBudget budget;
  auto nominal = protocol::decodeVariantIdentity(fixture.nominal, budget);
  if (!nominal)
    return std::nullopt;
  protocol::VariantDescriptor descriptor{std::move(*nominal), {}};
  for (const auto &arm : fixture.alternatives) {
    protocol::VariantAlternative alternative{arm.label, {}};
    for (const auto &spelling : arm.payload) {
      auto type = protocol::parseBoundType(spelling, false, 0, &budget);
      if (!type) {
        llvm::consumeError(type.takeError());
        return std::nullopt;
      }
      alternative.payload.push_back(std::move(*type));
    }
    descriptor.alternatives.push_back(std::move(alternative));
  }
  return protocol::encodeVariant(descriptor);
}
} // namespace zkc::test
#endif
