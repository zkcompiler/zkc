#ifndef ZKC_CONTRACTS_SERVICES_H
#define ZKC_CONTRACTS_SERVICES_H
#include "zkc/Contracts/Domains.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>
#include <optional>
#include <string>
#include <vector>
namespace zkc::protocol {
// Installed random-service signatures. Contracts identify distributions;
// registry references separately authenticate the actual provider root.
struct RandomService {
  llvm::StringLiteral contract, field;
};
inline constexpr RandomService randomServices[] = {
    {"random.bls12-381.fr/0", "bls12-381.fr"},
    {"random.bn254.fr/0", "bn254.fr"},
    {"random.ristretto255.scalar/0", "ristretto255.scalar"},
    {"random.koala-bear.ext8-binomial3/0", "koala-bear.ext8-binomial3"}};
inline llvm::StringRef randomServiceField(llvm::StringRef contract) {
  for (const auto &service : randomServices)
    if (service.contract == contract)
      return service.field;
  return {};
}
inline llvm::StringRef randomServiceContract(llvm::StringRef field) {
  for (const auto &service : randomServices)
    if (service.field == field)
      return service.contract;
  return {};
}
// UniformIndex(N) admits exactly the powers of two 1 through 2^63; the
// installed sampler masks one uniform 64-bit word to log2(N) bits.
inline bool uniformIndexBound(uint64_t bound) {
  return bound && !(bound & (bound - 1));
}
// Canonical unsigned decimal spelling of an admitted bound.
inline std::optional<uint64_t> parseUniformIndexBound(llvm::StringRef text) {
  uint64_t bound;
  if (text.empty() || text.size() > 19 || (text.size() > 1 && text[0] == '0') ||
      !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
      text.getAsInteger(10, bound) || !uniformIndexBound(bound))
    return {};
  return bound;
}
// Method signatures as logical type spellings. `draw` returns one element of
// the service field. `index` takes a UniformIndex bound and returns an index;
// it exists only where the catalog grants IndexRandomness to that field.
struct ServiceMethod {
  std::vector<std::string> inputs;
  std::string output;
};
inline std::optional<ServiceMethod> serviceMethod(llvm::StringRef contract,
                                                  llvm::StringRef method) {
  auto field = randomServiceField(contract);
  if (field.empty())
    return {};
  if (method == "draw")
    return ServiceMethod{{}, "field:" + field.str()};
  if (method == "index" &&
      installedDomains().hasFact("IndexRandomness", {field.str()}))
    return ServiceMethod{{"index"}, "index"};
  return {};
}
inline llvm::StringRef nativeChallengeField(llvm::StringRef suite) {
  // Native proof support is an explicit policy; the catalog owns the field.
  if (suite == "merlin3.bls12-381.fr64be/0" ||
      suite == "spongefish0.7.4.keccak.bls12-381.fr64be/0" ||
      suite == "merlin3.ristretto255.scalar64le/0" ||
      suite == "merlin3.koala-bear.ext8-binomial3.rejection31le/0")
    return installedDomains().associatedIdentity(suite, "ChallengeField");
  return {};
}
} // namespace zkc::protocol
#endif
