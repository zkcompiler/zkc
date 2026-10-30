#ifndef ZKC_CONTRACTS_SERVICES_H
#define ZKC_CONTRACTS_SERVICES_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Domains.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"
#include <cstdint>
#include <optional>
#include <string>
#include <vector>
namespace zkc::protocol {
// Source constructors name installed declarations, not reserved type spellings.
// The family selects the logical signature adapter; provider identities below
// independently select execution and its registered interpretation.
enum class ServiceFamily { Random };
struct SourceService {
  llvm::StringLiteral module, name;
  ServiceFamily family;
  unsigned parameters;
};
inline constexpr SourceService sourceServices[] = {
    {"zkc::prelude", "Random", ServiceFamily::Random, 1}};
inline const SourceService *sourceService(llvm::StringRef qualifiedName) {
  auto [module, name] = qualifiedName.rsplit("::");
  for (const auto &service : sourceServices)
    if (service.module == module && service.name == name)
      return &service;
  return nullptr;
}
// Installed random-service signatures. Contracts identify distributions;
// registry references separately authenticate the actual provider root.
struct RandomService {
  llvm::StringLiteral contract, field;
};
inline constexpr RandomService randomServices[] = {
    {"random.bls12-381.fr/0", "bls12-381.fr"},
    {"random.bn254.fr/0", "bn254.fr"},
    {"random.ristretto255.scalar/0", "ristretto255.scalar"},
    {"random.koala-bear.ext8-binomial3/0", "koala-bear.ext8-binomial3"},
    {"random.baby-bear.ext4-binomial11/0", "baby-bear.ext4-binomial11"},
    {"random.goldilocks.ext2-binomial7/0", "goldilocks.ext2-binomial7"}};
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
// UniformIndex(N) is an ideal range request over a positive u64 bound.
// A selected provider or construction separately admits its sampling algorithm.
inline bool uniformIndexBound(uint64_t bound) { return bound != 0; }
// Canonical unsigned decimal spelling of an admitted bound.
inline std::optional<uint64_t> parseUniformIndexBound(llvm::StringRef text) {
  uint64_t bound;
  if (text.empty() || text.size() > 20 || (text.size() > 1 && text[0] == '0') ||
      !llvm::all_of(text, [](char c) { return c >= '0' && c <= '9'; }) ||
      text.getAsInteger(10, bound) || !uniformIndexBound(bound))
    return {};
  return bound;
}
// Method signatures as typed logical declarations. `draw` returns one element
// of the service field. `index` takes a UniformIndex bound and returns an
// index; it exists only where the catalog grants IndexRandomness to that field.
struct ServiceMethod {
  std::vector<BoundType> inputs;
  BoundType output;
};
inline std::optional<ServiceMethod> serviceMethod(llvm::StringRef contract,
                                                  llvm::StringRef method) {
  auto field = randomServiceField(contract);
  if (field.empty())
    return {};
  if (method == "draw")
    return ServiceMethod{{}, {"field", field.str(), {}}};
  if (method == "index" &&
      installedDomains().hasFact("IndexRandomness", {field.str()}))
    return ServiceMethod{{{"index", {}, {}}}, {"index", {}, {}}};
  return {};
}
inline llvm::StringRef nativeChallengeField(llvm::StringRef suite) {
  // Native proof support is an explicit policy; the catalog owns the field.
  if (suite == "merlin3.bls12-381.fr64be/0" ||
      suite == "spongefish0.8.0.keccak.bls12-381.fr64be/0" ||
      suite == "merlin3.ristretto255.scalar64le/0" ||
      suite == "merlin3.koala-bear.ext8-binomial3.rejection31le/0" ||
      suite == "merlin3.baby-bear.ext4-binomial11.rejection31le/0" ||
      suite == "merlin3.goldilocks.ext2-binomial7.rejection64le/0" ||
      suite == "hash-chain.keccak256.bls12-381.fr64be/0" ||
      suite == "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0")
    return installedDomains().associatedIdentity(suite, "ChallengeField");
  return {};
}
} // namespace zkc::protocol
#endif
