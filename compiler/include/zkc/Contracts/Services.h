#ifndef ZKC_CONTRACTS_SERVICES_H
#define ZKC_CONTRACTS_SERVICES_H
#include "llvm/ADT/StringRef.h"
namespace zkc::protocol {
// Installed random-service signatures. Contracts identify distributions;
// registry references separately authenticate the actual provider root.
struct RandomService {
  llvm::StringLiteral contract, field;
};
inline constexpr RandomService randomServices[] = {
    {"random.bls12-381.fr/1", "bls12-381.fr"},
    {"random.bn254.fr/1", "bn254.fr"},
    {"random.ristretto255.scalar/1", "ristretto255.scalar"},
    {"random.koala-bear.ext8-binomial3/1", "koala-bear.ext8-binomial3"}};
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
inline llvm::StringRef nativeChallengeField(llvm::StringRef suite) {
  if (suite == "merlin3.bls12-381.fr64be/1" ||
      suite == "spongefish0.7.4.keccak.bls12-381.fr64be/1")
    return "bls12-381.fr";
  if (suite == "merlin3.ristretto255.scalar64le/1")
    return "ristretto255.scalar";
  if (suite == "merlin3.koala-bear.ext8-binomial3.rejection31le/1")
    return "koala-bear.ext8-binomial3";
  return {};
}
} // namespace zkc::protocol
#endif
