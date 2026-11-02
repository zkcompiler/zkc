#ifndef ZKC_CONTRACTS_SERVICES_H
#define ZKC_CONTRACTS_SERVICES_H
#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Declarations.h"
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
  llvm::StringRef module, name;
  ServiceFamily family;
  unsigned parameters;
};
inline const std::vector<SourceService> sourceServices = [] {
  std::vector<SourceService> rows;
  for (const auto &association : frontendAssociations())
    if (association.signature == FrontendSignature::RandomConstructor)
      rows.push_back(
          {association.module, association.name, ServiceFamily::Random, 1});
  return rows;
}();
inline const SourceService *sourceService(llvm::StringRef qualifiedName) {
  auto *association = frontendAssociation(qualifiedName);
  if (!association ||
      association->signature != FrontendSignature::RandomConstructor)
    return nullptr;
  for (const auto &row : sourceServices)
    if (row.module == association->module && row.name == association->name)
      return &row;
  return nullptr;
}
// Installed random-service signatures: the catalog's random-service rows, in
// declared order. Contracts identify distributions; registry references
// separately authenticate the actual provider root.
struct RandomService {
  llvm::StringRef contract, field;
};
llvm::ArrayRef<RandomService> randomServices();
inline llvm::StringRef randomServiceField(llvm::StringRef contract) {
  for (const auto &service : randomServices())
    if (service.contract == contract)
      return service.field;
  return {};
}
inline llvm::StringRef randomServiceContract(llvm::StringRef field) {
  for (const auto &service : randomServices())
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
  for (const auto &row : serviceMethodDeclarations()) {
    if (row.name != method ||
        (!row.capability.empty() &&
         !installedDomains().hasFact(row.capability, {field.str()})))
      continue;
    switch (row.signature) {
    case ServiceSignature::RandomDraw:
      return ServiceMethod{{}, {"field", field.str(), {}}};
    case ServiceSignature::RandomIndex:
      return ServiceMethod{{{"index", {}, {}}}, {"index", {}, {}}};
    case ServiceSignature::RandomIndices:
      return ServiceMethod{{{"index", {}, {}}, {"index", {}, {}}},
                           {"indices", {}, {}}};
    }
  }
  return {};
}
// The challenge field of an installed transcript suite. A suite has one
// exactly when the catalog declares it as a Transcript domain; the target
// still admits each transcript operation it executes.
inline llvm::StringRef nativeChallengeField(llvm::StringRef suite) {
  const auto &catalog = installedDomains();
  if (catalog.identitySort(suite) != "Transcript")
    return {};
  return catalog.associatedIdentity(suite, "ChallengeField");
}
} // namespace zkc::protocol
#endif
