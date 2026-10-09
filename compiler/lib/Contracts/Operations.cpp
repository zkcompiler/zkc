#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringMap.h"

namespace zkc::protocol {
namespace {
const Kernel *findKernel(llvm::StringRef key) {
  static const auto catalog = [] {
    llvm::StringMap<const Kernel *> entries;
    for (const auto &k : kernels())
      entries.try_emplace(k.key, &k);
    return entries;
  }();
  auto found = catalog.find(key);
  return found == catalog.end() ? nullptr : found->second;
}
} // namespace
bool isHistoryTransition(llvm::StringRef key) {
  const auto *contracts = operationContracts(key);
  return contracts && contracts->history.has_value();
}
const CosetConvention *cosetConvention(llvm::StringRef field) {
  // ark-bn254 0.6.0 Fr uses generator 5. Its maximal two-adic root is
  // 5^((r - 1) / 2^28); smaller roots are successive powers of two of it.
  static const CosetConvention bn254{"bn254.fr.two-adic.generator5/0",
                                     "bn254.fr",
                                     "19103219067921713944291392827692070036145"
                                     "651957329286315305642004821462161904",
                                     "shift * root(size)^i; i = 0..size-1", 28};
  if (field == "bn254.fr")
    return &bn254;
  static const CosetConvention koala{"koala-bear.two-adic.1791270792/0",
                                     "koala-bear", "1791270792",
                                     "shift * root(size)^i; i = 0..size-1", 24};
  return field == "koala-bear" || field == "koala-bear.ext8-binomial3"
             ? &koala
             : nullptr;
}
const OperationContracts *operationContracts(llvm::StringRef key) {
  const auto *kernel = findKernel(key);
  return kernel ? &kernel->contracts : nullptr;
}
const SamplingContract *samplingContract(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->sampling ? &*c->sampling : nullptr;
}
bool isAcceptanceGuard(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->acceptanceGuard;
}
bool isConjunction(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->conjunction;
}
bool isPublicReplay(llvm::StringRef key) {
  auto *c = operationContracts(key);
  return c && c->publicReplay;
}
bool isConstructionDraw(llvm::StringRef key) {
  auto *c = samplingContract(key);
  return c && !c->derivedCounterpart.empty();
}
bool hasUnclassifiedProviderEffect(llvm::StringRef key) {
  const auto *k = findKernel(key);
  if (!k)
    return true;
  if (k->contracts.sampling || k->contracts.observation)
    return false;
  if (key.starts_with("resource_unit."))
    return true;
  const generic::Operation *declaration = nullptr;
  for (const auto &candidate : executableOperationContracts())
    if (candidate.name == key) {
      declaration = &candidate;
      break;
    }
  if (!declaration)
    return true;
  const auto &signature = declaration->signature;
  const auto &scope = signature.scope;
  // A Type formal carries no copy bound. Propagate this uncertainty through
  // applications instead of classifying only the outer port constructor.
  std::vector<bool> affineTerms;
  auto potentiallyAffine = [&](llvm::StringRef head,
                               llvm::ArrayRef<unsigned> arguments) {
    const auto *permissions = typePermissions(head);
    return !permissions || !permissions->copy ||
           llvm::any_of(arguments, [&](unsigned i) {
             return i >= affineTerms.size() || affineTerms[i];
           });
  };
  for (auto [i, term] : llvm::enumerate(scope.terms)) {
    bool affine = scope.sorts[i] == "Type";
    if (affine && term.arguments)
      affine = potentiallyAffine(term.name, *term.arguments);
    affineTerms.push_back(affine);
  }
  return llvm::any_of(signature.inputs, [&](const generic::Type &type) {
    return potentiallyAffine(type.constructor, type.arguments);
  });
}
} // namespace zkc::protocol
