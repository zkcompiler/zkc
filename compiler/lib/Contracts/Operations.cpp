#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Domains.h"
#include "zkc/Contracts/OperationShapes.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringMap.h"

namespace zkc::protocol {
namespace {
const OperationShape *findOperationShape(llvm::StringRef key) {
  static const auto catalog = [] {
    llvm::StringMap<const OperationShape *> entries;
    for (const auto &k : operationShapes())
      entries.try_emplace(k.key, &k);
    return entries;
  }();
  auto found = catalog.find(key);
  return found == catalog.end() ? nullptr : found->second;
}
} // namespace
const ComputationContract *computationContract(llvm::StringRef key) {
  const auto *facets = operationContracts(key);
  return facets && facets->mathematical ? &*facets->mathematical : nullptr;
}
const ComputationContract *admitMathematicalMeaning(
    const BindingApplication &application, llvm::ArrayRef<BoundType> inputs,
    llvm::ArrayRef<BoundType> outputs, llvm::ArrayRef<std::string> parameters) {
  auto *facet = computationContract(application.contract);
  if (!facet)
    return nullptr;
  auto signature = resolveLogicalBinding(application);
  if (!signature) {
    llvm::consumeError(signature.takeError());
    return nullptr;
  }
  if (inputs != llvm::ArrayRef<BoundType>(signature->inputs) ||
      outputs != llvm::ArrayRef<BoundType>(signature->outputs))
    return nullptr;
  if (auto error = checkParameters(application, parameters,
                                   zkc::protocol::ParameterStage::Logical)) {
    llvm::consumeError(std::move(error));
    return nullptr;
  }
  return facet;
}
const ComputationContract *admitComputationContract(
    const BindingApplication &application, llvm::ArrayRef<BoundType> inputs,
    llvm::ArrayRef<BoundType> outputs, llvm::ArrayRef<std::string> parameters) {
  if (!application.implementation.empty())
    return nullptr;
  return admitMathematicalMeaning(application, inputs, outputs, parameters);
}
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
  // Plonky3 0.8.0 baby-bear/src/baby_bear.rs: TwoAdicData's entry 27
  // is 0x1a427a41; test_baby_bear_two_adicity_generators checks every root
  // against its successive squares. Goldilocks goldilocks/src/goldilocks.rs
  // TWO_ADIC_GENERATORS[32] is 0x185629dcda58878c; TwoAdicField indexes it.
  static const CosetConvention baby{"baby-bear.two-adic.440564289/0",
                                    "baby-bear", "440564289",
                                    "shift * root(size)^i; i = 0..size-1", 27};
  static const CosetConvention goldilocks{
      "goldilocks.two-adic.1753635133440165772/0", "goldilocks",
      "1753635133440165772", "shift * root(size)^i; i = 0..size-1", 32};
  const auto *registered = plonky3Field(field);
  if (!registered)
    return nullptr;
  // Even a nonbase extension shift uses the BASE root and two-adicity.
  for (const auto *convention : {&koala, &baby, &goldilocks})
    if (registered->base == convention->rootField)
      return convention;
  return nullptr;
}
const OperationContracts *operationContracts(llvm::StringRef key) {
  const auto *application = findOperationShape(key);
  return application ? &application->contracts : nullptr;
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
  const auto *k = findOperationShape(key);
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
