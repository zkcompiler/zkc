#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/Kernels.h"
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
  const auto *sample = samplingContract(key);
  return (contracts && contracts->observation) ||
         (sample && sample->provider == RandomnessProvider::Transcript) ||
         key == "external.monero.update" || key == "external.openvm.observe" ||
         key == "external.openvm.sample" ||
         key == "external.openvm.sample_ext" ||
         key == "external.openvm.sample_bits" ||
         key == "external.openvm.check_witness";
}
OperationContracts OperationContracts::replay() {
  OperationContracts c;
  c.publicReplay = true;
  return c;
}
OperationContracts OperationContracts::guard() {
  OperationContracts c;
  c.acceptanceGuard = true;
  return c;
}
OperationContracts OperationContracts::booleanConjunction() {
  auto c = replay();
  c.conjunction = true;
  return c;
}
OperationContracts OperationContracts::transcriptObservation() {
  OperationContracts c;
  c.observation = ObservationContract{};
  return c;
}
OperationContracts OperationContracts::diagonal() {
  OperationContracts c;
  c.diagonalMap = DiagonalMapContract{};
  return c;
}
OperationContracts OperationContracts::contraction() {
  OperationContracts c;
  c.linearContraction = LinearContractionContract{};
  return c;
}
OperationContracts OperationContracts::onCoset(CosetContract facet) {
  OperationContracts c;
  c.coset = facet;
  return c;
}
OperationContracts OperationContracts::exactDomainValue(DomainValueRule rule,
                                                        bool replay) {
  OperationContracts c;
  c.domainValue = DomainValueContract{rule};
  c.publicReplay = replay;
  return c;
}
const CosetConvention *cosetConvention(llvm::StringRef field) {
  // ark-bn254 0.6.0 Fr uses generator 5. Its maximal two-adic root is
  // 5^((r - 1) / 2^28); smaller roots are successive powers of two of it.
  static const CosetConvention bn254{"bn254.fr.two-adic.generator5/1",
                                     "bn254.fr",
                                     "19103219067921713944291392827692070036145"
                                     "651957329286315305642004821462161904",
                                     "shift * root(size)^i; i = 0..size-1", 28};
  if (field == "bn254.fr")
    return &bn254;
  static const CosetConvention koala{"koala-bear.two-adic.1791270792/1",
                                     "koala-bear", "1791270792",
                                     "shift * root(size)^i; i = 0..size-1", 24};
  return field == "koala-bear" || field == "koala-bear.ext8-binomial3"
             ? &koala
             : nullptr;
}
OperationContracts OperationContracts::sample(RandomnessProvider provider,
                                              SampleDomain domain,
                                              std::optional<unsigned> bound,
                                              llvm::StringRef counterpart) {
  OperationContracts c;
  c.sampling = SamplingContract{provider, domain, 0, 0, 1, bound, counterpart};
  return c;
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
  return llvm::any_of(k->inputs, [](const std::string &kind) {
    return kind == "rng" || kind == "transcript" || kind == "nonce" ||
           llvm::StringRef(kind).starts_with("capability");
  });
}
} // namespace zkc::protocol
