#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Kernels.h"
#include "zkc/Contracts/Operations.h"
#include "zkc/Contracts/TypeProperties.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <fstream>
#include <map>
#include <set>

using namespace zkc::protocol;
namespace {
void require(bool condition, llvm::StringRef message) {
  if (!condition) {
    llvm::errs() << message << '\n';
    std::exit(1);
  }
}
} // namespace
int main() {
  std::set<std::string> keys;
  std::ifstream fixture(ZKC_HISTORY_FIXTURE);
  require(fixture.is_open(), "history inventory fixture missing");
  std::map<std::string, bool> expectedHistory;
  std::string key;
  int history;
  while (fixture >> key >> history) {
    require(history == 0 || history == 1, "invalid history inventory value");
    require(expectedHistory.emplace(key, history != 0).second,
            "duplicate history inventory entry");
  }
  require(fixture.eof(), "invalid history inventory row");
  for (const auto &kernel : kernels()) {
    require(keys.insert(kernel.key.str()).second, "duplicate contract key");
    auto expected = expectedHistory.find(kernel.key.str());
    require(expected != expectedHistory.end(),
            "new contract needs history classification");
    require(isHistoryTransition(kernel.key) == expected->second,
            "history classification differs from shared inventory");
    require(operationContracts(kernel.key) == &kernel.contracts,
            "catalog does not own the contract facts");
    const bool opaqueResource = llvm::is_contained(kernel.inputs, "nonce") ||
                                kernel.key.starts_with("resource_unit.");
    require(hasUnclassifiedProviderEffect(kernel.key) == opaqueResource,
            "entropy/transcript coverage or opaque resource classification");
    if (auto sample = samplingContract(kernel.key)) {
      require(sample->stateInput < kernel.inputs.size() &&
                  sample->stateOutput < kernel.outputs.size() &&
                  sample->valueOutput < kernel.outputs.size(),
              "sampler port outside signature");
      const auto *provider = sample->provider == RandomnessProvider::Entropy
                                 ? "rng"
                                 : "transcript";
      require(kernel.inputs[sample->stateInput] == provider &&
                  kernel.outputs[sample->stateOutput] == provider,
              "sampler changed provider kind");
      require(sample->valueOutput != sample->stateOutput,
              "sample and successor ports overlap");
      if (sample->boundInput)
        require(*sample->boundInput < kernel.inputs.size() &&
                    kernel.inputs[*sample->boundInput] == "index",
                "sampler bound port is not an index");
      if (!sample->derivedCounterpart.empty()) {
        require(sample->provider == RandomnessProvider::Entropy,
                "only entropy draws select construction counterparts");
        auto derived = samplingContract(sample->derivedCounterpart);
        require(derived &&
                    derived->provider == RandomnessProvider::Transcript &&
                    derived->stateInput == sample->stateInput &&
                    derived->stateOutput == sample->stateOutput &&
                    derived->valueOutput == sample->valueOutput &&
                    derived->boundInput == sample->boundInput &&
                    derived->domain == sample->domain,
                "construction counterpart has incompatible ports");
        const auto target =
            llvm::find_if(kernels(), [&](const auto &candidate) {
              return candidate.key == sample->derivedCounterpart;
            });
        require(target != kernels().end() &&
                    target->inputs.size() == kernel.inputs.size() &&
                    target->outputs.size() == kernel.outputs.size(),
                "construction counterpart arity");
        for (unsigned i = 0; i < kernel.inputs.size(); ++i)
          if (i != sample->stateInput)
            require(target->inputs[i] == kernel.inputs[i],
                    "construction counterpart parameter kind");
        for (unsigned i = 0; i < kernel.outputs.size(); ++i)
          if (i != sample->stateOutput)
            require(target->outputs[i] == kernel.outputs[i],
                    "construction counterpart result kind");
      }
    }
    if (auto observation = kernel.contracts.observation) {
      require(observation->stateInput < kernel.inputs.size() &&
                  observation->payloadInput < kernel.inputs.size() &&
                  observation->stateOutput < kernel.outputs.size() &&
                  kernel.inputs[observation->stateInput] == "transcript" &&
                  kernel.outputs[observation->stateOutput] == "transcript",
              "observation port outside transcript signature");
      require(kernel.key.starts_with("transcript.observe.") &&
                  kernel.key.drop_front(19) ==
                      kernel.inputs[observation->payloadInput],
              "observation payload differs from its logical contract");
    }
    if (auto map = kernel.contracts.diagonalMap)
      require(map->factorsOperand < kernel.inputs.size() &&
                  map->valuesOperand < kernel.inputs.size() &&
                  map->result < kernel.outputs.size() &&
                  map->factorsOperand != map->valuesOperand,
              "diagonal map ports outside signature");
    if (auto contraction = kernel.contracts.linearContraction)
      require(contraction->coefficientsOperand < kernel.inputs.size() &&
                  contraction->valuesOperand < kernel.inputs.size() &&
                  contraction->coefficientsOperand !=
                      contraction->valuesOperand,
              "contraction ports outside signature");
  }
  for (const auto &type : boundTypeConstructors())
    require(hasTypeProperties(type.name),
            "registered type lacks custody facts");
  require(!operationContracts("unknown.sample") &&
              !isConstructionDraw("unknown.sample") &&
              !isPublicReplay("unknown.sample") &&
              hasUnclassifiedProviderEffect("unknown.sample"),
          "unknown operation acquired positive facts");
  require(!serializable("unknown:domain") && !discardable("unknown:domain") &&
              !duplicable("unknown:domain"),
          "unknown type acquired positive custody facts");
  for (const auto *kind :
       {"opening_state", "opening_states", "prover_key", "verifier_key"})
    require(!serializable(kind) && discardable(kind) && duplicable(kind),
            "immutable local custody confused with transport");
  for (const auto *kind : {"rng", "nonce", "transcript", "capability:custom"})
    require(affine(kind) && !serializable(kind) && !discardable(kind) &&
                !duplicable(kind),
            "provider token acquired immutable custody permissions");
  require(
      samplingContract("random.vector") && !isConstructionDraw("random.vector"),
      "private vector sampling confused with public challenge construction");
  const auto *pairing = operationContracts("pairing.check");
  require(pairing && !pairing->publicReplay && !pairing->acceptanceGuard &&
              !pairing->sampling && !pairing->linearContraction &&
              !hasUnclassifiedProviderEffect("pairing.check"),
          "pairing predicate grants neither acceptance nor replay authority");
  require(keys.size() == expectedHistory.size(),
          "uninstalled history inventory contract");
}
