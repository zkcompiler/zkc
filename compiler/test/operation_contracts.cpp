#include "zkc/Contracts/Bindings.h"
#include "zkc/Contracts/Implementations.h"
#include "zkc/Contracts/OperationShapes.h"
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
  using I = zkc::MathematicalIdentity;
  static_assert(
      unsigned(I::FieldAdd) == 0 && unsigned(I::FieldConstant) == 20 &&
      unsigned(I::PolynomialFixTable) == 35 &&
      unsigned(I::VectorLength) == 36 && unsigned(I::IndexPowerOfTwo) == 37 &&
      unsigned(I::QuotientMultiply) == 42 &&
      unsigned(I::MultilinearRestrictPrefix) == 43);
  require(zkc::mathematicalIntrinsics().size() == 43 &&
              zkc::mathematicalIntrinsics()[0].name == "container.at" &&
              zkc::mathematicalIntrinsics()[30].name == "poly.fix_table" &&
              zkc::mathematicalIntrinsics()[31].name == "vector.length" &&
              zkc::mathematicalIntrinsics()[32].name == "index.power_of_two" &&
              zkc::mathematicalIntrinsics()[37].name ==
                  "quotient.value.multiply" &&
              zkc::mathematicalIntrinsics()[38].name ==
                  "multilinear.restrict_prefix" &&
              zkc::mathematicalIdentityName(I::PolynomialMultiply) ==
                  "PolynomialMultiply",
          "mathematical source catalog identities changed");
  const auto *add = mathematicalMeaning(I::FieldAdd);
  const auto *multiply = mathematicalMeaning(I::FieldMultiply);
  const auto *subtract = mathematicalMeaning(I::FieldSubtract);
  require(add && add->law.associative && add->law.commutative &&
              add->law.leftIdentity == ScalarIdentity::Zero &&
              add->law.rightIdentity == ScalarIdentity::Zero &&
              add->law.annihilator == ScalarIdentity::None && multiply &&
              multiply->law.leftIdentity == ScalarIdentity::One &&
              multiply->law.rightIdentity == ScalarIdentity::One &&
              multiply->law.annihilator == ScalarIdentity::Zero && subtract &&
              !subtract->law.associative && !subtract->law.commutative &&
              subtract->law.leftIdentity == ScalarIdentity::None &&
              subtract->law.rightIdentity == ScalarIdentity::Zero,
          "zero, one, subtraction or annihilation laws changed");
  require(!mathematicalMeaning(I::IndexConstant) &&
              !mathematicalMeaning(I::BooleanAnd) &&
              !mathematicalMeaning(I::PolynomialMultiply) &&
              !mathematicalMeaning(I::MultilinearRestrictPrefix) &&
              !mathematicalMeaning(static_cast<I>(100000)) &&
              !computationContract("index.add") &&
              !computationContract("unknown.field.add"),
          "unrelated mathematics acquired scalar ring laws");
  const auto *access = computationContract("vector.get");
  require(access && access->access == AccessRule::Element &&
              !access->law.total && !access->law.associative,
          "checked access acquired totality");
  // Real absent-provider control: an immutable installation with no descriptor
  // or preference refuses both default selection and the exact pinned binding.
  auto absent = ImplementationCatalog::create({}, {});
  require(bool(absent) && absent->all().empty(),
          "empty implementation installation refused");
  for (const auto &binding :
       {BindingApplication{"field.add", {"bls12-381.fr"}, "arkworks/field.add"},
        BindingApplication{
            "curve.scale", {"bls12-381.g1"}, "arkworks/curve.scale"}}) {
    auto logical = resolveLogicalBinding(binding);
    require(bool(logical), "exact logical signature refused");
    const auto *meaning =
        admitMathematicalMeaning(binding, logical->inputs, logical->outputs);
    require(meaning, "logical meaning absent with installed provider");
    auto present = resolveBinding(binding, true);
    require(bool(present), "physical control lacks installed provider");
    auto missing = resolveBinding(binding, true, *absent);
    require(!missing, "absent physical implementation was selected");
    llvm::consumeError(missing.takeError());
    auto constrained = resolveBinding(binding, false, *absent);
    require(!constrained, "logical binding admission ignored an unavailable "
                          "explicit implementation");
    llvm::consumeError(constrained.takeError());
    auto preference = absent->defaultFor(binding);
    require(!preference, "empty installation acquired a default provider");
    llvm::consumeError(preference.takeError());
    require(admitMathematicalMeaning(binding, logical->inputs,
                                     logical->outputs) == meaning &&
                !admitComputationContract(binding, logical->inputs,
                                          logical->outputs),
            "provider availability changed meaning or pinned replacement "
            "eligibility");
    auto unconstrained = binding;
    unconstrained.implementation.clear();
    require(
        admitComputationContract(unconstrained, logical->inputs,
                                 logical->outputs) == meaning,
        "unconstrained logical replacement depends on physical availability");
    auto represented = logical->inputs;
    represented[0].representation = "physical.control";
    require(!admitMathematicalMeaning(binding, represented, logical->outputs),
            "logical meaning silently discarded a physical representation");
  }
  for (const auto &attributes :
       {std::vector<std::string>{"0"}, std::vector<std::string>{"1"}}) {
    auto error = checkGenericParameters("field.constant", attributes);
    require(!error, "generic zero/one literal needs no selected field");
  }
  for (const auto &attributes :
       {std::vector<std::string>{}, std::vector<std::string>{"0", "1"},
        std::vector<std::string>{"2"}, std::vector<std::string>{"01"}}) {
    auto error = checkGenericParameters("field.constant", attributes);
    require(bool(error), "generic literal retains arity and canonical bounds");
    llvm::consumeError(std::move(error));
  }
  auto unselected = checkParameters("field.constant", {"1"});
  require(bool(unselected), "closed literal still requires an admitted field");
  llvm::consumeError(std::move(unselected));
  std::set<std::string> keys;
  for (llvm::StringRef key :
       {"index.div", "index.wrapping_add", "field.inverse", "bool.not",
        "control.require", "sequence.at", "indices.at", "field_array.at",
        "fixed_vector.dot", "commitments.at", "vector.get", "bytes.at",
        "encoding.field_from_le", "hash.keccak256", "shake128.squeeze",
        "poly.domain_point", "oracle.check", "oracle.check_many"}) {
    const auto *contracts = operationContracts(key);
    require(contracts && contracts->deterministicData,
            "installed deterministic-data facet missing: " + key.str());
  }
  for (llvm::StringRef key :
       {"random.draw", "transcript.challenge", "external.monero.hash",
        "resource_unit.pass", "representation.convert", "table.relayout",
        "oracle.commit", "oracle.open", "oracle.open_many", "pcs.check",
        "opening_states.at", "numerical.map"}) {
    const auto *contracts = operationContracts(key);
    require(contracts && !contracts->deterministicData,
            "unclassified operation acquired deterministic data: " + key.str());
  }
  require(!operationContracts("index.future"),
          "unknown operation inherited deterministic data by prefix");
  for (llvm::StringRef key :
       {"index.div", "field.inverse", "sequence.at", "vector.get",
        "poly.domain_point", "control.require", "oracle.check",
        "oracle.check_many"})
    require(!isPublicReplay(key),
            "partial deterministic data acquired public replay: " + key.str());
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
  // This compiler-owned inventory covers the current executable contracts.
  for (const auto &kernel : operationShapes()) {
    require(keys.insert(kernel.key.str()).second, "duplicate contract key");
    auto expected = expectedHistory.find(kernel.key.str());
    require(expected != expectedHistory.end(),
            "new contract needs history classification");
    require(isHistoryTransition(kernel.key) == expected->second,
            "history classification differs from shared inventory");
    require(operationContracts(kernel.key) == &kernel.contracts,
            "catalog does not own the contract facts");
    const bool opaqueResource =
        llvm::is_contained(kernel.inputs, "nonce") ||
        kernel.key.starts_with("resource_unit.") ||
        // These have ordered history, but no ideal sampling/replay facet.
        kernel.key == "transcript.native.indexed.indices.search" ||
        kernel.key == "transcript.native.indexed.indices.gated" ||
        kernel.key == "representation.convert" ||
        (kernel.key.starts_with("sequence.") && !kernel.inputs.empty());
    require(hasUnclassifiedProviderEffect(kernel.key) == opaqueResource,
            "entropy/transcript coverage or opaque resource classification: " +
                kernel.key.str());
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
            llvm::find_if(operationShapes(), [&](const auto &candidate) {
              return candidate.key == sample->derivedCounterpart;
            });
        require(target != operationShapes().end() &&
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
      auto suffix = kernel.key;
      require((kernel.key == "transcript.observe" &&
               kernel.inputs[observation->payloadInput] == "bytes") ||
                  (suffix.consume_front("transcript.native.indexed.observe.") &&
                   suffix == kernel.inputs[observation->payloadInput]),
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
  for (const auto *kind : {"rng", "nonce", "transcript"})
    require(affine(kind) && !serializable(kind) && !discardable(kind) &&
                !duplicable(kind),
            "provider token acquired immutable custody permissions");
  for (const auto *kind : {"scalar:custom", "capability:custom"})
    require(!hasTypeProperties(kind) && !serializable(kind) &&
                !discardable(kind) && !duplicable(kind),
            "native container spelling acquired logical permissions");
  require(
      samplingContract("random.vector") && !isConstructionDraw("random.vector"),
      "private vector sampling confused with public challenge construction");
  const auto *pairing = operationContracts("pairing.check");
  require(pairing && !pairing->publicReplay && !pairing->acceptanceGuard &&
              !pairing->sampling && !pairing->linearContraction &&
              !hasUnclassifiedProviderEffect("pairing.check"),
          "pairing predicate grants neither acceptance nor replay authority");
  // The shared inventory also covers the installed physical-only adapter.
  // Its erasure row must not admit a logical invocation through discovery.
  BindingApplication relayout{
      "table.relayout",
      {"bls12-381.fr", "arkworks.mle-lsb/0", "arkworks.mle-msb/0"},
      "arkworks/table.relayout"};
  auto physicalRelayout = resolveBinding(relayout, true);
  require(bool(physicalRelayout), "physical relayout must be installed");
  auto logicalRelayout = resolveBinding(relayout, false);
  require(!logicalRelayout, "relayout must remain physical-only");
  llvm::consumeError(logicalRelayout.takeError());
  require(keys.count(relayout.contract),
          "physical adapter is absent from the catalog inventory");
  auto expectedRelayout = expectedHistory.find(relayout.contract);
  require(expectedRelayout != expectedHistory.end() &&
              !expectedRelayout->second &&
              !isHistoryTransition(relayout.contract),
          "physical relayout history classification");
  require(keys.size() == expectedHistory.size(),
          "uninstalled history inventory contract");
}
