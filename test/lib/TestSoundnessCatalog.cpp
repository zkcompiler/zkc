//===- TestSoundnessCatalog.cpp - native catalog/evaluator tests ---------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Soundness/SoundnessCatalog.h"
#include "zkc/Soundness/SoundnessEvaluator.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <string>
#include <type_traits>
#include <utility>

using namespace mlir;

namespace {
namespace snd = zkc::soundness;

constexpr const char *kClaimSchema = "zkc.subject.protocol_claim";
constexpr const char *kCatalogRevision = "native-test";
constexpr const char *kContractId = "native-test-contract";
constexpr const char *kContractRevision = "contract-digest";

static_assert(
    std::is_const_v<decltype(std::declval<snd::SoundnessCatalog &>().schemas)>);
static_assert(
    std::is_const_v<decltype(std::declval<snd::SoundnessCatalog &>().rules)>);
static_assert(std::is_const_v<
              decltype(std::declval<snd::SoundnessCatalog &>().bindings)>);

snd::SecurityIndex specialSoundnessIndex() {
  return {snd::SecurityNotion::SpecialSoundness,
          snd::SecurityTrack::Soundness,
          {},
          {}};
}

snd::SecurityIndex computationalIndex() {
  return {snd::SecurityNotion::ComputationalSpecialSoundness,
          snd::SecurityTrack::Soundness,
          {},
          {}};
}

zkc::registry::Rational fraction(llvm::StringRef numerator,
                                 llvm::StringRef denominator) {
  return llvm::cantFail(
      zkc::registry::Rational::fromDecimalPair(numerator, denominator));
}

snd::SchemaContext makeSchemas() {
  snd::SchemaContext schemas;
  schemas.securityIndices = {specialSoundnessIndex(), computationalIndex()};
  schemas.subjectSchemas.emplace(
      kClaimSchema, snd::SubjectSchema{kClaimSchema,
                                       {},
                                       snd::SubjectSchemaKind::ProtocolClaim});
  return schemas;
}

snd::CoordinateSequence oneCoordinate(std::string label, int64_t arity) {
  snd::CoordinateSequence coordinates;
  coordinates.kind = snd::CoordinateSequence::Kind::Explicit;
  coordinates.coordinates.push_back(
      {std::move(label),
       snd::QuantityTemplate::rational(
           zkc::registry::Rational::fromInteger(arity)),
       std::nullopt});
  return coordinates;
}

snd::RuleBound quantityBound(zkc::registry::Rational value) {
  snd::RuleBound bound;
  bound.kind = snd::RuleBoundKind::Quantity;
  bound.quantity = snd::QuantityTemplate::rational(std::move(value));
  return bound;
}

snd::SoundnessRule computationalRule() {
  snd::SoundnessRule rule;
  rule.ref = {"native.computational-entry", kCatalogRevision};
  rule.conclusionIndex = computationalIndex();
  rule.body = snd::ComputationalEntry{oneCoordinate("extraction", 2),
                                      quantityBound(fraction("1", "8"))};
  return rule;
}

snd::SoundnessRule preservationRule() {
  snd::SoundnessRule rule;
  rule.ref = {"native.special-soundness-preservation", kCatalogRevision};
  snd::PremisePort source;
  source.name = "source_ss";
  source.expectedSubjectSchema = kClaimSchema;
  source.expectedIndex = specialSoundnessIndex();
  source.expectedResult = snd::ResultSchema::Extraction;
  rule.premises.push_back(std::move(source));
  rule.conclusionIndex = computationalIndex();
  rule.body = snd::SpecialSoundnessPreservation{
      "source_ss", oneCoordinate("appended", 3),
      quantityBound(fraction("1", "16"))};
  return rule;
}

snd::RuleBinding reductionBinding(std::string id, const snd::ExactRef &ruleRef,
                                  bool hasSourcePremise) {
  snd::RuleBinding binding;
  binding.ref = {std::move(id), kCatalogRevision};
  binding.ruleRef = ruleRef;
  binding.subjectSchema = kClaimSchema;
  binding.anchor = {
      snd::ProtocolAnchorKind::ReductionContract,
      snd::ExactRef{kContractId, kContractRevision},
  };
  if (hasSourcePremise) {
    snd::SubjectRelation relation;
    relation.kind = snd::SubjectRelationKind::SameSubject;
    binding.premiseRelations.emplace("source_ss", std::move(relation));
  }
  return binding;
}

using RuleMap = std::map<std::string, snd::SoundnessRule, std::less<>>;
using BindingMap = std::map<std::string, snd::RuleBinding, std::less<>>;

llvm::Expected<snd::SoundnessCatalog> makeNativeCatalog() {
  RuleMap rules;
  snd::SoundnessRule computational = computationalRule();
  snd::SoundnessRule preservation = preservationRule();
  snd::ExactRef computationalRef = computational.ref;
  snd::ExactRef preservationRef = preservation.ref;
  rules.emplace(computational.ref.id, std::move(computational));
  rules.emplace(preservation.ref.id, std::move(preservation));

  BindingMap bindings;
  snd::RuleBinding computationalBinding =
      reductionBinding("native.computational-binding", computationalRef, false);
  snd::RuleBinding preservationBinding =
      reductionBinding("native.preservation-binding", preservationRef, true);
  bindings.emplace(computationalBinding.ref.id,
                   std::move(computationalBinding));
  bindings.emplace(preservationBinding.ref.id, std::move(preservationBinding));
  return snd::freezeSoundnessCatalog(makeSchemas(), std::move(rules),
                                     std::move(bindings));
}

snd::SealedSoundnessView makeSealedView() {
  snd::ClaimRef output{0, "native-claim-digest"};
  snd::SealedReduction reduction;
  reduction.transformerPosition = 4;
  reduction.contractRef = {kContractId, kContractRevision};
  reduction.orderedOutputs.push_back(output);

  snd::SealedSoundnessView sealed;
  sealed.artifactId = "native-artifact";
  sealed.claimsByIndex.push_back(output);
  sealed.reductionsByTransformerPosition.emplace(4, std::move(reduction));
  return sealed;
}

snd::SecurityJudgment
makeSpecialSoundnessPremise(const snd::ProtocolClaimSubject &subject) {
  snd::ClosedQuantity arity;
  arity.constant = zkc::registry::Rational::fromInteger(2);
  snd::SecurityJudgment premise;
  premise.subject.payload = subject;
  premise.index = specialSoundnessIndex();
  premise.result = snd::ExtractionResult{
      {snd::ExtractionCoordinate{"source", std::move(arity), std::nullopt}},
      std::nullopt};
  return premise;
}

std::string refusalText(const snd::SoundnessRefusal &refusal) {
  return std::string(snd::runtimePhaseName(refusal.phase)) + "/" +
         snd::runtimeRefusalCodeName(refusal.code) + " at " + refusal.location +
         ": " + refusal.detail;
}

struct TestSoundnessCatalogPass
    : public PassWrapper<TestSoundnessCatalogPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessCatalogPass)

  TestSoundnessCatalogPass() = default;
  TestSoundnessCatalogPass(const TestSoundnessCatalogPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override {
    return "test-soundness-native-catalog";
  }
  StringRef getDescription() const override {
    return "test native immutable soundness catalog and direct rule bodies";
  }

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };

    {
      RuleMap badRules;
      badRules.emplace("wrong-map-key", computationalRule());
      auto bad =
          snd::freezeSoundnessCatalog(makeSchemas(), std::move(badRules), {});
      if (bad)
        return fail("native catalog accepted a mismatched rule map key");
      llvm::consumeError(bad.takeError());
    }
    {
      snd::SchemaContext duplicateIndex = makeSchemas();
      duplicateIndex.securityIndices.push_back(specialSoundnessIndex());
      auto bad = snd::freezeSoundnessCatalog(std::move(duplicateIndex), {}, {});
      if (bad)
        return fail("native catalog accepted a duplicate security index");
      llvm::consumeError(bad.takeError());
    }
    {
      snd::SchemaContext malformedSubject = makeSchemas();
      malformedSubject.subjectSchemas.at(kClaimSchema).kind =
          snd::SubjectSchemaKind::ExternalInstance;
      auto bad =
          snd::freezeSoundnessCatalog(std::move(malformedSubject), {}, {});
      if (bad)
        return fail(
            "native catalog accepted an unused malformed subject schema");
      llvm::consumeError(bad.takeError());
    }
    {
      constexpr const char *kDecider = "zkc.side.batch_arity";
      snd::SchemaContext malformedDecider = makeSchemas();
      snd::MachineDeciderDefinition definition;
      definition.ref = {kDecider, "zkc.soundness"};
      definition.argumentTypes = {snd::ValueSort::Rational};
      definition.kind = snd::MachineDeciderKind::BatchArity;
      malformedDecider.machineDeciders.emplace(kDecider, std::move(definition));
      auto bad =
          snd::freezeSoundnessCatalog(std::move(malformedDecider), {}, {});
      if (bad)
        return fail(
            "native catalog accepted an unused malformed machine decider");
      llvm::consumeError(bad.takeError());
    }
    {
      snd::RuleBinding dangling = reductionBinding(
          "native.dangling-binding", {"absent-rule", kCatalogRevision}, false);
      BindingMap bindings;
      bindings.emplace(dangling.ref.id, std::move(dangling));
      auto bad =
          snd::freezeSoundnessCatalog(makeSchemas(), {}, std::move(bindings));
      if (bad)
        return fail("native catalog accepted an unresolved exact rule ref");
      llvm::consumeError(bad.takeError());
    }
    {
      snd::SoundnessRule rule = computationalRule();
      RuleMap rules;
      rules.emplace(rule.ref.id, rule);
      snd::RuleBinding binding =
          reductionBinding("native.binding-id", rule.ref, false);
      BindingMap bindings;
      bindings.emplace("wrong-binding-map-key", std::move(binding));
      auto bad = snd::freezeSoundnessCatalog(makeSchemas(), std::move(rules),
                                             std::move(bindings));
      if (bad)
        return fail("native catalog accepted a mismatched binding map key");
      llvm::consumeError(bad.takeError());
    }

    auto catalog = makeNativeCatalog();
    if (!catalog)
      return fail(llvm::toString(catalog.takeError()));

    const auto &computationalBinding =
        catalog->bindings.at("native.computational-binding");
    const auto &preservationBinding =
        catalog->bindings.at("native.preservation-binding");
    snd::SoundnessContextOutcome contextOutcome = snd::buildSoundnessContext(
        *catalog, {computationalBinding.ref, preservationBinding.ref});
    if (!contextOutcome.accepted())
      return fail("native context is ill-formed: " +
                  refusalText(*contextOutcome.refusal));
    const snd::SoundnessContext &context = *contextOutcome.context;

    snd::SealedSoundnessView sealed = makeSealedView();
    const snd::ClaimRef owner = sealed.claimsByIndex.front();
    snd::ApplicationSite site =
        snd::ReductionOccurrence{sealed.artifactId, owner, 4, 0};

    snd::ApplyOutcome computational = snd::applySoundnessRule(
        context, sealed, site, computationalBinding.ref, {});
    if (!computational.accepted())
      return fail("native ComputationalEntry refused: " +
                  refusalText(*computational.refusal));
    const auto *computationalResult = std::get_if<snd::ExtractionResult>(
        &computational.applied->conclusion.result);
    if (!computationalResult || computationalResult->coordinates.size() != 1 ||
        computationalResult->coordinates.front().label != "extraction" ||
        !computationalResult->failureBound ||
        computationalResult->failureBound->quantity.constant.compare(
            fraction("1", "8")) != 0)
      return fail("native ComputationalEntry returned the wrong exact result");
    llvm::outs() << "native catalog: computational entry exact\n";

    snd::ProtocolClaimSubject subject{sealed.artifactId, owner};
    snd::TypedPremiseJudgments premises{
        {"source_ss", makeSpecialSoundnessPremise(subject)}};
    snd::ApplyOutcome preservation = snd::applySoundnessRule(
        context, sealed, site, preservationBinding.ref, premises);
    if (!preservation.accepted())
      return fail("native SpecialSoundnessPreservation refused: " +
                  refusalText(*preservation.refusal));
    const auto *preserved = std::get_if<snd::ExtractionResult>(
        &preservation.applied->conclusion.result);
    if (!preserved || preserved->coordinates.size() != 2 ||
        preserved->coordinates[0].label != "source" ||
        preserved->coordinates[1].label != "appended" ||
        !preserved->failureBound ||
        preserved->failureBound->quantity.constant.compare(
            fraction("1", "16")) != 0)
      return fail("native SpecialSoundnessPreservation returned the wrong "
                  "exact result");
    llvm::outs() << "native catalog: special-soundness preservation exact\n";
    llvm::outs() << "native soundness catalog: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessCatalogPass() {
  PassRegistration<TestSoundnessCatalogPass>();
}
} // namespace zkc::test
