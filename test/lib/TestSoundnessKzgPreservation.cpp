//===- TestSoundnessKzgPreservation.cpp - executable KZG preservation -*- C++
//-*-===//

#include "SoundnessAdapterTestUtils.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "zkc/Soundness/SignatureFile.h"
#include "zkc/Soundness/SoundnessEvaluator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

namespace snd = zkc::soundness;

constexpr const char *kEbDbRule = "zkc.pcs.kzg_batch";
constexpr const char *kArsdhRule = "zkc.pcs.kzg_batch_arsdh";
constexpr const char *kContract = "kzg_batch";
constexpr const char *kFieldOrder =
    "524358751751261904794477405081859658376905525005276378226036586999"
    "38581184513";

std::string bindingId(llvm::StringRef rule) {
  return (rule + "@reduction:" + kContract).str();
}

std::string refusalText(const snd::SoundnessRefusal &refusal) {
  return std::string(snd::runtimePhaseName(refusal.phase)) + "/" +
         snd::runtimeRefusalCodeName(refusal.code) + " at " + refusal.location +
         ": " + refusal.detail;
}

snd::RuntimeValue exactAlgebra() {
  auto order = zkc::registry::Rational::fromDecimal(kFieldOrder);
  if (!order) {
    std::string detail = llvm::toString(order.takeError());
    llvm::report_fatal_error(llvm::StringRef(detail));
  }
  return snd::RuntimeValue::algebra(
      {"algebra:bls12_381:g1", "fr", std::move(*order)});
}

snd::ResolvedParameterEnvironment
parameterEnvironment(const snd::ExactRef &bindingRef) {
  snd::ResolvedParameterEnvironment result;
  result.bindingRef = bindingRef;
  result.values.emplace("algebra", exactAlgebra());
  result.values.emplace(
      "srs", snd::RuntimeValue::srs({"test.kzg.srs", "test.kzg.srs"}));
  result.values.emplace(
      "srs_max_degree",
      snd::RuntimeValue::integer(zkc::registry::Rational::fromInteger(64)));
  return result;
}

snd::SecurityJudgment
sourceAssumption(const snd::ConsumedClaimVectorSubject &subject) {
  snd::ClosedQuantity arity;
  arity.constant = zkc::registry::Rational::fromInteger(2);
  auto space = zkc::registry::Rational::fromDecimal(kFieldOrder);
  if (!space) {
    std::string detail = llvm::toString(space.takeError());
    llvm::report_fatal_error(llvm::StringRef(detail));
  }
  snd::ClosedQuantity challengeSpace;
  challengeSpace.constant = std::move(*space);

  snd::SecurityJudgment result;
  result.subject.payload = subject;
  result.index = {snd::SecurityNotion::SpecialSoundness,
                  snd::SecurityTrack::Knowledge,
                  {},
                  {}};
  result.result = snd::ExtractionResult{
      {snd::ExtractionCoordinate{"source", std::move(arity),
                                 std::move(challengeSpace)}},
      std::nullopt};
  return result;
}

snd::DerivationPlan makePlan(const snd::ApplicationSite &site,
                             const snd::ExactRef &bindingRef,
                             snd::SecurityJudgment assumption) {
  auto source = std::make_shared<snd::DerivationPlan>();
  source->node = snd::ExternalJudgmentAssumption{std::move(assumption)};
  snd::ApplyDerivationPlan root;
  root.site = site;
  root.bindingRef = bindingRef;
  root.premises.emplace("source_ss", std::move(source));
  snd::DerivationPlan plan;
  plan.node = std::move(root);
  return plan;
}

const snd::SecurityJudgment *rootConclusion(const snd::DeriveOutcome &outcome) {
  if (!outcome.accepted())
    return nullptr;
  const auto *application =
      std::get_if<snd::EvaluatedApplication>(&outcome.result->root.node);
  return application ? &application->conclusion : nullptr;
}

bool isOne(const zkc::registry::Rational &value) {
  return value.compare(zkc::registry::Rational::fromInteger(1)) == 0;
}

bool hasExactResource(const snd::PrimitiveGameTerm &term,
                      llvm::StringRef resource) {
  auto tau = term.resourceSubstitution.find("tau");
  return tau != term.resourceSubstitution.end() &&
         tau->second.constant.compare(
             zkc::registry::Rational::fromInteger(0)) == 0 &&
         tau->second.resourceTerms.size() == 1 &&
         tau->second.resourceTerms.front().resource == resource &&
         tau->second.resourceTerms.front().exponent == 1 &&
         isOne(tau->second.resourceTerms.front().coefficient);
}

bool hasCompleteHypotheses(const snd::SecurityJudgment &judgment) {
  std::set<std::string> propositions;
  unsigned assumptions = 0;
  for (const snd::Hypothesis &hypothesis : judgment.hypotheses) {
    if (std::holds_alternative<snd::AssumedJudgmentHolds>(hypothesis)) {
      ++assumptions;
      continue;
    }
    const auto &proposition = std::get<snd::PropositionInstance>(hypothesis);
    propositions.insert(proposition.ref.id);
  }
  // Both batching rules rest on the same Vandermonde-coefficient hypothesis,
  // which the signature declares once instead of once per rule.
  return assumptions == 1 &&
         propositions == std::set<std::string>{
                             "zkc.hyp.vandermonde_batch_coefficients",
                             "zkc.assume.srs_ceremony",
                             "zkc.side.algebra_match",
                             "zkc.side.degrees_within_srs",
                         };
}

struct TestSoundnessKzgPreservationPass
    : public PassWrapper<TestSoundnessKzgPreservationPass,
                         OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessKzgPreservationPass)

  TestSoundnessKzgPreservationPass() = default;
  TestSoundnessKzgPreservationPass(
      const TestSoundnessKzgPreservationPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override {
    return "test-soundness-kzg-preservation";
  }
  StringRef getDescription() const override {
    return "test executable same-point KZG special-soundness preservation";
  }

  Option<std::string> protocolVocabularyPath{
      *this, "protocol-vocabulary", llvm::cl::desc("protocol vocabulary")};
  Option<std::string> signaturePath{*this, "signature",
                                    llvm::cl::desc("the shipped signature")};
  Option<std::string> constructionProfileRegistryPath{
      *this, "construction-profile-registry",
      llvm::cl::desc("construction-profile registry")};

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };

    auto sealedOps = module.getOps<zkc::pir::SealedOp>();
    if (!llvm::hasSingleElement(sealedOps))
      return fail("KZG preservation test expects one sealed artifact");
    auto artifact = zkc::test::admitSoundnessFixture(
        *sealedOps.begin(), protocolVocabularyPath,
        constructionProfileRegistryPath);
    if (!artifact)
      return fail(llvm::toString(artifact.takeError()));
    auto view = snd::buildSealedSoundnessView(*artifact);
    if (!view)
      return fail(llvm::toString(view.takeError()));
    auto signature = snd::loadSignatureFromFile(signaturePath);
    if (!signature)
      return fail(llvm::toString(signature.takeError()));
    const snd::SoundnessCatalog *catalog = &signature->catalog;

    auto ebDbRule = catalog->rules.find(kEbDbRule);
    auto arsdhRule = catalog->rules.find(kArsdhRule);
    auto ebDbBinding = catalog->bindings.find(bindingId(kEbDbRule));
    auto arsdhBinding = catalog->bindings.find(bindingId(kArsdhRule));
    if (ebDbRule == catalog->rules.end() || arsdhRule == catalog->rules.end() ||
        ebDbBinding == catalog->bindings.end() ||
        arsdhBinding == catalog->bindings.end())
      return fail("both exact KZG preservation rules/bindings must adapt");
    if (view->reductionsByTransformerPosition.size() != 1)
      return fail("KZG fixture must contain one exact reduction");
    const auto &[transformerPosition, reduction] =
        *view->reductionsByTransformerPosition.begin();
    if (reduction.contractRef.id != kContract ||
        reduction.orderedInputs.size() != 2 ||
        reduction.orderedOutputs.size() != 1)
      return fail("KZG fixture resolved the wrong structural occurrence");

    const snd::ClaimRef &owner = reduction.orderedOutputs.front();
    snd::ReductionOccurrence occurrence{view->artifactId, owner,
                                        transformerPosition, 0};
    snd::ApplicationSite site = occurrence;
    auto consumed = snd::resolveAllReductionInputs(*view, occurrence);
    if (!consumed)
      return fail(llvm::toString(consumed.takeError()));
    snd::SecurityJudgment assumption = sourceAssumption(*consumed);

    snd::ResolvedParameterEnvironments parameters;
    parameters.emplace(ebDbBinding->second.ref.id,
                       parameterEnvironment(ebDbBinding->second.ref));
    parameters.emplace(arsdhBinding->second.ref.id,
                       parameterEnvironment(arsdhBinding->second.ref));
    snd::SoundnessContextOutcome contextOutcome = snd::buildSoundnessContext(
        *catalog, {ebDbBinding->second.ref, arsdhBinding->second.ref},
        std::move(parameters));
    if (!contextOutcome.accepted())
      return fail("KZG context is ill-formed: " +
                  refusalText(*contextOutcome.refusal));
    const snd::SoundnessContext &context = *contextOutcome.context;

    snd::SecuritySubject targetSubject;
    targetSubject.payload = snd::ProtocolClaimSubject{view->artifactId, owner};
    auto makeTarget = [&](const snd::SoundnessRule &rule) {
      return snd::DerivationTarget{
          targetSubject,
          {snd::SecurityNotion::ComputationalSpecialSoundness,
           snd::SecurityTrack::Knowledge,
           {},
           {}},
          rule.resources,
      };
    };
    snd::DerivationTarget ebDbTarget = makeTarget(ebDbRule->second);
    snd::DerivationTarget arsdhTarget = makeTarget(arsdhRule->second);

    auto derive = [&](const snd::SealedSoundnessView &selectedView,
                      const snd::ExactRef &bindingRef,
                      const snd::DerivationTarget &target) {
      snd::DerivationPlan plan = makePlan(site, bindingRef, assumption);
      return snd::deriveSoundness(context, selectedView, target, plan);
    };
    snd::DeriveOutcome ebDb =
        derive(*view, ebDbBinding->second.ref, ebDbTarget);
    if (!ebDb.accepted())
      return fail("EB+DB preservation refused: " + refusalText(*ebDb.refusal));
    snd::DeriveOutcome arsdh =
        derive(*view, arsdhBinding->second.ref, arsdhTarget);
    if (!arsdh.accepted())
      return fail("2*ARSDH preservation refused: " +
                  refusalText(*arsdh.refusal));

    auto checkResult =
        [&](const snd::DeriveOutcome &outcome,
            const std::vector<std::pair<std::string, std::string>> &games,
            int64_t coefficient) -> bool {
      const snd::SecurityJudgment *judgment = rootConclusion(outcome);
      const auto *result =
          judgment ? std::get_if<snd::ExtractionResult>(&judgment->result)
                   : nullptr;
      auto fieldOrder = zkc::registry::Rational::fromDecimal(kFieldOrder);
      if (!fieldOrder)
        return false;
      if (!judgment || !result || result->coordinates.size() != 2 ||
          result->coordinates[0].label != "source" ||
          result->coordinates[1].label != "batch" ||
          result->coordinates[1].arity.constant.compare(
              zkc::registry::Rational::fromInteger(2)) != 0 ||
          !result->coordinates[1].challengeSpace ||
          result->coordinates[1].challengeSpace->constant.compare(
              *fieldOrder) != 0 ||
          !result->failureBound ||
          result->failureBound->primitiveGameTerms.size() != games.size() ||
          !hasCompleteHypotheses(*judgment))
        return false;
      std::set<std::string> declaredResources;
      for (const snd::TypedDeclaration &resource :
           judgment->resourceVariables) {
        if (resource.sort != snd::ValueSort::Integer)
          return false;
        declaredResources.insert(resource.name);
      }
      for (size_t index = 0; index < games.size(); ++index) {
        const snd::PrimitiveGameTerm &term =
            result->failureBound->primitiveGameTerms[index];
        if (term.instance.ref.id != games[index].first ||
            term.coefficient.compare(
                zkc::registry::Rational::fromInteger(coefficient)) != 0 ||
            term.instance.arguments.size() != 2 ||
            term.instance.arguments[0] != exactAlgebra() ||
            term.instance.arguments[1] !=
                snd::RuntimeValue::integer(
                    zkc::registry::Rational::fromInteger(64)) ||
            !hasExactResource(term, games[index].second))
          return false;
      }
      std::set<std::string> expectedResources;
      for (const auto &[game, resource] : games) {
        (void)game;
        expectedResources.insert(resource);
      }
      return declaredResources == expectedResources;
    };

    if (!checkResult(ebDb,
                     {{"zkc.assume.kzg_eval_binding", "tau_eb"},
                      {"zkc.assume.kzg_degree_binding", "tau_db"}},
                     1))
      return fail("EB+DB preservation returned an incomplete exact judgment");
    llvm::outs() << "KZG preservation: EB + DB exact\n";
    if (!checkResult(arsdh, {{"zkc.assume.arsdh", "tau_arsdh"}}, 2))
      return fail("2*ARSDH preservation returned an incomplete exact "
                  "judgment");
    llvm::outs() << "KZG preservation: 2 * ARSDH exact\n";

    snd::SealedSoundnessView wrongPoint = *view;
    auto &wrongPointReduction =
        wrongPoint.reductionsByTransformerPosition.at(transformerPosition);
    wrongPointReduction.orderedInputAnchors[1]["point"] =
        "sha256:"
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    snd::DeriveOutcome pointRefusal =
        derive(wrongPoint, ebDbBinding->second.ref, ebDbTarget);
    if (pointRefusal.accepted() || !pointRefusal.refusal ||
        pointRefusal.refusal->phase != snd::RuntimePhase::ConditionEvaluation ||
        pointRefusal.refusal->location != "apply.conditions.S1")
      return fail("different-point batch did not fail closed at SamePoint");

    snd::SealedSoundnessView wrongOrder = *view;
    auto &wrongOrderReduction =
        wrongOrder.reductionsByTransformerPosition.at(transformerPosition);
    wrongOrderReduction.orderedInputAnchorEventPositions[0]["commitment"] =
        wrongOrderReduction.rounds.front().challengeEventPosition;
    snd::DeriveOutcome orderRefusal =
        derive(wrongOrder, ebDbBinding->second.ref, ebDbTarget);
    if (orderRefusal.accepted() || !orderRefusal.refusal ||
        orderRefusal.refusal->phase != snd::RuntimePhase::ConditionEvaluation ||
        orderRefusal.refusal->location != "apply.conditions.S6")
      return fail("post-material order violation did not fail closed at "
                  "BatchAfterMaterial");
    llvm::outs() << "KZG preservation: wrong point/order refused\n";
    llvm::outs() << "soundness KZG preservation: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessKzgPreservationPass() {
  PassRegistration<TestSoundnessKzgPreservationPass>();
}
} // namespace zkc::test
