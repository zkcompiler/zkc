//===- TestSoundnessEvaluator.cpp - executable soundness tests -*- C++ -*-===//

#include "SoundnessAdapterTestUtils.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "zkc/Soundness/SignatureFile.h"
#include "zkc/Soundness/SoundnessEvaluator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

namespace snd = zkc::soundness;

static_assert(
    std::is_const_v<decltype(std::declval<snd::SoundnessCatalog &>().rules)>);
static_assert(std::is_const_v<
              decltype(std::declval<snd::SoundnessCatalog &>().bindings)>);
static_assert(std::is_same_v<
              decltype(std::declval<const snd::SoundnessContext &>().findRule(
                  std::declval<const snd::ExactRef &>())),
              const snd::SoundnessRule *>);
static_assert(std::is_same_v<
              decltype(std::declval<const snd::SoundnessContext &>()
                           .findBinding(std::declval<const snd::ExactRef &>())),
              const snd::RuleBinding *>);
static_assert(!std::is_constructible_v<
              snd::SoundnessContext, const snd::SoundnessCatalog &,
              std::vector<snd::ExactRef>, snd::ResolvedParameterEnvironments>);
constexpr const char *kSumcheckRule = "zkc.rbr.sumcheck";
constexpr const char *kSrRule = "zkc.sr.from_rbr_knowledge";
constexpr const char *kFsRule = "zkc.fs.duplex_knowledge";

constexpr const char *kSumcheckBinding = "zkc.rbr.sumcheck@reduction:sumcheck";
constexpr const char *kSrBinding = "zkc.sr.from_rbr_knowledge@path:"
                                   "rbr_to_sr:knowledge:straightline";
constexpr const char *kFsBinding = "zkc.fs.duplex_knowledge@path:"
                                   "sr_to_fs_duplex:knowledge:straightline";

bool sameDeclarations(const std::vector<snd::TypedDeclaration> &left,
                      const std::vector<snd::TypedDeclaration> &right) {
  if (left.size() != right.size())
    return false;
  for (size_t index = 0; index < left.size(); ++index)
    if (left[index].name != right[index].name ||
        left[index].sort != right[index].sort)
      return false;
  return true;
}

std::string refusalText(const snd::SoundnessRefusal &refusal) {
  return std::string(snd::runtimePhaseName(refusal.phase)) + "/" +
         snd::runtimeRefusalCodeName(refusal.code) + " at " + refusal.location +
         ": " + refusal.detail;
}

LogicalResult expectApplyRefusal(ModuleOp module, snd::ApplyOutcome outcome,
                                 snd::RuntimePhase phase,
                                 snd::RuntimeRefusalCode code,
                                 llvm::StringRef label) {
  if (outcome.accepted() || !outcome.refusal) {
    module.emitError() << label << " unexpectedly accepted";
    return failure();
  }
  if (outcome.refusal->phase != phase || outcome.refusal->code != code) {
    module.emitError() << label << " produced the wrong refusal: "
                       << refusalText(*outcome.refusal);
    return failure();
  }
  llvm::outs() << label << ": refused\n";
  return success();
}

LogicalResult expectDeriveRefusal(ModuleOp module, snd::DeriveOutcome outcome,
                                  snd::RuntimePhase phase,
                                  snd::RuntimeRefusalCode code,
                                  llvm::StringRef label) {
  if (outcome.accepted() || !outcome.refusal) {
    module.emitError() << label << " unexpectedly accepted";
    return failure();
  }
  if (outcome.refusal->phase != phase || outcome.refusal->code != code) {
    module.emitError() << label << " produced the wrong refusal: "
                       << refusalText(*outcome.refusal);
    return failure();
  }
  llvm::outs() << label << ": refused\n";
  return success();
}

LogicalResult expectContextRefusal(ModuleOp module,
                                   snd::SoundnessContextOutcome outcome,
                                   snd::RuntimePhase phase,
                                   snd::RuntimeRefusalCode code,
                                   llvm::StringRef label) {
  if (outcome.accepted() || !outcome.refusal) {
    module.emitError() << label << " unexpectedly accepted";
    return failure();
  }
  if (outcome.refusal->phase != phase || outcome.refusal->code != code) {
    module.emitError() << label << " produced the wrong refusal: "
                       << refusalText(*outcome.refusal);
    return failure();
  }
  return success();
}

snd::SecuritySubject protocolSubject(const snd::SealedSoundnessView &view,
                                     const snd::ClaimRef &claim) {
  snd::SecuritySubject subject;
  subject.payload = snd::ProtocolClaimSubject{view.artifactId, claim};
  return subject;
}

snd::PropositionInstance
proposition(const snd::SoundnessContext &context, llvm::StringRef id,
            std::vector<snd::RuntimeValue> arguments = {}) {
  return {context.schemas().propositions.at(id.str()).ref,
          std::move(arguments)};
}

bool hasProposition(const snd::SecurityJudgment &judgment,
                    const snd::PropositionInstance &expected) {
  return llvm::any_of(
      judgment.hypotheses, [&](const snd::Hypothesis &hypothesis) {
        const auto *actual = std::get_if<snd::PropositionInstance>(&hypothesis);
        return actual && *actual == expected;
      });
}

bool hasAssumedJudgment(const snd::SecurityJudgment &judgment) {
  return llvm::any_of(judgment.hypotheses, [](const snd::Hypothesis &value) {
    return std::holds_alternative<snd::AssumedJudgmentHolds>(value);
  });
}

const snd::EvaluatedApplication *
applicationPremise(const snd::EvaluatedApplication &application,
                   llvm::StringRef port) {
  auto child = application.premises.find(port.str());
  if (child == application.premises.end() || !child->second)
    return nullptr;
  return std::get_if<snd::EvaluatedApplication>(&child->second->node);
}

struct TestSoundnessEvaluatorPass
    : public PassWrapper<TestSoundnessEvaluatorPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessEvaluatorPass)

  TestSoundnessEvaluatorPass() = default;
  TestSoundnessEvaluatorPass(const TestSoundnessEvaluatorPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-soundness-evaluator"; }
  StringRef getDescription() const override {
    return "test executable APPLY and DERIVE soundness semantics";
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
      return fail("soundness-evaluator test expects one sealed artifact");
    zkc::pir::SealedOp sealed = *sealedOps.begin();

    auto artifact = zkc::test::admitSoundnessFixture(
        sealed, protocolVocabularyPath, constructionProfileRegistryPath);
    if (!artifact)
      return fail(llvm::toString(artifact.takeError()));
    auto ownedView = snd::buildSealedSoundnessView(*artifact);
    if (!ownedView)
      return fail(llvm::toString(ownedView.takeError()));
    const snd::SealedSoundnessView *view = &*ownedView;
    auto signature = snd::loadSignatureFromFile(signaturePath);
    if (!signature)
      return fail(llvm::toString(signature.takeError()));
    const snd::SoundnessCatalog *catalog = &signature->catalog;

    std::vector<snd::ExactRef> selectedBindingRefs;
    for (llvm::StringRef id : {kSumcheckBinding, kSrBinding, kFsBinding}) {
      auto binding = catalog->bindings.find(id.str());
      if (binding == catalog->bindings.end())
        return fail("selected evaluator binding is absent: " + id);
      selectedBindingRefs.push_back(binding->second.ref);
    }
    // The field's order and class are not artifact facts: the sealed protocol
    // authenticates the payload class and each round's challenge space and not
    // the order. The caller supplies both, and the rule states the
    // correspondence to the artifact as a hypothesis.
    snd::ResolvedParameterEnvironments resolved;
    for (const snd::ExactRef &ref : selectedBindingRefs) {
      auto binding = catalog->bindings.find(ref.id);
      if (binding == catalog->bindings.end())
        continue;
      auto rule = catalog->rules.find(binding->second.ruleRef.id);
      if (rule == catalog->rules.end())
        continue;
      snd::ResolvedParameterEnvironment environment;
      environment.bindingRef = ref;
      for (const snd::TypedDeclaration &parameter : rule->second.parameters) {
        if (parameter.name == "field_order")
          environment.values.emplace(parameter.name,
                                     snd::RuntimeValue::integer(llvm::cantFail(
                                         zkc::registry::Rational::fromDecimal(
                                             "2305843009213697249"))));
        else if (parameter.name == "field_class")
          environment.values.emplace(parameter.name,
                                     snd::RuntimeValue::text("scalar"));
      }
      if (!environment.values.empty())
        resolved.emplace(ref.id, std::move(environment));
    }
    snd::SoundnessContextOutcome contextOutcome = snd::buildSoundnessContext(
        *catalog, selectedBindingRefs, std::move(resolved));
    if (!contextOutcome.accepted())
      return fail("selected soundness context is ill-formed: " +
                  refusalText(*contextOutcome.refusal));
    const snd::SoundnessContext &context = *contextOutcome.context;

    std::vector<snd::ExactRef> mismatchedBindingRefs = selectedBindingRefs;
    mismatchedBindingRefs.front().sourceRevision += ".mismatch";
    if (failed(expectContextRefusal(
            module,
            snd::buildSoundnessContext(*catalog,
                                       std::move(mismatchedBindingRefs)),
            snd::RuntimePhase::BindingResolution,
            snd::RuntimeRefusalCode::InvalidReference,
            "same-id/different-revision binding selection")))
      return signalPassFailure();

    auto zeroBindingRule = catalog->rules.find("zkc.pcs.kzg_css");
    if (zeroBindingRule == catalog->rules.end() ||
        context.findRule(zeroBindingRule->second.ref))
      return fail("catalog-only zero-binding rule became executable");

    snd::ResolvedParameterEnvironment surplusEnvironment;
    surplusEnvironment.bindingRef = selectedBindingRefs.front();
    surplusEnvironment.values.emplace(
        "surplus",
        snd::RuntimeValue::integer(zkc::registry::Rational::fromInteger(1)));
    snd::ResolvedParameterEnvironments surplusParameters;
    surplusParameters.emplace(surplusEnvironment.bindingRef.id,
                              std::move(surplusEnvironment));
    if (failed(expectContextRefusal(
            module,
            snd::buildSoundnessContext(*catalog, selectedBindingRefs,
                                       std::move(surplusParameters)),
            snd::RuntimePhase::BindingResolution,
            snd::RuntimeRefusalCode::InvalidReference,
            "surplus resolved parameter")))
      return signalPassFailure();

    if (view->reductionsByTransformerPosition.size() != 1)
      return fail("sumcheck fixture does not have one exact reduction");
    const auto &[transformerPosition, reduction] =
        *view->reductionsByTransformerPosition.begin();
    if (reduction.contractRef.id != "sumcheck" ||
        reduction.orderedOutputs.size() != 1)
      return fail("sumcheck fixture resolved to the wrong reduction facts");

    const snd::RuleBinding &sumcheckBinding =
        *context.findBinding(selectedBindingRefs[0]);
    const snd::RuleBinding &srBinding =
        *context.findBinding(selectedBindingRefs[1]);
    const snd::RuleBinding &fsBinding =
        *context.findBinding(selectedBindingRefs[2]);
    const snd::SoundnessRule &sumcheckRule =
        *context.findRule(sumcheckBinding.ruleRef);
    const snd::SoundnessRule &srRule = *context.findRule(srBinding.ruleRef);
    const snd::SoundnessRule &fsRule = *context.findRule(fsBinding.ruleRef);
    if (sumcheckRule.ref.id != kSumcheckRule || srRule.ref.id != kSrRule ||
        fsRule.ref.id != kFsRule)
      return fail("selected bindings resolved the wrong executable rules");

    const snd::ClaimRef &owner = reduction.orderedOutputs.front();
    snd::SecuritySubject subject = protocolSubject(*view, owner);
    snd::ApplicationSite reductionSite = snd::ReductionOccurrence{
        view->artifactId, owner, transformerPosition, 0};
    snd::ApplicationSite srSite = snd::PathOccurrence{view->artifactId, owner};
    snd::ApplicationSite fsSite = snd::PathOccurrence{view->artifactId, owner};

    auto perRound =
        zkc::registry::Rational::fromDecimalPair("1", "1152921504606846976");
    auto quadratic = zkc::registry::Rational::fromDecimalPair(
        "25",
        "115792089237316195423570985008687907853269984665640564039457584007"
        "913129639936");
    if (!perRound)
      return fail(llvm::toString(perRound.takeError()));
    if (!quadratic)
      return fail(llvm::toString(quadratic.takeError()));

    snd::ApplyOutcome native = snd::applySoundnessRule(
        context, *view, reductionSite, sumcheckBinding.ref, {});
    if (!native.accepted())
      return fail("native sumcheck APPLY refused: " +
                  refusalText(*native.refusal));

    const snd::SecurityJudgment &nativeConclusion = native.applied->conclusion;
    const auto *roundResult =
        std::get_if<snd::RoundResult>(&nativeConclusion.result);
    snd::ClosedQuantity expectedSpace;
    expectedSpace.constant =
        zkc::registry::Rational::fromInteger(2305843009213693952LL);
    snd::ClosedQuantity expectedPerRound;
    expectedPerRound.constant = *perRound;
    if (nativeConclusion.subject != subject ||
        nativeConclusion.index != sumcheckRule.conclusionIndex ||
        !nativeConclusion.resourceVariables.empty() || !roundResult ||
        roundResult->rounds.size() != 2)
      return fail("native sumcheck APPLY returned the wrong judgment shape");
    for (size_t index = 0; index < roundResult->rounds.size(); ++index) {
      const snd::RoundResultEntry &round = roundResult->rounds[index];
      if (round.roundIndex != std::to_string(index) ||
          round.challengeSpace != expectedSpace ||
          round.bound.quantity != expectedPerRound ||
          !round.bound.primitiveGameTerms.empty())
        return fail("native sumcheck APPLY returned the wrong exact round");
    }
    snd::RuntimeValue subjectValue = snd::RuntimeValue::subject(subject);
    snd::RuntimeValue fieldOrderValue =
        snd::RuntimeValue::integer(llvm::cantFail(
            zkc::registry::Rational::fromDecimal("2305843009213697249")));
    // Two distinct claims travel with the conclusion: that the payload class
    // is the field of the supplied order, and that root counting still gives
    // the stated bound when the challenge space is a subset of it.
    snd::PropositionInstance fieldOrder = proposition(
        context, "zkc.side.field_order_match", {subjectValue, fieldOrderValue});
    snd::PropositionInstance subset =
        proposition(context, "zkc.assume.subset_sampling_root_bound",
                    {subjectValue, fieldOrderValue});
    if (nativeConclusion.hypotheses.size() != 2 ||
        !hasProposition(nativeConclusion, subset) ||
        !hasProposition(nativeConclusion, fieldOrder) ||
        hasAssumedJudgment(nativeConclusion))
      return fail("native sumcheck APPLY returned the wrong hypotheses");
    llvm::outs() << "apply: native sumcheck exact\n";

    auto nativePlan = std::make_shared<snd::DerivationPlan>();
    nativePlan->node =
        snd::ApplyDerivationPlan{reductionSite, sumcheckBinding.ref, {}};
    auto srPlan = std::make_shared<snd::DerivationPlan>();
    snd::ApplyDerivationPlan srApplication{srSite, srBinding.ref, {}};
    srApplication.premises.emplace("source_rbr", nativePlan);
    srPlan->node = std::move(srApplication);
    snd::ApplyDerivationPlan fsApplication{fsSite, fsBinding.ref, {}};
    fsApplication.premises.emplace("source_sr", srPlan);
    snd::DerivationPlan plan;
    plan.node = std::move(fsApplication);

    snd::DerivationTarget target{subject, fsRule.conclusionIndex,
                                 fsRule.resources};
    snd::DeriveOutcome derived =
        snd::deriveSoundness(context, *view, target, plan);
    if (!derived.accepted())
      return fail("sumcheck-to-FS DERIVE refused: " +
                  refusalText(*derived.refusal));
    if (derived.result->artifactId != view->artifactId ||
        derived.result->target.subject != target.subject ||
        derived.result->target.index != target.index ||
        !sameDeclarations(derived.result->target.resourceVariables,
                          target.resourceVariables))
      return fail("DERIVE changed the exact requested target");

    const auto *fsEvaluated =
        std::get_if<snd::EvaluatedApplication>(&derived.result->root.node);
    const snd::EvaluatedApplication *srEvaluated =
        fsEvaluated ? applicationPremise(*fsEvaluated, "source_sr") : nullptr;
    const snd::EvaluatedApplication *nativeEvaluated =
        srEvaluated ? applicationPremise(*srEvaluated, "source_rbr") : nullptr;
    if (!fsEvaluated || !srEvaluated || !nativeEvaluated ||
        fsEvaluated->bindingRef != fsBinding.ref ||
        srEvaluated->bindingRef != srBinding.ref ||
        nativeEvaluated->bindingRef != sumcheckBinding.ref ||
        nativeEvaluated->conclusion != nativeConclusion)
      return fail(
          "DERIVE did not retain the exact three-node application tree");

    snd::ClosedQuantity expectedSr;
    expectedSr.resourceTerms.push_back({*perRound, "t", 1});
    const auto *srResult =
        std::get_if<snd::ScalarResult>(&srEvaluated->conclusion.result);
    if (srEvaluated->conclusion.index != srRule.conclusionIndex || !srResult ||
        srResult->bound.quantity != expectedSr ||
        !srResult->bound.primitiveGameTerms.empty() ||
        !sameDeclarations(srEvaluated->conclusion.resourceVariables,
                          srRule.resources))
      return fail("state-restoration application returned the wrong bound");

    snd::ClosedQuantity expectedFs;
    expectedFs.resourceTerms.push_back({*perRound, "t", 1});
    expectedFs.resourceTerms.push_back({*quadratic, "t", 2});
    const snd::SecurityJudgment &fsConclusion = fsEvaluated->conclusion;
    const auto *fsResult = std::get_if<snd::ScalarResult>(&fsConclusion.result);
    if (fsConclusion.subject != subject ||
        fsConclusion.index != fsRule.conclusionIndex || !fsResult ||
        fsResult->bound.quantity != expectedFs ||
        !fsResult->bound.primitiveGameTerms.empty() ||
        !sameDeclarations(fsConclusion.resourceVariables, fsRule.resources))
      return fail("Fiat-Shamir application returned the wrong exact bound");

    // Everything the sumcheck entry carried is inherited through the chain.
    std::vector<snd::PropositionInstance> expectedHypotheses = {
        subset,
        fieldOrder,
        proposition(context, "zkc.hyp.move_budget_is_query_budget"),
        proposition(context, "zkc.hyp.transcript_only_sr_extractor"),
        proposition(context, "zkc.hyp.injective_absorb_encoding",
                    {subjectValue}),
        proposition(context, "zkc.hyp.ideal_unsalted_sponge", {subjectValue}),
        proposition(context, "zkc.assume.ideal_permutation", {subjectValue}),
    };
    if (fsConclusion.hypotheses.size() != expectedHypotheses.size() ||
        hasAssumedJudgment(fsConclusion) ||
        !llvm::all_of(expectedHypotheses,
                      [&](const snd::PropositionInstance &expected) {
                        return hasProposition(fsConclusion, expected);
                      }))
      return fail("Fiat-Shamir application returned the wrong hypothesis set");
    llvm::outs() << "derive: sumcheck -> sr -> fs exact\n";

    // The owned projection does not alias a mutable copy of its aggregate.
    snd::SealedSoundnessView mutableBareView = *view;
    mutableBareView.artifactId = "caller-forged";
    if (mutableBareView.artifactId == view->artifactId)
      return fail("owned view aliases a mutable bare copy");

    snd::TypedPremiseJudgments fsPremise{
        {"source_sr", srEvaluated->conclusion}};
    snd::ApplicationSite wrongPath =
        snd::PathOccurrence{view->artifactId, owner};
    if (failed(expectApplyRefusal(
            module,
            snd::applySoundnessRule(context, *view, wrongPath,
                                    sumcheckBinding.ref, {}),
            snd::RuntimePhase::BindingResolution,
            snd::RuntimeRefusalCode::BindingMismatch, "path binding mismatch")))
      return signalPassFailure();

    if (failed(expectApplyRefusal(
            module,
            snd::applySoundnessRule(context, *view, srSite, srBinding.ref, {}),
            snd::RuntimePhase::PremiseResolution,
            snd::RuntimeRefusalCode::PremiseMismatch, "missing premise")))
      return signalPassFailure();

    snd::SealedSoundnessView falseCondition = *view;
    falseCondition.reductionsByTransformerPosition.at(transformerPosition)
        .rounds.at(0)
        .challengeSpace =
        zkc::registry::Rational::fromInteger(4611686018427387904LL);
    falseCondition.reductionsByTransformerPosition.at(transformerPosition)
        .rounds.at(0)
        .challengeSpaceLog2 = zkc::registry::Rational::fromInteger(62);
    if (failed(expectApplyRefusal(
            module,
            snd::applySoundnessRule(context, falseCondition, reductionSite,
                                    sumcheckBinding.ref, {}),
            snd::RuntimePhase::ConditionEvaluation,
            snd::RuntimeRefusalCode::ConditionFailed, "condition false")))
      return signalPassFailure();

    snd::SealedSoundnessView excessiveExponent = *view;
    if (!excessiveExponent.duplex)
      return fail("sumcheck fixture has no duplex facts");
    excessiveExponent.duplex->capacity = 4097;
    if (failed(expectApplyRefusal(
            module,
            snd::applySoundnessRule(context, excessiveExponent, fsSite,
                                    fsBinding.ref, fsPremise),
            snd::RuntimePhase::QuantityValidation,
            snd::RuntimeRefusalCode::ArithmeticDomain,
            "dynamic exponent range")))
      return signalPassFailure();

    snd::DerivationPlan rootAssumption;
    rootAssumption.node = snd::ExternalJudgmentAssumption{fsConclusion};
    if (failed(expectDeriveRefusal(
            module,
            snd::deriveSoundness(context, *view, target, rootAssumption),
            snd::RuntimePhase::Derivation,
            snd::RuntimeRefusalCode::PremiseMismatch, "root assume")))
      return signalPassFailure();

    llvm::outs() << "soundness evaluator: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessEvaluatorPass() {
  PassRegistration<TestSoundnessEvaluatorPass>();
}
} // namespace zkc::test
