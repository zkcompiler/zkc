//===- TestSoundnessSemanticRegressions.cpp - evaluator regressions -------===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Soundness/SignatureFile.h"
#include "zkc/Soundness/SoundnessEvaluator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

namespace snd = zkc::soundness;

constexpr llvm::StringLiteral kGrindingRule = "zkc.rbr.grinding";

std::string refusalText(const snd::SoundnessRefusal &refusal) {
  return std::string(snd::runtimePhaseName(refusal.phase)) + "/" +
         snd::runtimeRefusalCodeName(refusal.code) + " at " + refusal.location +
         ": " + refusal.detail;
}

snd::SecuritySubject protocolSubject(const snd::SealedSoundnessView &view,
                                     const snd::ClaimRef &claim) {
  snd::SecuritySubject subject;
  subject.payload = snd::ProtocolClaimSubject{view.artifactId, claim};
  return subject;
}

snd::ClosedQuantity integerQuantity(int64_t value) {
  snd::ClosedQuantity quantity;
  quantity.constant = zkc::registry::Rational::fromInteger(value);
  return quantity;
}

snd::RoundResultEntry roundEntry(llvm::StringRef label, int64_t space,
                                 int64_t bound) {
  snd::RoundResultEntry round;
  round.roundIndex = label.str();
  round.challengeSpace = integerQuantity(space);
  round.bound.quantity = integerQuantity(bound);
  return round;
}

LogicalResult expectApplyRefusal(ModuleOp module, snd::ApplyOutcome outcome,
                                 snd::RuntimePhase phase,
                                 snd::RuntimeRefusalCode code,
                                 llvm::StringRef location,
                                 llvm::StringRef label) {
  if (outcome.accepted() || !outcome.refusal) {
    module.emitError() << label << " unexpectedly accepted";
    return failure();
  }
  if (outcome.refusal->phase != phase || outcome.refusal->code != code ||
      outcome.refusal->location != location) {
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
                                  llvm::StringRef location,
                                  llvm::StringRef label) {
  if (outcome.accepted() || !outcome.refusal) {
    module.emitError() << label << " unexpectedly accepted";
    return failure();
  }
  if (outcome.refusal->phase != phase || outcome.refusal->code != code ||
      outcome.refusal->location != location) {
    module.emitError() << label << " produced the wrong refusal: "
                       << refusalText(*outcome.refusal);
    return failure();
  }
  llvm::outs() << label << ": refused\n";
  return success();
}

struct TestSoundnessSemanticRegressionsPass
    : public PassWrapper<TestSoundnessSemanticRegressionsPass,
                         OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(
      TestSoundnessSemanticRegressionsPass)

  TestSoundnessSemanticRegressionsPass() = default;
  TestSoundnessSemanticRegressionsPass(
      const TestSoundnessSemanticRegressionsPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override {
    return "test-soundness-semantic-regressions";
  }
  StringRef getDescription() const override {
    return "test focused executable soundness semantic regressions";
  }

  Option<std::string> protocolVocabularyPath{
      *this, "protocol-vocabulary", llvm::cl::desc("protocol vocabulary")};
  Option<std::string> signaturePath{*this, "signature",
                                    llvm::cl::desc("the shipped signature")};

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };

    auto vocabulary =
        zkc::registry::ProtocolVocabulary::loadFromFile(protocolVocabularyPath);
    if (!vocabulary)
      return fail(llvm::toString(vocabulary.takeError()));
    auto signature = snd::loadSignatureFromFile(signaturePath);
    if (!signature)
      return fail(llvm::toString(signature.takeError()));
    const snd::SoundnessCatalog *catalog = &signature->catalog;

    auto ruleEntry = catalog->rules.find(kGrindingRule.str());
    if (ruleEntry == catalog->rules.end())
      return fail("adapted grinding rule is absent");
    auto bindingEntry =
        llvm::find_if(catalog->bindings, [&](const auto &entry) {
          return entry.second.ruleRef == ruleEntry->second.ref;
        });
    if (bindingEntry == catalog->bindings.end())
      return fail("adapted grinding binding is absent");

    snd::SoundnessContextOutcome contextOutcome =
        snd::buildSoundnessContext(*catalog, {bindingEntry->second.ref});
    if (!contextOutcome.accepted())
      return fail("grinding context is ill-formed: " +
                  refusalText(*contextOutcome.refusal));
    const snd::SoundnessContext &context = *contextOutcome.context;

    const snd::SoundnessRule *rule = context.findRule(ruleEntry->second.ref);
    const snd::RuleBinding *binding =
        context.findBinding(bindingEntry->second.ref);
    if (!rule || !binding || rule->premises.size() != 1 ||
        rule->premises.front().name != "source_rbr")
      return fail("selected grinding semantics have the wrong premise shape");

    const snd::ClaimRef premiseClaim{
        0, "sha256:"
           "1111111111111111111111111111111111111111111111111111111111111111"};
    const snd::ClaimRef ownerClaim{
        1, "sha256:"
           "2222222222222222222222222222222222222222222222222222222222222222"};

    snd::SealedRoundFact powRound;
    powRound.position = 0;
    powRound.kind = "pow";
    powRound.challengeRole = "pow";
    powRound.challengeEventPosition = 10;
    powRound.challengePayloadClass = "pow_value";
    powRound.challengeDomain = "pow_space";
    powRound.challengeSpace = zkc::registry::Rational::fromInteger(8);
    powRound.messages.push_back({"nonce", {"nonce"}});
    powRound.challengeSpaceLog2 = zkc::registry::Rational::fromInteger(3);

    snd::SealedReduction reduction;
    reduction.transformerPosition = 1;
    reduction.contractRef = binding->anchor.ref;
    reduction.orderedInputs = {premiseClaim};
    reduction.orderedOutputs = {ownerClaim};
    reduction.rounds = {std::move(powRound)};
    reduction.roundAdjacency = snd::RoundAdjacencyValue{
        binding->anchor.ref,
        /*grindingTransformerPosition=*/1,
        premiseClaim,
        /*premiseTransformerPosition=*/0,
        /*powChallengeEventPosition=*/10,
        /*pinCheckEventPosition=*/11,
        /*successorChallengeEventPosition=*/12,
        /*premiseRoundPosition=*/0,
    };

    // The premise reduction the adjacency names.  An ordinal into the premise
    // contract's round list only selects the intended round while the premise
    // result is that reduction's rounds one for one, so the mock has to carry
    // it: without this the ordinal describes an artifact that cannot exist.
    snd::SealedRoundFact premiseRound;
    premiseRound.position = 0;
    premiseRound.challengeRole = "c";
    premiseRound.challengeEventPosition = 4;
    premiseRound.challengePayloadClass = "scalar";
    premiseRound.challengeDomain = "premise.c";
    premiseRound.challengeSpace = zkc::registry::Rational::fromInteger(17);
    snd::SealedRoundFact premiseRoundTwo = premiseRound;
    premiseRoundTwo.position = 1;
    premiseRoundTwo.challengeEventPosition = 6;
    premiseRoundTwo.challengeDomain = "premise.c2";
    premiseRoundTwo.challengeSpace = zkc::registry::Rational::fromInteger(19);

    snd::SealedReduction premiseReduction;
    premiseReduction.transformerPosition = 0;
    premiseReduction.contractRef = binding->anchor.ref;
    premiseReduction.orderedOutputs = {premiseClaim};
    premiseReduction.rounds = {std::move(premiseRound),
                               std::move(premiseRoundTwo)};

    snd::SealedSoundnessView view;
    view.artifactId = "soundness-semantic-regression";
    view.claimsByIndex = {premiseClaim, ownerClaim};
    view.reductionsByTransformerPosition.emplace(
        premiseReduction.transformerPosition, std::move(premiseReduction));
    view.reductionsByTransformerPosition.emplace(reduction.transformerPosition,
                                                 std::move(reduction));

    snd::ReductionOccurrence reductionSite{view.artifactId, ownerClaim,
                                           /*transformerPosition=*/1,
                                           /*outputIndex=*/0};
    snd::ApplicationSite site = reductionSite;

    snd::SecurityJudgment premise;
    premise.subject = protocolSubject(view, premiseClaim);
    premise.index = rule->premises.front().expectedIndex;
    premise.result =
        snd::RoundResult{{roundEntry("1", 17, 10), roundEntry("0", 19, 20)}};
    snd::TypedPremiseJudgments premises{{"source_rbr", premise}};

    snd::ApplyOutcome applied =
        snd::applySoundnessRule(context, view, site, binding->ref, premises);
    if (!applied.accepted())
      return fail("ordinal grinding APPLY refused: " +
                  refusalText(*applied.refusal));
    const auto *scaled =
        std::get_if<snd::RoundResult>(&applied.applied->conclusion.result);
    auto fiveFourths = zkc::registry::Rational::fromDecimalPair("5", "4");
    if (!fiveFourths)
      return fail(llvm::toString(fiveFourths.takeError()));
    snd::RoundResult expected = std::get<snd::RoundResult>(premise.result);
    expected.rounds[0].bound.quantity.constant = *fiveFourths;
    if (!scaled || *scaled != expected || scaled->rounds[0].roundIndex != "1" ||
        scaled->rounds[1].roundIndex != "0")
      return fail("authenticated predecessor ordinal 0 did not scale vector "
                  "position 0 exactly");
    llvm::outs() << "grinding ordinal 0 scales vector position 0: accepted\n";

    // A composed premise is longer than the premise reduction's own rounds, so
    // the ordinal no longer names the round it was authenticated against.  The
    // range check alone passes, which is exactly why this is checked.
    snd::TypedPremiseJudgments composedPremises = premises;
    std::get<snd::RoundResult>(composedPremises.at("source_rbr").result)
        .rounds.push_back(roundEntry("2", 23, 30));
    if (failed(expectApplyRefusal(module,
                                  snd::applySoundnessRule(context, view, site,
                                                          binding->ref,
                                                          composedPremises),
                                  snd::RuntimePhase::RuleEvaluation,
                                  snd::RuntimeRefusalCode::PremiseMismatch,
                                  "apply.body.selected_round",
                                  "grinding ordinal over a composed premise")))
      return signalPassFailure();

    snd::SealedSoundnessView mismatchedClaim = view;
    mismatchedClaim.reductionsByTransformerPosition.at(1)
        .roundAdjacency->premiseClaim = ownerClaim;
    if (failed(expectApplyRefusal(
            module,
            snd::applySoundnessRule(context, mismatchedClaim, site,
                                    binding->ref, premises),
            snd::RuntimePhase::RuleEvaluation,
            snd::RuntimeRefusalCode::PremiseMismatch,
            "apply.body.selected_round",
            "grinding adjacency exact premise claim")))
      return signalPassFailure();

    snd::SecurityJudgment preMarkedPremise = premise;
    preMarkedPremise.hypotheses.push_back(snd::AssumedJudgmentHolds{
        std::make_shared<const snd::SecurityJudgment>(premise)});
    auto assumption = std::make_shared<snd::DerivationPlan>();
    assumption->node =
        snd::ExternalJudgmentAssumption{std::move(preMarkedPremise)};
    snd::ApplyDerivationPlan rootApplication{site, binding->ref, {}};
    rootApplication.premises.emplace("source_rbr", assumption);
    snd::DerivationPlan plan;
    plan.node = std::move(rootApplication);
    snd::DerivationTarget target{protocolSubject(view, ownerClaim),
                                 rule->conclusionIndex, rule->resources};
    if (failed(expectDeriveRefusal(
            module, snd::deriveSoundness(context, view, target, plan),
            snd::RuntimePhase::Derivation,
            snd::RuntimeRefusalCode::InvalidPayload,
            "derive.root.premises.source_rbr.assumption.input.hypotheses",
            "derive pre-marked assumption")))
      return signalPassFailure();

    llvm::outs() << "soundness semantic regressions: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessSemanticRegressionsPass() {
  PassRegistration<TestSoundnessSemanticRegressionsPass>();
}
} // namespace zkc::test
