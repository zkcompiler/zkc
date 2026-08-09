//===- TestSoundnessRuleBodies.cpp - focused evaluator bodies -*- C++ -*-===//

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

#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

namespace snd = zkc::soundness;

constexpr const char *kSigmaRule = "zkc.ss.sigma";
constexpr const char *kSigmaBinding = "zkc.ss.sigma@reduction:sigma";
constexpr const char *kSsToRbrRule = "zkc.rbr.from_ss";
constexpr const char *kSsToRbrBinding =
    "zkc.rbr.from_ss@path:ss_to_rbr:soundness:standard";

std::string refusalText(const snd::SoundnessRefusal &refusal) {
  return std::string(snd::runtimePhaseName(refusal.phase)) + "/" +
         snd::runtimeRefusalCodeName(refusal.code) + " at " + refusal.location +
         ": " + refusal.detail;
}

bool hasAssumedJudgment(const snd::SecurityJudgment &judgment) {
  return llvm::any_of(judgment.hypotheses, [](const snd::Hypothesis &value) {
    return std::holds_alternative<snd::AssumedJudgmentHolds>(value);
  });
}

struct TestSoundnessRuleBodiesPass
    : public PassWrapper<TestSoundnessRuleBodiesPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessRuleBodiesPass)

  TestSoundnessRuleBodiesPass() = default;
  TestSoundnessRuleBodiesPass(const TestSoundnessRuleBodiesPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override {
    return "test-soundness-rule-bodies";
  }
  StringRef getDescription() const override {
    return "test focused positive soundness rule-body evaluation";
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
      return fail("soundness-rule-bodies test expects one sealed artifact");
    zkc::pir::SealedOp sealed = *sealedOps.begin();

    auto artifact = zkc::test::admitSoundnessFixture(
        sealed, protocolVocabularyPath, constructionProfileRegistryPath);
    if (!artifact)
      return fail(llvm::toString(artifact.takeError()));
    auto view = snd::buildSealedSoundnessView(*artifact);
    if (!view)
      return fail(llvm::toString(view.takeError()));
    auto signature = snd::loadSignatureFromFile(signaturePath);
    if (!signature)
      return fail(llvm::toString(signature.takeError()));
    const snd::SoundnessCatalog *catalog = &signature->catalog;

    auto sigmaRule = catalog->rules.find(kSigmaRule);
    auto sigmaBinding = catalog->bindings.find(kSigmaBinding);
    auto ssToRbrRule = catalog->rules.find(kSsToRbrRule);
    auto ssToRbrBinding = catalog->bindings.find(kSsToRbrBinding);
    if (sigmaRule == catalog->rules.end() ||
        sigmaBinding == catalog->bindings.end() ||
        ssToRbrRule == catalog->rules.end() ||
        ssToRbrBinding == catalog->bindings.end())
      return fail("focused registry-backed rule or binding is absent");

    if (view->reductionsByTransformerPosition.size() != 1)
      return fail("Schnorr fixture does not have one exact reduction");
    const auto &[transformerPosition, reduction] =
        *view->reductionsByTransformerPosition.begin();
    if (reduction.contractRef.id != "sigma" ||
        reduction.orderedOutputs.size() != 1)
      return fail("Schnorr fixture resolved to the wrong sigma reduction");

    snd::ResolvedParameterEnvironment sigmaParameters;
    sigmaParameters.bindingRef = sigmaBinding->second.ref;
    sigmaParameters.values.emplace(
        "algebra",
        snd::RuntimeValue::algebra(
            {"algebra:test:sigma", "scalar",
             zkc::registry::Rational::fromInteger(2305843009213693952LL)}));
    snd::ResolvedParameterEnvironments resolvedParameters;
    resolvedParameters.emplace(sigmaParameters.bindingRef.id,
                               std::move(sigmaParameters));

    std::vector<snd::ExactRef> selectedBindingRefs = {
        sigmaBinding->second.ref, ssToRbrBinding->second.ref};
    snd::SoundnessContextOutcome contextOutcome =
        snd::buildSoundnessContext(*catalog, std::move(selectedBindingRefs),
                                   std::move(resolvedParameters));
    if (!contextOutcome.accepted())
      return fail("focused soundness context is ill-formed: " +
                  refusalText(*contextOutcome.refusal));
    const snd::SoundnessContext &context = *contextOutcome.context;

    const snd::ClaimRef &owner = reduction.orderedOutputs.front();
    snd::ApplicationSite reductionSite = snd::ReductionOccurrence{
        view->artifactId, owner, transformerPosition, 0};
    snd::ApplyOutcome sigma = snd::applySoundnessRule(
        context, *view, reductionSite, sigmaBinding->second.ref, {});
    if (!sigma.accepted())
      return fail("Sigma SpecialSoundnessEntry APPLY refused: " +
                  refusalText(*sigma.refusal));

    snd::ClosedQuantity expectedArity;
    expectedArity.constant = zkc::registry::Rational::fromInteger(2);
    snd::ClosedQuantity expectedSpace;
    expectedSpace.constant =
        zkc::registry::Rational::fromInteger(2305843009213693952LL);
    const snd::SecurityJudgment &sigmaConclusion = sigma.applied->conclusion;
    const auto *extraction =
        std::get_if<snd::ExtractionResult>(&sigmaConclusion.result);
    if (sigmaConclusion.index != sigmaRule->second.conclusionIndex ||
        !extraction || extraction->coordinates.size() != 1 ||
        extraction->coordinates.front().label != "0" ||
        extraction->coordinates.front().arity != expectedArity ||
        extraction->coordinates.front().challengeSpace != expectedSpace ||
        extraction->failureBound || hasAssumedJudgment(sigmaConclusion))
      return fail(
          "Sigma SpecialSoundnessEntry returned the wrong exact judgment");
    llvm::outs() << "body: special soundness entry exact\n";

    snd::ApplicationSite pathSite =
        snd::PathOccurrence{view->artifactId, owner};
    snd::TypedPremiseJudgments premises{{"source_ss", sigmaConclusion}};
    snd::ApplyOutcome ssToRbr = snd::applySoundnessRule(
        context, *view, pathSite, ssToRbrBinding->second.ref, premises);
    if (!ssToRbr.accepted())
      return fail("SpecialSoundnessToRoundByRound APPLY refused: " +
                  refusalText(*ssToRbr.refusal));

    auto expectedBound =
        zkc::registry::Rational::fromDecimalPair("1", "2305843009213693952");
    if (!expectedBound)
      return fail(llvm::toString(expectedBound.takeError()));
    snd::ClosedQuantity expectedPerRound;
    expectedPerRound.constant = *expectedBound;
    const snd::SecurityJudgment &rbrConclusion = ssToRbr.applied->conclusion;
    const auto *rounds = std::get_if<snd::RoundResult>(&rbrConclusion.result);
    if (rbrConclusion.index != ssToRbrRule->second.conclusionIndex || !rounds ||
        rounds->rounds.size() != 1 ||
        rounds->rounds.front().roundIndex != "0" ||
        rounds->rounds.front().challengeSpace != expectedSpace ||
        rounds->rounds.front().bound.quantity != expectedPerRound ||
        !rounds->rounds.front().bound.primitiveGameTerms.empty() ||
        hasAssumedJudgment(rbrConclusion))
      return fail("SpecialSoundnessToRoundByRound returned the wrong exact "
                  "judgment");
    llvm::outs() << "body: special soundness to round-by-round exact\n";
    llvm::outs() << "soundness rule bodies: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessRuleBodiesPass() {
  PassRegistration<TestSoundnessRuleBodiesPass>();
}
} // namespace zkc::test
