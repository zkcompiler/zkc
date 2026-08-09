//===- TestSoundnessProjection.cpp - closed projection tests ----*- C++ -*-===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Soundness/SoundnessProjection.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

using zkc::registry::Rational;
using namespace zkc::soundness;

template <typename T>
LogicalResult expectRefusal(ModuleOp module, llvm::Expected<T> result,
                            llvm::StringRef expected, llvm::StringRef label) {
  if (result) {
    module.emitError() << label << " unexpectedly succeeded";
    return failure();
  }
  std::string detail = llvm::toString(result.takeError());
  if (!llvm::StringRef(detail).contains(expected)) {
    module.emitError() << label << " produced the wrong refusal: " << detail;
    return failure();
  }
  return success();
}

bool isNumber(const RuntimeValue &value, ValueSort sort, int64_t expected) {
  const auto *number = std::get_if<Rational>(&value.payload);
  return value.sort == sort && number &&
         number->compare(Rational::fromInteger(expected)) == 0;
}

SealedSoundnessView makeFixture() {
  ClaimRef source{0, "claim-source"};
  ClaimRef output{1, "claim-output"};

  SealedRoundFact iid;
  iid.position = 0;
  iid.kind = "fold";
  iid.challengeRole = "queries";
  iid.challengeEventPosition = 4;
  iid.challengePayloadClass = "field_element";
  iid.challengeDomain = "fri_query";
  iid.challengeSpace = Rational::fromInteger(16);
  iid.challengeCount = 3;
  iid.shape = ChallengeShape::Vector;
  iid.sampling = ChallengeSampling::UniformIndependent;
  iid.messages = {{"oracle", {"field_element"}}};
  iid.challengeSpaceLog2 = Rational::fromInteger(4);

  SealedRoundFact scalar;
  scalar.position = 1;
  scalar.kind = "scalar";
  scalar.challengeRole = "alpha";
  scalar.challengeEventPosition = 7;
  scalar.challengePayloadClass = "field_element";
  scalar.challengeDomain = "fri_alpha";
  scalar.challengeSpace = Rational::fromInteger(16);
  scalar.challengeCount = 1;
  scalar.shape = ChallengeShape::Scalar;
  scalar.sampling = ChallengeSampling::Uniform;
  scalar.messages = {{"oracle", {"field_element"}}};
  scalar.challengeSpaceLog2 = Rational::fromInteger(4);

  SealedReduction reduction;
  reduction.transformerPosition = 9;
  reduction.contractRef = {"fri-contract", "contract-digest"};
  reduction.orderedInputs = {source};
  reduction.orderedOutputs = {output};
  reduction.parameters.emplace(
      "n", SealedParameterAtom{SealedParameterAtom::Carrier::String,
                               std::string("16")});
  reduction.rounds = {std::move(iid), std::move(scalar)};

  SealedSoundnessView sealed;
  sealed.artifactId = "projection-fixture";
  sealed.claimsByIndex = {source, output};
  sealed.reductionsByTransformerPosition.emplace(reduction.transformerPosition,
                                                 std::move(reduction));
  return sealed;
}

ArtifactProjection roundField(llvm::StringRef kind, llvm::StringRef field,
                              ValueSort sort) {
  ArtifactProjection projection;
  projection.kind = ArtifactProjectionKind::ContractRoundFamilyField;
  projection.resultSort = sort;
  projection.field = field.str();
  projection.roundSelector.kind = ContractRoundSelectorKind::RoundKind;
  projection.roundSelector.roundKind = kind.str();
  projection.aggregate = ProjectionAggregate::UniqueEqual;
  return projection;
}

struct TestSoundnessProjectionPass
    : public PassWrapper<TestSoundnessProjectionPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessProjectionPass)

  TestSoundnessProjectionPass() = default;
  TestSoundnessProjectionPass(const TestSoundnessProjectionPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-soundness-projection"; }
  StringRef getDescription() const override {
    return "test closed soundness projections and machine deciders";
  }

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };

    SealedSoundnessView sealed = makeFixture();
    const ClaimRef &output = sealed.claimsByIndex[1];
    ReductionOccurrence occurrence{sealed.artifactId, output, 9, 0};
    ApplicationSite reductionSite = occurrence;

    ArtifactProjection parameter;
    parameter.kind = ArtifactProjectionKind::ReductionParameter;
    parameter.resultSort = ValueSort::Integer;
    parameter.field = "n";
    auto n = projectArtifactFact(sealed, reductionSite, parameter);
    if (!n || !isNumber(*n, ValueSort::Integer, 16))
      return fail(n ? "exact integer parameter projected incorrectly"
                    : llvm::toString(n.takeError()));

    auto iidCount = projectArtifactFact(
        sealed, reductionSite,
        roundField("fold", "ChallengeCount", ValueSort::Integer));
    if (!iidCount || !isNumber(*iidCount, ValueSort::Integer, 3))
      return fail(iidCount ? "IID challenge count projected incorrectly"
                           : llvm::toString(iidCount.takeError()));

    if (failed(expectRefusal(
            module,
            projectArtifactFact(
                sealed, reductionSite,
                roundField("scalar", "ChallengeCount", ValueSort::Integer)),
            "ChallengeCount requires an IID vector challenge",
            "scalar ChallengeCount")))
      return signalPassFailure();

    llvm::outs()
        << "projection: exact parameter and IID-only challenge count\n";
    llvm::outs() << "projection: scalar ChallengeCount refused\n";

    RuleBinding authorized;
    authorized.ref = {"fri-path-binding", "binding-digest"};
    authorized.anchor.kind = ProtocolAnchorKind::PathTransition;
    authorized.anchor.ref = {"fri-path-transition", "transition-digest"};
    PathOccurrence pathOccurrence{sealed.artifactId, output};
    ApplicationSite pathSite = pathOccurrence;

    auto transition =
        resolveApplicationPathTransition(sealed, pathSite, authorized);
    if (!transition || transition->sort != ValueSort::PathTransition)
      return fail(transition ? "authorized path resolved to the wrong sort"
                             : llvm::toString(transition.takeError()));
    const auto *pathValue =
        std::get_if<PathTransitionValue>(&transition->payload);
    if (!pathValue || pathValue->ref != authorized.anchor.ref ||
        pathValue->artifactId != sealed.artifactId ||
        pathValue->claim != output)
      return fail("authorized path did not preserve its exact identity");

    RuleBinding malformedAuthority = authorized;
    malformedAuthority.ref.sourceRevision.clear();
    if (failed(expectRefusal(module,
                             resolveApplicationPathTransition(
                                 sealed, pathSite, malformedAuthority),
                             "selected path binding reference is not exact",
                             "malformed path binding authority")))
      return signalPassFailure();
    llvm::outs() << "path: selected binding is the sole exact authority\n";

    auto expectDecider = [&](MachineDeciderKind kind,
                             std::vector<RuntimeValue> arguments, bool expected,
                             llvm::StringRef label) {
      auto result = evaluateMachineDecider(kind, arguments);
      if (!result) {
        fail(label + ": " + llvm::toString(result.takeError()));
        return false;
      }
      if (*result != expected) {
        fail(label + " returned the wrong Boolean");
        return false;
      }
      return true;
    };

    if (!expectDecider(MachineDeciderKind::FriRateBelowOne,
                       {RuntimeValue::integer(Rational::fromInteger(16)),
                        RuntimeValue::integer(Rational::fromInteger(8))},
                       true, "FRI rate positive") ||
        !expectDecider(MachineDeciderKind::FriRateBelowOne,
                       {RuntimeValue::integer(Rational::fromInteger(8)),
                        RuntimeValue::integer(Rational::fromInteger(8))},
                       false, "FRI rate boundary") ||
        !expectDecider(MachineDeciderKind::JohnsonFoldParam,
                       {RuntimeValue::integer(Rational::fromInteger(3))}, true,
                       "Johnson fold positive") ||
        !expectDecider(MachineDeciderKind::JohnsonFoldParam,
                       {RuntimeValue::integer(Rational::fromInteger(2))}, false,
                       "Johnson fold negative"))
      return;
    llvm::outs() << "FRI arithmetic: positive and negative cases exact\n";

    if (failed(expectRefusal(
            module,
            evaluateMachineDecider(
                MachineDeciderKind::JohnsonDelta,
                {RuntimeValue::rational(Rational::fromInteger(1)),
                 RuntimeValue::rational(Rational::fromInteger(1)),
                 RuntimeValue::integer(Rational::fromInteger(10000)),
                 RuntimeValue::integer(Rational::fromInteger(1))}),
            "exponent exceeds the v0 exact arithmetic range",
            "Johnson exponent range")) ||
        failed(expectRefusal(
            module,
            evaluateMachineDecider(
                MachineDeciderKind::UdrDomainFloor,
                {RuntimeValue::integer(Rational::fromInteger(10000)),
                 RuntimeValue::integer(Rational::fromInteger(1))}),
            "exponent exceeds the v0 exact arithmetic range",
            "UDR exponent range")))
      return signalPassFailure();
    llvm::outs() << "decider arithmetic: excessive exponents refused\n";

    ArtifactProjection contractProjection;
    contractProjection.kind =
        ArtifactProjectionKind::ConclusionReductionContract;
    contractProjection.resultSort = ValueSort::ReductionContract;
    auto contract =
        projectArtifactFact(sealed, reductionSite, contractProjection);
    if (!contract)
      return fail(llvm::toString(contract.takeError()));
    auto samePoint =
        evaluateMachineDecider(MachineDeciderKind::SamePoint, {*contract});
    if (!samePoint)
      return fail(llvm::toString(samePoint.takeError()));
    if (*samePoint)
      return fail("SamePoint accepted a contract with no input-anchor facts");

    llvm::outs() << "SamePoint: missing facts fail closed\n";
    llvm::outs() << "soundness projection: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessProjectionPass() {
  PassRegistration<TestSoundnessProjectionPass>();
}
} // namespace zkc::test
