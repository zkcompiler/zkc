//===- TestSoundnessRuntime.cpp - closed runtime safety tests ---*- C++ -*-===//

#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Soundness/SoundnessRuntime.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdint>
#include <map>
#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

using zkc::registry::Rational;
using namespace zkc::soundness;

ClosedQuantity integerQuantity(int64_t value) {
  ClosedQuantity result;
  result.constant = Rational::fromInteger(value);
  return result;
}

ClosedQuantity resourceQuantity(llvm::StringRef resource,
                                int64_t coefficient = 1,
                                uint64_t exponent = 1) {
  ClosedQuantity result;
  result.resourceTerms.push_back(
      {Rational::fromInteger(coefficient), resource.str(), exponent});
  return result;
}

Rational fraction(int64_t numerator, int64_t denominator) {
  auto value = Rational::fromDecimalPair(std::to_string(numerator),
                                         std::to_string(denominator));
  if (!value) {
    llvm::consumeError(value.takeError());
    return Rational();
  }
  return std::move(*value);
}

SchemaContext makeContext() {
  SchemaContext context;
  context.securityIndices = {
      {SecurityNotion::SpecialSoundness, SecurityTrack::Knowledge, {}, {}},
      {SecurityNotion::ComputationalSpecialSoundness,
       SecurityTrack::Knowledge,
       {},
       {}},
      {SecurityNotion::RoundByRound,
       SecurityTrack::Knowledge,
       "straightline",
       {}}};
  constexpr const char *kSubjectSchema = "zkc.subject.protocol_claim";
  context.subjectSchemas.emplace(
      kSubjectSchema,
      SubjectSchema{kSubjectSchema, {}, SubjectSchemaKind::ProtocolClaim});
  context.primitiveGames.emplace(
      "game", PrimitiveGameDefinition{{"game", "game-revision"},
                                      {},
                                      {{"tau", ValueSort::Integer}}});
  return context;
}

SecuritySubject makeSubject() {
  return SecuritySubject{
      ProtocolClaimSubject{"artifact", ClaimRef{0, "claim-digest"}}};
}

ExtractionResult makeExtraction() {
  ExtractionResult result;
  result.coordinates.push_back(
      ExtractionCoordinate{"witness", integerQuantity(1), integerQuantity(8)});
  return result;
}

SecurityJudgment makeSpecialSoundnessJudgment() {
  SecurityJudgment judgment;
  judgment.subject = makeSubject();
  judgment.index = {
      SecurityNotion::SpecialSoundness, SecurityTrack::Knowledge, {}, {}};
  judgment.result = makeExtraction();
  return judgment;
}

SecurityJudgment makeComputationalJudgment() {
  SecurityJudgment judgment = makeSpecialSoundnessJudgment();
  judgment.index = {SecurityNotion::ComputationalSpecialSoundness,
                    SecurityTrack::Knowledge,
                    {},
                    {}};

  PrimitiveGameTerm game;
  game.coefficient = Rational::fromInteger(1);
  game.instance.ref = {"game", "game-revision"};
  game.resourceSubstitution.emplace("tau", integerQuantity(1));

  ExtractionResult extraction = makeExtraction();
  extraction.failureBound = ClosedBound{};
  extraction.failureBound->primitiveGameTerms.push_back(std::move(game));
  judgment.result = std::move(extraction);
  return judgment;
}

LogicalResult expectRefusal(ModuleOp module, const RuntimeCheckResult &result,
                            RuntimeRefusalCode code, llvm::StringRef detail,
                            llvm::StringRef label) {
  if (result.accepted()) {
    module.emitError() << label << " unexpectedly succeeded";
    return failure();
  }
  if (result.refusal->code != code ||
      !llvm::StringRef(result.refusal->detail).contains(detail)) {
    module.emitError() << label << " produced the wrong refusal: "
                       << runtimeRefusalCodeName(result.refusal->code) << ": "
                       << result.refusal->detail;
    return failure();
  }
  return success();
}

struct TestSoundnessRuntimePass
    : public PassWrapper<TestSoundnessRuntimePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestSoundnessRuntimePass)

  TestSoundnessRuntimePass() = default;
  TestSoundnessRuntimePass(const TestSoundnessRuntimePass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-soundness-runtime"; }
  StringRef getDescription() const override {
    return "test closed soundness-runtime safety boundaries";
  }

  void runOnOperation() override {
    ModuleOp module = getOperation();
    SchemaContext context = makeContext();

    SecurityJudgment symbolicArity = makeSpecialSoundnessJudgment();
    symbolicArity.resourceVariables.push_back({"t", ValueSort::Integer});
    auto &coordinate =
        std::get<ExtractionResult>(symbolicArity.result).coordinates.front();
    coordinate.arity = integerQuantity(0);
    coordinate.arity.resourceTerms.push_back(
        {Rational::fromInteger(1), "t", 1});
    if (failed(expectRefusal(
            module, checkSecurityJudgmentWellFormed(context, symbolicArity),
            RuntimeRefusalCode::UnsupportedNormalForm,
            "must not depend on a resource valuation", "symbolic arity")))
      return signalPassFailure();

    SecurityJudgment fractionalSpace = makeSpecialSoundnessJudgment();
    auto &space = *std::get<ExtractionResult>(fractionalSpace.result)
                       .coordinates.front()
                       .challengeSpace;
    space.constant = fraction(3, 2);
    if (failed(expectRefusal(
            module, checkSecurityJudgmentWellFormed(context, fractionalSpace),
            RuntimeRefusalCode::ArithmeticDomain, "positive exact integer",
            "fractional challenge space")))
      return signalPassFailure();

    SecurityJudgment malformedIndex = makeSpecialSoundnessJudgment();
    malformedIndex.index = {
        SecurityNotion::RoundByRound, SecurityTrack::Knowledge, {}, {}};
    context.securityIndices.push_back(malformedIndex.index);
    if (failed(expectRefusal(
            module, checkSecurityJudgmentWellFormed(context, malformedIndex),
            RuntimeRefusalCode::UnknownIndex, "malformed", "index shape")))
      return signalPassFailure();

    SecurityJudgment unknownEnum = makeSpecialSoundnessJudgment();
    unknownEnum.index.notion = static_cast<SecurityNotion>(255);
    context.securityIndices.push_back(unknownEnum.index);
    if (failed(expectRefusal(
            module, checkSecurityJudgmentWellFormed(context, unknownEnum),
            RuntimeRefusalCode::UnknownIndex, "unknown security-index enum",
            "index enum")))
      return signalPassFailure();

    ClosedQuantity excessiveMonomial = integerQuantity(0);
    excessiveMonomial.resourceTerms.push_back(
        {Rational::fromInteger(1), "t", 4097});
    if (failed(expectRefusal(
            module, checkClosedQuantityWellFormed(excessiveMonomial),
            RuntimeRefusalCode::UnsupportedNormalForm,
            "exceeds the v0 exact range", "monomial exponent")))
      return signalPassFailure();

    ReductionContractRoundValue oversizedRound;
    oversizedRound.roundIndex = Rational::fromInteger(0);
    oversizedRound.challengeRole = "alpha";
    oversizedRound.challengePayloadClass = "field";
    oversizedRound.challengeDomain = "field";
    oversizedRound.challengeSpace = Rational::fromInteger(1);
    oversizedRound.challengeSpaceLog2 = Rational::fromInteger(4097);
    ReductionContractValue oversizedContract;
    oversizedContract.ref = {"contract", "contract-revision"};
    oversizedContract.inputCount = 1;
    oversizedContract.rounds.push_back(std::move(oversizedRound));
    if (failed(expectRefusal(
            module,
            checkRuntimeValueWellFormed(
                RuntimeValue::reductionContract(std::move(oversizedContract))),
            RuntimeRefusalCode::UnsupportedNormalForm,
            "exceeds the v0 exact range", "contract exponent")))
      return signalPassFailure();

    SecurityJudgment exactGame = makeComputationalJudgment();
    if (!checkSecurityJudgmentWellFormed(context, exactGame).accepted()) {
      module.emitError() << "exact primitive-game substitution was refused";
      return signalPassFailure();
    }

    SchemaContext duplicateSchema = context;
    duplicateSchema.primitiveGames.at("game").resources.push_back(
        {"tau", ValueSort::Integer});
    if (failed(expectRefusal(
            module, checkSecurityJudgmentWellFormed(duplicateSchema, exactGame),
            RuntimeRefusalCode::InvalidResource, "nonempty unique name",
            "duplicate game resource")))
      return signalPassFailure();

    SecurityJudgment extraSubstitution = exactGame;
    auto &gameTerm = std::get<ExtractionResult>(extraSubstitution.result)
                         .failureBound->primitiveGameTerms.front();
    gameTerm.resourceSubstitution.emplace("extra", integerQuantity(1));
    if (failed(expectRefusal(
            module, checkSecurityJudgmentWellFormed(context, extraSubstitution),
            RuntimeRefusalCode::InvalidResource, "exactly match",
            "extra game substitution")))
      return signalPassFailure();

    SchemaContext resourceFreeSchema = context;
    resourceFreeSchema.primitiveGames.at("game").resources.clear();
    SecurityJudgment resourceFreeGame = exactGame;
    std::get<ExtractionResult>(resourceFreeGame.result)
        .failureBound->primitiveGameTerms.front()
        .resourceSubstitution.clear();
    if (!checkSecurityJudgmentWellFormed(resourceFreeSchema, resourceFreeGame)
             .accepted()) {
      module.emitError()
          << "valid empty primitive-game resource schema was refused";
      return signalPassFailure();
    }

    ClosedBound exponentOne;
    exponentOne.quantity = resourceQuantity("x");
    ClosedQuantity affineReplacement = integerQuantity(1);
    affineReplacement.resourceTerms.push_back(
        {Rational::fromInteger(1), "y", 1});
    auto affineSpecialized = closedBoundSpecialize(
        exponentOne, {{"x", affineReplacement}}, "test.affine_specialize");
    ClosedBound expectedAffine;
    expectedAffine.quantity = affineReplacement;
    if (!affineSpecialized.accepted() ||
        *affineSpecialized.value != expectedAffine ||
        !checkClosedBoundWellFormed(*affineSpecialized.value).accepted()) {
      module.emitError()
          << "exponent-one specialization did not preserve an exact affine "
             "replacement";
      return signalPassFailure();
    }

    PrimitiveGameInstance mergeGame;
    mergeGame.ref = {"game", "game-revision"};
    auto makeGameTerm = [&](int64_t coefficient,
                            llvm::StringRef sourceResource) {
      PrimitiveGameTerm term;
      term.coefficient = Rational::fromInteger(coefficient);
      term.instance = mergeGame;
      term.resourceSubstitution.emplace("tau",
                                        resourceQuantity(sourceResource));
      return term;
    };
    ClosedBound collapsingGameTerms;
    collapsingGameTerms.primitiveGameTerms.push_back(makeGameTerm(2, "x"));
    collapsingGameTerms.primitiveGameTerms.push_back(makeGameTerm(3, "y"));
    if (!checkClosedBoundWellFormed(collapsingGameTerms).accepted()) {
      module.emitError()
          << "pre-specialization game terms were not distinct and canonical";
      return signalPassFailure();
    }
    auto mergedSpecialization = closedBoundSpecialize(
        collapsingGameTerms,
        {{"x", integerQuantity(1)}, {"y", integerQuantity(1)}},
        "test.merged_game_specialize");
    if (!mergedSpecialization.accepted() ||
        mergedSpecialization.value->primitiveGameTerms.size() != 1 ||
        mergedSpecialization.value->primitiveGameTerms.front()
                .coefficient.compare(Rational::fromInteger(5)) != 0 ||
        !checkClosedBoundWellFormed(*mergedSpecialization.value).accepted()) {
      module.emitError()
          << "specialization did not merge a collapsed primitive-game key";
      return signalPassFailure();
    }

    auto added = closedBoundAdd(*mergedSpecialization.value, ClosedBound{},
                                "test.bound_add");
    auto scaled = closedBoundScale(
        integerQuantity(2), *mergedSpecialization.value, "test.bound_scale");
    ClosedBound one;
    one.quantity = integerQuantity(1);
    ClosedBound two;
    two.quantity = integerQuantity(2);
    auto maximum = closedBoundMaximum({one, two}, "test.bound_maximum");
    for (const auto *operation : {&added, &scaled, &maximum})
      if (!operation->accepted() ||
          !checkClosedBoundWellFormed(*operation->value).accepted()) {
        module.emitError()
            << "a public closed-bound operation returned a noncanonical value";
        return signalPassFailure();
      }

    ClosedBound linearCandidate;
    linearCandidate.quantity = resourceQuantity("x");
    ClosedBound quadraticCeiling;
    quadraticCeiling.quantity = resourceQuantity("x", 1, 2);
    ClosedBoundComparisonResult incomparable =
        closedBoundLeq(linearCandidate, quadraticCeiling, "test.bound_leq");
    if (!incomparable.accepted() || *incomparable.value) {
      module.emitError()
          << "closed-bound comparison was not exact coefficientwise "
             "domination";
      return signalPassFailure();
    }

    // The comparison's edges, pinned directly. x against x^2 above is
    // already the deliberate conservatism — valuationwise true for
    // x >= 1, coefficientwise refused because the exponents are
    // different keys. The remaining edges: incomparability is a
    // negative answer in both directions and never a refusal, and a
    // game term's identity is its instance AND its resource
    // substitution, so the same game at a different substitution
    // dominates nothing.
    {
      ClosedBound overX;
      overX.quantity = resourceQuantity("x");
      ClosedBound overY;
      overY.quantity = resourceQuantity("y");
      auto forward = closedBoundLeq(overX, overY, "test.leq.incomparable");
      auto backward = closedBoundLeq(overY, overX, "test.leq.incomparable");
      if (!forward.accepted() || *forward.value || !backward.accepted() ||
          *backward.value) {
        module.emitError() << "incomparable bounds did not answer no in "
                              "both directions";
        return signalPassFailure();
      }

      auto gameTerm = [&](int64_t numerator, int64_t denominator,
                          const ClosedQuantity &tau) {
        PrimitiveGameTerm term;
        term.coefficient = fraction(numerator, denominator);
        term.instance.ref = {"game", "game-revision"};
        term.resourceSubstitution.emplace("tau", tau);
        return term;
      };
      ClosedBound halfAdvantage;
      halfAdvantage.primitiveGameTerms.push_back(
          gameTerm(1, 2, resourceQuantity("t")));
      ClosedBound fullAdvantage;
      fullAdvantage.primitiveGameTerms.push_back(
          gameTerm(1, 1, resourceQuantity("t")));
      auto dominated =
          closedBoundLeq(halfAdvantage, fullAdvantage, "test.leq.game");
      if (!dominated.accepted() || !*dominated.value) {
        module.emitError() << "a half-coefficient game term was not "
                              "dominated by the full one";
        return signalPassFailure();
      }
      ClosedBound otherSubstitution;
      otherSubstitution.primitiveGameTerms.push_back(
          gameTerm(1, 1, resourceQuantity("t", 1, 2)));
      auto distinct = closedBoundLeq(halfAdvantage, otherSubstitution,
                                     "test.leq.game_substitution");
      if (!distinct.accepted() || *distinct.value) {
        module.emitError() << "a game term was dominated across a different "
                              "resource substitution";
        return signalPassFailure();
      }
    }

    // Scaling's edges. A ground zero deletes the game support — the
    // scaled bound must not remember games at coefficient zero, since
    // an addend priced away has to vanish rather than linger. A
    // symbolic scale over anything but a ground quantity would mint a
    // resource-times-advantage or resource-times-resource product,
    // which the v0 normal form deliberately lacks; over a ground
    // quantity it is polynomial multiplication.
    {
      ClosedBound priced;
      priced.quantity = integerQuantity(5);
      PrimitiveGameTerm term;
      term.coefficient = Rational::fromInteger(1);
      term.instance.ref = {"game", "game-revision"};
      term.resourceSubstitution.emplace("tau", integerQuantity(1));
      priced.primitiveGameTerms.push_back(term);

      auto zeroed =
          closedBoundScale(integerQuantity(0), priced, "test.scale.zero");
      if (!zeroed.accepted() || !zeroed.value->primitiveGameTerms.empty() ||
          !zeroed.value->quantity.constant.isZero()) {
        module.emitError()
            << "scaling by zero left game support or a nonzero quantity";
        return signalPassFailure();
      }

      auto symbolicOverGame = closedBoundScale(resourceQuantity("t"), priced,
                                               "test.scale.symbolic_game");
      ClosedBound overS;
      overS.quantity = resourceQuantity("s");
      auto symbolicOverResource = closedBoundScale(
          resourceQuantity("t"), overS, "test.scale.symbolic_resource");
      for (const auto *refused : {&symbolicOverGame, &symbolicOverResource})
        if (refused->accepted() ||
            refused->refusal->code !=
                RuntimeRefusalCode::UnsupportedNormalForm) {
          module.emitError() << "a symbolic scale left the v0 normal form "
                                "without refusing";
          return signalPassFailure();
        }

      ClosedBound groundThree;
      groundThree.quantity = integerQuantity(3);
      auto polynomial = closedBoundScale(resourceQuantity("t"), groundThree,
                                         "test.scale.polynomial");
      if (!polynomial.accepted() ||
          polynomial.value->quantity != resourceQuantity("t", 3)) {
        module.emitError() << "a symbolic scale over a ground quantity did "
                              "not multiply exactly";
        return signalPassFailure();
      }
    }

    // Max is admitted only over ground statistical quantities — a
    // symbolic operand refuses rather than guessing a valuation.
    {
      ClosedBound symbolic;
      symbolic.quantity = resourceQuantity("t");
      auto refused =
          closedBoundMaximum({symbolic}, "test.maximum.symbolic");
      if (refused.accepted() ||
          refused.refusal->code != RuntimeRefusalCode::UnsupportedNormalForm) {
        module.emitError()
            << "a symbolic maximum did not refuse the v0 normal form";
        return signalPassFailure();
      }
    }

    // Specialization reaches both carriers: the quantity's monomials
    // and the game terms' resource substitutions close under the same
    // assignment, or the judgment would quantify over a resource its
    // own game support still names.
    {
      ClosedBound symbolic;
      symbolic.quantity = resourceQuantity("t", 1, 2);
      PrimitiveGameTerm term;
      term.coefficient = Rational::fromInteger(1);
      term.instance.ref = {"game", "game-revision"};
      term.resourceSubstitution.emplace("tau", resourceQuantity("t"));
      symbolic.primitiveGameTerms.push_back(term);
      std::map<std::string, ClosedQuantity, std::less<>> at;
      at.emplace("t", integerQuantity(3));
      auto closed = closedBoundSpecialize(symbolic, at, "test.specialize");
      if (!closed.accepted() ||
          closed.value->quantity != integerQuantity(9) ||
          closed.value->primitiveGameTerms.size() != 1 ||
          closed.value->primitiveGameTerms.front()
                  .resourceSubstitution.at("tau") != integerQuantity(3)) {
        module.emitError() << "specialization did not close the quantity "
                              "and the game substitution together";
        return signalPassFailure();
      }
    }

    llvm::outs() << "closed-bound algebra edges: exact\n";
    llvm::outs() << "soundness runtime safety: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestSoundnessRuntimePass() {
  PassRegistration<TestSoundnessRuntimePass>();
}
} // namespace zkc::test
