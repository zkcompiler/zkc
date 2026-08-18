//===- TestCompilerCore.cpp - compiler judgment tests ----------*- C++ -*-===//

#include "Compiler/CompilerCoreInternal.h"
#include "SoundnessAdapterTestUtils.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Compiler/CompilerCore.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "zkc/Soundness/SignatureFile.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

namespace cmp = zkc::compiler;
namespace snd = zkc::soundness;

struct FixtureAdapterPayload {
  std::string sourceKind;
  cmp::AuthenticatedArtifactObservation observation;
};

struct FakeTransformPayload {
  uint64_t stage = 0;
  cmp::AuthenticatedArtifactObservation observation;
};

constexpr const char *kSumcheckRule = "zkc.rbr.sumcheck";
constexpr const char *kSrRule = "zkc.sr.from_rbr_knowledge";
constexpr const char *kFsRule = "zkc.fs.duplex_knowledge";
constexpr const char *kSumcheckBinding = "zkc.rbr.sumcheck@reduction:sumcheck";
constexpr const char *kSrBinding = "zkc.sr.from_rbr_knowledge@path:"
                                   "rbr_to_sr:knowledge:straightline";
constexpr const char *kFsBinding = "zkc.fs.duplex_knowledge@path:"
                                   "sr_to_fs_duplex:knowledge:straightline";

snd::SecuritySubject protocolSubject(const snd::SealedSoundnessView &view,
                                     const snd::ClaimRef &claim) {
  snd::SecuritySubject subject;
  subject.payload = snd::ProtocolClaimSubject{view.artifactId, claim};
  return subject;
}

template <typename T> llvm::Expected<T> testError(const llvm::Twine &message) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), message);
}

struct AuthenticationFailureControl {
  bool armed = false;
  uint64_t successfulAuthenticationsBeforeFailure = 0;
};

template <typename Payload>
class FixtureArtifactSemantics final : public cmp::ArtifactSemantics {
public:
  FixtureArtifactSemantics(
      snd::ExactRef ref, snd::ExactRef payloadTypeRef,
      std::shared_ptr<AuthenticationFailureControl> failureControl = nullptr)
      : ref_(std::move(ref)), payloadTypeRef_(std::move(payloadTypeRef)),
        failureControl_(std::move(failureControl)) {}

  const snd::ExactRef &exactRef() const override { return ref_; }
  const snd::ExactRef &payloadTypeRef() const override {
    return payloadTypeRef_;
  }
  llvm::Expected<cmp::AuthenticatedArtifactObservation>
  authenticate(const cmp::ArtifactPayload &payload) const override {
    const auto *typed = cmp::artifactPayloadAs<Payload>(payload);
    if (!typed)
      return testError<cmp::AuthenticatedArtifactObservation>(
          "fixture semantics received the wrong immutable payload type");
    if (failureControl_ && failureControl_->armed) {
      if (failureControl_->successfulAuthenticationsBeforeFailure == 0)
        return testError<cmp::AuthenticatedArtifactObservation>(
            "fixture late authentication failure");
      --failureControl_->successfulAuthenticationsBeforeFailure;
    }
    return typed->observation;
  }

private:
  snd::ExactRef ref_;
  snd::ExactRef payloadTypeRef_;
  std::shared_ptr<AuthenticationFailureControl> failureControl_;
};

/// Arms an artifact-semantics failure after the closed domain has enumerated
/// its final schema. This leaves DOMAIN intact, lets the first candidate pass,
/// and makes the next candidate encounter a real provider error.
class ArmAfterSchemaDerivationProvider final
    : public cmp::DerivationPlanDomainProvider {
public:
  ArmAfterSchemaDerivationProvider(
      std::shared_ptr<const cmp::DerivationPlanDomainProvider> delegate,
      std::string schemaKey,
      std::shared_ptr<AuthenticationFailureControl> failureControl)
      : delegate_(std::move(delegate)), schemaKey_(std::move(schemaKey)),
        failureControl_(std::move(failureControl)) {}

  const snd::ExactRef &exactRef() const override {
    return delegate_->exactRef();
  }

  llvm::Expected<std::vector<snd::DerivationPlan>>
  enumerate(const cmp::CompilerRequest &request,
            const cmp::AuthenticatedCompilerArtifact &artifact,
            const cmp::RequestedTarget &target, const cmp::TargetSchema &schema,
            const snd::SecuritySubject &subject) const override {
    auto plans =
        delegate_->enumerate(request, artifact, target, schema, subject);
    if (plans && schema.key == schemaKey_) {
      failureControl_->successfulAuthenticationsBeforeFailure = 1;
      failureControl_->armed = true;
    }
    return plans;
  }

  llvm::Expected<bool>
  contains(const cmp::CompilerRequest &request,
           const cmp::AuthenticatedCompilerArtifact &artifact,
           const cmp::RequestedTarget &target, const cmp::TargetSchema &schema,
           const snd::SecuritySubject &subject,
           const snd::DerivationPlan &plan) const override {
    return delegate_->contains(request, artifact, target, schema, subject,
                               plan);
  }

private:
  std::shared_ptr<const cmp::DerivationPlanDomainProvider> delegate_;
  std::string schemaKey_;
  std::shared_ptr<AuthenticationFailureControl> failureControl_;
};

snd::ClaimRef fakeClaim(uint64_t index, llvm::StringRef digest) {
  return snd::ClaimRef{index, digest.str()};
}

snd::ClosedQuantity constantQuantity(int64_t value) {
  snd::ClosedQuantity result;
  result.constant = zkc::registry::Rational::fromInteger(value);
  return result;
}

cmp::ResourceSubstitution
identitySubstitution(const std::vector<snd::TypedDeclaration> &resources) {
  cmp::ResourceSubstitution result;
  for (const snd::TypedDeclaration &resource : resources) {
    snd::ClosedQuantity value;
    value.resourceTerms.push_back(
        {zkc::registry::Rational::fromInteger(1), resource.name, 1});
    result.emplace(resource.name, std::move(value));
  }
  return result;
}

cmp::BoundExpr candidateRead(std::string targetKey,
                             cmp::TargetMemberSelector members,
                             cmp::BoundProjection projection,
                             cmp::SchemaResourceSubstitutions substitutions) {
  cmp::BoundExpr result;
  result.payload =
      cmp::CandidateTargetRead{std::move(targetKey), std::move(members),
                               std::move(projection), std::move(substitutions)};
  return result;
}

cmp::BoundExpr zeroBound() {
  cmp::BoundExpr result;
  result.payload = cmp::ZeroBound{};
  return result;
}

cmp::BoundExpr sourceProjection(snd::DerivationTarget target,
                                snd::DerivationPlan plan,
                                cmp::BoundProjection projection,
                                cmp::ResourceSubstitution substitution,
                                cmp::SourceMemberOf relation) {
  cmp::BoundExpr result;
  result.payload = cmp::SourceProjection{
      std::move(target), std::move(plan), std::move(projection),
      std::move(substitution), std::move(relation)};
  return result;
}

cmp::BoundExprPtr boundPtr(cmp::BoundExpr expression) {
  return std::make_shared<const cmp::BoundExpr>(std::move(expression));
}

cmp::BoundExpr addBounds(std::vector<cmp::BoundExpr> operands) {
  cmp::AddBounds add;
  for (cmp::BoundExpr &operand : operands)
    add.operands.push_back(boundPtr(std::move(operand)));
  cmp::BoundExpr result;
  result.payload = std::move(add);
  return result;
}

cmp::BoundExpr maxBounds(std::vector<cmp::BoundExpr> operands) {
  cmp::MaxBounds maximum;
  for (cmp::BoundExpr &operand : operands)
    maximum.operands.push_back(boundPtr(std::move(operand)));
  cmp::BoundExpr result;
  result.payload = std::move(maximum);
  return result;
}

cmp::BoundExpr scaleBound(snd::ClosedQuantity scale, cmp::BoundExpr operand) {
  cmp::BoundExpr result;
  result.payload =
      cmp::ScaleBound{std::move(scale), boundPtr(std::move(operand))};
  return result;
}

bool fakeTransformPlansEqual(const cmp::TransformPlan &lhs,
                             const cmp::TransformPlan &rhs) {
  if (lhs.applications.size() != rhs.applications.size())
    return false;
  for (size_t index = 0; index < lhs.applications.size(); ++index) {
    const cmp::TransformApplication &left = lhs.applications[index];
    const cmp::TransformApplication &right = rhs.applications[index];
    if (left.familyRef != right.familyRef ||
        left.matchedClaims != right.matchedClaims ||
        left.parameters != right.parameters)
      return false;
  }
  return true;
}

class FakeTransformDomainProvider final : public cmp::TransformDomainProvider {
public:
  FakeTransformDomainProvider(snd::ExactRef ref,
                              snd::ExactRef artifactSemanticsRef,
                              cmp::TransformPlan plan)
      : ref_(std::move(ref)),
        artifactSemanticsRef_(std::move(artifactSemanticsRef)),
        plan_(std::move(plan)) {}

  const snd::ExactRef &exactRef() const override { return ref_; }
  const snd::ExactRef &artifactSemanticsRef() const override {
    return artifactSemanticsRef_;
  }
  llvm::Expected<std::vector<cmp::TransformPlan>>
  enumerate(const cmp::CompilerRequest &,
            const cmp::AuthenticatedCompilerArtifact &) const override {
    return std::vector<cmp::TransformPlan>{plan_};
  }
  llvm::Expected<bool> contains(const cmp::CompilerRequest &,
                                const cmp::AuthenticatedCompilerArtifact &,
                                const cmp::TransformPlan &plan) const override {
    return fakeTransformPlansEqual(plan_, plan);
  }

private:
  snd::ExactRef ref_;
  snd::ExactRef artifactSemanticsRef_;
  cmp::TransformPlan plan_;
};

class FakeTransformFamily final : public cmp::TransformFamily {
public:
  enum class Mode {
    Good,
    InvalidCheckerOutput,
    AmbiguousPrimary,
    // Claims a property LEGAL does not check. The transform is otherwise
    // identical to Good, which is the point being tested: a claim changes
    // the record and changes no verdict.
    ClaimsProperty,
    // Attributes its claim to a family and application that did not make it.
    MisattributedClaim,
  };

  FakeTransformFamily(
      snd::ExactRef ref, snd::ExactRef artifactSemanticsRef, Mode mode,
      std::optional<snd::ExactRef> realizedSemanticsRef = std::nullopt)
      : ref_(std::move(ref)),
        artifactSemanticsRef_(std::move(artifactSemanticsRef)),
        realizedSemanticsRef_(
            realizedSemanticsRef.value_or(artifactSemanticsRef_)),
        mode_(mode) {}

  const snd::ExactRef &exactRef() const override { return ref_; }
  const snd::ExactRef &artifactSemanticsRef() const override {
    return artifactSemanticsRef_;
  }

  std::vector<cmp::PreservationClaim>
  preservationClaims(cmp::AuthenticatedArtifactHandle before,
                     cmp::AuthenticatedArtifactHandle after,
                     const cmp::CanonicalTransformApplication &canonical,
                     uint64_t applicationIndex) const override {
    (void)before;
    (void)after;
    (void)canonical;
    // A fixture property. The vocabulary a real family draws from is not
    // decided here, so the test uses a name no program has to honour.
    if (mode_ == Mode::ClaimsProperty)
      return {{"fixture.property", ref_, applicationIndex}};
    if (mode_ == Mode::MisattributedClaim)
      return {{"fixture.property", snd::ExactRef{"zkc.family.elsewhere", "rev"},
               applicationIndex}};
    return {};
  }

  llvm::Expected<cmp::CanonicalTransformApplication>
  recognize(cmp::AuthenticatedArtifactHandle before,
            const cmp::TransformApplication &requested) const override {
    if (!before || !before->artifact || !before->artifact->adapterPayload)
      return testError<cmp::CanonicalTransformApplication>(
          "fake transform has no predecessor payload");
    const auto *payload = cmp::artifactPayloadAs<FakeTransformPayload>(
        *before->artifact->adapterPayload);
    if (!payload || payload->stage > 1 || requested.familyRef != ref_)
      return testError<cmp::CanonicalTransformApplication>(
          "fake transform saw the wrong actual predecessor");
    std::vector<snd::ClaimRef> expected =
        payload->stage == 0
            ? std::vector<snd::ClaimRef>{fakeClaim(0, "source-a"),
                                         fakeClaim(1, "source-b")}
            : std::vector<snd::ClaimRef>{fakeClaim(0, "merged")};
    if (requested.matchedClaims != expected || !requested.parameters.empty())
      return testError<cmp::CanonicalTransformApplication>(
          "fake transform match is not canonical for this predecessor");
    return cmp::CanonicalTransformApplication{ref_, expected, {}};
  }

  llvm::Expected<cmp::ArtifactHandle>
  realize(cmp::AuthenticatedArtifactHandle before,
          const cmp::CanonicalTransformApplication &canonical) const override {
    if (!before || !before->artifact || !before->artifact->adapterPayload)
      return testError<cmp::ArtifactHandle>(
          "fake transform has no predecessor payload");
    const auto *payload = cmp::artifactPayloadAs<FakeTransformPayload>(
        *before->artifact->adapterPayload);
    if (!payload || payload->stage > 1 || canonical.familyRef != ref_)
      return testError<cmp::ArtifactHandle>(
          "fake transform cannot realize this predecessor");

    snd::SealedSoundnessView view = before->observation.soundness;
    view.reductionsByTransformerPosition.clear();
    if (payload->stage == 0) {
      view.artifactId = "compiler.fake.stage1";
      view.claimsByIndex = {fakeClaim(0, "merged"), fakeClaim(1, "survivor-1")};
    } else {
      view.artifactId = "compiler.fake.stage2";
      view.claimsByIndex = {fakeClaim(0, "finished"),
                            fakeClaim(1, "survivor-2")};
    }
    const std::string artifactId = view.artifactId;
    cmp::AuthenticatedArtifactObservation observation{
        artifactId, view, before->observation.verifierProofReads};
    auto typedPayload = cmp::makeArtifactPayload(
        snd::ExactRef{"compiler.fake.payload", "compiler-v0"},
        FakeTransformPayload{payload->stage + 1, std::move(observation)});
    return std::make_shared<const cmp::OwnedCompilerArtifact>(
        realizedSemanticsRef_, std::move(typedPayload));
  }

  llvm::Expected<std::vector<cmp::ClaimCorrespondence>>
  check(cmp::AuthenticatedArtifactHandle before,
        cmp::AuthenticatedArtifactHandle after,
        const cmp::CanonicalTransformApplication &canonical,
        uint64_t applicationIndex) const override {
    if (!before || !after || !before->artifact || !after->artifact ||
        !before->artifact->adapterPayload || !after->artifact->adapterPayload)
      return testError<std::vector<cmp::ClaimCorrespondence>>(
          "fake checker has no owned stage pair");
    const auto *source = cmp::artifactPayloadAs<FakeTransformPayload>(
        *before->artifact->adapterPayload);
    const auto *target = cmp::artifactPayloadAs<FakeTransformPayload>(
        *after->artifact->adapterPayload);
    if (!source || !target || target->stage != source->stage + 1 ||
        applicationIndex != source->stage || canonical.familyRef != ref_)
      return testError<std::vector<cmp::ClaimCorrespondence>>(
          "fake checker did not receive the actual adjacent stage pair");

    cmp::ClaimCorrespondence primary;
    primary.applicationIndex = applicationIndex;
    primary.familyRef = ref_;
    primary.orderedConsumed = canonical.orderedConsumed;
    cmp::ClaimCorrespondence survivor;
    survivor.applicationIndex = applicationIndex;
    survivor.familyRef = ref_;
    if (source->stage == 0) {
      primary.orderedProduced = {{mode_ == Mode::InvalidCheckerOutput
                                      ? fakeClaim(0, "not-the-real-output")
                                      : fakeClaim(0, "merged"),
                                  "merged"}};
      survivor.orderedConsumed = {fakeClaim(2, "source-survivor")};
      survivor.orderedProduced = {{fakeClaim(1, "survivor-1"), "survivor"}};
    } else {
      primary.orderedProduced = {{fakeClaim(0, "finished"), "finished"}};
      survivor.orderedConsumed = {fakeClaim(1, "survivor-1")};
      survivor.orderedProduced = {{fakeClaim(1, "survivor-2"), "survivor"}};
    }
    std::vector<cmp::ClaimCorrespondence> result{primary, survivor};
    if (mode_ == Mode::AmbiguousPrimary)
      result.push_back(primary);
    return result;
  }

private:
  snd::ExactRef ref_;
  snd::ExactRef artifactSemanticsRef_;
  snd::ExactRef realizedSemanticsRef_;
  Mode mode_;
};

void collectEvaluatedPropositions(
    const snd::EvaluatedDerivation &derivation,
    std::vector<snd::PropositionInstance> &propositions) {
  const snd::SecurityJudgment *conclusion = nullptr;
  if (const auto *assumption =
          std::get_if<snd::EvaluatedAssumption>(&derivation.node)) {
    conclusion = &assumption->conclusion;
  } else {
    const auto &application =
        std::get<snd::EvaluatedApplication>(derivation.node);
    conclusion = &application.conclusion;
    for (const auto &[port, premise] : application.premises) {
      (void)port;
      if (premise)
        collectEvaluatedPropositions(*premise, propositions);
    }
  }
  for (const snd::Hypothesis &hypothesis : conclusion->hypotheses)
    if (const auto *proposition =
            std::get_if<snd::PropositionInstance>(&hypothesis);
        proposition && std::find(propositions.begin(), propositions.end(),
                                 *proposition) == propositions.end())
      propositions.push_back(*proposition);
}

struct TestCompilerCorePass
    : public PassWrapper<TestCompilerCorePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestCompilerCorePass)

  TestCompilerCorePass() = default;
  TestCompilerCorePass(const TestCompilerCorePass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override { return "test-compiler-core"; }
  StringRef getDescription() const override {
    return "test compiler judgments, checked compilation, and decision "
           "checking";
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
    auto expectError = [&](auto value, llvm::StringRef label) {
      if (value) {
        fail(label + " unexpectedly accepted");
        return false;
      }
      llvm::consumeError(value.takeError());
      return true;
    };

    auto sealedOps = module.getOps<zkc::pir::SealedOp>();
    if (!llvm::hasSingleElement(sealedOps))
      return fail("compiler-core test expects one sealed artifact");
    zkc::pir::SealedOp sealed = *sealedOps.begin();

    auto vocabulary =
        zkc::registry::ProtocolVocabulary::loadFromFile(protocolVocabularyPath);
    if (!vocabulary)
      return fail(llvm::toString(vocabulary.takeError()));
    auto profiles = zkc::registry::ConstructionProfileRegistry::loadFromFile(
        constructionProfileRegistryPath);
    if (!profiles)
      return fail(llvm::toString(profiles.takeError()));

    auto admitted = zkc::test::admitSoundnessFixture(
        sealed, protocolVocabularyPath, constructionProfileRegistryPath);
    if (!admitted)
      return fail(llvm::toString(admitted.takeError()));
    auto view = snd::buildSealedSoundnessView(*admitted);
    if (!view)
      return fail(llvm::toString(view.takeError()));
    auto signature = snd::loadSignatureFromFile(signaturePath);
    if (!signature)
      return fail(llvm::toString(signature.takeError()));
    const snd::SoundnessCatalog *catalog = &signature->catalog;

    auto nativeRuleIt = catalog->rules.find(kSumcheckRule);
    auto srRuleIt = catalog->rules.find(kSrRule);
    auto fsRuleIt = catalog->rules.find(kFsRule);
    auto nativeBindingIt = catalog->bindings.find(kSumcheckBinding);
    auto srBindingIt = catalog->bindings.find(kSrBinding);
    auto fsBindingIt = catalog->bindings.find(kFsBinding);
    if (nativeRuleIt == catalog->rules.end() ||
        srRuleIt == catalog->rules.end() || fsRuleIt == catalog->rules.end() ||
        nativeBindingIt == catalog->bindings.end() ||
        srBindingIt == catalog->bindings.end() ||
        fsBindingIt == catalog->bindings.end())
      return fail("compiler-core fixture lacks the selected soundness chain");
    const snd::SoundnessRule &nativeRule = nativeRuleIt->second;
    const snd::SoundnessRule &fsRule = fsRuleIt->second;
    const snd::RuleBinding &nativeBinding = nativeBindingIt->second;
    const snd::RuleBinding &srBinding = srBindingIt->second;
    const snd::RuleBinding &fsBinding = fsBindingIt->second;
    // The sumcheck entry's field order and class are caller-supplied: the
    // artifact authenticates the payload class and the per-round challenge
    // space, not the order the theorem is stated over.
    snd::ResolvedParameterEnvironment fieldParameters;
    fieldParameters.bindingRef = nativeBinding.ref;
    fieldParameters.values.emplace(
        "field_order",
        snd::RuntimeValue::integer(llvm::cantFail(
            zkc::registry::Rational::fromDecimal("2305843009213697249"))));
    fieldParameters.values.emplace("field_class",
                                   snd::RuntimeValue::text("scalar"));
    snd::ResolvedParameterEnvironments resolvedParameters;
    resolvedParameters.emplace(nativeBinding.ref.id,
                               std::move(fieldParameters));
    snd::SoundnessContextOutcome soundnessContextOutcome =
        snd::buildSoundnessContext(*catalog,
                                   std::vector<snd::ExactRef>{nativeBinding.ref,
                                                              srBinding.ref,
                                                              fsBinding.ref},
                                   std::move(resolvedParameters));
    if (!soundnessContextOutcome.accepted())
      return fail("compiler fixture soundness context is ill-formed: " +
                  (soundnessContextOutcome.refusal
                       ? soundnessContextOutcome.refusal->detail
                       : "missing checked context"));
    auto soundnessContext = std::make_shared<const snd::SoundnessContext>(
        std::move(*soundnessContextOutcome.context));

    if (view->reductionsByTransformerPosition.size() != 1)
      return fail("compiler fixture must contain one reduction");
    const auto &[transformerPosition, reduction] =
        *view->reductionsByTransformerPosition.begin();
    if (reduction.orderedOutputs.size() != 1)
      return fail("compiler fixture reduction must contain one output");
    const snd::ClaimRef owner = reduction.orderedOutputs.front();
    snd::SecuritySubject subject = protocolSubject(*view, owner);
    snd::ApplicationSite nativeSite = snd::ReductionOccurrence{
        view->artifactId, owner, transformerPosition, 0};
    snd::ApplicationSite srSite = snd::PathOccurrence{view->artifactId, owner};
    snd::ApplicationSite fsSite = snd::PathOccurrence{view->artifactId, owner};
    auto nativePlan = std::make_shared<snd::DerivationPlan>();
    nativePlan->node =
        snd::ApplyDerivationPlan{nativeSite, nativeBinding.ref, {}};
    auto srPlan = std::make_shared<snd::DerivationPlan>();
    snd::ApplyDerivationPlan srApplication{srSite, srBinding.ref, {}};
    srApplication.premises.emplace("source_rbr", nativePlan);
    srPlan->node = std::move(srApplication);
    snd::DerivationPlan derivation;
    snd::ApplyDerivationPlan fsApplication{fsSite, fsBinding.ref, {}};
    fsApplication.premises.emplace("source_sr", srPlan);
    derivation.node = std::move(fsApplication);

    snd::DerivationTarget derivationTarget{
        subject, fsRule.conclusionIndex.index, fsRule.resources};
    snd::DeriveOutcome expected = snd::deriveSoundness(
        *soundnessContext, *view, derivationTarget, derivation);
    if (!expected.accepted())
      return fail("compiler fixture DERIVE refused: " +
                  expected.refusal->detail);
    const auto *expectedApplication =
        std::get_if<snd::EvaluatedApplication>(&expected.result->root.node);
    if (!expectedApplication)
      return fail("compiler fixture expected an applied scalar root");
    const auto *expectedScalar =
        std::get_if<snd::ScalarResult>(&expectedApplication->conclusion.result);
    if (!expectedScalar)
      return fail("compiler fixture expected a scalar target");

    snd::ExactRef codecRef{"test.codec.fixed8", "test-rev-1"};
    snd::ExactRef fixturePayloadTypeRef{"compiler.fixture.payload",
                                        "compiler-v0"};
    snd::ExactRef fixtureSemanticsRef{"compiler.fixture.semantics",
                                      "compiler-v0"};
    std::vector<cmp::VerifierProofRead> fixtureReads{
        {"proof.round-message", codecRef, 2}};
    cmp::AuthenticatedArtifactObservation fixtureObservation{
        view->artifactId, *view, fixtureReads};
    auto adapterPayload = cmp::makeArtifactPayload(
        fixturePayloadTypeRef,
        FixtureAdapterPayload{"sealed-pir-test-fixture",
                              std::move(fixtureObservation)});
    auto artifact = std::make_shared<const cmp::OwnedCompilerArtifact>(
        fixtureSemanticsRef, std::move(adapterPayload));

    snd::ExactRef transformProviderRef{"compiler.transform.identity",
                                       "compiler-v0"};
    snd::ExactRef derivationProviderRef{"compiler.derivation.listed",
                                        "compiler-v0"};
    snd::ExactRef widthProfileRef{"compiler.codec-width.fixture",
                                  "compiler-v0"};

    cmp::CompilerRequest request;
    request.source = artifact;
    request.transformDomainProviderRef = transformProviderRef;
    request.derivationPlanProviderRef = derivationProviderRef;
    cmp::RequestedTarget target;
    target.key = "final-fs";
    target.orderedSourceClaims = {owner};
    target.admittedSchemaKeys = {"fs-a", "fs-b"};
    request.targets.push_back(target);
    request.targetSchemas.push_back(
        {"fs-a", fsRule.conclusionIndex.index, fsRule.resources});
    request.targetSchemas.push_back(
        {"fs-b", fsRule.conclusionIndex.index, fsRule.resources});
    request.derivationSurface.allowedBindingRefs = {
        nativeBinding.ref, srBinding.ref, fsBinding.ref};
    for (const snd::Hypothesis &hypothesis :
         expectedApplication->conclusion.hypotheses)
      if (const auto *proposition =
              std::get_if<snd::PropositionInstance>(&hypothesis))
        request.derivationSurface.allowedHypotheses.push_back(*proposition);
    request.derivationSurface.allowedPrimitiveGames =
        snd::gameSupport(expectedApplication->conclusion.result);
    cmp::SchemaResourceSubstitutions fsSubstitutions;
    fsSubstitutions.emplace("fs-a", identitySubstitution(fsRule.resources));
    fsSubstitutions.emplace("fs-b", identitySubstitution(fsRule.resources));
    request.soundnessConstraints.push_back(
        {cmp::ComparisonDomain{fsRule.resources},
         candidateRead("final-fs", cmp::ExactTargetMember{0},
                       {cmp::BoundProjectionKind::Scalar, {}}, fsSubstitutions),
         zeroBound(), expectedScalar->bound});
    request.objectives.push_back(
        {"proof-bytes", cmp::ObjectiveKind::StaticProofBytes,
         cmp::ObjectiveDirection::Minimize, widthProfileRef});

    auto transformProvider =
        std::make_shared<const cmp::IdentityTransformDomainProvider>(
            transformProviderRef, fixtureSemanticsRef);
    std::vector<cmp::ListedDerivationAlternative> alternatives{
        {"final-fs", "fs-a", subject, derivation},
        {"final-fs", "fs-b", subject, derivation},
    };
    auto derivationProvider =
        std::make_shared<const cmp::ListedDerivationPlanDomainProvider>(
            derivationProviderRef, std::move(alternatives));
    cmp::CompilerSemanticContext context;
    context.soundnessContext = soundnessContext;
    context.artifactSemantics.emplace(
        fixtureSemanticsRef.id,
        std::make_shared<const FixtureArtifactSemantics<FixtureAdapterPayload>>(
            fixtureSemanticsRef, fixturePayloadTypeRef));
    context.transformDomains.emplace(transformProviderRef.id,
                                     transformProvider);
    context.derivationDomains.emplace(derivationProviderRef.id,
                                      derivationProvider);
    cmp::CodecWidthProfile widthProfile;
    widthProfile.ref = widthProfileRef;
    widthProfile.codecs.emplace(
        codecRef.id,
        cmp::CodecWidth{codecRef, zkc::registry::Rational::fromInteger(8)});
    context.codecWidthProfiles.emplace(widthProfileRef.id, widthProfile);

    auto planDomain = cmp::domain(context, request);
    if (!planDomain)
      return fail(llvm::toString(planDomain.takeError()));
    if (planDomain->scope != cmp::ComparisonScopeKind::ClosedDomain ||
        planDomain->plans.size() != 2)
      return fail("closed DOMAIN did not preserve two schema alternatives");
    llvm::outs() << "compiler domain: 2 canonical alternatives\n";

    for (uint64_t ordinal = 0; ordinal < planDomain->plans.size(); ++ordinal) {
      auto valid = cmp::validate(context, request, *planDomain, ordinal);
      if (!valid)
        return fail(llvm::toString(valid.takeError()));
      if (valid->candidate.derivations.size() != 1)
        return fail("VALID did not retain the exact DERIVE result");
      auto value = cmp::score(context, request, *planDomain, ordinal);
      if (!value)
        return fail(llvm::toString(value.takeError()));
      if (value->objectiveValues.size() != 1 ||
          value->objectiveValues.front().compare(
              zkc::registry::Rational::fromInteger(16)) != 0)
        return fail("SCORE did not use exact static proof-byte arithmetic");
    }
    llvm::outs() << "compiler derive: shared DERIVE accepted\n";

    auto selection = cmp::select(context, request, *planDomain);
    if (!selection)
      return fail(llvm::toString(selection.takeError()));
    if (selection->selectedOrdinal != std::optional<uint64_t>(0))
      return fail("SELECT did not use canonical domain ordinal for a tie");
    llvm::outs() << "compiler select: ordinal tie-break exact\n";

    auto compiled = cmp::compile(context, request);
    if (!compiled)
      return fail(llvm::toString(compiled.takeError()));
    if (compiled->selectedOrdinal != selection->selectedOrdinal)
      return fail("checked compilation disagreed with canonical SELECT");
    auto verdict = cmp::checkDecision(context, request, *compiled);
    if (!verdict)
      return fail(llvm::toString(verdict.takeError()));
    if (!verdict->accepted)
      return fail("decision checker rejected exact recomputation: " +
                  verdict->detail);
    cmp::CompilerResult wrong = *compiled;
    wrong.selectedOrdinal = 1;
    auto wrongVerdict = cmp::checkDecision(context, request, wrong);
    if (!wrongVerdict)
      return fail(llvm::toString(wrongVerdict.takeError()));
    if (wrongVerdict->accepted)
      return fail("decision checker accepted the wrong selected ordinal");

    cmp::CompilerRequest mixedEligibility = request;
    auto &mixedRead = std::get<cmp::CandidateTargetRead>(
        mixedEligibility.soundnessConstraints.front().candidate.payload);
    cmp::ResourceSubstitution doubled = identitySubstitution(fsRule.resources);
    for (auto &[name, quantity] : doubled) {
      (void)name;
      for (snd::ResourceMonomial &term : quantity.resourceTerms)
        term.coefficient = zkc::registry::Rational::fromInteger(2);
    }
    mixedRead.resourceSubstitutions.at("fs-a") = std::move(doubled);
    auto mixedDomain = cmp::domain(context, mixedEligibility);
    if (!mixedDomain)
      return fail(llvm::toString(mixedDomain.takeError()));
    if (mixedDomain->plans.size() != 2)
      return fail("mixed eligibility changed the canonical domain");
    if (!expectError(cmp::validate(context, mixedEligibility, *mixedDomain, 0),
                     "first mixed candidate loss"))
      return;
    auto mixedSecond =
        cmp::validate(context, mixedEligibility, *mixedDomain, 1);
    if (!mixedSecond)
      return fail(llvm::toString(mixedSecond.takeError()));
    auto mixedCompiled = cmp::compile(context, mixedEligibility);
    if (!mixedCompiled)
      return fail(llvm::toString(mixedCompiled.takeError()));
    if (mixedCompiled->selectedOrdinal != std::optional<uint64_t>(1))
      return fail("compiler did not skip the first ineligible candidate");

    auto staleVerdict =
        cmp::checkDecision(context, mixedEligibility, *compiled);
    if (!staleVerdict)
      return fail(llvm::toString(staleVerdict.takeError()));
    if (staleVerdict->accepted)
      return fail("decision checker reused the producer's prior selection");
    auto mixedVerdict =
        cmp::checkDecision(context, mixedEligibility, *mixedCompiled);
    if (!mixedVerdict)
      return fail(llvm::toString(mixedVerdict.takeError()));
    if (!mixedVerdict->accepted)
      return fail("decision checker rejected recomputed mixed selection: " +
                  mixedVerdict->detail);
    llvm::outs() << "compiler check decision: full selection recomputed\n";

    snd::DerivationPlan refusedDerivation;
    refusedDerivation.node =
        snd::ExternalJudgmentAssumption{expectedApplication->conclusion};
    cmp::CompilerSemanticContext semanticRefusal = context;
    semanticRefusal.derivationDomains.at(derivationProviderRef.id) =
        std::make_shared<const cmp::ListedDerivationPlanDomainProvider>(
            derivationProviderRef,
            std::vector<cmp::ListedDerivationAlternative>{
                {"final-fs", "fs-a", subject, derivation},
                {"final-fs", "fs-b", subject, std::move(refusedDerivation)}});
    auto semanticRefusalCompilation = cmp::compile(semanticRefusal, request);
    if (!semanticRefusalCompilation)
      return fail(llvm::toString(semanticRefusalCompilation.takeError()));
    if (semanticRefusalCompilation->selectedOrdinal !=
        std::optional<uint64_t>(0))
      return fail("semantic DERIVE refusal was not candidate-local");

    auto lateFailureControl = std::make_shared<AuthenticationFailureControl>();
    cmp::CompilerSemanticContext lateFailure = context;
    lateFailure.artifactSemantics.at(fixtureSemanticsRef.id) =
        std::make_shared<const FixtureArtifactSemantics<FixtureAdapterPayload>>(
            fixtureSemanticsRef, fixturePayloadTypeRef, lateFailureControl);
    lateFailure.derivationDomains.at(derivationProviderRef.id) =
        std::make_shared<const ArmAfterSchemaDerivationProvider>(
            derivationProvider, "fs-b", lateFailureControl);
    auto lateFailureCompilation = cmp::compile(lateFailure, request);
    if (lateFailureCompilation)
      return fail("compiler swallowed a later artifact-semantics error");
    std::string lateFailureDetail =
        llvm::toString(lateFailureCompilation.takeError());
    if (!llvm::StringRef(lateFailureDetail)
             .contains("fixture late authentication failure"))
      return fail("compiler returned the wrong late operational failure: " +
                  lateFailureDetail);
    llvm::outs() << "compiler operational failure: late error propagated\n";

    cmp::PlanDomain forgedDomain = *planDomain;
    forgedDomain.plans.front().targets.clear();
    if (!expectError(cmp::realize(context, request, forgedDomain, 0),
                     "REALIZE forged domain") ||
        !expectError(cmp::validate(context, request, forgedDomain, 0),
                     "VALID forged domain") ||
        !expectError(cmp::score(context, request, forgedDomain, 0),
                     "SCORE forged domain") ||
        !expectError(cmp::select(context, request, forgedDomain),
                     "SELECT forged domain"))
      return;
    cmp::CompilerRequest noTargetRequest = request;
    noTargetRequest.targets.clear();
    noTargetRequest.targetSchemas.clear();
    noTargetRequest.soundnessConstraints.clear();
    auto noTargetDomain = cmp::domain(context, noTargetRequest);
    if (!noTargetDomain)
      return fail(llvm::toString(noTargetDomain.takeError()));
    if (!expectError(cmp::validate(context, request, *noTargetDomain, 0),
                     "cross-request DOMAIN substitution"))
      return;

    cmp::CompilerRequest submittedRequest = request;
    submittedRequest.comparisonScope =
        cmp::SubmittedFrontierScope{planDomain->plans};
    auto submittedDomain = cmp::domain(context, submittedRequest);
    if (!submittedDomain)
      return fail(llvm::toString(submittedDomain.takeError()));
    if (submittedDomain->scope != cmp::ComparisonScopeKind::SubmittedFrontier ||
        submittedDomain->plans.size() != 2)
      return fail("submitted DOMAIN changed the explicit frontier");
    llvm::outs() << "compiler submitted frontier: exact\n";

    cmp::CompilerRequest tightLoss = request;
    tightLoss.soundnessConstraints.front().ceiling = snd::ClosedBound();
    auto tightDomain = cmp::domain(context, tightLoss);
    if (!tightDomain)
      return fail(llvm::toString(tightDomain.takeError()));
    if (!expectError(cmp::validate(context, tightLoss, *tightDomain, 0),
                     "tight scalar loss ceiling"))
      return;
    auto tightCompilation = cmp::compile(context, tightLoss);
    if (!tightCompilation)
      return fail(llvm::toString(tightCompilation.takeError()));
    if (tightCompilation->selectedOrdinal)
      return fail("candidate loss rejection remained selectable");

    cmp::CompilerRequest unrepresentableMaximum = request;
    cmp::BoundExpr scalarCandidate =
        unrepresentableMaximum.soundnessConstraints.front().candidate;
    unrepresentableMaximum.soundnessConstraints.front().candidate =
        maxBounds({std::move(scalarCandidate)});
    auto unrepresentableCompilation =
        cmp::compile(context, unrepresentableMaximum);
    if (!unrepresentableCompilation)
      return fail(llvm::toString(unrepresentableCompilation.takeError()));
    if (unrepresentableCompilation->selectedOrdinal)
      return fail("unrepresentable exact maximum remained selectable");

    cmp::CompilerRequest partialSchema = request;
    auto &partialSchemaRead = std::get<cmp::CandidateTargetRead>(
        partialSchema.soundnessConstraints.front().candidate.payload);
    partialSchemaRead.resourceSubstitutions.erase("fs-b");
    if (!expectError(cmp::domain(context, partialSchema),
                     "partial schema substitution"))
      return;
    cmp::CompilerRequest surplusSchema = request;
    auto &surplusSchemaRead = std::get<cmp::CandidateTargetRead>(
        surplusSchema.soundnessConstraints.front().candidate.payload);
    surplusSchemaRead.resourceSubstitutions.emplace(
        "fs-surplus", identitySubstitution(fsRule.resources));
    if (!expectError(cmp::domain(context, surplusSchema),
                     "surplus schema substitution"))
      return;
    if (fsRule.resources.empty())
      return fail("compiler fixture needs a symbolic FS resource");
    cmp::CompilerRequest partialResource = request;
    auto &partialResourceRead = std::get<cmp::CandidateTargetRead>(
        partialResource.soundnessConstraints.front().candidate.payload);
    partialResourceRead.resourceSubstitutions.at("fs-a").erase(
        fsRule.resources.front().name);
    if (!expectError(cmp::domain(context, partialResource),
                     "partial resource substitution"))
      return;
    cmp::CompilerRequest surplusResource = request;
    auto &surplusResourceRead = std::get<cmp::CandidateTargetRead>(
        surplusResource.soundnessConstraints.front().candidate.payload);
    surplusResourceRead.resourceSubstitutions.at("fs-a").emplace(
        "surplus-resource", snd::ClosedQuantity());
    if (!expectError(cmp::domain(context, surplusResource),
                     "surplus resource substitution"))
      return;

    cmp::CompilerRequest nullExpression = request;
    cmp::BoundExpr nullCandidate;
    nullCandidate.payload = cmp::AddBounds{{cmp::BoundExprPtr()}};
    nullExpression.soundnessConstraints.front().candidate =
        std::move(nullCandidate);
    if (!expectError(cmp::domain(context, nullExpression),
                     "null bound-expression operand"))
      return;
    cmp::CompilerRequest cyclicExpression = request;
    auto recursiveExpression = std::make_shared<cmp::BoundExpr>();
    recursiveExpression->payload =
        cmp::ScaleBound{constantQuantity(1), recursiveExpression};
    cmp::BoundExpr cyclicCandidate;
    cyclicCandidate.payload =
        cmp::ScaleBound{constantQuantity(1), recursiveExpression};
    cyclicExpression.soundnessConstraints.front().candidate =
        std::move(cyclicCandidate);
    if (!expectError(cmp::domain(context, cyclicExpression),
                     "cyclic bound expression"))
      return;
    recursiveExpression->payload = cmp::ZeroBound{};
    llvm::outs()
        << "compiler constraints: exact substitutions and recursion closed\n";

    cmp::CompilerRequest missingHypothesis = request;
    missingHypothesis.derivationSurface.allowedHypotheses.clear();
    auto hypothesisDomain = cmp::domain(context, missingHypothesis);
    if (!hypothesisDomain)
      return fail(llvm::toString(hypothesisDomain.takeError()));
    if (!expectError(
            cmp::validate(context, missingHypothesis, *hypothesisDomain, 0),
            "missing exact hypothesis"))
      return;
    llvm::outs()
        << "compiler valid: exact total loss and hypothesis constraints\n";

    cmp::CompilerSemanticContext missingWidth = context;
    missingWidth.codecWidthProfiles.at(widthProfileRef.id).codecs.clear();
    auto noEligible = cmp::compile(missingWidth, request);
    if (!noEligible)
      return fail(llvm::toString(noEligible.takeError()));
    if (noEligible->selectedOrdinal)
      return fail("unknown codec width remained selectable");
    auto noEligibleVerdict =
        cmp::checkDecision(missingWidth, request, *noEligible);
    if (!noEligibleVerdict)
      return fail(llvm::toString(noEligibleVerdict.takeError()));
    if (!noEligibleVerdict->accepted)
      return fail(
          "decision checker rejected the recomputed no-selection result");
    llvm::outs() << "compiler missing width: no eligible candidate\n";

    snd::DerivationTarget nativeTarget{
        subject, nativeRule.conclusionIndex.index, nativeRule.resources};
    snd::DeriveOutcome nativeExpected = snd::deriveSoundness(
        *soundnessContext, *view, nativeTarget, *nativePlan);
    if (!nativeExpected.accepted())
      return fail("compiler native RBR DERIVE refused: " +
                  nativeExpected.refusal->detail);
    const auto *nativeApplication = std::get_if<snd::EvaluatedApplication>(
        &nativeExpected.result->root.node);
    if (!nativeApplication)
      return fail("compiler native RBR fixture is not an application");
    const auto *nativeRounds =
        std::get_if<snd::RoundResult>(&nativeApplication->conclusion.result);
    if (!nativeRounds || nativeRounds->rounds.size() < 2)
      return fail("compiler native RBR fixture needs two exact rounds");

    snd::ClosedBoundOperationResult roundMaximum = snd::closedBoundMaximum(
        {nativeRounds->rounds[0].bound, nativeRounds->rounds[1].bound},
        "test.compiler.round.maximum");
    snd::ClosedBoundOperationResult roundSum = snd::closedBoundAdd(
        nativeRounds->rounds[0].bound, nativeRounds->rounds[1].bound,
        "test.compiler.round.add");
    snd::ClosedBoundOperationResult roundScale = snd::closedBoundScale(
        constantQuantity(2), nativeRounds->rounds[0].bound,
        "test.compiler.round.scale");
    if (!roundMaximum.accepted() || !roundSum.accepted() ||
        !roundScale.accepted())
      return fail("compiler round fixture left the exact bound algebra");

    snd::ExactRef roundDerivationProviderRef{"compiler.derivation.native-rbr",
                                             "compiler-v0"};
    auto roundDerivationProvider =
        std::make_shared<const cmp::ListedDerivationPlanDomainProvider>(
            roundDerivationProviderRef,
            std::vector<cmp::ListedDerivationAlternative>{
                {"native-rbr", "rbr", subject, *nativePlan}});
    cmp::CompilerSemanticContext roundContext = context;
    roundContext.derivationDomains.emplace(roundDerivationProviderRef.id,
                                           roundDerivationProvider);
    cmp::CompilerRequest roundRequest = request;
    roundRequest.derivationPlanProviderRef = roundDerivationProviderRef;
    roundRequest.targets.clear();
    roundRequest.targets.push_back({"native-rbr", {owner}, {}, {"rbr"}});
    roundRequest.targetSchemas = {
        {"rbr", nativeRule.conclusionIndex.index, nativeRule.resources}};
    roundRequest.soundnessConstraints.clear();
    collectEvaluatedPropositions(
        nativeExpected.result->root,
        roundRequest.derivationSurface.allowedHypotheses);
    for (const snd::PrimitiveGameInstance &game :
         snd::gameSupport(nativeApplication->conclusion.result))
      if (std::find(
              roundRequest.derivationSurface.allowedPrimitiveGames.begin(),
              roundRequest.derivationSurface.allowedPrimitiveGames.end(),
              game) ==
          roundRequest.derivationSurface.allowedPrimitiveGames.end())
        roundRequest.derivationSurface.allowedPrimitiveGames.push_back(game);

    cmp::SchemaResourceSubstitutions rbrSubstitutions;
    rbrSubstitutions.emplace("rbr", identitySubstitution(nativeRule.resources));
    auto roundRead = [&](cmp::BoundProjection projection) {
      return candidateRead("native-rbr", cmp::ExactTargetMember{0},
                           std::move(projection), rbrSubstitutions);
    };
    const cmp::ComparisonDomain roundDomain{nativeRule.resources};
    roundRequest.soundnessConstraints.push_back(
        {roundDomain,
         roundRead({cmp::BoundProjectionKind::Round,
                    nativeRounds->rounds[0].roundIndex}),
         zeroBound(), nativeRounds->rounds[0].bound});
    roundRequest.soundnessConstraints.push_back(
        {roundDomain, roundRead({cmp::BoundProjectionKind::RoundMaximum, {}}),
         zeroBound(), *roundMaximum.value});
    roundRequest.soundnessConstraints.push_back(
        {roundDomain,
         addBounds({roundRead({cmp::BoundProjectionKind::Round,
                               nativeRounds->rounds[0].roundIndex}),
                    roundRead({cmp::BoundProjectionKind::Round,
                               nativeRounds->rounds[1].roundIndex})}),
         zeroBound(), *roundSum.value});
    roundRequest.soundnessConstraints.push_back(
        {roundDomain,
         maxBounds({roundRead({cmp::BoundProjectionKind::Round,
                               nativeRounds->rounds[0].roundIndex}),
                    roundRead({cmp::BoundProjectionKind::Round,
                               nativeRounds->rounds[1].roundIndex})}),
         zeroBound(), *roundMaximum.value});
    roundRequest.soundnessConstraints.push_back(
        {roundDomain,
         scaleBound(constantQuantity(2),
                    roundRead({cmp::BoundProjectionKind::Round,
                               nativeRounds->rounds[0].roundIndex})),
         zeroBound(), *roundScale.value});

    auto roundPlanDomain = cmp::domain(roundContext, roundRequest);
    if (!roundPlanDomain)
      return fail(llvm::toString(roundPlanDomain.takeError()));
    if (roundPlanDomain->plans.size() != 1)
      return fail("native RBR DOMAIN did not remain singleton");
    auto roundValid =
        cmp::validate(roundContext, roundRequest, *roundPlanDomain, 0);
    if (!roundValid)
      return fail(llvm::toString(roundValid.takeError()));

    cmp::CompilerRequest missingRound = roundRequest;
    auto &missingRoundRead = std::get<cmp::CandidateTargetRead>(
        missingRound.soundnessConstraints.front().candidate.payload);
    missingRoundRead.projection.exactRoundIndex = "not-an-exact-round";
    auto missingRoundDomain = cmp::domain(roundContext, missingRound);
    if (!missingRoundDomain)
      return fail(llvm::toString(missingRoundDomain.takeError()));
    if (!expectError(
            cmp::validate(roundContext, missingRound, *missingRoundDomain, 0),
            "missing exact round projection"))
      return;
    cmp::CompilerRequest tightRound = roundRequest;
    tightRound.soundnessConstraints.resize(1);
    tightRound.soundnessConstraints.front().ceiling = snd::ClosedBound();
    auto tightRoundDomain = cmp::domain(roundContext, tightRound);
    if (!tightRoundDomain)
      return fail(llvm::toString(tightRoundDomain.takeError()));
    if (!expectError(
            cmp::validate(roundContext, tightRound, *tightRoundDomain, 0),
            "tight round claim-total ceiling"))
      return;
    llvm::outs()
        << "compiler rounds: exact round/max and bound algebra accepted\n";

    snd::SealedSoundnessView fakeSourceView = *view;
    fakeSourceView.artifactId = "compiler.fake.stage0";
    fakeSourceView.claimsByIndex = {fakeClaim(0, "source-a"),
                                    fakeClaim(1, "source-b"),
                                    fakeClaim(2, "source-survivor")};
    fakeSourceView.reductionsByTransformerPosition.clear();
    snd::ExactRef fakePayloadTypeRef{"compiler.fake.payload", "compiler-v0"};
    snd::ExactRef fakeSemanticsRef{"compiler.fake.semantics", "compiler-v0"};
    cmp::AuthenticatedArtifactObservation fakeSourceObservation{
        fakeSourceView.artifactId, fakeSourceView, fixtureReads};
    auto fakePayload = cmp::makeArtifactPayload(
        fakePayloadTypeRef,
        FakeTransformPayload{0, std::move(fakeSourceObservation)});
    auto fakeSource = std::make_shared<const cmp::OwnedCompilerArtifact>(
        fakeSemanticsRef, std::move(fakePayload));
    snd::ExactRef fakeFamilyRef{"compiler.transform.fake-checked",
                                "compiler-v0"};
    snd::ExactRef fakeTransformProviderRef{"compiler.domain.fake-checked",
                                           "compiler-v0"};
    snd::ExactRef fakeDerivationProviderRef{"compiler.derivation.fake-listed",
                                            "compiler-v0"};
    cmp::TransformPlan fakeTransform;
    fakeTransform.applications.push_back(
        {fakeFamilyRef,
         {fakeClaim(0, "source-a"), fakeClaim(1, "source-b")},
         {}});
    fakeTransform.applications.push_back(
        {fakeFamilyRef, {fakeClaim(0, "merged")}, {}});
    auto fakeFamily = std::make_shared<const FakeTransformFamily>(
        fakeFamilyRef, fakeSemanticsRef, FakeTransformFamily::Mode::Good);
    auto fakeTransformProvider =
        std::make_shared<const FakeTransformDomainProvider>(
            fakeTransformProviderRef, fakeSemanticsRef, fakeTransform);

    auto finalSubject = [](const snd::ClaimRef &claim) {
      snd::SecuritySubject result;
      result.payload = snd::ProtocolClaimSubject{"compiler.fake.stage2", claim};
      return result;
    };
    const snd::SecuritySubject finishedSubject =
        finalSubject(fakeClaim(0, "finished"));
    const snd::SecuritySubject survivorSubject =
        finalSubject(fakeClaim(1, "survivor-2"));
    auto expectedSrPremise = expectedApplication->premises.find("source_sr");
    if (expectedSrPremise == expectedApplication->premises.end() ||
        !expectedSrPremise->second)
      return fail("compiler fixture lacks the evaluated SR premise");
    const auto *expectedSrApplication = std::get_if<snd::EvaluatedApplication>(
        &expectedSrPremise->second->node);
    if (!expectedSrApplication)
      return fail("compiler fixture SR premise is not an application");
    auto assumedPlan = [&](const snd::SecuritySubject &targetSubject) {
      snd::SecurityJudgment judgment = expectedSrApplication->conclusion;
      judgment.subject = targetSubject;
      judgment.hypotheses.erase(
          std::remove_if(
              judgment.hypotheses.begin(), judgment.hypotheses.end(),
              [](const snd::Hypothesis &hypothesis) {
                return std::holds_alternative<snd::AssumedJudgmentHolds>(
                    hypothesis);
              }),
          judgment.hypotheses.end());
      auto assumption = std::make_shared<snd::DerivationPlan>();
      assumption->node = snd::ExternalJudgmentAssumption{std::move(judgment)};
      const auto &protocol =
          std::get<snd::ProtocolClaimSubject>(targetSubject.payload);
      snd::ApplyDerivationPlan application{
          snd::PathOccurrence{protocol.artifactId, protocol.claim},
          fsBinding.ref,
          {}};
      application.premises.emplace("source_sr", std::move(assumption));
      snd::DerivationPlan root;
      root.node = std::move(application);
      return root;
    };
    std::vector<cmp::ListedDerivationAlternative> fakeAlternatives{
        {"fake-final", "fs-a", finishedSubject, assumedPlan(finishedSubject)},
        {"fake-final", "fs-a", survivorSubject, assumedPlan(survivorSubject)},
        {"fake-merged", "fs-a", finishedSubject, assumedPlan(finishedSubject)},
    };
    auto fakeDerivationProvider =
        std::make_shared<const cmp::ListedDerivationPlanDomainProvider>(
            fakeDerivationProviderRef, std::move(fakeAlternatives));

    cmp::CompilerRequest fakeRequest = request;
    fakeRequest.source = fakeSource;
    fakeRequest.transformDomainProviderRef = fakeTransformProviderRef;
    fakeRequest.derivationPlanProviderRef = fakeDerivationProviderRef;
    fakeRequest.targets.clear();
    cmp::RequestedTarget fakeFinal;
    fakeFinal.key = "fake-final";
    fakeFinal.orderedSourceClaims = fakeSourceView.claimsByIndex;
    fakeFinal.admittedSchemaKeys = {"fs-a"};
    fakeRequest.targets.push_back(fakeFinal);
    cmp::RequestedTarget fakeOutputs = fakeFinal;
    fakeOutputs.key = "fake-merged";
    fakeOutputs.selector.kind = cmp::TargetSelectorKind::TransformOutputs;
    fakeOutputs.selector.familyRef = fakeFamilyRef;
    fakeOutputs.selector.outputRole = "merged";
    fakeRequest.targets.push_back(fakeOutputs);
    fakeRequest.targetSchemas = {
        {"fs-a", fsRule.conclusionIndex.index, fsRule.resources}};
    fakeRequest.soundnessConstraints.clear();
    fakeRequest.comparisonScope = cmp::ClosedDomainScope();
    for (const snd::Hypothesis &hypothesis :
         expectedSrApplication->conclusion.hypotheses)
      if (const auto *proposition =
              std::get_if<snd::PropositionInstance>(&hypothesis);
          proposition &&
          std::find(fakeRequest.derivationSurface.allowedHypotheses.begin(),
                    fakeRequest.derivationSurface.allowedHypotheses.end(),
                    *proposition) ==
              fakeRequest.derivationSurface.allowedHypotheses.end())
        fakeRequest.derivationSurface.allowedHypotheses.push_back(*proposition);

    cmp::CompilerSemanticContext fakeContext = context;
    fakeContext.artifactSemantics.emplace(
        fakeSemanticsRef.id,
        std::make_shared<const FixtureArtifactSemantics<FakeTransformPayload>>(
            fakeSemanticsRef, fakePayloadTypeRef));
    fakeContext.transformDomains.emplace(fakeTransformProviderRef.id,
                                         fakeTransformProvider);
    fakeContext.transformFamilies.emplace(fakeFamilyRef.id, fakeFamily);
    fakeContext.derivationDomains.emplace(fakeDerivationProviderRef.id,
                                          fakeDerivationProvider);
    auto previewTrace =
        cmp::realizeTransform(fakeContext, fakeRequest, fakeTransform);
    if (!previewTrace)
      return fail(llvm::toString(previewTrace.takeError()));
    // A family that claims nothing leaves the record empty, and that is the
    // ordinary state rather than a gap: LEGAL establishes the transition and
    // the bound, so a consumer who needs anything else has been told nothing
    // and must obtain it elsewhere.
    if (!previewTrace->preservationClaims.empty())
      return fail("a family claiming nothing left a preservation claim");

    // The same transform, by a family that claims to preserve completeness.
    // The verdict must not move: a claim is a record of who is on the hook,
    // not something LEGAL reads.
    {
      snd::ExactRef claimingRef{"compiler.transform.fake-claiming",
                                "compiler-v0"};
      cmp::CompilerSemanticContext claimingContext = fakeContext;
      claimingContext.transformFamilies.emplace(
          claimingRef.id, std::make_shared<const FakeTransformFamily>(
                              claimingRef, fakeSemanticsRef,
                              FakeTransformFamily::Mode::ClaimsProperty));
      cmp::TransformPlan claimingPlan;
      claimingPlan.applications.push_back(
          {claimingRef,
           {fakeClaim(0, "source-a"), fakeClaim(1, "source-b")},
           {}});
      auto claimingTrace =
          cmp::realizeTransform(claimingContext, fakeRequest, claimingPlan);
      if (!claimingTrace)
        return fail("a preservation claim changed a legal transform's verdict");
      if (claimingTrace->preservationClaims.size() != 1 ||
          claimingTrace->preservationClaims[0].propertyRef !=
              "fixture.property" ||
          claimingTrace->preservationClaims[0].familyRef != claimingRef ||
          claimingTrace->preservationClaims[0].applicationIndex != 0)
        return fail("the trace did not record the preservation claim");

      // Compare against the same plan by the non-claiming family: the
      // correspondences are what LEGAL establishes, and they are identical.
      cmp::TransformPlan sameShape;
      sameShape.applications.push_back(
          {fakeFamilyRef,
           {fakeClaim(0, "source-a"), fakeClaim(1, "source-b")},
           {}});
      auto silentTrace =
          cmp::realizeTransform(fakeContext, fakeRequest, sameShape);
      if (!silentTrace || silentTrace->correspondences.size() !=
                              claimingTrace->correspondences.size())
        return fail("a preservation claim changed what LEGAL established");

      // A claim has to name its own author. Attributing one elsewhere would
      // put a family on the hook for an argument it never made.
      snd::ExactRef misattributedRef{"compiler.transform.fake-misattributed",
                                     "compiler-v0"};
      cmp::CompilerSemanticContext misattributedContext = fakeContext;
      misattributedContext.transformFamilies.emplace(
          misattributedRef.id,
          std::make_shared<const FakeTransformFamily>(
              misattributedRef, fakeSemanticsRef,
              FakeTransformFamily::Mode::MisattributedClaim));
      cmp::TransformPlan misattributedPlan;
      misattributedPlan.applications.push_back(
          {misattributedRef,
           {fakeClaim(0, "source-a"), fakeClaim(1, "source-b")},
           {}});
      if (!expectError(cmp::realizeTransform(misattributedContext, fakeRequest,
                                             misattributedPlan),
                       "preservation claim names another family"))
        return;
    }
    std::optional<snd::ClosedBound> finishedPreviewBound;
    for (const snd::SecuritySubject &previewSubject :
         {finishedSubject, survivorSubject}) {
      snd::DerivationPlan previewPlan = assumedPlan(previewSubject);
      snd::DerivationTarget previewTarget{
          previewSubject, fsRule.conclusionIndex.index, fsRule.resources};
      snd::DeriveOutcome preview = snd::deriveSoundness(
          *soundnessContext, previewTrace->finalArtifact->observation.soundness,
          previewTarget, previewPlan);
      if (!preview.accepted())
        return fail("fake compiler preview DERIVE refused: " +
                    preview.refusal->detail);
      const auto *previewApplication =
          std::get_if<snd::EvaluatedApplication>(&preview.result->root.node);
      const auto *previewScalar =
          previewApplication ? std::get_if<snd::ScalarResult>(
                                   &previewApplication->conclusion.result)
                             : nullptr;
      if (!previewScalar)
        return fail("fake compiler preview did not produce a scalar bound");
      if (previewSubject == finishedSubject)
        finishedPreviewBound = previewScalar->bound;
      collectEvaluatedPropositions(
          preview.result->root,
          fakeRequest.derivationSurface.allowedHypotheses);
    }
    if (!finishedPreviewBound)
      return fail("fake compiler preview lost its transformed target bound");

    auto fakeSourceSubject = [](const snd::ClaimRef &claim) {
      snd::SecuritySubject result;
      result.payload = snd::ProtocolClaimSubject{"compiler.fake.stage0", claim};
      return result;
    };
    const snd::SecuritySubject sourceASubject =
        fakeSourceSubject(fakeClaim(0, "source-a"));
    const snd::SecuritySubject sourceSurvivorSubject =
        fakeSourceSubject(fakeClaim(2, "source-survivor"));
    snd::DerivationPlan sourceAPlan = assumedPlan(sourceASubject);
    snd::DerivationTarget sourceATarget{
        sourceASubject, fsRule.conclusionIndex.index, fsRule.resources};
    snd::DeriveOutcome sourceAPreview = snd::deriveSoundness(
        *soundnessContext, fakeSourceView, sourceATarget, sourceAPlan);
    if (!sourceAPreview.accepted())
      return fail("fake compiler source-baseline DERIVE refused: " +
                  sourceAPreview.refusal->detail);
    const auto *sourceAApplication = std::get_if<snd::EvaluatedApplication>(
        &sourceAPreview.result->root.node);
    const auto *sourceAScalar =
        sourceAApplication ? std::get_if<snd::ScalarResult>(
                                 &sourceAApplication->conclusion.result)
                           : nullptr;
    if (!sourceAScalar || sourceAScalar->bound != *finishedPreviewBound)
      return fail(
          "fake compiler source and transformed bounds are not comparable");
    collectEvaluatedPropositions(
        sourceAPreview.result->root,
        fakeRequest.derivationSurface.allowedHypotheses);

    cmp::SchemaResourceSubstitutions fakeSubstitutions;
    fakeSubstitutions.emplace("fs-a", identitySubstitution(fsRule.resources));
    fakeRequest.soundnessConstraints.push_back(
        {cmp::ComparisonDomain{fsRule.resources},
         candidateRead("fake-merged", cmp::ExactTargetMember{0},
                       {cmp::BoundProjectionKind::Scalar, {}},
                       fakeSubstitutions),
         sourceProjection(sourceATarget, sourceAPlan,
                          {cmp::BoundProjectionKind::Scalar, {}},
                          identitySubstitution(fsRule.resources),
                          {"fake-merged", fakeClaim(0, "source-a")}),
         snd::ClosedBound()});

    auto fakeDomain = cmp::domain(fakeContext, fakeRequest);
    if (!fakeDomain)
      return fail(llvm::toString(fakeDomain.takeError()));
    snd::DerivationPlan expectedFinishedPlan = assumedPlan(finishedSubject);
    snd::DerivationPlan expectedSurvivorPlan = assumedPlan(survivorSubject);
    if (fakeDomain->plans.size() != 1 ||
        fakeDomain->plans.front().targets.size() != 2 ||
        fakeDomain->plans.front().targets[0].derivations.size() != 2 ||
        fakeDomain->plans.front().targets[1].derivations.size() != 1 ||
        !cmp::derivationPlansEqual(
            fakeDomain->plans.front().targets[0].derivations[0],
            expectedFinishedPlan) ||
        !cmp::derivationPlansEqual(
            fakeDomain->plans.front().targets[0].derivations[1],
            expectedSurvivorPlan) ||
        !cmp::derivationPlansEqual(
            fakeDomain->plans.front().targets[1].derivations[0],
            expectedFinishedPlan))
      return fail("checked lineage did not preserve final/output selection");
    auto fakeValid = cmp::validate(fakeContext, fakeRequest, *fakeDomain, 0);
    if (!fakeValid)
      return fail(llvm::toString(fakeValid.takeError()));
    if (fakeValid->candidate.trace.correspondences.size() != 4 ||
        fakeValid->candidate.trace.finalArtifact->observation.artifactId !=
            "compiler.fake.stage2" ||
        fakeValid->candidate.derivations.size() != 3)
      return fail(
          "nonidentity VALID lost its checked trace or exact derivations");
    auto fakeScored = cmp::score(fakeContext, fakeRequest, *fakeDomain, 0);
    if (!fakeScored)
      return fail(llvm::toString(fakeScored.takeError()));
    auto fakeSelection = cmp::select(fakeContext, fakeRequest, *fakeDomain);
    if (!fakeSelection ||
        fakeSelection->selectedOrdinal != std::optional<uint64_t>(0))
      return fail("nonidentity SELECT did not select its checked candidate");
    cmp::CompilerResult fakeResult{fakeSelection->selectedOrdinal};
    auto fakeVerdict = cmp::checkDecision(fakeContext, fakeRequest, fakeResult);
    if (!fakeVerdict)
      return fail(llvm::toString(fakeVerdict.takeError()));
    if (!fakeVerdict->accepted)
      return fail("nonidentity decision check rejected exact recomputation: " +
                  fakeVerdict->detail);
    llvm::outs()
        << "compiler transform: sequential lineage and assume leaves exact\n";

    cmp::CompilerRequest unrelatedBaseline = fakeRequest;
    auto &unrelatedSource = std::get<cmp::SourceProjection>(
        unrelatedBaseline.soundnessConstraints.front().baseline.payload);
    unrelatedSource.sourceTarget = {
        sourceSurvivorSubject, fsRule.conclusionIndex.index, fsRule.resources};
    unrelatedSource.sourceDerivationPlan = assumedPlan(sourceSurvivorSubject);
    unrelatedSource.targetRelation.exactSourceClaimRef =
        fakeClaim(2, "source-survivor");
    auto unrelatedDomain = cmp::domain(fakeContext, unrelatedBaseline);
    if (!unrelatedDomain)
      return fail(llvm::toString(unrelatedDomain.takeError()));
    if (!expectError(
            cmp::validate(fakeContext, unrelatedBaseline, *unrelatedDomain, 0),
            "unrelated source baseline"))
      return;

    cmp::CompilerRequest crossKeyBaseline = fakeRequest;
    auto &crossKeySource = std::get<cmp::SourceProjection>(
        crossKeyBaseline.soundnessConstraints.front().baseline.payload);
    crossKeySource.targetRelation.targetKey = "fake-final";
    if (!expectError(cmp::domain(fakeContext, crossKeyBaseline),
                     "cross-key source baseline"))
      return;
    llvm::outs() << "compiler introduced: related source envelope exact\n";

    cmp::CompilerRequest emptyAdd = fakeRequest;
    cmp::RequestedTarget emptyTarget = fakeOutputs;
    emptyTarget.key = "fake-empty";
    emptyTarget.selector.outputRole = "never-produced";
    emptyAdd.targets.push_back(std::move(emptyTarget));
    emptyAdd.soundnessConstraints.clear();
    emptyAdd.soundnessConstraints.push_back(
        {cmp::ComparisonDomain{fsRule.resources},
         candidateRead(
             "fake-empty", cmp::FoldTargetMembers{cmp::TargetFoldKind::Add},
             {cmp::BoundProjectionKind::Scalar, {}}, fakeSubstitutions),
         zeroBound(), snd::ClosedBound()});
    auto emptyAddDomain = cmp::domain(fakeContext, emptyAdd);
    if (!emptyAddDomain)
      return fail(llvm::toString(emptyAddDomain.takeError()));
    auto emptyAddValid =
        cmp::validate(fakeContext, emptyAdd, *emptyAddDomain, 0);
    if (!emptyAddValid)
      return fail(llvm::toString(emptyAddValid.takeError()));

    cmp::CompilerRequest emptyMaximum = emptyAdd;
    auto &emptyMaximumRead = std::get<cmp::CandidateTargetRead>(
        emptyMaximum.soundnessConstraints.front().candidate.payload);
    std::get<cmp::FoldTargetMembers>(emptyMaximumRead.members).aggregate =
        cmp::TargetFoldKind::Max;
    auto emptyMaximumDomain = cmp::domain(fakeContext, emptyMaximum);
    if (!emptyMaximumDomain)
      return fail(llvm::toString(emptyMaximumDomain.takeError()));
    if (!expectError(
            cmp::validate(fakeContext, emptyMaximum, *emptyMaximumDomain, 0),
            "empty target maximum"))
      return;
    llvm::outs() << "compiler empty folds: add zero and max refusal exact\n";

    cmp::CompilerRequest wrongAuthorityRequest = fakeRequest;
    wrongAuthorityRequest.source =
        std::make_shared<const cmp::OwnedCompilerArtifact>(
            snd::ExactRef{"compiler.fake.semantics.unknown", "compiler-v0"},
            fakeSource->adapterPayload);
    if (!expectError(cmp::domain(fakeContext, wrongAuthorityRequest),
                     "unknown artifact semantics authority"))
      return;
    cmp::AuthenticatedArtifactObservation wrongTypeObservation{
        fakeSourceView.artifactId, fakeSourceView, fixtureReads};
    auto wrongTypePayload = cmp::makeArtifactPayload(
        fakePayloadTypeRef,
        FixtureAdapterPayload{"wrong-payload-type",
                              std::move(wrongTypeObservation)});
    cmp::CompilerRequest wrongPayloadRequest = fakeRequest;
    wrongPayloadRequest.source =
        std::make_shared<const cmp::OwnedCompilerArtifact>(
            fakeSemanticsRef, std::move(wrongTypePayload));
    if (!expectError(cmp::domain(fakeContext, wrongPayloadRequest),
                     "artifact semantic payload type"))
      return;

    auto expectBadFamily = [&](llvm::StringRef id,
                               FakeTransformFamily::Mode mode,
                               llvm::StringRef label) {
      snd::ExactRef badRef{id.str(), "compiler-v0"};
      auto badFamily = std::make_shared<const FakeTransformFamily>(
          badRef, fakeSemanticsRef, mode);
      cmp::CompilerSemanticContext badContext = fakeContext;
      badContext.transformFamilies.emplace(badRef.id, badFamily);
      cmp::TransformPlan badPlan;
      badPlan.applications.push_back(
          {badRef, {fakeClaim(0, "source-a"), fakeClaim(1, "source-b")}, {}});
      return expectError(
          cmp::realizeTransform(badContext, fakeRequest, badPlan), label);
    };
    if (!expectBadFamily("compiler.transform.fake-invalid",
                         FakeTransformFamily::Mode::InvalidCheckerOutput,
                         "invalid transform checker output") ||
        !expectBadFamily("compiler.transform.fake-ambiguous",
                         FakeTransformFamily::Mode::AmbiguousPrimary,
                         "ambiguous transform checker output"))
      return;
    snd::ExactRef alternateSemanticsRef{"compiler.fake.semantics.successor",
                                        "compiler-v0"};
    snd::ExactRef changedSemanticsFamilyRef{
        "compiler.transform.fake-changed-semantics", "compiler-v0"};
    cmp::CompilerSemanticContext changedSemanticsContext = fakeContext;
    changedSemanticsContext.artifactSemantics.emplace(
        alternateSemanticsRef.id,
        std::make_shared<const FixtureArtifactSemantics<FakeTransformPayload>>(
            alternateSemanticsRef, fakePayloadTypeRef));
    changedSemanticsContext.transformFamilies.emplace(
        changedSemanticsFamilyRef.id,
        std::make_shared<const FakeTransformFamily>(
            changedSemanticsFamilyRef, fakeSemanticsRef,
            FakeTransformFamily::Mode::Good, alternateSemanticsRef));
    cmp::TransformPlan changedSemanticsPlan;
    changedSemanticsPlan.applications.push_back(
        {changedSemanticsFamilyRef,
         {fakeClaim(0, "source-a"), fakeClaim(1, "source-b")},
         {}});
    if (!expectError(cmp::realizeTransform(changedSemanticsContext, fakeRequest,
                                           changedSemanticsPlan),
                     "transform successor artifact semantics change"))
      return;
    cmp::CompilerRequest partialLineage = fakeRequest;
    partialLineage.targets.resize(1);
    partialLineage.targets.front().orderedSourceClaims = {
        fakeClaim(0, "source-a")};
    if (!expectError(cmp::domain(fakeContext, partialLineage),
                     "partial many-to-one lineage"))
      return;
    llvm::outs()
        << "compiler transform refusals: authority checker and lineage "
           "closed\n";

    cmp::CompilerRequest nonidentity = request;
    cmp::CompilerPlan transformed = planDomain->plans.front();
    transformed.transform.applications.push_back(
        {{"compiler.transform.unknown", "compiler-v0"}, {owner}, {}});
    nonidentity.comparisonScope =
        cmp::SubmittedFrontierScope{{std::move(transformed)}};
    if (!expectError(cmp::domain(context, nonidentity), "nonidentity plan"))
      return;

    cmp::CompilerRequest cyclic = request;
    cmp::CompilerPlan cyclicPlan = planDomain->plans.front();
    auto cycle = std::make_shared<snd::DerivationPlan>();
    snd::ApplyDerivationPlan cycleApplication{fsSite, fsBinding.ref, {}};
    cycleApplication.premises.emplace("cycle", cycle);
    cycle->node = std::move(cycleApplication);
    cyclicPlan.targets.front().derivations.front() = *cycle;
    cyclic.comparisonScope =
        cmp::SubmittedFrontierScope{{std::move(cyclicPlan)}};
    if (!expectError(cmp::domain(context, cyclic), "cyclic plan"))
      return;

    llvm::outs() << "compiler refusals: nonidentity/cycle closed\n";
    llvm::outs() << "compiler core: PASS\n";
  }
};

} // namespace

namespace zkc::test {
void registerTestCompilerCorePass() {
  PassRegistration<TestCompilerCorePass>();
}
} // namespace zkc::test
