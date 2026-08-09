//===- TestPirCompilerProvider.cpp - real PIR compiler path ----*- C++ -*-===//

#include "Artifact/ArtifactInternal.h"
#include "Compiler/CompilerCoreInternal.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/Pass/Pass.h"
#include "zkc/Artifact/Artifact.h"
#include "zkc/Compiler/PirCompilerProvider.h"
#include "zkc/Dialect/Pir/PirOps.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/ConstructionProfileRegistry.h"
#include "zkc/Registry/ProtocolVocabulary.h"
#include "zkc/Soundness/SignatureFile.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using namespace mlir;

namespace {

namespace cmp = zkc::compiler;
namespace reg = zkc::registry;
namespace snd = zkc::soundness;

static_assert(!std::is_constructible_v<cmp::AuthenticatedCompilerArtifact,
                                       cmp::ArtifactHandle,
                                       cmp::AuthenticatedArtifactObservation>);

constexpr llvm::StringLiteral kFieldOrder =
    "524358751751261904794477405081859658376905525005276378226036586999"
    "38581184513";
constexpr llvm::StringLiteral kEbDbRule = "zkc.pcs.kzg_batch";
constexpr llvm::StringLiteral kArsdhRule = "zkc.pcs.kzg_batch_arsdh";
constexpr llvm::StringLiteral kContract = "kzg_batch";
constexpr llvm::StringLiteral kTargetKey = "batch-css";
constexpr llvm::StringLiteral kEbDbSchema = "css-eb-db";
constexpr llvm::StringLiteral kArsdhSchema = "css-arsdh";

template <typename T> llvm::Expected<T> testError(const llvm::Twine &message) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), message);
}

llvm::Error testFailure(const llvm::Twine &message) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), message);
}

template <typename RegistryT>
llvm::Expected<std::shared_ptr<const RegistryT>>
loadSharedRegistry(llvm::StringRef path) {
  auto loaded = RegistryT::loadFromFile(path);
  if (!loaded)
    return loaded.takeError();
  return std::make_shared<const RegistryT>(std::move(*loaded));
}

reg::Rational fieldOrder() {
  auto parsed = reg::Rational::fromDecimal(kFieldOrder);
  if (!parsed) {
    std::string detail = llvm::toString(parsed.takeError());
    llvm::report_fatal_error(llvm::StringRef(detail));
  }
  return std::move(*parsed);
}

snd::RuntimeValue exactAlgebra() {
  return snd::RuntimeValue::algebra(
      {"algebra:bls12_381:g1", "fr", fieldOrder()});
}

std::string bindingId(llvm::StringRef rule) {
  return (rule + "@reduction:" + kContract).str();
}

snd::ResolvedParameterEnvironment
parameterEnvironment(const snd::ExactRef &bindingRef) {
  snd::ResolvedParameterEnvironment result;
  result.bindingRef = bindingRef;
  result.values.emplace("algebra", exactAlgebra());
  result.values.emplace(
      "srs", snd::RuntimeValue::srs({"test.kzg.srs", "test.kzg.srs"}));
  result.values.emplace("srs_max_degree", snd::RuntimeValue::integer(
                                              reg::Rational::fromInteger(64)));
  return result;
}

snd::SecurityJudgment
sourceAssumption(const snd::ConsumedClaimVectorSubject &subject) {
  snd::ClosedQuantity arity;
  arity.constant = reg::Rational::fromInteger(subject.orderedSources.size());
  snd::ClosedQuantity challengeSpace;
  challengeSpace.constant = fieldOrder();

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
                             const snd::SecurityJudgment &assumption) {
  auto source = std::make_shared<snd::DerivationPlan>();
  source->node = snd::ExternalJudgmentAssumption{assumption};
  snd::ApplyDerivationPlan root;
  root.site = site;
  root.bindingRef = bindingRef;
  root.premises.emplace("source_ss", std::move(source));
  snd::DerivationPlan result;
  result.node = std::move(root);
  return result;
}

const snd::SecurityJudgment &
conclusionOf(const snd::EvaluatedDerivation &derivation) {
  if (const auto *assumption =
          std::get_if<snd::EvaluatedAssumption>(&derivation.node))
    return assumption->conclusion;
  return std::get<snd::EvaluatedApplication>(derivation.node).conclusion;
}

const snd::SecurityJudgment *rootConclusion(const snd::DeriveOutcome &outcome) {
  if (!outcome.accepted())
    return nullptr;
  return &conclusionOf(outcome.result->root);
}

void collectSurface(const snd::EvaluatedDerivation &derivation,
                    cmp::DerivationSurface &surface) {
  const snd::SecurityJudgment &conclusion = conclusionOf(derivation);
  for (const snd::PrimitiveGameInstance &game :
       snd::gameSupport(conclusion.result))
    if (!llvm::is_contained(surface.allowedPrimitiveGames, game))
      surface.allowedPrimitiveGames.push_back(game);
  for (const snd::Hypothesis &hypothesis : conclusion.hypotheses)
    if (const auto *proposition =
            std::get_if<snd::PropositionInstance>(&hypothesis);
        proposition &&
        !llvm::is_contained(surface.allowedHypotheses, *proposition))
      surface.allowedHypotheses.push_back(*proposition);

  if (const auto *application =
          std::get_if<snd::EvaluatedApplication>(&derivation.node))
    for (const auto &[port, premise] : application->premises) {
      (void)port;
      if (premise)
        collectSurface(*premise, surface);
    }
}

snd::ClosedQuantity unitResource(llvm::StringRef resource) {
  snd::ClosedQuantity result;
  result.resourceTerms.push_back(
      {reg::Rational::fromInteger(1), resource.str(), 1});
  return result;
}

cmp::ResourceSubstitution
identitySubstitution(const std::vector<snd::TypedDeclaration> &resources) {
  cmp::ResourceSubstitution result;
  for (const snd::TypedDeclaration &resource : resources)
    result.emplace(resource.name, unitResource(resource.name));
  return result;
}

bool isInteger(const reg::Rational &value, int64_t expected) {
  return value.compare(reg::Rational::fromInteger(expected)) == 0;
}

snd::ExactScalarValue integerValue(int64_t value) {
  snd::ExactScalarValue result;
  result.sort = snd::ValueSort::Integer;
  result.payload = reg::Rational::fromInteger(value);
  return result;
}

bool exactIntegerValue(const snd::ExactScalarValue &value,
                       const reg::Rational &expected) {
  if (value.sort != snd::ValueSort::Integer)
    return false;
  const auto *integer = std::get_if<reg::Rational>(&value.payload);
  return integer && integer->compare(expected) == 0;
}

bool applicationEqual(const cmp::TransformApplication &left,
                      const cmp::TransformApplication &right) {
  return left.familyRef == right.familyRef &&
         left.matchedClaims == right.matchedClaims &&
         left.parameters == right.parameters;
}

struct RoutedArtifactState {
  std::string routes;
  std::string holeContractDigest;
};

llvm::Expected<RoutedArtifactState>
routedArtifactState(cmp::AuthenticatedArtifactHandle artifact) {
  if (!artifact || !artifact->artifact || !artifact->artifact->adapterPayload)
    return testError<RoutedArtifactState>(
        "routed compiler artifact has no immutable payload");
  const auto *payload = cmp::artifactPayloadAs<cmp::PirArtifactPayload>(
      *artifact->artifact->adapterPayload);
  if (!payload)
    return testError<RoutedArtifactState>(
        "routed compiler artifact has the wrong payload type");
  if (payload->artifact().id() != artifact->observation.artifactId)
    return testError<RoutedArtifactState>(
        "routed compiler artifact observation changed its admitted identity");

  auto clone = zkc::artifact::detail::ArtifactAccess::cloneForReopen(
      payload->artifact());
  zkc::pir::SealedOp sealed = clone.sealed();
  DictionaryAttr routes = sealed.getRoutesAttr();
  if (!routes || routes.empty())
    return testError<RoutedArtifactState>(
        "routed compiler artifact lost its construction routes");
  auto routesJson = zkc::encoding::attributeToCanonicalJson(routes);
  if (!routesJson)
    return routesJson.takeError();
  auto routeBytes = zkc::encoding::canonicalJsonBytes(*routesJson);
  if (!routeBytes)
    return routeBytes.takeError();

  DictionaryAttr vocabulary = sealed.getVocab().value_or(DictionaryAttr());
  auto sectionEntry =
      vocabulary ? vocabulary.getNamed("hole_contracts") : std::nullopt;
  auto section = sectionEntry
                     ? dyn_cast<DictionaryAttr>(sectionEntry->getValue())
                     : DictionaryAttr();
  auto citationEntry =
      section ? section.getNamed("zkc.hole.sigma-commit") : std::nullopt;
  auto citation = citationEntry
                      ? dyn_cast<StringAttr>(citationEntry->getValue())
                      : StringAttr();
  if (!citation || !zkc::encoding::isSha256Ref(citation.getValue()))
    return testError<RoutedArtifactState>(
        "routed compiler artifact lost its exact HoleContract citation");
  return RoutedArtifactState{std::move(*routeBytes), citation.getValue().str()};
}

llvm::Error requireRoutedSuccessor(cmp::AuthenticatedArtifactHandle source,
                                   cmp::AuthenticatedArtifactHandle successor) {
  auto before = routedArtifactState(std::move(source));
  if (!before)
    return before.takeError();
  auto after = routedArtifactState(std::move(successor));
  if (!after)
    return after.takeError();
  if (before->routes != after->routes)
    return testFailure("compiler successor changed its construction routes");
  if (before->holeContractDigest != after->holeContractDigest)
    return testFailure("compiler successor changed its HoleContract citation");
  return llvm::Error::success();
}

llvm::Expected<cmp::AuthenticatedArtifactHandle>
authenticate(const cmp::PirArtifactSemantics &semantics,
             cmp::ArtifactHandle artifact) {
  return semantics.authenticateArtifact(std::move(artifact));
}

struct ExactKzgEnvironment {
  std::shared_ptr<const cmp::PirArtifactSemantics> semantics;
  std::shared_ptr<const cmp::PirArtifactSemantics> alternateProfilesSemantics;
  std::shared_ptr<const cmp::PirArtifactSemantics> alternateHoleSemantics;
  std::shared_ptr<const cmp::SamePointKzgBatchTransformFamily> family;
  std::shared_ptr<const cmp::SamePointKzgBatchTransformDomainProvider> domain;
  std::shared_ptr<const snd::SoundnessContext> soundness;
  const snd::SoundnessRule *ebDbRule = nullptr;
  const snd::SoundnessRule *arsdhRule = nullptr;
  const snd::RuleBinding *ebDbBinding = nullptr;
  const snd::RuleBinding *arsdhBinding = nullptr;
};

struct TestPirCompilerProviderPass
    : public PassWrapper<TestPirCompilerProviderPass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(TestPirCompilerProviderPass)

  TestPirCompilerProviderPass() = default;
  TestPirCompilerProviderPass(const TestPirCompilerProviderPass &other)
      : PassWrapper(other) {}

  StringRef getArgument() const override {
    return "test-pir-compiler-provider";
  }
  StringRef getDescription() const override {
    return "test the real PIR/KZG provider through CompilerCore";
  }

  Option<std::string> protocolVocabularyPath{
      *this, "protocol-vocabulary", llvm::cl::desc("protocol vocabulary")};
  Option<std::string> signaturePath{*this, "signature",
                                    llvm::cl::desc("the shipped signature")};
  Option<std::string> constructionProfileRegistryPath{
      *this, "construction-profile-registry",
      llvm::cl::desc("construction-profile registry")};
  Option<std::string> sourceArtifactPath{
      *this, "source-artifact", llvm::cl::desc("admitted PIR artifact")};
  Option<unsigned> expectedGroups{
      *this, "expected-groups", llvm::cl::desc("expected disjoint KZG groups"),
      llvm::cl::init(1)};
  Option<bool> expectRoutes{
      *this, "expect-routes",
      llvm::cl::desc("require routed successor preservation"),
      llvm::cl::init(false)};

  void runOnOperation() override {
    ModuleOp module = getOperation();
    auto fail = [&](const llvm::Twine &message) {
      module.emitError() << message;
      signalPassFailure();
    };

    if (expectedGroups != 1 && expectedGroups != 2)
      return fail("PIR compiler provider test expects one or two groups");
    if (sourceArtifactPath.empty())
      return fail("PIR compiler provider test requires a source artifact");

    auto environment = makeEnvironment();
    if (!environment)
      return fail(llvm::toString(environment.takeError()));
    auto admitted = zkc::artifact::loadAndAdmitArtifact(
        sourceArtifactPath, environment->semantics->environment());
    if (!admitted)
      return fail(llvm::toString(admitted.takeError()));

    auto wrongProfiles =
        environment->alternateProfilesSemantics->createArtifact(*admitted);
    if (wrongProfiles)
      return fail("compiler admitted an artifact from different profiles");
    llvm::consumeError(wrongProfiles.takeError());
    auto wrongHoles =
        environment->alternateHoleSemantics->createArtifact(*admitted);
    if (wrongHoles)
      return fail("compiler admitted an artifact from a different vocabulary");
    llvm::consumeError(wrongHoles.takeError());
    llvm::outs() << "PIR compiler admission: full environment exact\n";

    auto source = environment->semantics->createArtifact(std::move(*admitted));
    if (!source)
      return fail(llvm::toString(source.takeError()));
    auto authenticatedSource = authenticate(*environment->semantics, *source);
    if (!authenticatedSource)
      return fail(llvm::toString(authenticatedSource.takeError()));
    const size_t expectedSourceReads = 2 * expectedGroups;
    if ((*authenticatedSource)->observation.verifierProofReads.size() !=
        expectedSourceReads)
      return fail("source-derived KZG proof reads have the wrong cardinality");

    snd::ExactRef derivationProviderRef{"compiler.derivation.kzg-listed",
                                        "zkc.compiler.test"};
    snd::ExactRef widthProfileRef{"compiler.width.bls12-381",
                                  "zkc.compiler.test"};
    auto emptyDerivations =
        std::make_shared<const cmp::ListedDerivationPlanDomainProvider>(
            derivationProviderRef,
            std::vector<cmp::ListedDerivationAlternative>{});

    cmp::CompilerSemanticContext context;
    context.soundnessContext = environment->soundness;
    context.artifactSemantics.emplace(environment->semantics->exactRef().id,
                                      environment->semantics);
    context.transformDomains.emplace(environment->domain->exactRef().id,
                                     environment->domain);
    context.transformFamilies.emplace(environment->family->exactRef().id,
                                      environment->family);
    context.derivationDomains.emplace(derivationProviderRef.id,
                                      emptyDerivations);

    cmp::CodecWidthProfile widthProfile;
    widthProfile.ref = widthProfileRef;
    for (const cmp::VerifierProofRead &read :
         (*authenticatedSource)->observation.verifierProofReads) {
      if (read.codecRef.id != "bls_g1_be48" || read.count != 1)
        return fail("source proof reads are not exact BLS12-381 G1 reads");
      auto [found, inserted] = widthProfile.codecs.emplace(
          read.codecRef.id,
          cmp::CodecWidth{read.codecRef, reg::Rational::fromInteger(48)});
      if (!inserted && found->second.codecRef != read.codecRef)
        return fail("one codec id resolved to two exact revisions");
    }
    context.codecWidthProfiles.emplace(widthProfile.ref.id,
                                       std::move(widthProfile));

    cmp::CompilerRequest request;
    request.source = *source;
    request.transformDomainProviderRef = environment->domain->exactRef();
    request.derivationPlanProviderRef = derivationProviderRef;
    request.objectives.push_back(
        {"proof-bytes", cmp::ObjectiveKind::StaticProofBytes,
         cmp::ObjectiveDirection::Minimize, widthProfileRef});
    request.limits.maxTransformApplications = expectedGroups;
    request.limits.maxDomainPlans = 64;

    auto nullDomain =
        std::make_shared<const cmp::SamePointKzgBatchTransformDomainProvider>(
            nullptr, fieldOrder());
    if (!nullDomain->artifactSemanticsRef().id.empty() ||
        !nullDomain->artifactSemanticsRef().sourceRevision.empty())
      return fail("null PIR transform domain exposed nonempty semantics");
    cmp::CompilerSemanticContext nullDomainContext = context;
    nullDomainContext.transformDomains[nullDomain->exactRef().id] = nullDomain;
    cmp::CompilerRequest nullDomainRequest = request;
    nullDomainRequest.transformDomainProviderRef = nullDomain->exactRef();
    auto nullDomainResult = cmp::domain(nullDomainContext, nullDomainRequest);
    if (nullDomainResult)
      return fail("null PIR transform domain unexpectedly entered DOMAIN");
    llvm::consumeError(nullDomainResult.takeError());

    auto nullFamily =
        std::make_shared<const cmp::SamePointKzgBatchTransformFamily>(nullptr);
    if (!nullFamily->artifactSemanticsRef().id.empty() ||
        !nullFamily->artifactSemanticsRef().sourceRevision.empty())
      return fail("null PIR transform family exposed nonempty semantics");
    cmp::CompilerSemanticContext nullFamilyContext = context;
    nullFamilyContext.transformFamilies[nullFamily->exactRef().id] = nullFamily;
    cmp::CompilerRequest nullFamilyRequest = request;
    cmp::CompilerPlan nullFamilyPlan;
    nullFamilyPlan.transform.applications.push_back(
        {nullFamily->exactRef(), {}, {}});
    nullFamilyRequest.comparisonScope =
        cmp::SubmittedFrontierScope{{std::move(nullFamilyPlan)}};
    auto nullFamilyResult = cmp::domain(nullFamilyContext, nullFamilyRequest);
    if (nullFamilyResult)
      return fail("null PIR transform family unexpectedly entered DOMAIN");
    llvm::consumeError(nullFamilyResult.takeError());

    if (expectedGroups == 1) {
      if (llvm::Error error =
              runOneGroup(*environment, context, request, *authenticatedSource))
        return fail(llvm::toString(std::move(error)));
      return;
    }
    if (llvm::Error error =
            runTwoGroups(*environment, context, request, *authenticatedSource))
      return fail(llvm::toString(std::move(error)));
  }

private:
  llvm::Expected<ExactKzgEnvironment> makeEnvironment() const {
    auto vocabulary =
        loadSharedRegistry<reg::ProtocolVocabulary>(protocolVocabularyPath);
    if (!vocabulary)
      return vocabulary.takeError();
    auto profiles = loadSharedRegistry<reg::ConstructionProfileRegistry>(
        constructionProfileRegistryPath);
    if (!profiles)
      return profiles.takeError();

    auto signature = snd::loadSignatureFromFile(signaturePath);
    if (!signature)
      return signature.takeError();
    const snd::SoundnessCatalog *adapted = &signature->catalog;
    auto ebDbRule = adapted->rules.find(kEbDbRule.str());
    auto arsdhRule = adapted->rules.find(kArsdhRule.str());
    auto ebDbBinding = adapted->bindings.find(bindingId(kEbDbRule));
    auto arsdhBinding = adapted->bindings.find(bindingId(kArsdhRule));
    if (ebDbRule == adapted->rules.end() || arsdhRule == adapted->rules.end() ||
        ebDbBinding == adapted->bindings.end() ||
        arsdhBinding == adapted->bindings.end())
      return testError<ExactKzgEnvironment>(
          "exact KZG soundness alternatives did not adapt");

    snd::ResolvedParameterEnvironments parameters;
    parameters.emplace(ebDbBinding->second.ref.id,
                       parameterEnvironment(ebDbBinding->second.ref));
    parameters.emplace(arsdhBinding->second.ref.id,
                       parameterEnvironment(arsdhBinding->second.ref));
    snd::SoundnessContextOutcome soundnessOutcome = snd::buildSoundnessContext(
        *adapted,
        std::vector<snd::ExactRef>{ebDbBinding->second.ref,
                                   arsdhBinding->second.ref},
        std::move(parameters));
    if (!soundnessOutcome.accepted())
      return testError<ExactKzgEnvironment>(
          "exact KZG soundness context is ill-formed: " +
          soundnessOutcome.refusal->detail);
    auto soundness = std::make_shared<const snd::SoundnessContext>(
        std::move(*soundnessOutcome.context));

    auto semantics = std::make_shared<const cmp::PirArtifactSemantics>(
        reg::ProtocolEnvironment(**vocabulary, **profiles));
    auto family = std::make_shared<const cmp::SamePointKzgBatchTransformFamily>(
        semantics);
    auto domain =
        std::make_shared<const cmp::SamePointKzgBatchTransformDomainProvider>(
            semantics, fieldOrder());
    auto otherBatchDomain =
        std::make_shared<const cmp::SamePointKzgBatchTransformDomainProvider>(
            semantics, reg::Rational::fromInteger(17));
    auto semanticsTwin = std::make_shared<const cmp::PirArtifactSemantics>(
        reg::ProtocolEnvironment(**vocabulary, **profiles));
    auto familyTwin =
        std::make_shared<const cmp::SamePointKzgBatchTransformFamily>(
            semanticsTwin);
    auto domainTwin =
        std::make_shared<const cmp::SamePointKzgBatchTransformDomainProvider>(
            semanticsTwin, fieldOrder());

    auto alternateProfiles = reg::ConstructionProfileRegistry::parse(
        R"json({
          "registry": "zkc.construction_profiles",
          "sponges": {
            "alternate": {
              "alphabet_order": "2",
              "capacity": 1,
              "rate": 1
            }
          },
          "codecs": {}
        })json",
        "compiler-provider-alternate-construction-registry");
    if (!alternateProfiles)
      return alternateProfiles.takeError();
    auto alternateSemantics = std::make_shared<const cmp::PirArtifactSemantics>(
        reg::ProtocolEnvironment(**vocabulary, std::move(*alternateProfiles)));

    llvm::json::Value alternateVocabularyJson =
        (*vocabulary)->toCanonicalJson();
    llvm::json::Object *alternateVocabularyObject =
        alternateVocabularyJson.getAsObject();
    llvm::json::Object *holeContracts =
        alternateVocabularyObject
            ? alternateVocabularyObject->getObject("hole_contracts")
            : nullptr;
    llvm::json::Object *commitContract =
        holeContracts ? holeContracts->getObject("zkc.hole.sigma-commit")
                      : nullptr;
    if (!commitContract)
      return testError<ExactKzgEnvironment>(
          "test vocabulary has no sigma commit HoleContract");
    (*commitContract)["kind"] = "extend";
    auto alternateVocabularyBytes =
        zkc::encoding::canonicalJsonBytes(alternateVocabularyJson);
    if (!alternateVocabularyBytes)
      return alternateVocabularyBytes.takeError();
    auto alternateVocabulary = reg::ProtocolVocabulary::parse(
        *alternateVocabularyBytes,
        "compiler-provider-alternate-hole-contract-vocabulary");
    if (!alternateVocabulary)
      return alternateVocabulary.takeError();
    auto alternateHoleSemantics =
        std::make_shared<const cmp::PirArtifactSemantics>(
            reg::ProtocolEnvironment(std::move(*alternateVocabulary),
                                     **profiles));

    if (semantics->exactRef().id != cmp::pirArtifactSemanticsV1Ref().id ||
        family->exactRef().id != cmp::samePointKzgBatchV1Ref().id ||
        domain->exactRef().id != cmp::samePointKzgBatchDomainV1Ref().id ||
        semantics->exactRef().sourceRevision.rfind("sha256:", 0) != 0 ||
        family->exactRef().sourceRevision.rfind("sha256:", 0) != 0 ||
        domain->exactRef().sourceRevision.rfind("sha256:", 0) != 0 ||
        semantics->exactRef() == cmp::pirArtifactSemanticsV1Ref() ||
        family->exactRef() == cmp::samePointKzgBatchV1Ref() ||
        domain->exactRef() == cmp::samePointKzgBatchDomainV1Ref() ||
        otherBatchDomain->exactRef() == domain->exactRef() ||
        semanticsTwin->exactRef() != semantics->exactRef() ||
        familyTwin->exactRef() != family->exactRef() ||
        domainTwin->exactRef() != domain->exactRef() ||
        alternateSemantics->exactRef() == semantics->exactRef() ||
        alternateHoleSemantics->exactRef() == semantics->exactRef())
      return testError<ExactKzgEnvironment>(
          "PIR providers do not carry configuration-bound exact refs");

    llvm::outs() << "PIR compiler semantics: HoleContracts identity exact\n";
    // The configured refs are golden below: the compiler-configuration
    // preimage is identity-bearing, so an unannounced preimage change must
    // fail here rather than ride a refactor. A legitimate registry edit
    // updates the pinned values in the same change.
    llvm::outs() << "configured semantics ref: "
                 << semantics->exactRef().sourceRevision << "\n";
    llvm::outs() << "configured family ref: "
                 << family->exactRef().sourceRevision << "\n";
    llvm::outs() << "configured domain ref: "
                 << domain->exactRef().sourceRevision << "\n";

    // SoundnessContext owns a catalog copy, so exact declarations are
    // reached through that owned snapshot rather than the loaded signature.
    return ExactKzgEnvironment{
        std::move(semantics),
        std::move(alternateSemantics),
        std::move(alternateHoleSemantics),
        std::move(family),
        std::move(domain),
        std::move(soundness),
        nullptr,
        nullptr,
        nullptr,
        nullptr,
    };
  }

  llvm::Error populateSelectedDeclarations(ExactKzgEnvironment &environment) {
    for (const snd::ExactRef &ref :
         environment.soundness->selectedBindingRefs()) {
      const snd::RuleBinding *binding = environment.soundness->findBinding(ref);
      if (!binding)
        return testFailure(
            "owned soundness context lost a selected KZG binding");
      const snd::SoundnessRule *rule =
          environment.soundness->findRule(binding->ruleRef);
      if (ref.id == bindingId(kEbDbRule)) {
        environment.ebDbBinding = binding;
        environment.ebDbRule = rule;
      }
      if (ref.id == bindingId(kArsdhRule)) {
        environment.arsdhBinding = binding;
        environment.arsdhRule = rule;
      }
    }
    if (!environment.ebDbRule || !environment.arsdhRule ||
        !environment.ebDbBinding || !environment.arsdhBinding)
      return testFailure(
          "owned soundness context lost exact selected KZG declarations");
    return llvm::Error::success();
  }

  llvm::Error runOneGroup(ExactKzgEnvironment &environment,
                          cmp::CompilerSemanticContext &context,
                          cmp::CompilerRequest &request,
                          cmp::AuthenticatedArtifactHandle source) {
    if (llvm::Error declarations = populateSelectedDeclarations(environment))
      return declarations;
    auto transforms = environment.domain->enumerate(request, *source);
    if (!transforms)
      return transforms.takeError();
    if (transforms->size() != 2 || !transforms->front().applications.empty() ||
        transforms->back().applications.size() != 1)
      return testFailure(
          "one KZG group did not produce identity plus one transform");

    cmp::TransformApplication reordered =
        transforms->back().applications.front();
    std::reverse(reordered.matchedClaims.begin(),
                 reordered.matchedClaims.end());
    auto reorderedMatch = environment.family->recognize(source, reordered);
    if (reorderedMatch)
      return testFailure("reordered KZG claim vector unexpectedly recognized");
    llvm::consumeError(reorderedMatch.takeError());
    cmp::TransformPlan reorderedPlan = transforms->back();
    reorderedPlan.applications.front() = std::move(reordered);
    auto containsReordered =
        environment.domain->contains(request, *source, reorderedPlan);
    if (!containsReordered)
      return containsReordered.takeError();
    if (*containsReordered)
      return testFailure("KZG domain admitted a noncanonical claim ordering");

    cmp::TransformPlan alteredSpace = transforms->back();
    alteredSpace.applications.front()
        .parameters[cmp::samePointKzgBatchSpaceParameter().str()] =
        integerValue(17);
    auto containsAlteredSpace =
        environment.domain->contains(request, *source, alteredSpace);
    if (!containsAlteredSpace)
      return containsAlteredSpace.takeError();
    if (*containsAlteredSpace)
      return testFailure("KZG domain admitted an altered batch space");

    auto preview = cmp::realizeTransform(context, request, transforms->back());
    if (!preview)
      return preview.takeError();
    if (preview->finalArtifact->observation.verifierProofReads.size() != 1)
      return testFailure(
          "one-group KZG transform did not derive one final proof read");
    if (expectRoutes)
      if (llvm::Error error =
              requireRoutedSuccessor(source, preview->finalArtifact))
        return error;

    const snd::SealedReduction *reduction = nullptr;
    for (const auto &[position, candidate] :
         preview->finalArtifact->observation.soundness
             .reductionsByTransformerPosition) {
      (void)position;
      if (candidate.contractRef.id == kContract)
        reduction = &candidate;
    }
    if (!reduction || reduction->orderedInputs.size() != 2 ||
        reduction->orderedOutputs.size() != 1)
      return testFailure(
          "one-group KZG transform has no exact batch reduction");
    auto reductionPosition = preview->finalArtifact->observation.soundness
                                 .reductionsByTransformerPosition.find(
                                     reduction->transformerPosition);
    if (reductionPosition == preview->finalArtifact->observation.soundness
                                 .reductionsByTransformerPosition.end())
      return testFailure("batch reduction position is not canonical");

    const snd::ClaimRef batchOutput = reduction->orderedOutputs.front();
    snd::ReductionOccurrence occurrence{
        preview->finalArtifact->observation.artifactId, batchOutput,
        reduction->transformerPosition, 0};
    auto consumed = snd::resolveAllReductionInputs(
        preview->finalArtifact->observation.soundness, occurrence);
    if (!consumed)
      return consumed.takeError();
    const snd::SecurityJudgment assumption = sourceAssumption(*consumed);
    const snd::ApplicationSite site = occurrence;
    snd::SecuritySubject targetSubject;
    targetSubject.payload = snd::ProtocolClaimSubject{
        preview->finalArtifact->observation.artifactId, batchOutput};

    snd::DerivationPlan ebDbPlan =
        makePlan(site, environment.ebDbBinding->ref, assumption);
    snd::DerivationPlan arsdhPlan =
        makePlan(site, environment.arsdhBinding->ref, assumption);
    snd::DerivationTarget ebDbTarget{targetSubject,
                                     environment.ebDbRule->conclusionIndex,
                                     environment.ebDbRule->resources};
    snd::DerivationTarget arsdhTarget{targetSubject,
                                      environment.arsdhRule->conclusionIndex,
                                      environment.arsdhRule->resources};
    snd::DeriveOutcome ebDb = snd::deriveSoundness(
        *environment.soundness, preview->finalArtifact->observation.soundness,
        ebDbTarget, ebDbPlan);
    snd::DeriveOutcome arsdh = snd::deriveSoundness(
        *environment.soundness, preview->finalArtifact->observation.soundness,
        arsdhTarget, arsdhPlan);
    if (!ebDb.accepted() || !arsdh.accepted())
      return testFailure(
          "shared DERIVE rejected a selected KZG soundness alternative");
    const auto *ebDbResult =
        std::get_if<snd::ExtractionResult>(&rootConclusion(ebDb)->result);
    const auto *arsdhResult =
        std::get_if<snd::ExtractionResult>(&rootConclusion(arsdh)->result);
    if (!ebDbResult || !arsdhResult || !ebDbResult->failureBound ||
        !arsdhResult->failureBound ||
        ebDbResult->failureBound->primitiveGameTerms.size() != 2 ||
        arsdhResult->failureBound->primitiveGameTerms.size() != 1 ||
        !isInteger(
            arsdhResult->failureBound->primitiveGameTerms.front().coefficient,
            2))
      return testFailure(
          "KZG derivations have the wrong exact EB/DB or ARSDH bounds");

    std::vector<cmp::ListedDerivationAlternative> alternatives{
        {kTargetKey.str(), kEbDbSchema.str(), targetSubject, ebDbPlan},
        {kTargetKey.str(), kArsdhSchema.str(), targetSubject, arsdhPlan},
    };
    auto derivations =
        std::make_shared<const cmp::ListedDerivationPlanDomainProvider>(
            request.derivationPlanProviderRef, std::move(alternatives));
    context.derivationDomains[request.derivationPlanProviderRef.id] =
        derivations;

    cmp::RequestedTarget target;
    target.key = kTargetKey.str();
    target.orderedSourceClaims = source->observation.soundness.claimsByIndex;
    target.selector.kind = cmp::TargetSelectorKind::TransformOutputs;
    target.selector.familyRef = environment.family->exactRef();
    target.selector.outputRole = cmp::samePointKzgBatchOutputRole().str();
    target.admittedSchemaKeys = {kEbDbSchema.str(), kArsdhSchema.str()};
    request.targets.push_back(std::move(target));
    request.targetSchemas.push_back({kEbDbSchema.str(),
                                     environment.ebDbRule->conclusionIndex,
                                     environment.ebDbRule->resources});
    request.targetSchemas.push_back({kArsdhSchema.str(),
                                     environment.arsdhRule->conclusionIndex,
                                     environment.arsdhRule->resources});
    request.derivationSurface.allowedBindingRefs = {
        environment.ebDbBinding->ref, environment.arsdhBinding->ref};
    collectSurface(ebDb.result->root, request.derivationSurface);
    collectSurface(arsdh.result->root, request.derivationSurface);

    std::vector<snd::TypedDeclaration> comparisonResources =
        environment.ebDbRule->resources;
    comparisonResources.insert(comparisonResources.end(),
                               environment.arsdhRule->resources.begin(),
                               environment.arsdhRule->resources.end());
    cmp::CandidateTargetRead candidateRead;
    candidateRead.targetKey = kTargetKey.str();
    candidateRead.members = cmp::FoldTargetMembers{cmp::TargetFoldKind::Add};
    candidateRead.projection.kind = cmp::BoundProjectionKind::ExtractionFailure;
    candidateRead.resourceSubstitutions.emplace(
        kEbDbSchema.str(),
        identitySubstitution(environment.ebDbRule->resources));
    candidateRead.resourceSubstitutions.emplace(
        kArsdhSchema.str(),
        identitySubstitution(environment.arsdhRule->resources));
    cmp::BoundExpr candidate;
    candidate.payload = std::move(candidateRead);

    snd::ClosedBound ceiling = *ebDbResult->failureBound;
    snd::PrimitiveGameTerm arsdhCeiling =
        arsdhResult->failureBound->primitiveGameTerms.front();
    arsdhCeiling.coefficient = reg::Rational::fromInteger(1);
    ceiling.primitiveGameTerms.push_back(std::move(arsdhCeiling));
    request.soundnessConstraints.push_back(cmp::SoundnessConstraint{
        cmp::ComparisonDomain{std::move(comparisonResources)},
        std::move(candidate),
        cmp::BoundExpr{cmp::ZeroBound{}},
        std::move(ceiling),
    });

    auto planDomain = cmp::domain(context, request);
    if (!planDomain)
      return planDomain.takeError();
    if (planDomain->plans.size() != 3)
      return testFailure(
          "one-group compiler domain is not identity/EBDB/ARSDH");

    std::vector<std::optional<cmp::ScoredCandidate>> candidates;
    for (size_t ordinal = 0; ordinal < planDomain->plans.size(); ++ordinal) {
      auto valid = cmp::validate(context, request, *planDomain, ordinal);
      if (!valid) {
        llvm::consumeError(valid.takeError());
        candidates.push_back(std::nullopt);
        continue;
      }
      auto scored = cmp::score(context, request, *planDomain, ordinal);
      if (!scored)
        return scored.takeError();
      candidates.push_back(std::move(*scored));
    }
    if (!candidates[0] || !candidates[1] || candidates[2] ||
        !isInteger(candidates[0]->objectiveValues.front(), 96) ||
        !isInteger(candidates[1]->objectiveValues.front(), 48))
      return testFailure(
          "typed loss eligibility or exact KZG byte scores are wrong");
    if (candidates[1]->candidate.candidate.derivations.size() != 1 ||
        conclusionOf(candidates[1]
                         ->candidate.candidate.derivations.front()
                         .result.root) != *rootConclusion(ebDb))
      return testFailure(
          "compiler did not use the shared DERIVE result semantics");

    auto selection = cmp::select(context, request, *planDomain);
    if (!selection || selection->selectedOrdinal != 1)
      return selection ? testFailure(
                             "compiler did not deterministically select EB/DB")
                       : selection.takeError();
    cmp::CompilerResult result{selection->selectedOrdinal};
    auto verdict = cmp::checkDecision(context, request, result);
    if (!verdict)
      return verdict.takeError();
    if (!verdict->accepted)
      return testFailure(
          "decision checker rejected the exact real-provider result: " +
          verdict->detail);

    llvm::outs()
        << "PIR compiler one-group: identity + EB/DB + ARSDH\n"
        << "PIR compiler soundness: shared DERIVE, typed ceiling exact\n"
        << "PIR compiler objective: 96 -> 48 bytes\n"
        << "PIR compiler selection: EB/DB ordinal 1\n";
    if (expectRoutes)
      llvm::outs() << "PIR compiler routed successor: routes and HoleContract "
                      "citation re-admitted\n";
    return llvm::Error::success();
  }

  llvm::Error runTwoGroups(ExactKzgEnvironment &environment,
                           cmp::CompilerSemanticContext &context,
                           cmp::CompilerRequest &request,
                           cmp::AuthenticatedArtifactHandle source) {
    auto transformPlans = environment.domain->enumerate(request, *source);
    if (!transformPlans)
      return transformPlans.takeError();
    if (transformPlans->size() != 4 ||
        transformPlans->back().applications.size() != 2)
      return testFailure(
          "two KZG groups did not produce four canonical combinations");
    auto exactClaims = [](const cmp::TransformApplication &application,
                          llvm::ArrayRef<snd::ClaimRef> expected) {
      return llvm::equal(application.matchedClaims, expected);
    };
    llvm::ArrayRef<snd::ClaimRef> sourceClaims =
        source->observation.soundness.claimsByIndex;
    if (!transformPlans->at(0).applications.empty() ||
        transformPlans->at(1).applications.size() != 1 ||
        transformPlans->at(2).applications.size() != 1 ||
        transformPlans->at(3).applications.size() != 2 ||
        !exactClaims(transformPlans->at(1).applications.front(),
                     sourceClaims.take_front(2)) ||
        !exactClaims(transformPlans->at(2).applications.front(),
                     sourceClaims.slice(2, 2)) ||
        !applicationEqual(transformPlans->at(3).applications.front(),
                          transformPlans->at(1).applications.front()) ||
        !exactClaims(transformPlans->at(3).applications.back(),
                     sourceClaims.slice(2, 2)))
      return testFailure(
          "two-group domain ordinals are not identity, first, second, pair");
    for (const cmp::TransformApplication &application :
         transformPlans->back().applications) {
      if (application.parameters.size() != 1 ||
          application.parameters.begin()->first !=
              cmp::samePointKzgBatchSpaceParameter() ||
          !exactIntegerValue(application.parameters.begin()->second,
                             fieldOrder()))
        return testFailure(
            "multi-application plan lost its exact batch-space parameter");
    }

    auto planDomain = cmp::domain(context, request);
    if (!planDomain)
      return planDomain.takeError();
    if (planDomain->plans.size() != 4)
      return testFailure("CompilerCore changed the two-group transform domain");
    auto trace = cmp::realizeTransform(context, request,
                                       planDomain->plans.back().transform);
    if (!trace)
      return trace.takeError();
    if (trace->finalArtifact->observation.verifierProofReads.size() != 2)
      return testFailure(
          "two sequential batches did not derive two final proof reads");

    for (const snd::ClaimRef &second :
         planDomain->plans.back().transform.applications[1].matchedClaims) {
      bool cameFromCheckedSurvivor = false;
      for (const cmp::ClaimCorrespondence &correspondence :
           trace->correspondences)
        if (correspondence.applicationIndex == 0 &&
            correspondence.orderedConsumed.size() == 1 &&
            correspondence.orderedProduced.size() == 1 &&
            correspondence.orderedProduced.front().outputRole ==
                cmp::transformSurvivorOutputRole() &&
            correspondence.orderedProduced.front().claim == second)
          cameFromCheckedSurvivor = true;
      if (!cameFromCheckedSurvivor)
        return testFailure(
            "second application was not named through the checked "
            "intermediate survivor namespace");
    }

    size_t batchReductions = 0;
    for (const auto &[position, reduction] :
         trace->finalArtifact->observation.soundness
             .reductionsByTransformerPosition) {
      (void)position;
      if (reduction.contractRef.id == kContract)
        ++batchReductions;
    }
    if (batchReductions != 2)
      return testFailure(
          "two-step realization has the wrong final batch reductions");

    auto identity = cmp::validate(context, request, *planDomain, 0);
    if (!identity)
      return identity.takeError();
    auto full = cmp::validate(context, request, *planDomain, 3);
    if (!full)
      return full.takeError();
    auto identityScore = cmp::score(context, request, *planDomain, 0);
    if (!identityScore)
      return identityScore.takeError();
    auto fullScore = cmp::score(context, request, *planDomain, 3);
    if (!fullScore)
      return fullScore.takeError();
    if (!isInteger(identityScore->objectiveValues.front(), 192) ||
        !isInteger(fullScore->objectiveValues.front(), 96))
      return testFailure(
          "two-group static proof-byte scores are not source-derived");

    cmp::CompilerRequest oneApplication = request;
    oneApplication.limits.maxTransformApplications = 1;
    auto bounded = environment.domain->enumerate(oneApplication, *source);
    if (!bounded)
      return bounded.takeError();
    if (bounded->size() != 3 ||
        llvm::any_of(*bounded, [](const cmp::TransformPlan &plan) {
          return plan.applications.size() > 1;
        }))
      return testFailure(
          "KZG domain did not respect the application-count bound");

    cmp::CompilerRequest tooFewPlans = request;
    tooFewPlans.limits.maxDomainPlans = 3;
    auto overflow = environment.domain->enumerate(tooFewPlans, *source);
    if (overflow)
      return testFailure("KZG domain exceeded the exact finite plan bound");
    llvm::consumeError(overflow.takeError());

    auto contains =
        environment.domain->contains(request, *source, transformPlans->back());
    if (!contains)
      return contains.takeError();
    if (!*contains)
      return testFailure("KZG domain rejected its canonical sequential plan");

    cmp::TransformPlan reversed = transformPlans->back();
    std::reverse(reversed.applications.begin(), reversed.applications.end());
    auto containsReversed =
        environment.domain->contains(request, *source, reversed);
    if (!containsReversed)
      return containsReversed.takeError();
    if (*containsReversed)
      return testFailure("KZG domain admitted a reversed application sequence");

    llvm::outs()
        << "PIR compiler two-group: 4 canonical combinations\n"
        << "PIR compiler namespace: second application uses checked survivors\n"
        << "PIR compiler multi-step: 192 -> 96 bytes\n"
        << "PIR compiler bounds: application and plan limits exact\n";
    return llvm::Error::success();
  }
};

} // namespace

namespace zkc::test {
void registerTestPirCompilerProviderPass() {
  PassRegistration<TestPirCompilerProviderPass>();
}
} // namespace zkc::test
