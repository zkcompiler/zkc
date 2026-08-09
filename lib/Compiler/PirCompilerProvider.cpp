//===- PirCompilerProvider.cpp - exact PIR compiler providers ------------===//

#include "zkc/Compiler/PirCompilerProvider.h"

#include "Dialect/Pir/Transforms/ProtocolArtifacts.h"
#include "zkc/Dialect/Pir/Transforms/KzgBatchOpen.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Registry/ProtocolEnvironment.h"
#include "zkc/Semantics/SealEngine.h"
#include "zkc/Soundness/PirSoundnessAdapter.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace mlir;

namespace zkc::compiler {

namespace {

constexpr llvm::StringLiteral kBatchSpace = "batch_space";
constexpr llvm::StringLiteral kBatchOutputRole = "batch_opening";
constexpr llvm::StringLiteral kSurvivorOutputRole = "survivor";

template <typename T> llvm::Expected<T> providerError(const llvm::Twine &text) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), text);
}

llvm::json::Value exactRefJson(const ExactRef &ref) {
  return llvm::json::Array{ref.id, ref.sourceRevision};
}

ExactRef configuredRef(const ExactRef &implementation, llvm::StringRef domain,
                       llvm::json::Value configuration) {
  llvm::json::Object preimage{
      {"implementation", exactRefJson(implementation)},
      {"configuration", std::move(configuration)},
  };
  return {
      implementation.id,
      llvm::cantFail(encoding::taggedSha256Ref(
          domain, llvm::json::Value(std::move(preimage)))),
  };
}

ExactRef
configuredSemanticsRef(const registry::ProtocolEnvironment &environment) {
  llvm::json::Object configuration{
      {"payload_type", exactRefJson(pirSealedPayloadV1Ref())},
      {"registries", environment.compilerConfiguration()},
  };
  return configuredRef(pirArtifactSemanticsV1Ref(),
                       "zkc/compiler/pir-artifact-semantics-config\n",
                       llvm::json::Value(std::move(configuration)));
}

llvm::Error
requireSameEnvironment(const registry::ProtocolEnvironment &admitted,
                       const registry::ProtocolEnvironment &compiler) {
  auto admittedBytes =
      encoding::canonicalJsonBytes(admitted.compilerConfiguration());
  if (!admittedBytes)
    return admittedBytes.takeError();
  auto compilerBytes =
      encoding::canonicalJsonBytes(compiler.compilerConfiguration());
  if (!compilerBytes)
    return compilerBytes.takeError();
  if (*admittedBytes != *compilerBytes)
    return llvm::createStringError(
        "admitted PIR artifact belongs to a different compiler environment");
  return llvm::Error::success();
}

ExactRef configuredFamilyRef(const PirArtifactSemantics *semantics) {
  llvm::json::Object configuration;
  configuration["artifact_semantics"] =
      semantics ? exactRefJson(semantics->exactRef())
                : llvm::json::Value(nullptr);
  return configuredRef(samePointKzgBatchV1Ref(),
                       "zkc/compiler/same-point-kzg-family-config\n",
                       llvm::json::Value(std::move(configuration)));
}

ExactRef configuredDomainRef(const PirArtifactSemantics *semantics,
                             const registry::Rational &batchSpace) {
  llvm::json::Object configuration{
      {"family", exactRefJson(configuredFamilyRef(semantics))},
      {"batch_space", batchSpace.str()},
  };
  return configuredRef(samePointKzgBatchDomainV1Ref(),
                       "zkc/compiler/same-point-kzg-domain-config\n",
                       llvm::json::Value(std::move(configuration)));
}

bool positiveInteger(const registry::Rational &value) {
  return value.denStr() == "1" &&
         value.compare(registry::Rational::fromInteger(0)) > 0;
}

llvm::Expected<const PirArtifactPayload *>
typedPayload(const OwnedCompilerArtifact &artifact,
             const PirArtifactSemantics &semantics) {
  if (artifact.artifactSemanticsRef != semantics.exactRef() ||
      !artifact.adapterPayload ||
      artifact.adapterPayload->exactTypeRef() != semantics.payloadTypeRef())
    return providerError<const PirArtifactPayload *>(
        "artifact is not authorized by the exact PIR representation provider");
  const auto *payload =
      artifactPayloadAs<PirArtifactPayload>(*artifact.adapterPayload);
  if (!payload)
    return providerError<const PirArtifactPayload *>(
        "artifact payload has the wrong immutable C++ representation");
  return payload;
}

llvm::Expected<AuthenticatedArtifactHandle>
authenticateForProvider(ArtifactHandle artifact,
                        const PirArtifactSemantics &semantics) {
  return semantics.authenticateArtifact(std::move(artifact));
}

struct OpenArtifact {
  artifact::detail::MutablePirArtifact storage;
  pir::ProtocolOp protocol;
};

llvm::Expected<OpenArtifact>
openArtifact(const OwnedCompilerArtifact &artifact,
             const PirArtifactSemantics &semantics) {
  auto payload = typedPayload(artifact, semantics);
  if (!payload)
    return payload.takeError();
  auto opened = pir::openAdmittedProtocolForTransform((*payload)->artifact());
  if (!opened)
    return opened.takeError();
  auto protocols = opened->module().getOps<pir::ProtocolOp>();
  if (!llvm::hasSingleElement(protocols))
    return providerError<OpenArtifact>(
        "reopened PIR artifact must contain exactly one open protocol");
  return OpenArtifact{std::move(*opened), *protocols.begin()};
}

soundness::ClaimRef compilerClaim(const pir::KzgBatchOpenClaimRef &claim) {
  return {claim.claimIndex, claim.descriptorDigest};
}

pir::KzgBatchOpenClaimRef kzgClaim(const soundness::ClaimRef &claim) {
  return {claim.claimIndex, claim.descriptorDigest};
}

soundness::ExactScalarValue
batchSpaceValue(const registry::Rational &batchSpace) {
  soundness::ExactScalarValue value;
  value.sort = soundness::ValueSort::Integer;
  value.payload = batchSpace;
  return value;
}

llvm::Expected<registry::Rational> readBatchSpace(
    const std::map<std::string, soundness::ExactScalarValue, std::less<>>
        &parameters) {
  if (parameters.size() != 1)
    return providerError<registry::Rational>(
        "same-point KZG requires exactly the batch_space parameter");
  auto found = parameters.find(kBatchSpace.str());
  if (found == parameters.end() ||
      found->second.sort != soundness::ValueSort::Integer)
    return providerError<registry::Rational>(
        "same-point KZG batch_space is not an exact integer");
  const auto *value = std::get_if<registry::Rational>(&found->second.payload);
  if (!value || !positiveInteger(*value))
    return providerError<registry::Rational>(
        "same-point KZG batch_space must be a positive exact integer");
  return *value;
}

bool applicationsEqual(const TransformApplication &left,
                       const TransformApplication &right) {
  return left.familyRef == right.familyRef &&
         left.matchedClaims == right.matchedClaims &&
         left.parameters == right.parameters;
}

bool plansEqual(const TransformPlan &left, const TransformPlan &right) {
  if (left.applications.size() != right.applications.size())
    return false;
  for (size_t index = 0; index < left.applications.size(); ++index)
    if (!applicationsEqual(left.applications[index], right.applications[index]))
      return false;
  return true;
}

llvm::Expected<pir::KzgBatchOpenApplication>
recognizeCanonical(pir::ProtocolOp protocol,
                   const std::vector<soundness::ClaimRef> &claims) {
  std::vector<pir::KzgBatchOpenClaimRef> ordered;
  ordered.reserve(claims.size());
  for (const soundness::ClaimRef &claim : claims)
    ordered.push_back(kzgClaim(claim));
  return pir::recognizeSamePointKzgBatchOpenApplication(protocol, ordered);
}

llvm::Expected<const soundness::SealedReduction *>
findBatchReduction(const soundness::SealedSoundnessView &after,
                   const CanonicalTransformApplication &canonical) {
  const soundness::SealedReduction *match = nullptr;
  for (const auto &[position, reduction] :
       after.reductionsByTransformerPosition) {
    (void)position;
    if (reduction.contractRef.id != "kzg_batch" ||
        reduction.orderedInputs != canonical.orderedConsumed)
      continue;
    if (match)
      return providerError<const soundness::SealedReduction *>(
          "replay-checked KZG result has multiple primary batch reductions");
    match = &reduction;
  }
  if (!match || match->orderedOutputs.size() != 1)
    return providerError<const soundness::SealedReduction *>(
        "replay-checked KZG result has no unique primary batch output");
  return match;
}

llvm::Expected<std::vector<ClaimCorrespondence>>
buildCorrespondences(const AuthenticatedCompilerArtifact &before,
                     const AuthenticatedCompilerArtifact &after,
                     const CanonicalTransformApplication &canonical,
                     uint64_t applicationIndex,
                     const soundness::ClaimRef &batchOutput) {
  std::vector<ClaimCorrespondence> result;
  result.push_back({applicationIndex,
                    canonical.familyRef,
                    canonical.orderedConsumed,
                    {{batchOutput, kBatchOutputRole.str()}}});

  std::set<uint64_t> consumed;
  for (const soundness::ClaimRef &claim : canonical.orderedConsumed)
    consumed.insert(claim.claimIndex);

  std::map<std::string, std::vector<soundness::ClaimRef>, std::less<>>
      beforeByDigest;
  for (const soundness::ClaimRef &claim :
       before.observation.soundness.claimsByIndex)
    if (!consumed.count(claim.claimIndex))
      beforeByDigest[claim.descriptorDigest].push_back(claim);

  std::map<std::string, std::vector<soundness::ClaimRef>, std::less<>>
      afterByDigest;
  for (const soundness::ClaimRef &claim :
       after.observation.soundness.claimsByIndex) {
    if (claim == batchOutput ||
        std::find(canonical.orderedConsumed.begin(),
                  canonical.orderedConsumed.end(),
                  claim) != canonical.orderedConsumed.end())
      continue;
    afterByDigest[claim.descriptorDigest].push_back(claim);
  }
  if (beforeByDigest.size() != afterByDigest.size())
    return providerError<std::vector<ClaimCorrespondence>>(
        "replay-checked KZG result changed the survivor descriptor set");

  for (const auto &[digest, predecessors] : beforeByDigest) {
    auto successors = afterByDigest.find(digest);
    if (successors == afterByDigest.end() ||
        successors->second.size() != predecessors.size())
      return providerError<std::vector<ClaimCorrespondence>>(
          "replay-checked KZG result changed survivor multiplicity");
    for (size_t index = 0; index < predecessors.size(); ++index)
      result.push_back(
          {applicationIndex,
           canonical.familyRef,
           {predecessors[index]},
           {{successors->second[index], kSurvivorOutputRole.str()}}});
  }
  return result;
}

} // namespace

const ExactRef &pirArtifactSemanticsV1Ref() {
  static const ExactRef ref{"pir_artifact", "zkc.compiler.artifact-semantics"};
  return ref;
}

const ExactRef &pirSealedPayloadV1Ref() {
  static const ExactRef ref{"pir_sealed_module",
                            "zkc.compiler.artifact-payload"};
  return ref;
}

const ExactRef &samePointKzgBatchV1Ref() {
  static const ExactRef ref{"same_point_kzg_batch",
                            "zkc.compiler.transform-family"};
  return ref;
}

const ExactRef &samePointKzgBatchDomainV1Ref() {
  static const ExactRef ref{"same_point_kzg_batch_domain",
                            "zkc.compiler.transform-domain"};
  return ref;
}

llvm::StringRef samePointKzgBatchSpaceParameter() { return kBatchSpace; }

llvm::StringRef samePointKzgBatchOutputRole() { return kBatchOutputRole; }

llvm::StringRef transformSurvivorOutputRole() { return kSurvivorOutputRole; }

PirArtifactSemantics::PirArtifactSemantics(
    registry::ProtocolEnvironment environment)
    : environment_(std::move(environment)),
      ref_(configuredSemanticsRef(environment_)) {}

llvm::Expected<AuthenticatedArtifactObservation>
PirArtifactSemantics::authenticate(const ArtifactPayload &payload) const {
  if (payload.exactTypeRef() != payloadTypeRef())
    return providerError<AuthenticatedArtifactObservation>(
        "PIR semantics received the wrong payload type");
  const auto *typed = artifactPayloadAs<PirArtifactPayload>(payload);
  if (!typed)
    return providerError<AuthenticatedArtifactObservation>(
        "PIR semantics received a differently typed immutable payload");
  if (llvm::Error error =
          requireSameEnvironment(typed->artifact().environment(), environment_))
    return std::move(error);

  auto view = soundness::buildSealedSoundnessView(typed->artifact());
  if (!view)
    return view.takeError();
  auto observed = pir::deriveVerifierProofReads(typed->artifact());
  if (!observed)
    return observed.takeError();

  AuthenticatedArtifactObservation result;
  result.artifactId = view->artifactId;
  result.soundness = std::move(*view);
  for (const pir::VerifierProofReadObservation &read : *observed)
    result.verifierProofReads.push_back(
        {read.payloadClass, {read.codecId, read.codecDigest}, read.count});
  return result;
}

llvm::Expected<ArtifactHandle> PirArtifactSemantics::createArtifact(
    artifact::AdmittedPirArtifact admitted) const {
  if (llvm::Error error =
          requireSameEnvironment(admitted.environment(), environment_))
    return std::move(error);
  PirArtifactPayload typed(std::move(admitted));
  auto payload = makeArtifactPayload(payloadTypeRef(), std::move(typed));
  return std::make_shared<const OwnedCompilerArtifact>(exactRef(),
                                                       std::move(payload));
}

SamePointKzgBatchTransformFamily::SamePointKzgBatchTransformFamily(
    std::shared_ptr<const PirArtifactSemantics> semantics)
    : semantics_(std::move(semantics)),
      artifactSemanticsRef_(semantics_ ? semantics_->exactRef() : ExactRef{}),
      ref_(configuredFamilyRef(semantics_.get())) {}

llvm::Expected<CanonicalTransformApplication>
SamePointKzgBatchTransformFamily::recognize(
    AuthenticatedArtifactHandle before,
    const TransformApplication &requested) const {
  if (!semantics_ || !before || requested.familyRef != exactRef())
    return providerError<CanonicalTransformApplication>(
        "same-point KZG recognize lacks its exact family, semantics, or "
        "predecessor");
  auto batchSpace = readBatchSpace(requested.parameters);
  if (!batchSpace)
    return batchSpace.takeError();
  auto opened = openArtifact(*before->artifact, *semantics_);
  if (!opened)
    return opened.takeError();
  auto recognized =
      recognizeCanonical(opened->protocol, requested.matchedClaims);
  if (!recognized)
    return recognized.takeError();

  CanonicalTransformApplication canonical;
  canonical.familyRef = exactRef();
  for (const pir::KzgBatchOpenClaimRef &claim : recognized->orderedClaims)
    canonical.orderedConsumed.push_back(compilerClaim(claim));
  canonical.parameters = requested.parameters;
  return canonical;
}

llvm::Expected<ArtifactHandle> SamePointKzgBatchTransformFamily::realize(
    AuthenticatedArtifactHandle before,
    const CanonicalTransformApplication &canonical) const {
  if (!semantics_ || !before || canonical.familyRef != exactRef())
    return providerError<ArtifactHandle>(
        "same-point KZG realize lacks its exact family, semantics, or "
        "predecessor");
  auto batchSpace = readBatchSpace(canonical.parameters);
  if (!batchSpace)
    return batchSpace.takeError();
  const registry::ProtocolEnvironment &environment = semantics_->environment();
  auto opened = openArtifact(*before->artifact, *semantics_);
  if (!opened)
    return opened.takeError();
  auto recognized =
      recognizeCanonical(opened->protocol, canonical.orderedConsumed);
  if (!recognized)
    return recognized.takeError();
  std::vector<soundness::ClaimRef> recognizedClaims;
  for (const pir::KzgBatchOpenClaimRef &claim : recognized->orderedClaims)
    recognizedClaims.push_back(compilerClaim(claim));
  if (recognizedClaims != canonical.orderedConsumed)
    return providerError<ArtifactHandle>(
        "same-point KZG canonical application changed on its predecessor");

  auto realized = pir::realizeSamePointKzgBatchOpenApplication(
      opened->protocol, *recognized, batchSpace->str());
  if (!realized)
    return realized.takeError();
  auto sealed = semantics::SealEngine(environment).seal(opened->protocol);
  if (failed(sealed))
    return providerError<ArtifactHandle>(
        "same-point KZG successor failed the protocol seal judgment");
  auto snapshot = artifact::snapshotArtifact(*sealed);
  if (!snapshot)
    return snapshot.takeError();
  auto admitted = artifact::admitArtifact(std::move(*snapshot), environment);
  if (!admitted)
    return admitted.takeError();
  return semantics_->createArtifact(std::move(*admitted));
}

llvm::Expected<std::vector<ClaimCorrespondence>>
SamePointKzgBatchTransformFamily::check(
    AuthenticatedArtifactHandle before, AuthenticatedArtifactHandle after,
    const CanonicalTransformApplication &canonical,
    uint64_t applicationIndex) const {
  if (!semantics_ || !before || !after || canonical.familyRef != exactRef())
    return providerError<std::vector<ClaimCorrespondence>>(
        "same-point KZG check lacks its exact family, semantics, or artifacts");
  auto batchSpace = readBatchSpace(canonical.parameters);
  if (!batchSpace)
    return batchSpace.takeError();
  auto openedBefore = openArtifact(*before->artifact, *semantics_);
  if (!openedBefore)
    return openedBefore.takeError();
  auto recognized =
      recognizeCanonical(openedBefore->protocol, canonical.orderedConsumed);
  if (!recognized)
    return recognized.takeError();
  auto replay = pir::realizeSamePointKzgBatchOpenApplication(
      openedBefore->protocol, *recognized, batchSpace->str());
  if (!replay)
    return replay.takeError();
  const registry::ProtocolEnvironment &environment = semantics_->environment();
  auto replaySealed =
      semantics::SealEngine(environment).seal(openedBefore->protocol);
  if (failed(replaySealed))
    return providerError<std::vector<ClaimCorrespondence>>(
        "same-point KZG deterministic replay failed to seal");
  auto afterPayload = typedPayload(*after->artifact, *semantics_);
  if (!afterPayload)
    return afterPayload.takeError();
  if ((*replaySealed).getId() != (*afterPayload)->artifact().id())
    return providerError<std::vector<ClaimCorrespondence>>(
        "same-point KZG deterministic replay rejected the successor");

  auto batchReduction =
      findBatchReduction(after->observation.soundness, canonical);
  if (!batchReduction)
    return batchReduction.takeError();
  return buildCorrespondences(*before, *after, canonical, applicationIndex,
                              (*batchReduction)->orderedOutputs.front());
}

namespace {

/// Advance source-claim identities through one checked application.  Domain
/// plans name claims in each application's actual predecessor namespace, not
/// forever in the source namespace.  KZG source claims are currently a stable
/// canonical prefix, but deriving the next namespace from checked survivor
/// correspondences keeps that representation fact out of domain semantics.
llvm::Expected<std::vector<std::optional<soundness::ClaimRef>>>
remapSourceClaims(
    const std::vector<std::optional<soundness::ClaimRef>> &currentBySource,
    const CanonicalTransformApplication &canonical,
    llvm::ArrayRef<ClaimCorrespondence> correspondences,
    uint64_t applicationIndex) {
  size_t primaryCount = 0;
  std::map<uint64_t, std::pair<soundness::ClaimRef, soundness::ClaimRef>>
      survivorByPredecessorIndex;
  for (const ClaimCorrespondence &correspondence : correspondences) {
    if (correspondence.applicationIndex != applicationIndex ||
        correspondence.familyRef != canonical.familyRef)
      return providerError<std::vector<std::optional<soundness::ClaimRef>>>(
          "checked KZG correspondence changed its application identity");
    if (correspondence.orderedConsumed == canonical.orderedConsumed) {
      ++primaryCount;
      continue;
    }
    if (correspondence.orderedConsumed.size() != 1 ||
        correspondence.orderedProduced.size() != 1 ||
        correspondence.orderedProduced.front().outputRole !=
            kSurvivorOutputRole)
      return providerError<std::vector<std::optional<soundness::ClaimRef>>>(
          "checked KZG survivor correspondence is not one exact remap");
    const soundness::ClaimRef &predecessor =
        correspondence.orderedConsumed.front();
    if (!survivorByPredecessorIndex
             .emplace(
                 predecessor.claimIndex,
                 std::make_pair(predecessor,
                                correspondence.orderedProduced.front().claim))
             .second)
      return providerError<std::vector<std::optional<soundness::ClaimRef>>>(
          "checked KZG correspondences remap one predecessor twice");
  }
  if (primaryCount != 1)
    return providerError<std::vector<std::optional<soundness::ClaimRef>>>(
        "checked KZG correspondences have no unique primary merge");

  std::vector<std::optional<soundness::ClaimRef>> next = currentBySource;
  for (std::optional<soundness::ClaimRef> &current : next) {
    if (!current)
      continue;
    if (llvm::is_contained(canonical.orderedConsumed, *current)) {
      current.reset();
      continue;
    }
    auto successor = survivorByPredecessorIndex.find(current->claimIndex);
    if (successor == survivorByPredecessorIndex.end() ||
        successor->second.first != *current)
      return providerError<std::vector<std::optional<soundness::ClaimRef>>>(
          "checked KZG correspondences omit a live source survivor");
    current = successor->second.second;
  }
  return next;
}

llvm::Expected<TransformPlan> buildSequentialPlan(
    const CompilerRequest &request, const AuthenticatedCompilerArtifact &source,
    llvm::ArrayRef<pir::KzgBatchOpenApplication> discovered,
    llvm::ArrayRef<size_t> chosen,
    const std::shared_ptr<const PirArtifactSemantics> &semantics,
    const registry::Rational &batchSpace) {
  if (!request.source || request.source != source.artifact)
    return providerError<TransformPlan>(
        "KZG domain source is not the request-owned source artifact");

  std::vector<std::optional<soundness::ClaimRef>> currentBySource;
  currentBySource.reserve(source.observation.soundness.claimsByIndex.size());
  for (const soundness::ClaimRef &claim :
       source.observation.soundness.claimsByIndex)
    currentBySource.push_back(claim);

  SamePointKzgBatchTransformFamily family(semantics);
  TransformPlan plan;
  auto authenticatedSource =
      authenticateForProvider(source.artifact, *semantics);
  if (!authenticatedSource)
    return authenticatedSource.takeError();
  AuthenticatedArtifactHandle predecessor = std::move(*authenticatedSource);
  for (auto [applicationIndex, discoveredIndex] : llvm::enumerate(chosen)) {
    if (discoveredIndex >= discovered.size())
      return providerError<TransformPlan>(
          "KZG domain selected an unknown discovered group");

    TransformApplication requested;
    requested.familyRef = family.exactRef();
    requested.parameters.emplace(kBatchSpace.str(),
                                 batchSpaceValue(batchSpace));
    for (const pir::KzgBatchOpenClaimRef &sourceClaim :
         discovered[discoveredIndex].orderedClaims) {
      if (sourceClaim.claimIndex >= currentBySource.size() ||
          source.observation.soundness.claimsByIndex[sourceClaim.claimIndex] !=
              compilerClaim(sourceClaim) ||
          !currentBySource[sourceClaim.claimIndex])
        return providerError<TransformPlan>(
            "KZG domain cannot map a discovered source claim into its "
            "sequential predecessor");
      requested.matchedClaims.push_back(
          *currentBySource[sourceClaim.claimIndex]);
    }

    auto canonical = family.recognize(predecessor, requested);
    if (!canonical)
      return canonical.takeError();
    auto successor = family.realize(predecessor, *canonical);
    if (!successor)
      return successor.takeError();
    auto authenticatedSuccessor =
        authenticateForProvider(*successor, *semantics);
    if (!authenticatedSuccessor)
      return authenticatedSuccessor.takeError();
    auto correspondences = family.check(predecessor, *authenticatedSuccessor,
                                        *canonical, applicationIndex);
    if (!correspondences)
      return correspondences.takeError();
    auto remapped = remapSourceClaims(currentBySource, *canonical,
                                      *correspondences, applicationIndex);
    if (!remapped)
      return remapped.takeError();

    plan.applications.push_back(std::move(requested));
    currentBySource = std::move(*remapped);
    predecessor = std::move(*authenticatedSuccessor);
  }
  return plan;
}

} // namespace

SamePointKzgBatchTransformDomainProvider::
    SamePointKzgBatchTransformDomainProvider(
        std::shared_ptr<const PirArtifactSemantics> semantics,
        registry::Rational batchSpace)
    : semantics_(std::move(semantics)),
      artifactSemanticsRef_(semantics_ ? semantics_->exactRef() : ExactRef{}),
      batchSpace_(std::move(batchSpace)),
      ref_(configuredDomainRef(semantics_.get(), batchSpace_)) {}

llvm::Expected<std::vector<TransformPlan>>
SamePointKzgBatchTransformDomainProvider::enumerate(
    const CompilerRequest &request,
    const AuthenticatedCompilerArtifact &source) const {
  if (!semantics_ || !positiveInteger(batchSpace_))
    return providerError<std::vector<TransformPlan>>(
        "same-point KZG domain lacks exact semantics or positive batch space");
  auto opened = openArtifact(*source.artifact, *semantics_);
  if (!opened)
    return opened.takeError();
  auto discovered =
      pir::discoverSamePointKzgBatchOpenApplications(opened->protocol);
  if (!discovered)
    return discovered.takeError();

  std::set<uint64_t> allClaims;
  for (const pir::KzgBatchOpenApplication &application : *discovered)
    for (const pir::KzgBatchOpenClaimRef &claim : application.orderedClaims)
      if (!allClaims.insert(claim.claimIndex).second)
        return providerError<std::vector<TransformPlan>>(
            "discovered same-point KZG groups are not pairwise disjoint");

  std::vector<TransformPlan> result(1);
  if (result.size() > request.limits.maxDomainPlans)
    return providerError<std::vector<TransformPlan>>(
        "same-point KZG identity exceeds the finite domain-plan bound");
  const size_t maximum = std::min<size_t>(
      discovered->size(), request.limits.maxTransformApplications);

  std::vector<size_t> chosen;
  auto appendCombinations = [&](auto &&self, size_t start,
                                size_t remaining) -> llvm::Error {
    if (remaining == 0) {
      auto plan = buildSequentialPlan(request, source, *discovered, chosen,
                                      semantics_, batchSpace_);
      if (!plan)
        return plan.takeError();
      result.push_back(std::move(*plan));
      if (result.size() > request.limits.maxDomainPlans)
        return llvm::createStringError(
            "same-point KZG combinations exceed the finite domain-plan bound");
      return llvm::Error::success();
    }
    for (size_t index = start; index + remaining <= discovered->size();
         ++index) {
      chosen.push_back(index);
      if (llvm::Error error = self(self, index + 1, remaining - 1))
        return error;
      chosen.pop_back();
    }
    return llvm::Error::success();
  };
  for (size_t count = 1; count <= maximum; ++count)
    if (llvm::Error error = appendCombinations(appendCombinations, /*start=*/0,
                                               /*remaining=*/count))
      return std::move(error);
  return result;
}

llvm::Expected<bool> SamePointKzgBatchTransformDomainProvider::contains(
    const CompilerRequest &request, const AuthenticatedCompilerArtifact &source,
    const TransformPlan &plan) const {
  auto plans = enumerate(request, source);
  if (!plans)
    return plans.takeError();
  return llvm::any_of(*plans, [&](const TransformPlan &candidate) {
    return plansEqual(candidate, plan);
  });
}

} // namespace zkc::compiler
