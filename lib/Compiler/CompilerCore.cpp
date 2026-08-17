//===- CompilerCore.cpp - Closed compiler selection semantics -------------===//
#include "zkc/Compiler/CompilerCore.h"
#include "zkc/Soundness/KernelPredicates.h"

#include "CompilerCoreInternal.h"

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <set>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>

namespace zkc::compiler {
namespace {

/// A candidate-local semantic refusal. This error type is used only to carry
/// an explicitly classified refusal through the existing stage helpers; the
/// selection boundary converts it to a value outcome. All other errors remain
/// operational failures and propagate to the caller.
class CandidateIneligibleError final
    : public llvm::ErrorInfo<CandidateIneligibleError> {
public:
  static char ID;

  explicit CandidateIneligibleError(std::string detail)
      : detail_(std::move(detail)) {}

  void log(llvm::raw_ostream &stream) const override { stream << detail_; }
  std::error_code convertToErrorCode() const override {
    return llvm::inconvertibleErrorCode();
  }

private:
  std::string detail_;
};

char CandidateIneligibleError::ID = 0;

template <typename T>
llvm::Expected<T> candidateIneligible(const llvm::Twine &message) {
  return llvm::make_error<CandidateIneligibleError>(message.str());
}

llvm::Error candidateIneligibleFailure(const llvm::Twine &message) {
  return llvm::make_error<CandidateIneligibleError>(message.str());
}

template <typename T> llvm::Expected<T> error(const llvm::Twine &message) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), message);
}

llvm::Error failure(const llvm::Twine &message) {
  return llvm::createStringError(llvm::inconvertibleErrorCode(), message);
}

bool siteEqual(const soundness::ApplicationSite &lhs,
               const soundness::ApplicationSite &rhs) {
  if (lhs.index() != rhs.index())
    return false;
  if (const auto *left = std::get_if<soundness::ReductionOccurrence>(&lhs)) {
    const auto &right = std::get<soundness::ReductionOccurrence>(rhs);
    return left->artifactId == right.artifactId &&
           left->ownerClaim == right.ownerClaim &&
           left->transformerPosition == right.transformerPosition &&
           left->outputIndex == right.outputIndex;
  }
  const auto &left = std::get<soundness::PathOccurrence>(lhs);
  const auto &right = std::get<soundness::PathOccurrence>(rhs);
  return left.artifactId == right.artifactId && left.claim == right.claim;
}

using PlanPair = std::pair<const soundness::DerivationPlan *,
                           const soundness::DerivationPlan *>;

struct PlanPairLess {
  bool operator()(const PlanPair &lhs, const PlanPair &rhs) const {
    return std::tie(lhs.first, lhs.second) < std::tie(rhs.first, rhs.second);
  }
};

bool plansEqualImpl(const soundness::DerivationPlan &lhs,
                    const soundness::DerivationPlan &rhs,
                    std::set<PlanPair, PlanPairLess> &active,
                    std::set<PlanPair, PlanPairLess> &done) {
  PlanPair pair{&lhs, &rhs};
  if (done.count(pair))
    return true;
  if (!active.insert(pair).second)
    return false;
  if (lhs.node.index() != rhs.node.index()) {
    active.erase(pair);
    return false;
  }
  if (const auto *left =
          std::get_if<soundness::ExternalJudgmentAssumption>(&lhs.node)) {
    bool equal = left->assertedJudgment ==
                 std::get<soundness::ExternalJudgmentAssumption>(rhs.node)
                     .assertedJudgment;
    active.erase(pair);
    if (equal)
      done.insert(pair);
    return equal;
  }
  const auto &left = std::get<soundness::ApplyDerivationPlan>(lhs.node);
  const auto &right = std::get<soundness::ApplyDerivationPlan>(rhs.node);
  if (!siteEqual(left.site, right.site) ||
      left.bindingRef != right.bindingRef ||
      left.premises.size() != right.premises.size()) {
    active.erase(pair);
    return false;
  }
  auto leftPremise = left.premises.begin();
  auto rightPremise = right.premises.begin();
  for (; leftPremise != left.premises.end(); ++leftPremise, ++rightPremise) {
    if (leftPremise->first != rightPremise->first || !leftPremise->second ||
        !rightPremise->second ||
        !plansEqualImpl(*leftPremise->second, *rightPremise->second, active,
                        done)) {
      active.erase(pair);
      return false;
    }
  }
  active.erase(pair);
  done.insert(pair);
  return true;
}

bool scalarEqual(const soundness::ExactScalarValue &lhs,
                 const soundness::ExactScalarValue &rhs) {
  return lhs == rhs;
}

bool transformApplicationEqual(const TransformApplication &lhs,
                               const TransformApplication &rhs) {
  if (lhs.familyRef != rhs.familyRef ||
      lhs.matchedClaims != rhs.matchedClaims ||
      lhs.parameters.size() != rhs.parameters.size())
    return false;
  auto left = lhs.parameters.begin();
  auto right = rhs.parameters.begin();
  for (; left != lhs.parameters.end(); ++left, ++right)
    if (left->first != right->first ||
        !scalarEqual(left->second, right->second))
      return false;
  return true;
}

bool transformPlansEqual(const TransformPlan &lhs, const TransformPlan &rhs) {
  if (lhs.applications.size() != rhs.applications.size())
    return false;
  for (size_t index = 0; index < lhs.applications.size(); ++index)
    if (!transformApplicationEqual(lhs.applications[index],
                                   rhs.applications[index]))
      return false;
  return true;
}

bool targetPlansEqual(const CompilerTargetPlan &lhs,
                      const CompilerTargetPlan &rhs) {
  if (lhs.targetKey != rhs.targetKey || lhs.schemaKey != rhs.schemaKey ||
      lhs.derivations.size() != rhs.derivations.size())
    return false;
  for (size_t index = 0; index < lhs.derivations.size(); ++index)
    if (!derivationPlansEqual(lhs.derivations[index], rhs.derivations[index]))
      return false;
  return true;
}

llvm::Error checkSite(const soundness::ApplicationSite &site,
                      const std::string &location) {
  if (const auto *reduction =
          std::get_if<soundness::ReductionOccurrence>(&site)) {
    if (reduction->artifactId.empty() ||
        reduction->ownerClaim.descriptorDigest.empty())
      return failure(location + ": malformed reduction occurrence");
    return llvm::Error::success();
  }
  const auto &path = std::get<soundness::PathOccurrence>(site);
  if (path.artifactId.empty() || path.claim.descriptorDigest.empty())
    return failure(location + ": malformed path occurrence");
  return llvm::Error::success();
}

struct PlanWalkState {
  uint64_t nodes = 0;
  std::set<const soundness::DerivationPlan *> active;
  std::set<const soundness::DerivationPlan *> done;
};

llvm::Error checkPlanImpl(const soundness::DerivationPlan &plan,
                          const soundness::SoundnessContext &context,
                          const CompilerLimits &limits, uint64_t depth,
                          PlanWalkState &state, const std::string &location) {
  if (depth > limits.maxDerivationDepth)
    return failure(location + ": derivation depth exceeds its bound");
  if (state.active.count(&plan))
    return failure(location + ": derivation plan contains an active cycle");
  if (state.done.count(&plan))
    return llvm::Error::success();
  if (++state.nodes > limits.maxDerivationNodes)
    return failure(location + ": derivation node count exceeds its bound");
  state.active.insert(&plan);

  if (const auto *assumption =
          std::get_if<soundness::ExternalJudgmentAssumption>(&plan.node)) {
    soundness::RuntimeCheckResult check =
        soundness::checkSecurityJudgmentWellFormed(
            context.schemas(), assumption->assertedJudgment, location);
    state.active.erase(&plan);
    if (!check.accepted())
      return failure(location +
                     ": malformed assumed judgment: " + check.refusal->detail);
    state.done.insert(&plan);
    return llvm::Error::success();
  }

  const auto &application = std::get<soundness::ApplyDerivationPlan>(plan.node);
  if (!validRef(application.bindingRef)) {
    state.active.erase(&plan);
    return failure(location + ": application binding reference is not exact");
  }
  if (!context.findBinding(application.bindingRef)) {
    state.active.erase(&plan);
    return failure(location +
                   ": application binding reference is not selected");
  }
  if (llvm::Error site = checkSite(application.site, location + ".site")) {
    state.active.erase(&plan);
    return site;
  }
  for (const auto &[port, child] : application.premises) {
    if (port.empty() || !child) {
      state.active.erase(&plan);
      return failure(location + ": empty premise port or null child");
    }
    if (llvm::Error childError =
            checkPlanImpl(*child, context, limits, depth + 1, state,
                          location + ".premises." + port)) {
      state.active.erase(&plan);
      return childError;
    }
  }
  state.active.erase(&plan);
  state.done.insert(&plan);
  return llvm::Error::success();
}

llvm::Error checkPlan(const soundness::DerivationPlan &plan,
                      const soundness::SoundnessContext &context,
                      const CompilerLimits &limits, llvm::StringRef location) {
  PlanWalkState state;
  return checkPlanImpl(plan, context, limits, 1, state, location.str());
}

bool containsClaim(const AuthenticatedCompilerArtifact &artifact,
                   const soundness::ClaimRef &claim) {
  const auto &claims = artifact.observation.soundness.claimsByIndex;
  return claim.claimIndex < claims.size() && claims[claim.claimIndex] == claim;
}

llvm::Error checkObservationShape(
    llvm::StringRef artifactId, const soundness::SealedSoundnessView &soundness,
    const std::vector<VerifierProofRead> &verifierProofReads) {
  if (artifactId.empty() || soundness.artifactId != artifactId)
    return failure(
        "compiler artifact id and sealed soundness-view id must agree");
  for (size_t index = 0; index < soundness.claimsByIndex.size(); ++index) {
    const soundness::ClaimRef &claim = soundness.claimsByIndex[index];
    if (claim.claimIndex != index || claim.descriptorDigest.empty())
      return failure(
          "compiler artifact claims must be canonically indexed and nonempty");
  }
  for (const VerifierProofRead &read : verifierProofReads)
    if (read.payloadClass.empty() || !validRef(read.codecRef) ||
        read.count == 0)
      return failure("compiler artifact has a malformed verifier proof read");
  return llvm::Error::success();
}

llvm::Error checkArtifact(const OwnedCompilerArtifact &artifact) {
  if (!validRef(artifact.artifactSemanticsRef))
    return failure(
        "compiler artifact has no exact artifact-semantics authority");
  if (!artifact.adapterPayload ||
      !validRef(artifact.adapterPayload->exactTypeRef()))
    return failure("compiler artifact has no exact immutable adapter payload");
  return llvm::Error::success();
}

template <typename T, typename Key>
bool hasDuplicate(const std::vector<T> &values, Key key) {
  std::set<std::string, std::less<>> seen;
  for (const T &value : values) {
    std::string name = key(value);
    if (name.empty() || !seen.insert(name).second)
      return true;
  }
  return false;
}

bool containsRef(const std::vector<ExactRef> &refs, const ExactRef &ref) {
  return std::find(refs.begin(), refs.end(), ref) != refs.end();
}

bool exactRefListWellFormed(const std::vector<ExactRef> &refs) {
  std::set<std::string, std::less<>> ids;
  for (const ExactRef &ref : refs)
    if (!validRef(ref) || !ids.insert(ref.id).second)
      return false;
  return true;
}

llvm::Error
checkArguments(const std::vector<soundness::RuntimeValue> &arguments,
               const std::vector<soundness::ValueSort> &sorts,
               llvm::StringRef location) {
  if (arguments.size() != sorts.size())
    return failure(location + ": exact argument arity is wrong");
  for (size_t index = 0; index < arguments.size(); ++index) {
    if (arguments[index].sort != sorts[index])
      return failure(location + ": exact argument sort is wrong");
    soundness::RuntimeCheckResult check =
        soundness::checkRuntimeValueWellFormed(
            arguments[index],
            (location + ".argument[" + llvm::Twine(index) + "]").str());
    if (!check.accepted())
      return failure(location +
                     ": malformed exact argument: " + check.refusal->detail);
  }
  return llvm::Error::success();
}

const TransformDomainProvider *
findTransformProvider(const CompilerSemanticContext &context,
                      const ExactRef &ref) {
  auto found = context.transformDomains.find(ref.id);
  if (found == context.transformDomains.end() || !found->second ||
      found->second->exactRef() != ref)
    return nullptr;
  return found->second.get();
}

const DerivationPlanDomainProvider *
findDerivationProvider(const CompilerSemanticContext &context,
                       const ExactRef &ref) {
  auto found = context.derivationDomains.find(ref.id);
  if (found == context.derivationDomains.end() || !found->second ||
      found->second->exactRef() != ref)
    return nullptr;
  return found->second.get();
}

const CodecWidthProfile *
findWidthProfile(const CompilerSemanticContext &context, const ExactRef &ref) {
  auto found = context.codecWidthProfiles.find(ref.id);
  if (found == context.codecWidthProfiles.end() || found->second.ref != ref)
    return nullptr;
  return &found->second;
}

const ArtifactSemantics *
findArtifactSemantics(const CompilerSemanticContext &context,
                      const ExactRef &ref) {
  auto found = context.artifactSemantics.find(ref.id);
  if (found == context.artifactSemantics.end() || !found->second ||
      found->second->exactRef() != ref)
    return nullptr;
  return found->second.get();
}

llvm::Expected<AuthenticatedArtifactHandle>
authenticateArtifact(const CompilerSemanticContext &context,
                     const ArtifactHandle &artifact) {
  if (!artifact)
    return error<AuthenticatedArtifactHandle>(
        "artifact authentication received a null artifact");
  if (llvm::Error shape = checkArtifact(*artifact))
    return std::move(shape);
  const ArtifactSemantics *semantics =
      findArtifactSemantics(context, artifact->artifactSemanticsRef);
  if (!semantics)
    return error<AuthenticatedArtifactHandle>(
        "compiler artifact names no exact artifact-semantics authority");
  return semantics->authenticateArtifact(artifact);
}

llvm::Error checkTransformPlanStructure(const CompilerSemanticContext &context,
                                        const CompilerRequest &request,
                                        const TransformPlan &plan,
                                        llvm::StringRef location) {
  if (plan.applications.size() > request.limits.maxTransformApplications)
    return failure(location +
                   ": transform application count exceeds its bound");
  for (size_t index = 0; index < plan.applications.size(); ++index) {
    const TransformApplication &application = plan.applications[index];
    if (!validRef(application.familyRef))
      return failure(location + ": transform family reference is not exact");
    auto family = context.transformFamilies.find(application.familyRef.id);
    if (family == context.transformFamilies.end() || !family->second ||
        family->second->exactRef() != application.familyRef ||
        !validRef(family->second->artifactSemanticsRef()) ||
        family->second->artifactSemanticsRef() !=
            request.source->artifactSemanticsRef)
      return failure(
          location +
          ": transform family is absent or uses different artifact semantics");
    std::set<uint64_t> consumed;
    for (const soundness::ClaimRef &claim : application.matchedClaims)
      if (claim.descriptorDigest.empty() ||
          !consumed.insert(claim.claimIndex).second)
        return failure(
            location +
            ": matched claims must be nonempty and occurrence-distinct");
    for (const auto &[name, value] : application.parameters) {
      if (name.empty())
        return failure(location + ": transform parameter name is empty");
      bool carrierMatches = false;
      switch (value.sort) {
      case soundness::ValueSort::Integer: {
        const auto *number = std::get_if<registry::Rational>(&value.payload);
        carrierMatches = number && number->denStr() == "1";
        break;
      }
      case soundness::ValueSort::Rational:
        carrierMatches =
            std::holds_alternative<registry::Rational>(value.payload);
        break;
      case soundness::ValueSort::String:
        carrierMatches = std::holds_alternative<std::string>(value.payload);
        break;
      case soundness::ValueSort::Boolean:
        carrierMatches = std::holds_alternative<bool>(value.payload);
        break;
      default:
        break;
      }
      if (!carrierMatches)
        return failure(location +
                       ": transform parameter has the wrong exact carrier");
    }
  }
  return llvm::Error::success();
}

const RequestedTarget *findTarget(const CompilerRequest &request,
                                  llvm::StringRef key) {
  auto found = std::find_if(
      request.targets.begin(), request.targets.end(),
      [&](const RequestedTarget &target) { return target.key == key; });
  return found == request.targets.end() ? nullptr : &*found;
}

const TargetSchema *findSchema(const CompilerRequest &request,
                               llvm::StringRef key) {
  auto found = std::find_if(
      request.targetSchemas.begin(), request.targetSchemas.end(),
      [&](const TargetSchema &schema) { return schema.key == key; });
  return found == request.targetSchemas.end() ? nullptr : &*found;
}

llvm::Error
checkDeclarations(const std::vector<soundness::TypedDeclaration> &declarations,
                  const llvm::Twine &location) {
  std::set<std::string, std::less<>> names;
  for (const soundness::TypedDeclaration &declaration : declarations) {
    if (declaration.name.empty() || !names.insert(declaration.name).second)
      return failure(location + ": resource names must be nonempty and unique");
    if (declaration.sort != soundness::ValueSort::Integer &&
        declaration.sort != soundness::ValueSort::Rational)
      return failure(location + ": resources must be exact numeric values");
  }
  return llvm::Error::success();
}

using ResourceSorts = std::map<std::string, soundness::ValueSort, std::less<>>;

ResourceSorts
resourceSorts(const std::vector<soundness::TypedDeclaration> &declarations) {
  ResourceSorts result;
  for (const soundness::TypedDeclaration &declaration : declarations)
    result.emplace(declaration.name, declaration.sort);
  return result;
}

bool quantityResourcesClosed(const soundness::ClosedQuantity &quantity,
                             const ResourceSorts &resources) {
  return std::all_of(quantity.resourceTerms.begin(),
                     quantity.resourceTerms.end(),
                     [&](const soundness::ResourceMonomial &term) {
                       return resources.count(term.resource);
                     });
}

bool integerValued(const soundness::ClosedQuantity &quantity,
                   const ResourceSorts &resources) {
  if (quantity.constant.denStr() != "1")
    return false;
  for (const soundness::ResourceMonomial &term : quantity.resourceTerms) {
    auto resource = resources.find(term.resource);
    if (resource == resources.end() ||
        resource->second != soundness::ValueSort::Integer ||
        term.coefficient.denStr() != "1")
      return false;
  }
  return true;
}

llvm::Error
checkQuantityInDomain(const soundness::ClosedQuantity &quantity,
                      const std::vector<soundness::TypedDeclaration> &domain,
                      std::optional<soundness::ValueSort> expectedSort,
                      const llvm::Twine &location) {
  soundness::RuntimeCheckResult wellFormed =
      soundness::checkClosedQuantityWellFormed(quantity, location.str());
  if (!wellFormed.accepted())
    return failure(location + ": malformed closed quantity: " +
                   wellFormed.refusal->detail);
  ResourceSorts sorts = resourceSorts(domain);
  if (!quantityResourcesClosed(quantity, sorts))
    return failure(location +
                   ": quantity names a resource outside the comparison "
                   "domain");
  if (expectedSort == soundness::ValueSort::Integer &&
      !integerValued(quantity, sorts))
    return failure(location +
                   ": integer resource has a noninteger substitution");
  if (expectedSort && *expectedSort != soundness::ValueSort::Integer &&
      *expectedSort != soundness::ValueSort::Rational)
    return failure(location + ": substitution target is not numeric");
  return llvm::Error::success();
}

llvm::Error checkResourceSubstitution(
    const std::vector<soundness::TypedDeclaration> &source,
    const ResourceSubstitution &substitution,
    const std::vector<soundness::TypedDeclaration> &domain,
    const llvm::Twine &location) {
  std::set<std::string, std::less<>> expected;
  for (const soundness::TypedDeclaration &declaration : source)
    expected.insert(declaration.name);
  std::set<std::string, std::less<>> actual;
  for (const auto &[name, value] : substitution) {
    actual.insert(name);
    auto declaration =
        std::find_if(source.begin(), source.end(),
                     [&](const soundness::TypedDeclaration &candidate) {
                       return candidate.name == name;
                     });
    if (declaration == source.end())
      return failure(location + ": substitution has a surplus source key");
    if (llvm::Error checked = checkQuantityInDomain(
            value, domain, declaration->sort, location + "." + name))
      return checked;
  }
  if (actual != expected)
    return failure(location +
                   ": substitution does not exactly cover source resources");
  return llvm::Error::success();
}

llvm::Error checkProjection(const BoundProjection &projection,
                            const llvm::Twine &location) {
  switch (projection.kind) {
  case BoundProjectionKind::ExtractionFailure:
  case BoundProjectionKind::Scalar:
  case BoundProjectionKind::RoundMaximum:
    if (!projection.exactRoundIndex.empty())
      return failure(location +
                     ": only an exact Round projection carries an index");
    return llvm::Error::success();
  case BoundProjectionKind::Round:
    if (projection.exactRoundIndex.empty())
      return failure(location + ": Round projection requires an exact index");
    return llvm::Error::success();
  }
  return failure(location + ": projection kind is unknown");
}

llvm::Error
checkSchemaSubstitutions(const CompilerRequest &request,
                         const RequestedTarget &target,
                         const SchemaResourceSubstitutions &substitutions,
                         const std::vector<soundness::TypedDeclaration> &domain,
                         const llvm::Twine &location) {
  std::set<std::string, std::less<>> expected(target.admittedSchemaKeys.begin(),
                                              target.admittedSchemaKeys.end());
  std::set<std::string, std::less<>> actual;
  for (const auto &[schemaKey, substitution] : substitutions) {
    if (!actual.insert(schemaKey).second)
      return failure(location + ": duplicate schema substitution");
    const TargetSchema *schema = findSchema(request, schemaKey);
    if (!schema || !expected.count(schemaKey))
      return failure(location +
                     ": substitution names a schema not admitted by target");
    if (llvm::Error checked =
            checkResourceSubstitution(schema->resources, substitution, domain,
                                      location + "." + schemaKey))
      return checked;
  }
  if (actual != expected)
    return failure(
        location +
        ": schema substitution map does not exactly cover target schemas");
  return llvm::Error::success();
}

enum class BoundExprMode { Candidate, Baseline };

struct BoundExprCheckState {
  std::set<const BoundExpr *> active;
  std::set<const BoundExpr *> done;
  std::set<std::string, std::less<>> targetKeys;
};

llvm::Error
checkBoundExpr(const BoundExpr &expression, BoundExprMode mode,
               const CompilerSemanticContext &context,
               const CompilerRequest &request,
               const std::vector<soundness::TypedDeclaration> &domain,
               const std::set<std::string, std::less<>> &candidateTargetKeys,
               BoundExprCheckState &state, const llvm::Twine &location) {
  if (state.active.count(&expression))
    return failure(location + ": bound expression has a cycle");
  if (state.done.count(&expression))
    return llvm::Error::success();
  state.active.insert(&expression);

  auto finish = [&]() {
    state.active.erase(&expression);
    state.done.insert(&expression);
    return llvm::Error::success();
  };

  if (std::holds_alternative<ZeroBound>(expression.payload)) {
    if (mode != BoundExprMode::Baseline)
      return failure(location +
                     ": candidate expression cannot use a Zero leaf");
    return finish();
  }
  if (const auto *read =
          std::get_if<CandidateTargetRead>(&expression.payload)) {
    if (mode != BoundExprMode::Candidate)
      return failure(location +
                     ": baseline expression cannot read candidate targets");
    const RequestedTarget *target = findTarget(request, read->targetKey);
    if (!target)
      return failure(location + ": candidate read names no target");
    if (!std::holds_alternative<ExactTargetMember>(read->members) &&
        !std::holds_alternative<FoldTargetMembers>(read->members))
      return failure(location + ": candidate member selector is malformed");
    if (const auto *fold = std::get_if<FoldTargetMembers>(&read->members);
        fold && fold->aggregate != TargetFoldKind::Add &&
        fold->aggregate != TargetFoldKind::Max)
      return failure(location + ": candidate fold has an unknown aggregate");
    state.targetKeys.insert(read->targetKey);
    if (llvm::Error checked =
            checkProjection(read->projection, location + ".projection"))
      return checked;
    if (llvm::Error checked = checkSchemaSubstitutions(
            request, *target, read->resourceSubstitutions, domain,
            location + ".resource_substitutions"))
      return checked;
    return finish();
  }

  if (const auto *source = std::get_if<SourceProjection>(&expression.payload)) {
    if (mode != BoundExprMode::Baseline)
      return failure(location +
                     ": candidate expression cannot read a source baseline");
    const RequestedTarget *target =
        findTarget(request, source->targetRelation.targetKey);
    if (!target || !candidateTargetKeys.count(source->targetRelation.targetKey))
      return failure(
          location +
          ": source baseline is not tied to a same-key candidate read");
    auto member = std::find(target->orderedSourceClaims.begin(),
                            target->orderedSourceClaims.end(),
                            source->targetRelation.exactSourceClaimRef);
    if (member == target->orderedSourceClaims.end())
      return failure(location +
                     ": source baseline claim is outside the target frontier");
    const auto *subject = std::get_if<soundness::ProtocolClaimSubject>(
        &source->sourceTarget.subject.payload);
    auto authenticatedSource = authenticateArtifact(context, request.source);
    if (!authenticatedSource)
      return authenticatedSource.takeError();
    if (!subject ||
        subject->artifactId != (*authenticatedSource)->observation.artifactId ||
        subject->claim != source->targetRelation.exactSourceClaimRef)
      return failure(
          location +
          ": source baseline target is not the exact named source claim");
    if (std::find(context.soundnessContext->schemas().securityIndices.begin(),
                  context.soundnessContext->schemas().securityIndices.end(),
                  source->sourceTarget.index) ==
        context.soundnessContext->schemas().securityIndices.end())
      return failure(location +
                     ": source baseline uses an unadmitted security index");
    if (llvm::Error declarations =
            checkDeclarations(source->sourceTarget.resourceVariables,
                              location + ".source_target.resources"))
      return declarations;
    if (llvm::Error projection =
            checkProjection(source->projection, location + ".projection"))
      return projection;
    if (llvm::Error substitution =
            checkResourceSubstitution(source->sourceTarget.resourceVariables,
                                      source->resourceSubstitution, domain,
                                      location + ".resource_substitution"))
      return substitution;
    if (llvm::Error plan = checkPlan(
            source->sourceDerivationPlan, *context.soundnessContext,
            request.limits, (location + ".source_derivation_plan").str()))
      return plan;
    return finish();
  }

  const std::vector<BoundExprPtr> *operands = nullptr;
  if (const auto *add = std::get_if<AddBounds>(&expression.payload))
    operands = &add->operands;
  else if (const auto *maximum = std::get_if<MaxBounds>(&expression.payload))
    operands = &maximum->operands;
  if (operands) {
    if (operands->empty())
      return failure(location + ": bound Add/Max must be nonempty");
    for (size_t index = 0; index < operands->size(); ++index) {
      if (!(*operands)[index])
        return failure(location + ": bound Add/Max has a null operand");
      if (llvm::Error checked = checkBoundExpr(
              *(*operands)[index], mode, context, request, domain,
              candidateTargetKeys, state,
              location + ".operands[" + llvm::Twine(index) + "]"))
        return checked;
    }
    return finish();
  }

  const auto &scale = std::get<ScaleBound>(expression.payload);
  if (!scale.operand)
    return failure(location + ": bound Scale has a null operand");
  if (llvm::Error checked = checkQuantityInDomain(
          scale.scale, domain, std::nullopt, location + ".scale"))
    return checked;
  if (llvm::Error checked =
          checkBoundExpr(*scale.operand, mode, context, request, domain,
                         candidateTargetKeys, state, location + ".operand"))
    return checked;
  return finish();
}

llvm::Error
checkBoundInDomain(const CompilerSemanticContext &context,
                   const CompilerRequest &request,
                   const soundness::ClosedBound &bound,
                   const std::vector<soundness::TypedDeclaration> &domain,
                   const llvm::Twine &location) {
  soundness::RuntimeCheckResult wellFormed =
      soundness::checkClosedBoundWellFormed(bound, location.str());
  if (!wellFormed.accepted())
    return failure(location +
                   ": malformed closed bound: " + wellFormed.refusal->detail);
  ResourceSorts sorts = resourceSorts(domain);
  if (!quantityResourcesClosed(bound.quantity, sorts))
    return failure(location + ": bound quantity names an undeclared resource");
  for (size_t index = 0; index < bound.primitiveGameTerms.size(); ++index) {
    const soundness::PrimitiveGameTerm &term = bound.primitiveGameTerms[index];
    if (std::find(request.derivationSurface.allowedPrimitiveGames.begin(),
                  request.derivationSurface.allowedPrimitiveGames.end(),
                  term.instance) ==
        request.derivationSurface.allowedPrimitiveGames.end())
      return failure(location +
                     ": ceiling uses a primitive game outside the allowed "
                     "derivation surface");
    auto game = context.soundnessContext->schemas().primitiveGames.find(
        term.instance.ref.id);
    if (game == context.soundnessContext->schemas().primitiveGames.end() ||
        game->second.ref != term.instance.ref)
      return failure(location + ": ceiling names no exact primitive game");
    if (llvm::Error substitution = checkResourceSubstitution(
            game->second.resources, term.resourceSubstitution, domain,
            location + ".primitive_game_terms[" + llvm::Twine(index) +
                "].resource_substitution"))
      return substitution;
  }
  return llvm::Error::success();
}

llvm::Error checkSoundnessConstraintRequest(
    const CompilerSemanticContext &context, const CompilerRequest &request,
    const SoundnessConstraint &constraint, uint64_t constraintIndex) {
  const std::string location =
      "request.soundness_constraints[" + std::to_string(constraintIndex) + "]";
  if (llvm::Error declarations =
          checkDeclarations(constraint.comparisonDomain.resources,
                            location + ".comparison_domain"))
    return declarations;
  const std::set<std::string, std::less<>> noCandidateTargets;
  BoundExprCheckState candidateState;
  if (llvm::Error candidate = checkBoundExpr(
          constraint.candidate, BoundExprMode::Candidate, context, request,
          constraint.comparisonDomain.resources, noCandidateTargets,
          candidateState, location + ".candidate"))
    return candidate;
  BoundExprCheckState baselineState;
  if (llvm::Error baseline = checkBoundExpr(
          constraint.baseline, BoundExprMode::Baseline, context, request,
          constraint.comparisonDomain.resources, candidateState.targetKeys,
          baselineState, location + ".baseline"))
    return baseline;
  return checkBoundInDomain(context, request, constraint.ceiling,
                            constraint.comparisonDomain.resources,
                            location + ".ceiling");
}

llvm::Error checkRequest(const CompilerSemanticContext &context,
                         const CompilerRequest &request) {
  if (!request.source)
    return failure("compiler request has no source artifact");
  auto source = authenticateArtifact(context, request.source);
  if (!source)
    return source.takeError();
  if (!context.soundnessContext)
    return failure("compiler request has no immutable soundness context");
  const TransformDomainProvider *transformProvider =
      findTransformProvider(context, request.transformDomainProviderRef);
  if (!transformProvider ||
      !findDerivationProvider(context, request.derivationPlanProviderRef))
    return failure("compiler request names an unknown exact domain provider");
  if (!validRef(transformProvider->artifactSemanticsRef()) ||
      transformProvider->artifactSemanticsRef() !=
          request.source->artifactSemanticsRef)
    return failure(
        "transform domain and source require different artifact semantics");

  const CompilerLimits &limits = request.limits;
  if (!limits.maxTransformApplications || !limits.maxTargets ||
      !limits.maxDerivationNodes || !limits.maxDerivationDepth ||
      !limits.maxAlternativesPerSubject || !limits.maxDomainPlans)
    return failure("compiler limits must all be positive finite bounds");
  if (request.targets.size() > limits.maxTargets)
    return failure("compiler target count exceeds its bound");
  if (hasDuplicate(request.targets,
                   [](const RequestedTarget &target) { return target.key; }) ||
      hasDuplicate(request.targetSchemas,
                   [](const TargetSchema &schema) { return schema.key; }))
    return failure(
        "compiler target and schema keys must be nonempty and unique");

  for (const TargetSchema &schema : request.targetSchemas) {
    if (std::find(context.soundnessContext->schemas().securityIndices.begin(),
                  context.soundnessContext->schemas().securityIndices.end(),
                  schema.index) ==
        context.soundnessContext->schemas().securityIndices.end())
      return failure("target schema names an unadmitted security index");
    if (llvm::Error declarations =
            checkDeclarations(schema.resources, "target schema " + schema.key))
      return declarations;
  }

  for (const RequestedTarget &target : request.targets) {
    switch (target.selector.kind) {
    case TargetSelectorKind::FinalFrontier:
      if (!target.selector.familyRef.id.empty() ||
          !target.selector.familyRef.sourceRevision.empty() ||
          !target.selector.outputRole.empty())
        return failure(
            "FinalFrontier must not carry transform-output coordinates");
      break;
    case TargetSelectorKind::TransformOutputs: {
      if (!validRef(target.selector.familyRef) ||
          target.selector.outputRole.empty())
        return failure(
            "TransformOutputs requires an exact family and output role");
      auto family =
          context.transformFamilies.find(target.selector.familyRef.id);
      if (family == context.transformFamilies.end() || !family->second ||
          family->second->exactRef() != target.selector.familyRef)
        return failure(
            "TransformOutputs names an unknown exact transform family");
      if (!validRef(family->second->artifactSemanticsRef()) ||
          family->second->artifactSemanticsRef() !=
              request.source->artifactSemanticsRef)
        return failure(
            "TransformOutputs family and source require different artifact "
            "semantics");
      break;
    }
    }
    if (target.orderedSourceClaims.empty())
      return failure("requested target source lineage must be nonempty");
    std::set<uint64_t> indices;
    for (const soundness::ClaimRef &claim : target.orderedSourceClaims)
      if (!containsClaim(**source, claim) ||
          !indices.insert(claim.claimIndex).second)
        return failure("requested target has an unknown or duplicate claim");
    if (target.admittedSchemaKeys.empty())
      return failure("a requested target must admit at least one schema");
    std::set<std::string, std::less<>> schemaKeys;
    for (const std::string &key : target.admittedSchemaKeys)
      if (!findSchema(request, key) || !schemaKeys.insert(key).second)
        return failure(
            "requested target names an unknown or duplicate target schema");
  }

  const DerivationSurface &surface = request.derivationSurface;
  if (!exactRefListWellFormed(surface.allowedBindingRefs))
    return failure("derivation-surface references must be exact and unique");
  for (const ExactRef &ref : surface.allowedBindingRefs) {
    const soundness::RuleBinding *binding =
        context.soundnessContext->findBinding(ref);
    if (!binding || !context.soundnessContext->findRule(binding->ruleRef))
      return failure("derivation surface names an unknown selected binding");
  }
  for (size_t index = 0; index < surface.allowedPrimitiveGames.size();
       ++index) {
    const soundness::PrimitiveGameInstance &instance =
        surface.allowedPrimitiveGames[index];
    if (!validRef(instance.ref))
      return failure(
          "derivation surface primitive-game reference is not exact");
    auto game = context.soundnessContext->schemas().primitiveGames.find(
        instance.ref.id);
    if (game == context.soundnessContext->schemas().primitiveGames.end() ||
        game->second.ref != instance.ref)
      return failure("derivation surface names an unknown primitive game");
    if (llvm::Error arguments = checkArguments(
            instance.arguments, game->second.instanceArgumentTypes,
            "request.allowed_primitive_game"))
      return arguments;
    for (size_t prior = 0; prior < index; ++prior)
      if (surface.allowedPrimitiveGames[prior] == instance)
        return failure(
            "derivation surface duplicates an exact primitive-game instance");
  }
  for (size_t index = 0; index < surface.allowedHypotheses.size(); ++index) {
    const soundness::PropositionInstance &hypothesis =
        surface.allowedHypotheses[index];
    if (!validRef(hypothesis.ref))
      return failure("derivation surface proposition reference is not exact");
    auto schema = context.soundnessContext->schemas().propositions.find(
        hypothesis.ref.id);
    if (schema == context.soundnessContext->schemas().propositions.end() ||
        schema->second.ref != hypothesis.ref)
      return failure("derivation surface names an unknown proposition");
    if (llvm::Error arguments =
            checkArguments(hypothesis.arguments, schema->second.argumentTypes,
                           "request.allowed_hypothesis"))
      return arguments;
    for (size_t prior = 0; prior < index; ++prior)
      if (surface.allowedHypotheses[prior] == hypothesis)
        return failure(
            "derivation surface duplicates an exact qualitative hypothesis");
  }

  for (size_t index = 0; index < request.soundnessConstraints.size(); ++index)
    if (llvm::Error constraint = checkSoundnessConstraintRequest(
            context, request, request.soundnessConstraints[index], index))
      return constraint;

  if (hasDuplicate(request.objectives,
                   [](const Objective &objective) { return objective.key; }))
    return failure("objective keys must be nonempty and unique");
  for (const Objective &objective : request.objectives) {
    if (objective.kind != ObjectiveKind::StaticProofBytes)
      return failure("unsupported compiler objective kind");
    if (objective.direction != ObjectiveDirection::Minimize &&
        objective.direction != ObjectiveDirection::Maximize)
      return failure("unsupported compiler objective direction");
    const CodecWidthProfile *profile =
        findWidthProfile(context, objective.codecWidthProfileRef);
    if (!profile)
      return failure("objective names an unknown exact codec-width profile");
    for (const auto &[id, width] : profile->codecs)
      if (id != width.codecRef.id || !validRef(width.codecRef) ||
          width.byteWidth.denStr() != "1" ||
          width.byteWidth.compare(registry::Rational::fromInteger(0)) <= 0)
        return failure("codec-width profile is malformed");
  }

  if (!std::holds_alternative<ClosedDomainScope>(request.comparisonScope) &&
      !std::holds_alternative<SubmittedFrontierScope>(request.comparisonScope))
    return failure("compiler comparison scope is malformed");
  return llvm::Error::success();
}

struct ProductionTag {
  uint64_t applicationIndex = 0;
  ExactRef familyRef;
  std::string outputRole;
};

bool productionTagEqual(const ProductionTag &lhs, const ProductionTag &rhs) {
  return lhs.applicationIndex == rhs.applicationIndex &&
         lhs.familyRef == rhs.familyRef && lhs.outputRole == rhs.outputRole;
}

struct LineageElement {
  soundness::ClaimRef claim;
  std::vector<uint64_t> sourceOrdinals;
  std::vector<ProductionTag> provenance;
};

template <typename T, typename Equal>
void appendUnique(std::vector<T> &destination, const std::vector<T> &source,
                  Equal equal) {
  for (const T &value : source)
    if (std::none_of(destination.begin(), destination.end(),
                     [&](const T &present) { return equal(present, value); }))
      destination.push_back(value);
}

llvm::Expected<std::vector<LineageElement>>
resolveTargetLineage(const CheckedTransformTrace &trace,
                     const RequestedTarget &target) {
  std::vector<LineageElement> frontier;
  for (size_t index = 0; index < target.orderedSourceClaims.size(); ++index)
    frontier.push_back(LineageElement{
        target.orderedSourceClaims[index], {static_cast<uint64_t>(index)}, {}});

  size_t correspondenceOffset = 0;
  while (correspondenceOffset < trace.correspondences.size()) {
    const uint64_t applicationIndex =
        trace.correspondences[correspondenceOffset].applicationIndex;
    size_t applicationEnd = correspondenceOffset;
    while (applicationEnd < trace.correspondences.size() &&
           trace.correspondences[applicationEnd].applicationIndex ==
               applicationIndex)
      ++applicationEnd;

    struct Replacement {
      size_t firstPosition = 0;
      std::vector<size_t> positions;
      std::vector<LineageElement> produced;
    };
    std::vector<Replacement> replacements;
    std::vector<std::optional<size_t>> consumedBy(frontier.size());

    for (size_t correspondenceIndex = correspondenceOffset;
         correspondenceIndex < applicationEnd; ++correspondenceIndex) {
      const ClaimCorrespondence &correspondence =
          trace.correspondences[correspondenceIndex];
      std::vector<size_t> positions;
      for (const soundness::ClaimRef &consumed :
           correspondence.orderedConsumed) {
        auto found = std::find_if(
            frontier.begin(), frontier.end(),
            [&](const LineageElement &item) { return item.claim == consumed; });
        if (found != frontier.end())
          positions.push_back(static_cast<size_t>(found - frontier.begin()));
      }
      if (positions.empty())
        continue;
      if (positions.size() != correspondence.orderedConsumed.size())
        return error<std::vector<LineageElement>>(
            "target lineage intersects only part of a checked correspondence");
      if (!std::is_sorted(positions.begin(), positions.end()) ||
          std::adjacent_find(positions.begin(), positions.end()) !=
              positions.end())
        return error<std::vector<LineageElement>>(
            "target lineage does not contain consumed claims once in "
            "canonical correspondence order");

      Replacement replacement;
      replacement.firstPosition = positions.front();
      replacement.positions = positions;
      std::vector<uint64_t> inheritedRoots;
      std::vector<ProductionTag> inheritedProvenance;
      for (size_t position : positions) {
        if (consumedBy[position])
          return error<std::vector<LineageElement>>(
              "target lineage has overlapping checked correspondences");
        consumedBy[position] = replacements.size();
        appendUnique(inheritedRoots, frontier[position].sourceOrdinals,
                     [](uint64_t lhs, uint64_t rhs) { return lhs == rhs; });
        appendUnique(inheritedProvenance, frontier[position].provenance,
                     productionTagEqual);
      }
      for (const ProducedClaim &produced : correspondence.orderedProduced) {
        LineageElement next{produced.claim, inheritedRoots,
                            inheritedProvenance};
        ProductionTag tag{applicationIndex, correspondence.familyRef,
                          produced.outputRole};
        if (std::none_of(next.provenance.begin(), next.provenance.end(),
                         [&](const ProductionTag &present) {
                           return productionTagEqual(present, tag);
                         }))
          next.provenance.push_back(std::move(tag));
        replacement.produced.push_back(std::move(next));
      }
      replacements.push_back(std::move(replacement));
    }

    if (!replacements.empty()) {
      std::vector<LineageElement> next;
      for (size_t position = 0; position < frontier.size(); ++position) {
        if (!consumedBy[position]) {
          next.push_back(frontier[position]);
          continue;
        }
        const Replacement &replacement = replacements[*consumedBy[position]];
        if (position == replacement.firstPosition)
          next.insert(next.end(), replacement.produced.begin(),
                      replacement.produced.end());
      }
      std::set<uint64_t> indices;
      for (const LineageElement &element : next)
        if (!indices.insert(element.claim.claimIndex).second)
          return error<std::vector<LineageElement>>(
              "target lineage replay produced an ambiguous claim frontier");
      frontier = std::move(next);
    }
    correspondenceOffset = applicationEnd;
  }

  std::vector<LineageElement> result;
  for (const LineageElement &element : frontier) {
    if (!containsClaim(*trace.finalArtifact, element.claim))
      return error<std::vector<LineageElement>>(
          "target lineage does not resolve into the checked final artifact");
    bool selected = target.selector.kind == TargetSelectorKind::FinalFrontier;
    if (target.selector.kind == TargetSelectorKind::TransformOutputs)
      selected =
          std::any_of(element.provenance.begin(), element.provenance.end(),
                      [&](const ProductionTag &tag) {
                        return tag.familyRef == target.selector.familyRef &&
                               tag.outputRole == target.selector.outputRole;
                      });
    if (!selected)
      continue;
    result.push_back(element);
  }
  if (target.selector.kind == TargetSelectorKind::FinalFrontier &&
      result.empty())
    return error<std::vector<LineageElement>>(
        "FinalFrontier resolved to an empty target");
  return result;
}

llvm::Expected<std::vector<soundness::SecuritySubject>>
resolveTargetSubjects(const CheckedTransformTrace &trace,
                      const RequestedTarget &target) {
  auto lineage = resolveTargetLineage(trace, target);
  if (!lineage)
    return lineage.takeError();
  std::vector<soundness::SecuritySubject> result;
  result.reserve(lineage->size());
  for (const LineageElement &element : *lineage) {
    soundness::SecuritySubject subject;
    subject.payload = soundness::ProtocolClaimSubject{
        trace.finalArtifact->observation.artifactId, element.claim};
    result.push_back(std::move(subject));
  }
  return result;
}

llvm::Error capProduct(uint64_t left, uint64_t right, uint64_t cap,
                       llvm::StringRef location) {
  if (right && left > cap / right)
    return failure(location + ": finite product exceeds its domain bound");
  return llvm::Error::success();
}

llvm::Expected<std::vector<CompilerTargetPlan>> enumerateTargetPlans(
    const CompilerSemanticContext &context, const CompilerRequest &request,
    const DerivationPlanDomainProvider &provider, const RequestedTarget &target,
    const CheckedTransformTrace &trace) {
  auto subjects = resolveTargetSubjects(trace, target);
  if (!subjects)
    return subjects.takeError();
  if (subjects->empty())
    return std::vector<CompilerTargetPlan>{
        CompilerTargetPlan{target.key, std::nullopt, {}}};

  std::vector<CompilerTargetPlan> targetPlans;
  for (const std::string &schemaKey : target.admittedSchemaKeys) {
    const TargetSchema *schema = findSchema(request, schemaKey);
    if (!schema)
      return error<std::vector<CompilerTargetPlan>>(
          "target schema disappeared after request validation");
    std::vector<std::vector<soundness::DerivationPlan>> alternatives;
    bool complete = true;
    for (size_t subjectIndex = 0; subjectIndex < subjects->size();
         ++subjectIndex) {
      auto listed = provider.enumerate(request, *trace.finalArtifact, target,
                                       *schema, (*subjects)[subjectIndex]);
      if (!listed)
        return listed.takeError();
      if (listed->size() > request.limits.maxAlternativesPerSubject)
        return error<std::vector<CompilerTargetPlan>>(
            "derivation provider exceeded the alternatives bound");
      for (size_t index = 0; index < listed->size(); ++index) {
        if (llvm::Error check = checkPlan(
                (*listed)[index], *context.soundnessContext, request.limits,
                "domain." + target.key + "." + schemaKey + ".subject[" +
                    std::to_string(subjectIndex) + "].alternative[" +
                    std::to_string(index) + "]"))
          return std::move(check);
        for (size_t prior = 0; prior < index; ++prior)
          if (derivationPlansEqual((*listed)[prior], (*listed)[index]))
            return error<std::vector<CompilerTargetPlan>>(
                "derivation provider emitted a duplicate alternative");
      }
      if (listed->empty()) {
        complete = false;
        break;
      }
      alternatives.push_back(std::move(*listed));
    }
    if (!complete)
      continue;

    std::vector<std::vector<soundness::DerivationPlan>> products(1);
    for (size_t subjectIndex = 0; subjectIndex < subjects->size();
         ++subjectIndex) {
      if (llvm::Error cap = capProduct(
              products.size(), alternatives[subjectIndex].size(),
              request.limits.maxDomainPlans, "target derivation product"))
        return std::move(cap);
      std::vector<std::vector<soundness::DerivationPlan>> next;
      for (const auto &prefix : products)
        for (const soundness::DerivationPlan &plan :
             alternatives[subjectIndex]) {
          std::vector<soundness::DerivationPlan> expanded = prefix;
          expanded.push_back(plan);
          next.push_back(std::move(expanded));
        }
      products = std::move(next);
    }
    for (auto &product : products)
      targetPlans.push_back(
          CompilerTargetPlan{target.key, schemaKey, std::move(product)});
    if (targetPlans.size() > request.limits.maxDomainPlans)
      return error<std::vector<CompilerTargetPlan>>(
          "target domain exceeds its finite bound");
  }
  return targetPlans;
}

llvm::Error
checkSubmittedPlan(const CompilerSemanticContext &context,
                   const CompilerRequest &request,
                   const TransformDomainProvider &transformProvider,
                   const DerivationPlanDomainProvider &derivationProvider,
                   const CompilerPlan &plan, uint64_t ordinal) {
  if (llvm::Error structure = checkTransformPlanStructure(
          context, request, plan.transform,
          "submitted[" + std::to_string(ordinal) + "].transform"))
    return structure;
  auto source = authenticateArtifact(context, request.source);
  if (!source)
    return source.takeError();
  auto member = transformProvider.contains(request, **source, plan.transform);
  if (!member)
    return member.takeError();
  if (!*member)
    return failure("submitted plan is outside the transform domain");
  auto trace = realizeTransform(context, request, plan.transform);
  if (!trace)
    return trace.takeError();
  if (plan.targets.size() != request.targets.size())
    return failure("submitted plan does not exactly cover requested targets");
  for (size_t targetIndex = 0; targetIndex < request.targets.size();
       ++targetIndex) {
    const RequestedTarget &requested = request.targets[targetIndex];
    const CompilerTargetPlan &submitted = plan.targets[targetIndex];
    auto subjects = resolveTargetSubjects(*trace, requested);
    if (!subjects)
      return subjects.takeError();
    if (submitted.targetKey != requested.key)
      return failure("submitted target plan changed canonical target order");
    if (subjects->empty()) {
      if (submitted.schemaKey || !submitted.derivations.empty())
        return failure(
            "empty target resolution must use the unique empty target plan");
      continue;
    }
    if (!submitted.schemaKey ||
        std::find(requested.admittedSchemaKeys.begin(),
                  requested.admittedSchemaKeys.end(),
                  *submitted.schemaKey) == requested.admittedSchemaKeys.end())
      return failure("submitted target plan uses an inadmissible schema");
    const TargetSchema *schema = findSchema(request, *submitted.schemaKey);
    if (!schema || submitted.derivations.size() != subjects->size())
      return failure("submitted target plan has the wrong derivation arity");
    for (size_t index = 0; index < subjects->size(); ++index) {
      const soundness::DerivationPlan &derivation =
          submitted.derivations[index];
      if (llvm::Error check =
              checkPlan(derivation, *context.soundnessContext, request.limits,
                        "submitted[" + std::to_string(ordinal) + "].target[" +
                            std::to_string(targetIndex) + "].derivation[" +
                            std::to_string(index) + "]"))
        return check;
      auto derivationMember =
          derivationProvider.contains(request, *trace->finalArtifact, requested,
                                      *schema, (*subjects)[index], derivation);
      if (!derivationMember)
        return derivationMember.takeError();
      if (!*derivationMember)
        return failure(
            "submitted derivation is outside the listed finite domain");
    }
  }
  return llvm::Error::success();
}

const soundness::SecurityJudgment &
conclusionOf(const soundness::EvaluatedDerivation &derivation) {
  if (const auto *assumption =
          std::get_if<soundness::EvaluatedAssumption>(&derivation.node))
    return assumption->conclusion;
  return std::get<soundness::EvaluatedApplication>(derivation.node).conclusion;
}

llvm::Error checkHypothesesAndGames(const DerivationSurface &surface,
                                    const soundness::SecurityJudgment &judgment,
                                    bool allowAssumptionMarkers,
                                    llvm::StringRef location) {
  for (const soundness::Hypothesis &hypothesis : judgment.hypotheses) {
    if (const auto *proposition =
            std::get_if<soundness::PropositionInstance>(&hypothesis)) {
      if (std::find(surface.allowedHypotheses.begin(),
                    surface.allowedHypotheses.end(),
                    *proposition) == surface.allowedHypotheses.end())
        return candidateIneligibleFailure(
            location + ": conclusion uses a forbidden exact proposition");
      continue;
    }
    const auto &marker = std::get<soundness::AssumedJudgmentHolds>(hypothesis);
    if (!marker.assertedJudgment)
      return failure(location + ": conclusion has a malformed Assume marker");
    if (!allowAssumptionMarkers)
      return candidateIneligibleFailure(
          location + ": conclusion has no authorizing explicit Assume leaf");
  }
  for (const soundness::PrimitiveGameInstance &game :
       soundness::gameSupport(judgment.result))
    if (std::find(surface.allowedPrimitiveGames.begin(),
                  surface.allowedPrimitiveGames.end(),
                  game) == surface.allowedPrimitiveGames.end())
      return candidateIneligibleFailure(
          location + ": conclusion uses a forbidden primitive-game instance");
  return llvm::Error::success();
}

llvm::Expected<bool>
checkEvaluatedSurfaceImpl(const CompilerSemanticContext &context,
                          const DerivationSurface &surface,
                          const soundness::EvaluatedDerivation &derivation,
                          const std::string &location) {
  if (const auto *assumption =
          std::get_if<soundness::EvaluatedAssumption>(&derivation.node)) {
    if (llvm::Error input = checkHypothesesAndGames(
            surface, assumption->input, false, location + ".assume.input"))
      return std::move(input);
    size_t matchingMarkers = 0;
    for (const soundness::Hypothesis &hypothesis :
         assumption->conclusion.hypotheses) {
      const auto *marker =
          std::get_if<soundness::AssumedJudgmentHolds>(&hypothesis);
      if (marker && marker->assertedJudgment &&
          *marker->assertedJudgment == assumption->input)
        ++matchingMarkers;
    }
    if (matchingMarkers != 1)
      return error<bool>(
          location +
          ": evaluated Assume leaf lacks its unique canonical DERIVE marker");
    if (llvm::Error conclusion =
            checkHypothesesAndGames(surface, assumption->conclusion, true,
                                    location + ".assume.conclusion"))
      return std::move(conclusion);
    return true;
  }

  const auto &application =
      std::get<soundness::EvaluatedApplication>(derivation.node);
  if (!containsRef(surface.allowedBindingRefs, application.bindingRef))
    return candidateIneligible<bool>(location +
                                     ": derivation uses a forbidden binding");
  const soundness::RuleBinding *binding =
      context.soundnessContext->findBinding(application.bindingRef);
  if (!binding || !context.soundnessContext->findRule(binding->ruleRef))
    return error<bool>(location +
                       ": derivation binding resolves no executable rule");
  bool hasAssumptionLeaf = false;
  for (const auto &[port, premise] : application.premises) {
    if (!premise)
      return error<bool>(location +
                         ": evaluated derivation has a null premise");
    auto child = checkEvaluatedSurfaceImpl(context, surface, *premise,
                                           location + ".premises." + port);
    if (!child)
      return child.takeError();
    hasAssumptionLeaf = hasAssumptionLeaf || *child;
  }
  if (llvm::Error support = checkHypothesesAndGames(
          surface, application.conclusion, hasAssumptionLeaf, location))
    return std::move(support);
  return hasAssumptionLeaf;
}

llvm::Error
checkEvaluatedSurface(const CompilerSemanticContext &context,
                      const DerivationSurface &surface,
                      const soundness::EvaluatedDerivation &derivation,
                      const std::string &location) {
  auto checked =
      checkEvaluatedSurfaceImpl(context, surface, derivation, location);
  if (!checked)
    return checked.takeError();
  return llvm::Error::success();
}

llvm::Expected<soundness::ClosedBound>
takeBoundOperation(soundness::ClosedBoundOperationResult operation,
                   llvm::StringRef location) {
  if (!operation.accepted()) {
    if (!operation.refusal)
      return error<soundness::ClosedBound>(
          location +
          ": Soundness bound algebra returned no exact operation result");
    if (operation.refusal->code ==
        soundness::RuntimeRefusalCode::UnsupportedNormalForm)
      return candidateIneligible<soundness::ClosedBound>(
          location +
          ": Soundness bound algebra refused: " + operation.refusal->detail);
    return error<soundness::ClosedBound>(
        location +
        ": Soundness bound algebra refused: " + operation.refusal->detail);
  }
  return std::move(*operation.value);
}

llvm::Expected<soundness::ClosedBound>
projectBound(const soundness::SecurityJudgment &judgment,
             const BoundProjection &projection, llvm::StringRef location) {
  switch (projection.kind) {
  case BoundProjectionKind::ExtractionFailure: {
    if (judgment.index.notion !=
        soundness::SecurityNotion::ComputationalSpecialSoundness)
      return candidateIneligible<soundness::ClosedBound>(
          location +
          ": ExtractionFailure requires computational special soundness");
    const auto *extraction =
        std::get_if<soundness::ExtractionResult>(&judgment.result);
    if (!extraction)
      return error<soundness::ClosedBound>(
          location + ": extraction judgment has the wrong result shape");
    if (!extraction->failureBound)
      return candidateIneligible<soundness::ClosedBound>(
          location + ": target has no extraction-failure bound");
    return *extraction->failureBound;
  }
  case BoundProjectionKind::Scalar: {
    if (judgment.index.notion != soundness::SecurityNotion::StateRestoration &&
        judgment.index.notion != soundness::SecurityNotion::FiatShamir)
      return candidateIneligible<soundness::ClosedBound>(
          location + ": Scalar requires state-restoration or Fiat-Shamir");
    const auto *scalar = std::get_if<soundness::ScalarResult>(&judgment.result);
    if (!scalar)
      return error<soundness::ClosedBound>(
          location + ": scalar judgment has the wrong result shape");
    return scalar->bound;
  }
  case BoundProjectionKind::Round:
  case BoundProjectionKind::RoundMaximum: {
    if (judgment.index.notion != soundness::SecurityNotion::RoundByRound)
      return candidateIneligible<soundness::ClosedBound>(
          location + ": Round projection requires round-by-round soundness");
    const auto *rounds = std::get_if<soundness::RoundResult>(&judgment.result);
    if (!rounds)
      return error<soundness::ClosedBound>(
          location + ": round-by-round judgment has the wrong result shape");
    if (projection.kind == BoundProjectionKind::Round) {
      auto found =
          std::find_if(rounds->rounds.begin(), rounds->rounds.end(),
                       [&](const soundness::RoundResultEntry &round) {
                         return round.roundIndex == projection.exactRoundIndex;
                       });
      if (found == rounds->rounds.end())
        return candidateIneligible<soundness::ClosedBound>(
            location + ": target has no exact requested round");
      return found->bound;
    }
    std::vector<soundness::ClosedBound> alternatives;
    alternatives.reserve(rounds->rounds.size());
    for (const soundness::RoundResultEntry &round : rounds->rounds)
      alternatives.push_back(round.bound);
    return takeBoundOperation(
        soundness::closedBoundMaximum(alternatives,
                                      (location + ".round_maximum").str()),
        location);
  }
  }
  return error<soundness::ClosedBound>(location +
                                       ": unknown target-bound projection");
}

llvm::Expected<soundness::ClosedBound>
specializeProjectedBound(const soundness::SecurityJudgment &judgment,
                         const BoundProjection &projection,
                         const ResourceSubstitution &substitution,
                         llvm::StringRef location) {
  auto projected = projectBound(judgment, projection, location);
  if (!projected)
    return projected.takeError();
  return takeBoundOperation(
      soundness::closedBoundSpecialize(*projected, substitution,
                                       (location + ".specialize").str()),
      location);
}

std::vector<const ResolvedDerivation *>
resolvedTargetDerivations(const Candidate &candidate, llvm::StringRef key) {
  std::vector<const ResolvedDerivation *> result;
  for (const ResolvedDerivation &derivation : candidate.derivations)
    if (derivation.targetKey == key)
      result.push_back(&derivation);
  return result;
}

llvm::Error collectCandidateReadClaims(const BoundExpr &expression,
                                       const Candidate &candidate,
                                       llvm::StringRef targetKey,
                                       std::vector<soundness::ClaimRef> &claims,
                                       std::set<const BoundExpr *> &active) {
  if (!active.insert(&expression).second)
    return failure("candidate read collection encountered a cycle");
  auto appendMember = [&](uint64_t member) -> llvm::Error {
    auto derivations = resolvedTargetDerivations(candidate, targetKey);
    if (member >= derivations.size())
      return failure("candidate read member disappeared after evaluation");
    const auto *subject = std::get_if<soundness::ProtocolClaimSubject>(
        &conclusionOf(derivations[member]->result.root).subject.payload);
    if (!subject)
      return failure("candidate target conclusion is not a protocol claim");
    claims.push_back(subject->claim);
    return llvm::Error::success();
  };

  if (const auto *read =
          std::get_if<CandidateTargetRead>(&expression.payload)) {
    if (read->targetKey == targetKey) {
      if (const auto *exact = std::get_if<ExactTargetMember>(&read->members)) {
        if (llvm::Error member = appendMember(exact->ordinal)) {
          active.erase(&expression);
          return member;
        }
      } else {
        auto derivations = resolvedTargetDerivations(candidate, targetKey);
        for (size_t index = 0; index < derivations.size(); ++index) {
          if (llvm::Error member = appendMember(index)) {
            active.erase(&expression);
            return member;
          }
        }
      }
    }
  } else if (const auto *add = std::get_if<AddBounds>(&expression.payload)) {
    for (const BoundExprPtr &operand : add->operands) {
      if (llvm::Error nested = collectCandidateReadClaims(
              *operand, candidate, targetKey, claims, active)) {
        active.erase(&expression);
        return nested;
      }
    }
  } else if (const auto *maximum =
                 std::get_if<MaxBounds>(&expression.payload)) {
    for (const BoundExprPtr &operand : maximum->operands) {
      if (llvm::Error nested = collectCandidateReadClaims(
              *operand, candidate, targetKey, claims, active)) {
        active.erase(&expression);
        return nested;
      }
    }
  } else if (const auto *scale = std::get_if<ScaleBound>(&expression.payload)) {
    if (llvm::Error nested = collectCandidateReadClaims(
            *scale->operand, candidate, targetKey, claims, active)) {
      active.erase(&expression);
      return nested;
    }
  }
  active.erase(&expression);
  return llvm::Error::success();
}

llvm::Expected<bool> sourceMemberReachesCandidateRead(
    const CompilerRequest &request, const Candidate &candidate,
    const BoundExpr &candidateExpression, const SourceMemberOf &relation) {
  const RequestedTarget *target = findTarget(request, relation.targetKey);
  if (!target)
    return error<bool>("source baseline names no requested target");
  auto source = std::find(target->orderedSourceClaims.begin(),
                          target->orderedSourceClaims.end(),
                          relation.exactSourceClaimRef);
  if (source == target->orderedSourceClaims.end())
    return error<bool>("source baseline claim is outside its target frontier");
  const uint64_t sourceOrdinal =
      static_cast<uint64_t>(source - target->orderedSourceClaims.begin());
  auto lineage = resolveTargetLineage(candidate.trace, *target);
  if (!lineage)
    return lineage.takeError();
  std::vector<soundness::ClaimRef> reads;
  std::set<const BoundExpr *> active;
  if (llvm::Error collected = collectCandidateReadClaims(
          candidateExpression, candidate, relation.targetKey, reads, active))
    return std::move(collected);
  for (const LineageElement &element : *lineage)
    if (std::find(reads.begin(), reads.end(), element.claim) != reads.end() &&
        std::find(element.sourceOrdinals.begin(), element.sourceOrdinals.end(),
                  sourceOrdinal) != element.sourceOrdinals.end())
      return true;
  return false;
}

struct BoundEvalState {
  std::set<const BoundExpr *> active;
};

llvm::Expected<soundness::ClosedBound>
evaluateBoundExpr(const BoundExpr &expression, BoundExprMode mode,
                  const CompilerSemanticContext &context,
                  const CompilerRequest &request, const Candidate &candidate,
                  const BoundExpr &candidateExpression, BoundEvalState &state,
                  llvm::StringRef location) {
  if (!state.active.insert(&expression).second)
    return error<soundness::ClosedBound>(
        location + ": bound evaluation encountered a cycle");
  auto leave = [&]() { state.active.erase(&expression); };

  if (std::holds_alternative<ZeroBound>(expression.payload)) {
    if (mode != BoundExprMode::Baseline) {
      leave();
      return error<soundness::ClosedBound>(
          location + ": Zero is not a candidate-bound leaf");
    }
    leave();
    return soundness::ClosedBound{};
  }
  if (const auto *read =
          std::get_if<CandidateTargetRead>(&expression.payload)) {
    if (mode != BoundExprMode::Candidate) {
      leave();
      return error<soundness::ClosedBound>(
          location + ": candidate target read appears in a baseline");
    }
    auto derivations = resolvedTargetDerivations(candidate, read->targetKey);
    auto evaluateMember = [&](uint64_t member, llvm::StringRef readLocation)
        -> llvm::Expected<soundness::ClosedBound> {
      if (member >= derivations.size())
        return error<soundness::ClosedBound>(
            readLocation + ": candidate target member is out of range");
      const ResolvedDerivation &derivation = *derivations[member];
      auto substitution =
          read->resourceSubstitutions.find(derivation.schemaKey);
      if (substitution == read->resourceSubstitutions.end())
        return error<soundness::ClosedBound>(
            readLocation + ": candidate schema has no exact substitution");
      return specializeProjectedBound(conclusionOf(derivation.result.root),
                                      read->projection, substitution->second,
                                      readLocation);
    };

    if (const auto *exact = std::get_if<ExactTargetMember>(&read->members)) {
      auto result = evaluateMember(exact->ordinal, location);
      leave();
      return result;
    }
    const auto &fold = std::get<FoldTargetMembers>(read->members);
    std::vector<soundness::ClosedBound> values;
    values.reserve(derivations.size());
    for (size_t index = 0; index < derivations.size(); ++index) {
      auto value = evaluateMember(
          index, (location + ".members[" + llvm::Twine(index) + "]").str());
      if (!value) {
        leave();
        return value.takeError();
      }
      values.push_back(std::move(*value));
    }
    if (fold.aggregate == TargetFoldKind::Max) {
      auto result = takeBoundOperation(
          soundness::closedBoundMaximum(values, (location + ".maximum").str()),
          location);
      leave();
      return result;
    }
    soundness::ClosedBound sum;
    for (size_t index = 0; index < values.size(); ++index) {
      auto next = takeBoundOperation(
          soundness::closedBoundAdd(
              sum, values[index],
              (location + ".sum[" + llvm::Twine(index) + "]").str()),
          location);
      if (!next) {
        leave();
        return next.takeError();
      }
      sum = std::move(*next);
    }
    leave();
    return sum;
  }
  if (const auto *source = std::get_if<SourceProjection>(&expression.payload)) {
    if (mode != BoundExprMode::Baseline) {
      leave();
      return error<soundness::ClosedBound>(
          location + ": source projection appears in a candidate bound");
    }
    auto reaches = sourceMemberReachesCandidateRead(
        request, candidate, candidateExpression, source->targetRelation);
    if (!reaches) {
      leave();
      return reaches.takeError();
    }
    if (!*reaches) {
      leave();
      return candidateIneligible<soundness::ClosedBound>(
          location +
          ": source baseline is unrelated to every same-key candidate read");
    }
    soundness::DeriveOutcome derived = soundness::deriveSoundness(
        *context.soundnessContext,
        candidate.trace.source->observation.soundness, source->sourceTarget,
        source->sourceDerivationPlan);
    if (!derived.accepted()) {
      leave();
      if (!derived.refusal)
        return error<soundness::ClosedBound>(
            location +
            ": source baseline DERIVE returned no exact derivation result");
      return candidateIneligible<soundness::ClosedBound>(
          location +
          ": source baseline DERIVE refused: " + derived.refusal->detail);
    }
    if (derived.result->artifactId !=
        candidate.trace.source->observation.artifactId) {
      leave();
      return error<soundness::ClosedBound>(
          location + ": source baseline changed artifact identity");
    }
    if (llvm::Error surface = checkEvaluatedSurface(
            context, request.derivationSurface, derived.result->root,
            (location + ".surface").str())) {
      leave();
      return std::move(surface);
    }
    auto result = specializeProjectedBound(
        conclusionOf(derived.result->root), source->projection,
        source->resourceSubstitution, location);
    leave();
    return result;
  }

  const std::vector<BoundExprPtr> *operands = nullptr;
  bool maximum = false;
  if (const auto *add = std::get_if<AddBounds>(&expression.payload))
    operands = &add->operands;
  else if (const auto *max = std::get_if<MaxBounds>(&expression.payload)) {
    operands = &max->operands;
    maximum = true;
  }
  if (operands) {
    std::vector<soundness::ClosedBound> values;
    values.reserve(operands->size());
    for (size_t index = 0; index < operands->size(); ++index) {
      auto value = evaluateBoundExpr(
          *(*operands)[index], mode, context, request, candidate,
          candidateExpression, state,
          (location + ".operands[" + llvm::Twine(index) + "]").str());
      if (!value) {
        leave();
        return value.takeError();
      }
      values.push_back(std::move(*value));
    }
    if (maximum) {
      auto result = takeBoundOperation(
          soundness::closedBoundMaximum(values, (location + ".maximum").str()),
          location);
      leave();
      return result;
    }
    soundness::ClosedBound sum;
    for (size_t index = 0; index < values.size(); ++index) {
      auto next = takeBoundOperation(
          soundness::closedBoundAdd(
              sum, values[index],
              (location + ".sum[" + llvm::Twine(index) + "]").str()),
          location);
      if (!next) {
        leave();
        return next.takeError();
      }
      sum = std::move(*next);
    }
    leave();
    return sum;
  }

  const auto &scale = std::get<ScaleBound>(expression.payload);
  auto operand = evaluateBoundExpr(*scale.operand, mode, context, request,
                                   candidate, candidateExpression, state,
                                   (location + ".operand").str());
  if (!operand) {
    leave();
    return operand.takeError();
  }
  auto result = takeBoundOperation(
      soundness::closedBoundScale(scale.scale, *operand,
                                  (location + ".scale").str()),
      location);
  leave();
  return result;
}

llvm::Error checkSoundnessConstraint(const CompilerSemanticContext &context,
                                     const CompilerRequest &request,
                                     const Candidate &candidate,
                                     const SoundnessConstraint &constraint,
                                     uint64_t index) {
  const std::string location =
      "valid.soundness_constraints[" + std::to_string(index) + "]";
  BoundEvalState candidateState;
  auto candidateBound = evaluateBoundExpr(
      constraint.candidate, BoundExprMode::Candidate, context, request,
      candidate, constraint.candidate, candidateState, location + ".candidate");
  if (!candidateBound)
    return candidateBound.takeError();
  BoundEvalState baselineState;
  auto baseline = evaluateBoundExpr(
      constraint.baseline, BoundExprMode::Baseline, context, request, candidate,
      constraint.candidate, baselineState, location + ".baseline");
  if (!baseline)
    return baseline.takeError();
  auto allowed = takeBoundOperation(
      soundness::closedBoundAdd(*baseline, constraint.ceiling,
                                location + ".allowed"),
      location);
  if (!allowed)
    return allowed.takeError();

  soundness::ClosedBoundComparisonResult comparison = soundness::closedBoundLeq(
      *candidateBound, *allowed, location + ".compare");
  if (!comparison.accepted())
    return failure(location + ": Soundness bound comparison refused: " +
                   (comparison.refusal ? comparison.refusal->detail
                                       : "missing exact comparison result"));
  if (!*comparison.value)
    return candidateIneligibleFailure(
        location +
        ": candidate loss exceeds its exact coefficientwise ceiling");
  return llvm::Error::success();
}

int compareScores(const CompilerRequest &request, const ScoredCandidate &lhs,
                  const ScoredCandidate &rhs) {
  for (size_t index = 0; index < request.objectives.size(); ++index) {
    int comparison =
        lhs.objectiveValues[index].compare(rhs.objectiveValues[index]);
    if (!comparison)
      continue;
    if (request.objectives[index].direction == ObjectiveDirection::Minimize)
      return comparison;
    return -comparison;
  }
  if (lhs.candidate.candidate.ordinal < rhs.candidate.candidate.ordinal)
    return -1;
  if (lhs.candidate.candidate.ordinal > rhs.candidate.candidate.ordinal)
    return 1;
  return 0;
}

} // namespace

llvm::Expected<AuthenticatedArtifactHandle>
ArtifactSemantics::authenticateArtifact(ArtifactHandle artifact) const {
  if (!artifact)
    return error<AuthenticatedArtifactHandle>(
        "artifact authentication received a null artifact");
  if (llvm::Error shape = checkArtifact(*artifact))
    return std::move(shape);
  if (!validRef(exactRef()) || artifact->artifactSemanticsRef != exactRef())
    return error<AuthenticatedArtifactHandle>(
        "artifact does not name this exact artifact-semantics authority");
  if (!validRef(payloadTypeRef()) ||
      payloadTypeRef() != artifact->adapterPayload->exactTypeRef())
    return error<AuthenticatedArtifactHandle>(
        "artifact-semantics authority does not admit this exact payload type");
  auto authenticated = authenticate(*artifact->adapterPayload);
  if (!authenticated)
    return authenticated.takeError();
  if (llvm::Error shape = checkObservationShape(
          authenticated->artifactId, authenticated->soundness,
          authenticated->verifierProofReads))
    return std::move(shape);
  return AuthenticatedArtifactHandle(new AuthenticatedCompilerArtifact(
      std::move(artifact), std::move(*authenticated)));
}

bool derivationPlansEqual(const soundness::DerivationPlan &lhs,
                          const soundness::DerivationPlan &rhs) {
  std::set<PlanPair, PlanPairLess> active;
  std::set<PlanPair, PlanPairLess> done;
  return plansEqualImpl(lhs, rhs, active, done);
}

bool compilerPlansEqual(const CompilerPlan &lhs, const CompilerPlan &rhs) {
  if (!transformPlansEqual(lhs.transform, rhs.transform) ||
      lhs.targets.size() != rhs.targets.size())
    return false;
  for (size_t index = 0; index < lhs.targets.size(); ++index)
    if (!targetPlansEqual(lhs.targets[index], rhs.targets[index]))
      return false;
  return true;
}

IdentityTransformDomainProvider::IdentityTransformDomainProvider(
    ExactRef ref, ExactRef artifactSemanticsRef)
    : ref_(std::move(ref)),
      artifactSemanticsRef_(std::move(artifactSemanticsRef)) {}

llvm::Expected<std::vector<TransformPlan>>
IdentityTransformDomainProvider::enumerate(
    const CompilerRequest &,
    const AuthenticatedCompilerArtifact &source) const {
  if (!validRef(ref_) || !validRef(artifactSemanticsRef_) ||
      source.artifact->artifactSemanticsRef != artifactSemanticsRef_)
    return error<std::vector<TransformPlan>>(
        "identity transform provider has incompatible exact semantics");
  return std::vector<TransformPlan>{TransformPlan()};
}

llvm::Expected<bool> IdentityTransformDomainProvider::contains(
    const CompilerRequest &, const AuthenticatedCompilerArtifact &source,
    const TransformPlan &plan) const {
  if (!validRef(ref_) || !validRef(artifactSemanticsRef_) ||
      source.artifact->artifactSemanticsRef != artifactSemanticsRef_)
    return error<bool>(
        "identity transform provider has incompatible exact semantics");
  return plan.applications.empty();
}

ListedDerivationPlanDomainProvider::ListedDerivationPlanDomainProvider(
    ExactRef ref, std::vector<ListedDerivationAlternative> alternatives)
    : ref_(std::move(ref)), alternatives_(std::move(alternatives)) {}

llvm::Expected<std::vector<soundness::DerivationPlan>>
ListedDerivationPlanDomainProvider::enumerate(
    const CompilerRequest &, const AuthenticatedCompilerArtifact &,
    const RequestedTarget &target, const TargetSchema &schema,
    const soundness::SecuritySubject &subject) const {
  if (!validRef(ref_))
    return error<std::vector<soundness::DerivationPlan>>(
        "listed derivation provider reference is not exact");
  std::vector<soundness::DerivationPlan> result;
  for (const ListedDerivationAlternative &alternative : alternatives_)
    if (alternative.targetKey == target.key &&
        alternative.schemaKey == schema.key && alternative.subject == subject)
      result.push_back(alternative.plan);
  return result;
}

llvm::Expected<bool> ListedDerivationPlanDomainProvider::contains(
    const CompilerRequest &request,
    const AuthenticatedCompilerArtifact &artifact,
    const RequestedTarget &target, const TargetSchema &schema,
    const soundness::SecuritySubject &subject,
    const soundness::DerivationPlan &plan) const {
  auto alternatives = enumerate(request, artifact, target, schema, subject);
  if (!alternatives)
    return alternatives.takeError();
  return std::any_of(alternatives->begin(), alternatives->end(),
                     [&](const soundness::DerivationPlan &candidate) {
                       return derivationPlansEqual(candidate, plan);
                     });
}

llvm::Error
checkCanonicalApplication(const AuthenticatedCompilerArtifact &before,
                          const TransformApplication &requested,
                          const CanonicalTransformApplication &canonical) {
  if (canonical.familyRef != requested.familyRef)
    return failure(
        "transform recognizer changed the exact transform family reference");
  if (canonical.parameters != requested.parameters)
    return failure(
        "transform recognizer changed an explicit transform parameter");
  if (canonical.orderedConsumed.empty() ||
      canonical.orderedConsumed.size() != requested.matchedClaims.size())
    return failure(
        "transform recognizer changed the matched claim occurrence set");
  std::set<uint64_t> canonicalIndices;
  for (const soundness::ClaimRef &claim : canonical.orderedConsumed) {
    if (!containsClaim(before, claim) ||
        !canonicalIndices.insert(claim.claimIndex).second)
      return failure(
          "transform recognizer returned an unknown or duplicate claim");
    if (std::find(requested.matchedClaims.begin(),
                  requested.matchedClaims.end(),
                  claim) == requested.matchedClaims.end())
      return failure(
          "transform recognizer introduced a claim outside the requested "
          "match");
  }
  return llvm::Error::success();
}

llvm::Error
checkCorrespondences(const AuthenticatedCompilerArtifact &before,
                     const AuthenticatedCompilerArtifact &after,
                     const CanonicalTransformApplication &canonical,
                     uint64_t applicationIndex,
                     const std::vector<ClaimCorrespondence> &correspondences) {
  if (correspondences.empty())
    return failure(
        "transform checker returned no application-level correspondence");
  size_t primaryCount = 0;
  std::set<uint64_t> consumedIndices;
  std::set<uint64_t> producedIndices;
  for (const ClaimCorrespondence &correspondence : correspondences) {
    if (correspondence.applicationIndex != applicationIndex ||
        correspondence.familyRef != canonical.familyRef)
      return failure(
          "transform checker changed the application index or exact family");
    if (correspondence.orderedConsumed.empty() ||
        correspondence.orderedProduced.empty())
      return failure(
          "transform correspondence must consume and produce nonempty "
          "ordered claim vectors");
    const bool primary =
        correspondence.orderedConsumed == canonical.orderedConsumed;
    if (primary) {
      ++primaryCount;
    } else {
      if (correspondence.orderedConsumed.size() != 1 ||
          correspondence.orderedProduced.size() != 1)
        return failure(
            "a non-primary correspondence must be an explicit one-to-one "
            "survivor remap");
      if (std::find(canonical.orderedConsumed.begin(),
                    canonical.orderedConsumed.end(),
                    correspondence.orderedConsumed.front()) !=
          canonical.orderedConsumed.end())
        return failure(
            "a survivor remap cannot consume part of the primary match");
    }
    for (const soundness::ClaimRef &claim : correspondence.orderedConsumed)
      if (!containsClaim(before, claim) ||
          !consumedIndices.insert(claim.claimIndex).second)
        return failure(
            "transform correspondence has an unknown or multiply consumed "
            "predecessor claim");
    for (const ProducedClaim &produced : correspondence.orderedProduced)
      if (produced.outputRole.empty() ||
          !containsClaim(after, produced.claim) ||
          !producedIndices.insert(produced.claim.claimIndex).second)
        return failure("transform correspondence has an unknown, duplicate, or "
                       "unlabelled successor claim");
  }
  if (primaryCount != 1)
    return failure(
        "transform checker must return one unique primary correspondence for "
        "the canonical match");
  return llvm::Error::success();
}

bool operator==(const PreservationClaim &lhs, const PreservationClaim &rhs) {
  return lhs.propertyRef == rhs.propertyRef && lhs.familyRef == rhs.familyRef &&
         lhs.applicationIndex == rhs.applicationIndex;
}

llvm::Expected<CheckedTransformTrace>
realizeTransform(const CompilerSemanticContext &context,
                 const CompilerRequest &request, const TransformPlan &plan) {
  if (!request.source)
    return error<CheckedTransformTrace>(
        "transform realization has no owned source artifact");
  auto source = authenticateArtifact(context, request.source);
  if (!source)
    return source.takeError();
  if (llvm::Error structure =
          checkTransformPlanStructure(context, request, plan, "realize"))
    return std::move(structure);

  CheckedTransformTrace trace{*source, *source, {}};
  AuthenticatedArtifactHandle predecessor = *source;
  for (size_t index = 0; index < plan.applications.size(); ++index) {
    const TransformApplication &application = plan.applications[index];
    auto family = context.transformFamilies.find(application.familyRef.id);
    if (family == context.transformFamilies.end() || !family->second ||
        family->second->exactRef() != application.familyRef ||
        family->second->artifactSemanticsRef() !=
            predecessor->artifact->artifactSemanticsRef)
      return error<CheckedTransformTrace>(
          "transform application names an unknown exact family");
    auto canonical = family->second->recognize(predecessor, application);
    if (!canonical)
      return canonical.takeError();
    if (llvm::Error check =
            checkCanonicalApplication(*predecessor, application, *canonical))
      return std::move(check);
    auto successor = family->second->realize(predecessor, *canonical);
    if (!successor)
      return successor.takeError();
    if (!*successor)
      return error<CheckedTransformTrace>(
          "transform realization returned a null owned artifact");
    if ((*successor)->artifactSemanticsRef !=
        family->second->artifactSemanticsRef())
      return error<CheckedTransformTrace>(
          "transform successor changed its declared artifact semantics");
    auto authenticated = authenticateArtifact(context, *successor);
    if (!authenticated)
      return authenticated.takeError();
    auto correspondences =
        family->second->check(predecessor, *authenticated, *canonical, index);
    if (!correspondences)
      return correspondences.takeError();
    if (llvm::Error checked = checkCorrespondences(
            *predecessor, **authenticated, *canonical, index, *correspondences))
      return std::move(checked);
    trace.correspondences.insert(trace.correspondences.end(),
                                 correspondences->begin(),
                                 correspondences->end());
    // Collected after the check and never consulted by it. A family that
    // preserves a property does so by an argument LEGAL does not contain, so
    // what the trace records is the claim and its author, not a verdict.
    std::vector<PreservationClaim> claims = family->second->preservationClaims(
        predecessor, *authenticated, *canonical, index);
    for (const PreservationClaim &claim : claims) {
      if (claim.propertyRef.empty())
        return error<CheckedTransformTrace>(
            "a preservation claim names no property");
      if (claim.familyRef != family->second->exactRef() ||
          claim.applicationIndex != index)
        return error<CheckedTransformTrace>(
            "a preservation claim names another family or application");
    }
    trace.preservationClaims.insert(trace.preservationClaims.end(),
                                    claims.begin(), claims.end());
    predecessor = std::move(*authenticated);
  }
  trace.finalArtifact = std::move(predecessor);
  return trace;
}

llvm::Expected<PlanDomain> domain(const CompilerSemanticContext &context,
                                  const CompilerRequest &request) {
  if (llvm::Error check = checkRequest(context, request))
    return std::move(check);
  auto source = authenticateArtifact(context, request.source);
  if (!source)
    return source.takeError();
  const TransformDomainProvider *transformProvider =
      findTransformProvider(context, request.transformDomainProviderRef);
  const DerivationPlanDomainProvider *derivationProvider =
      findDerivationProvider(context, request.derivationPlanProviderRef);

  if (const auto *submitted =
          std::get_if<SubmittedFrontierScope>(&request.comparisonScope)) {
    if (submitted->plans.size() > request.limits.maxDomainPlans)
      return error<PlanDomain>(
          "submitted frontier exceeds the finite plan-domain bound");
    for (size_t ordinal = 0; ordinal < submitted->plans.size(); ++ordinal) {
      if (llvm::Error check = checkSubmittedPlan(
              context, request, *transformProvider, *derivationProvider,
              submitted->plans[ordinal], ordinal))
        return std::move(check);
      for (size_t prior = 0; prior < ordinal; ++prior)
        if (compilerPlansEqual(submitted->plans[prior],
                               submitted->plans[ordinal]))
          return error<PlanDomain>(
              "submitted frontier contains duplicate compiler plans");
    }
    return PlanDomain{ComparisonScopeKind::SubmittedFrontier, submitted->plans};
  }

  auto transforms = transformProvider->enumerate(request, **source);
  if (!transforms)
    return transforms.takeError();
  if (transforms->size() > request.limits.maxDomainPlans)
    return error<PlanDomain>(
        "transform provider exceeded the finite plan-domain bound");

  PlanDomain result;
  result.scope = ComparisonScopeKind::ClosedDomain;
  for (size_t transformIndex = 0; transformIndex < transforms->size();
       ++transformIndex) {
    const TransformPlan &transform = (*transforms)[transformIndex];
    if (llvm::Error structure = checkTransformPlanStructure(
            context, request, transform,
            "domain.transform[" + std::to_string(transformIndex) + "]"))
      return std::move(structure);
    auto trace = realizeTransform(context, request, transform);
    if (!trace)
      return trace.takeError();

    std::vector<CompilerPlan> products{CompilerPlan{transform, {}}};
    for (const RequestedTarget &target : request.targets) {
      auto targetPlans = enumerateTargetPlans(
          context, request, *derivationProvider, target, *trace);
      if (!targetPlans)
        return targetPlans.takeError();
      if (targetPlans->empty()) {
        products.clear();
        break;
      }
      if (llvm::Error cap = capProduct(products.size(), targetPlans->size(),
                                       request.limits.maxDomainPlans,
                                       "compiler plan product"))
        return std::move(cap);
      std::vector<CompilerPlan> next;
      for (const CompilerPlan &prefix : products)
        for (const CompilerTargetPlan &targetPlan : *targetPlans) {
          CompilerPlan expanded = prefix;
          expanded.targets.push_back(targetPlan);
          next.push_back(std::move(expanded));
        }
      products = std::move(next);
    }
    for (CompilerPlan &plan : products) {
      for (const CompilerPlan &prior : result.plans)
        if (compilerPlansEqual(prior, plan))
          return error<PlanDomain>(
              "closed domain contains duplicate compiler plans");
      result.plans.push_back(std::move(plan));
      if (result.plans.size() > request.limits.maxDomainPlans)
        return error<PlanDomain>("closed domain exceeds its finite plan bound");
    }
  }
  return result;
}

namespace {

bool planDomainsEqual(const PlanDomain &lhs, const PlanDomain &rhs) {
  if (lhs.scope != rhs.scope || lhs.plans.size() != rhs.plans.size())
    return false;
  for (size_t ordinal = 0; ordinal < lhs.plans.size(); ++ordinal)
    if (!compilerPlansEqual(lhs.plans[ordinal], rhs.plans[ordinal]))
      return false;
  return true;
}

llvm::Expected<PlanDomain>
recomputeExactDomain(const CompilerSemanticContext &context,
                     const CompilerRequest &request,
                     const PlanDomain &submitted) {
  auto canonical = domain(context, request);
  if (!canonical)
    return canonical.takeError();
  if (!planDomainsEqual(*canonical, submitted))
    return error<PlanDomain>(
        "stage input is not the exact DOMAIN for this context and request");
  return canonical;
}

llvm::Expected<Candidate>
realizeCanonical(const CompilerSemanticContext &context,
                 const CompilerRequest &request, const PlanDomain &planDomain,
                 uint64_t ordinal) {
  if (ordinal >= planDomain.plans.size())
    return error<Candidate>("candidate ordinal is outside the plan domain");
  const CompilerPlan &plan = planDomain.plans[ordinal];
  auto trace = realizeTransform(context, request, plan.transform);
  if (!trace)
    return trace.takeError();

  Candidate candidate;
  candidate.ordinal = ordinal;
  candidate.plan = plan;
  candidate.trace = std::move(*trace);
  for (size_t targetIndex = 0; targetIndex < plan.targets.size();
       ++targetIndex) {
    const CompilerTargetPlan &targetPlan = plan.targets[targetIndex];
    if (!targetPlan.schemaKey)
      continue;
    if (targetIndex >= request.targets.size())
      return error<Candidate>(
          "candidate target plan exceeds requested target order");
    auto subjects =
        resolveTargetSubjects(candidate.trace, request.targets[targetIndex]);
    if (!subjects)
      return subjects.takeError();
    if (subjects->size() != targetPlan.derivations.size())
      return error<Candidate>(
          "candidate derivation plans do not cover resolved subjects");
    const TargetSchema *schema = findSchema(request, *targetPlan.schemaKey);
    if (!schema)
      return error<Candidate>("candidate target schema is absent after DOMAIN");
    for (size_t derivationIndex = 0;
         derivationIndex < targetPlan.derivations.size(); ++derivationIndex) {
      const soundness::DerivationPlan &planned =
          targetPlan.derivations[derivationIndex];
      soundness::DerivationTarget target{(*subjects)[derivationIndex],
                                         schema->index, schema->resources};
      soundness::DeriveOutcome derived = soundness::deriveSoundness(
          *context.soundnessContext,
          candidate.trace.finalArtifact->observation.soundness, target,
          planned);
      if (!derived.accepted()) {
        if (!derived.refusal)
          return error<Candidate>(
              "DERIVE returned no exact candidate derivation result");
        return candidateIneligible<Candidate>("DERIVE refused candidate: " +
                                              derived.refusal->detail);
      }
      if (derived.result->artifactId !=
          candidate.trace.finalArtifact->observation.artifactId)
        return error<Candidate>(
            "DERIVE changed the candidate artifact identity");
      candidate.derivations.push_back({targetPlan.targetKey,
                                       *targetPlan.schemaKey,
                                       std::move(*derived.result)});
    }
  }
  return candidate;
}

llvm::Expected<ValidCandidate>
validateCanonical(const CompilerSemanticContext &context,
                  const CompilerRequest &request, const PlanDomain &planDomain,
                  uint64_t ordinal) {
  auto candidate = realizeCanonical(context, request, planDomain, ordinal);
  if (!candidate)
    return candidate.takeError();

  for (const ResolvedDerivation &derivation : candidate->derivations) {
    if (llvm::Error surface = checkEvaluatedSurface(
            context, request.derivationSurface, derivation.result.root,
            "valid." + derivation.targetKey))
      return std::move(surface);
  }
  for (size_t index = 0; index < request.soundnessConstraints.size(); ++index)
    if (llvm::Error constraint = checkSoundnessConstraint(
            context, request, *candidate, request.soundnessConstraints[index],
            index))
      return std::move(constraint);

  ValidCandidate valid;
  valid.candidate = std::move(*candidate);
  return valid;
}

llvm::Expected<ScoredCandidate>
scoreValidated(const CompilerSemanticContext &context,
               const CompilerRequest &request, ValidCandidate candidate) {
  ScoredCandidate scored;
  scored.candidate = std::move(candidate);
  for (size_t objectiveIndex = 0; objectiveIndex < request.objectives.size();
       ++objectiveIndex) {
    const Objective &objective = request.objectives[objectiveIndex];
    if (objective.kind != ObjectiveKind::StaticProofBytes)
      return error<ScoredCandidate>("SCORE received an unsupported objective");
    const CodecWidthProfile *profile =
        findWidthProfile(context, objective.codecWidthProfileRef);
    if (!profile)
      return error<ScoredCandidate>(
          "SCORE cannot resolve the exact codec-width profile");
    registry::Rational total;
    for (const VerifierProofRead &read :
         scored.candidate.candidate.trace.finalArtifact->observation
             .verifierProofReads) {
      auto width = profile->codecs.find(read.codecRef.id);
      if (width == profile->codecs.end() ||
          width->second.codecRef != read.codecRef)
        return candidateIneligible<ScoredCandidate>(
            "SCORE has no exact width for an observed proof codec");
      auto count = registry::Rational::fromDecimal(std::to_string(read.count));
      if (!count)
        return count.takeError();
      total = total.add(width->second.byteWidth.mul(*count));
    }
    scored.objectiveValues.push_back(std::move(total));
  }
  return scored;
}

struct CandidateIneligible {};

template <typename T>
using CandidateOutcome = std::variant<T, CandidateIneligible>;

template <typename T>
llvm::Expected<CandidateOutcome<T>>
classifyCandidateOutcome(llvm::Expected<T> evaluated) {
  if (evaluated)
    return CandidateOutcome<T>(std::in_place_type<T>, std::move(*evaluated));

  llvm::Error remaining =
      llvm::handleErrors(evaluated.takeError(),
                         [](const CandidateIneligibleError &) -> llvm::Error {
                           return llvm::Error::success();
                         });
  if (remaining)
    return std::move(remaining);
  return CandidateOutcome<T>(std::in_place_type<CandidateIneligible>);
}

using CandidateEvaluation = CandidateOutcome<ScoredCandidate>;

llvm::Expected<CandidateEvaluation>
evaluateCandidateCanonical(const CompilerSemanticContext &context,
                           const CompilerRequest &request,
                           const PlanDomain &planDomain, uint64_t ordinal) {
  auto validated = classifyCandidateOutcome(
      validateCanonical(context, request, planDomain, ordinal));
  if (!validated)
    return validated.takeError();
  if (auto *ineligible = std::get_if<CandidateIneligible>(&*validated))
    return CandidateEvaluation(std::in_place_type<CandidateIneligible>,
                               std::move(*ineligible));

  auto scored = classifyCandidateOutcome(scoreValidated(
      context, request, std::move(std::get<ValidCandidate>(*validated))));
  if (!scored)
    return scored.takeError();
  return std::move(*scored);
}

llvm::Expected<Selection>
selectCanonical(const CompilerSemanticContext &context,
                const CompilerRequest &request, const PlanDomain &planDomain) {
  std::optional<ScoredCandidate> best;
  for (size_t ordinal = 0; ordinal < planDomain.plans.size(); ++ordinal) {
    auto evaluated =
        evaluateCandidateCanonical(context, request, planDomain, ordinal);
    if (!evaluated)
      return evaluated.takeError();
    if (std::holds_alternative<CandidateIneligible>(*evaluated))
      continue;
    ScoredCandidate scored = std::move(std::get<ScoredCandidate>(*evaluated));
    if (!best || compareScores(request, scored, *best) < 0)
      best = std::move(scored);
  }
  Selection selection;
  if (best)
    selection.selectedOrdinal = best->candidate.candidate.ordinal;
  return selection;
}

} // namespace

llvm::Expected<Candidate> realize(const CompilerSemanticContext &context,
                                  const CompilerRequest &request,
                                  const PlanDomain &planDomain,
                                  uint64_t ordinal) {
  auto canonical = recomputeExactDomain(context, request, planDomain);
  if (!canonical)
    return canonical.takeError();
  return realizeCanonical(context, request, *canonical, ordinal);
}

llvm::Expected<ValidCandidate> validate(const CompilerSemanticContext &context,
                                        const CompilerRequest &request,
                                        const PlanDomain &planDomain,
                                        uint64_t ordinal) {
  auto canonical = recomputeExactDomain(context, request, planDomain);
  if (!canonical)
    return canonical.takeError();
  return validateCanonical(context, request, *canonical, ordinal);
}

llvm::Expected<ScoredCandidate> score(const CompilerSemanticContext &context,
                                      const CompilerRequest &request,
                                      const PlanDomain &planDomain,
                                      uint64_t ordinal) {
  auto canonical = recomputeExactDomain(context, request, planDomain);
  if (!canonical)
    return canonical.takeError();
  auto valid = validateCanonical(context, request, *canonical, ordinal);
  if (!valid)
    return valid.takeError();
  return scoreValidated(context, request, std::move(*valid));
}

llvm::Expected<Selection> select(const CompilerSemanticContext &context,
                                 const CompilerRequest &request,
                                 const PlanDomain &planDomain) {
  auto canonical = recomputeExactDomain(context, request, planDomain);
  if (!canonical)
    return canonical.takeError();
  return selectCanonical(context, request, *canonical);
}

llvm::Expected<CompilerResult> compile(const CompilerSemanticContext &context,
                                       const CompilerRequest &request) {
  auto planDomain = domain(context, request);
  if (!planDomain)
    return planDomain.takeError();

  auto selected = selectCanonical(context, request, *planDomain);
  if (!selected)
    return selected.takeError();
  return CompilerResult{selected->selectedOrdinal};
}

llvm::Expected<DecisionVerdict>
checkDecision(const CompilerSemanticContext &context,
              const CompilerRequest &request, const CompilerResult &submitted) {
  auto recomputed = compile(context, request);
  if (!recomputed)
    return recomputed.takeError();
  if (submitted.selectedOrdinal != recomputed->selectedOrdinal)
    return DecisionVerdict{false, "result selected the wrong domain ordinal"};
  return DecisionVerdict{true, "compiler result exactly matches recomputation"};
}

} // namespace zkc::compiler
