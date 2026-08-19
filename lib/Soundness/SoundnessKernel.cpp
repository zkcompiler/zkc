//===- SoundnessKernel.cpp - Owned theorem/soundness core ----------------===//
#include "zkc/Soundness/SoundnessKernel.h"

#include "SoundnessSchemaValidation.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <type_traits>
#include <utility>

namespace zkc::soundness {

bool operator==(const ExactRef &lhs, const ExactRef &rhs) {
  return lhs.id == rhs.id && lhs.sourceRevision == rhs.sourceRevision;
}

bool operator!=(const ExactRef &lhs, const ExactRef &rhs) {
  return !(lhs == rhs);
}

bool operator==(const SecurityIndex &lhs, const SecurityIndex &rhs) {
  return lhs.notion == rhs.notion && lhs.track == rhs.track &&
         lhs.variant == rhs.variant && lhs.model == rhs.model &&
         lhs.quantification == rhs.quantification;
}

bool matchSecurityIndex(const SecurityIndexPattern &pattern,
                        const SecurityIndex &index,
                        std::optional<SecurityQuantification> &binding) {
  // Every coordinate but the one the variable may cover is compared
  // exactly, so a pattern can never admit a premise in a track or a
  // notion it did not name.
  SecurityIndex expected = pattern.index;
  if (!pattern.quantificationVariable.empty())
    expected.quantification = index.quantification;
  if (expected != index)
    return false;
  if (pattern.quantificationVariable.empty())
    return true;
  // A rule may name one variable across several premises; the second
  // occurrence is a constraint, not a rebinding.
  if (binding && *binding != index.quantification)
    return false;
  binding = index.quantification;
  return true;
}

SecurityIndex instantiateSecurityIndex(const SecurityIndexPattern &pattern,
                                       SecurityQuantification binding) {
  SecurityIndex index = pattern.index;
  if (!pattern.quantificationVariable.empty())
    index.quantification = binding;
  return index;
}

bool operator!=(const SecurityIndex &lhs, const SecurityIndex &rhs) {
  return !(lhs == rhs);
}

bool operator==(const AlgebraInstanceValue &lhs,
                const AlgebraInstanceValue &rhs) {
  return lhs.group == rhs.group && lhs.fieldClass == rhs.fieldClass &&
         lhs.fieldOrder.compare(rhs.fieldOrder) == 0;
}

QuantityTemplate QuantityTemplate::rational(registry::Rational value) {
  QuantityTemplate result;
  result.kind = QuantityKind::RationalLiteral;
  result.literal = value;
  return result;
}

QuantityTemplate QuantityTemplate::named(QuantityKind kind, std::string name) {
  QuantityTemplate result;
  result.kind = kind;
  result.name = std::move(name);
  return result;
}

QuantityTemplate
QuantityTemplate::node(QuantityKind kind,
                       std::vector<QuantityTemplate> operands) {
  QuantityTemplate result;
  result.kind = kind;
  result.operands = std::move(operands);
  return result;
}

namespace {

RuleWfResult accepted() { return {}; }

RuleWfResult refuse(RuleWfRefusalCode code, std::string location,
                    std::string detail) {
  return RuleWfResult{
      RuleWfRefusal{code, std::move(location), std::move(detail)}};
}

bool isNumeric(ValueSort sort) {
  return sort == ValueSort::Integer || sort == ValueSort::Rational;
}

bool validSecurityTrack(SecurityTrack track) {
  switch (track) {
  case SecurityTrack::Soundness:
  case SecurityTrack::Knowledge:
  case SecurityTrack::Completeness:
    return true;
  }
  return false;
}

bool validResultSchema(ResultSchema result) {
  switch (result) {
  case ResultSchema::Extraction:
  case ResultSchema::Round:
  case ResultSchema::Scalar:
    return true;
  }
  return false;
}

bool validValueSort(ValueSort sort) {
  switch (sort) {
  case ValueSort::Integer:
  case ValueSort::Rational:
  case ValueSort::String:
  case ValueSort::Boolean:
  case ValueSort::Subject:
  case ValueSort::ReductionContract:
  case ValueSort::PathTransition:
  case ValueSort::RoundAdjacency:
  case ValueSort::AlgebraInstance:
  case ValueSort::SrsInstance:
  case ValueSort::FriDomainInstance:
    return true;
  }
  return false;
}

constexpr const char *kProtocolClaimSchema = "zkc.subject.protocol_claim";
constexpr const char *kConsumedClaimVectorSchema =
    "zkc.subject.consumed_claim_vector";
constexpr const char *kMachineDeciderRevision = "zkc.soundness";

bool validSubjectSchemaImpl(const std::string &lookupRef,
                            const SubjectSchema &schema) {
  if (lookupRef.empty() || schema.ref != lookupRef ||
      std::any_of(schema.argumentTypes.begin(), schema.argumentTypes.end(),
                  [](ValueSort sort) { return !validValueSort(sort); }))
    return false;

  switch (schema.kind) {
  case SubjectSchemaKind::ProtocolClaim:
    return schema.ref == kProtocolClaimSchema && schema.argumentTypes.empty();
  case SubjectSchemaKind::ConsumedClaimVector:
    return schema.ref == kConsumedClaimVectorSchema &&
           schema.argumentTypes.empty();
  case SubjectSchemaKind::ExternalInstance:
    return schema.ref != kProtocolClaimSchema &&
           schema.ref != kConsumedClaimVectorSchema &&
           !schema.argumentTypes.empty();
  }
  return false;
}

struct CanonicalMachineDecider {
  const char *id;
  std::vector<ValueSort> argumentTypes;
};

CanonicalMachineDecider canonicalMachineDecider(MachineDeciderKind kind) {
  switch (kind) {
  case MachineDeciderKind::OneMessageRole:
    return {"zkc.side.one_message_role", {ValueSort::ReductionContract}};
  case MachineDeciderKind::MultiplicitiesMatchTable:
    return {"zkc.side.multiplicities_match_table",
            {ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::LookupFitsCharacteristic:
    return {"zkc.side.lookup_fits_characteristic",
            {ValueSort::Integer, ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::SpaceEmbeds:
    return {"zkc.side.space_embeds",
            {ValueSort::ReductionContract, ValueSort::Integer}};
  case MachineDeciderKind::BoundBites:
    return {"zkc.side.bound_bites", {ValueSort::ReductionContract}};
  case MachineDeciderKind::FieldClass:
    return {"zkc.side.field_class",
            {ValueSort::ReductionContract, ValueSort::String}};
  case MachineDeciderKind::SpaceCoversArity:
    return {"zkc.side.space_covers_arity",
            {ValueSort::ReductionContract, ValueSort::Integer}};
  case MachineDeciderKind::BatchArity:
    return {"zkc.side.batch_arity", {ValueSort::Integer}};
  case MachineDeciderKind::SpaceCoversBatch:
    return {"zkc.side.space_covers_batch",
            {ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::SamePoint:
    return {"zkc.side.same_point", {ValueSort::ReductionContract}};
  case MachineDeciderKind::BatchAfterMaterial:
    return {"zkc.side.batch_after_material", {ValueSort::ReductionContract}};
  case MachineDeciderKind::FriShape:
    return {"zkc.side.fri_shape",
            {ValueSort::Integer, ValueSort::Integer, ValueSort::Integer,
             ValueSort::Integer}};
  case MachineDeciderKind::JohnsonFoldParam:
    return {"zkc.side.johnson_fold_param", {ValueSort::Integer}};
  case MachineDeciderKind::JohnsonSlack:
    return {"zkc.side.johnson_slack",
            {ValueSort::Rational, ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::JohnsonMultiplicity:
    return {"zkc.side.johnson_multiplicity",
            {ValueSort::Integer, ValueSort::Rational, ValueSort::Integer}};
  case MachineDeciderKind::JohnsonDelta:
    return {"zkc.side.johnson_delta",
            {ValueSort::Rational, ValueSort::Rational, ValueSort::Integer}};
  case MachineDeciderKind::UdrDomainFloor:
    return {"zkc.side.udr_domain_floor",
            {ValueSort::Integer, ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::UdrThetaWindow:
    return {"zkc.side.udr_theta_window",
            {ValueSort::Rational, ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::PowPinned:
    return {"zkc.side.pow_pinned", {ValueSort::RoundAdjacency}};
  case MachineDeciderKind::PowAdjacent:
    return {"zkc.side.pow_adjacent", {ValueSort::RoundAdjacency}};
  case MachineDeciderKind::RandomWordsEtaFloor:
    return {"zkc.side.random_words_eta_floor",
            {ValueSort::Rational, ValueSort::Integer, ValueSort::Integer}};
  case MachineDeciderKind::ThresholdDeltaWindow:
    return {"zkc.side.threshold_delta_window",
            {ValueSort::Rational, ValueSort::Integer}};
  case MachineDeciderKind::DuplexSpine:
    return {"zkc.side.duplex_spine", {ValueSort::PathTransition}};
  case MachineDeciderKind::CodecBiasDeclared:
    return {"zkc.side.codec_bias_declared", {ValueSort::PathTransition}};
  }
  return {"", {}};
}

bool validMachineDeciderImpl(const std::string &lookupRef,
                             const MachineDeciderDefinition &definition) {
  CanonicalMachineDecider canonical = canonicalMachineDecider(definition.kind);
  return !lookupRef.empty() &&
         definition.ref == ExactRef{canonical.id, kMachineDeciderRevision} &&
         lookupRef == definition.ref.id &&
         definition.argumentTypes == canonical.argumentTypes;
}

bool validContractRoundField(ContractRoundField field) {
  switch (field) {
  case ContractRoundField::ChallengeSpace:
  case ContractRoundField::ChallengeCount:
  case ContractRoundField::RoundDegree:
  case ContractRoundField::ChallengeSpaceLog2:
    return true;
  }
  return false;
}

bool validPremiseCoordinateField(PremiseCoordinateField field) {
  switch (field) {
  case PremiseCoordinateField::Arity:
  case PremiseCoordinateField::ChallengeSpace:
    return true;
  }
  return false;
}

bool validExactRef(const ExactRef &ref) {
  return !ref.id.empty() && !ref.sourceRevision.empty();
}

bool validIndexShape(const SecurityIndex &index) {
  if (!validSecurityTrack(index.track))
    return false;
  // The completeness notion and track come together or not at all: a
  // completeness judgment prices honest-prover acceptance and must not read
  // as a soundness or knowledge claim, and no soundness notion may borrow
  // the completeness spelling (docs/spec/soundness.md §3.2).
  if ((index.notion == SecurityNotion::Completeness) !=
      (index.track == SecurityTrack::Completeness))
    return false;
  switch (index.notion) {
  case SecurityNotion::SpecialSoundness:
  case SecurityNotion::ComputationalSpecialSoundness:
    return index.variant.empty() && index.model.empty();
  case SecurityNotion::RoundByRound:
  case SecurityNotion::StateRestoration:
    return !index.variant.empty() && index.model.empty();
  case SecurityNotion::FiatShamir:
    return !index.variant.empty() && index.model == "duplex";
  case SecurityNotion::Completeness:
    return index.variant.empty() && index.model.empty();
  }
  return false;
}

bool admittedIndex(const SchemaContext &context, const SecurityIndex &index) {
  return validIndexShape(index) &&
         std::find(context.securityIndices.begin(),
                   context.securityIndices.end(),
                   index) != context.securityIndices.end();
}

ResultSchema resultFor(const SecurityIndex &index) {
  switch (index.notion) {
  case SecurityNotion::SpecialSoundness:
  case SecurityNotion::ComputationalSpecialSoundness:
    return ResultSchema::Extraction;
  case SecurityNotion::RoundByRound:
    return ResultSchema::Round;
  case SecurityNotion::StateRestoration:
  case SecurityNotion::FiatShamir:
  case SecurityNotion::Completeness:
    return ResultSchema::Scalar;
  }
  return ResultSchema::Scalar;
}

template <typename Range, typename Name>
std::optional<std::string> duplicateName(const Range &range, Name name) {
  std::set<std::string> seen;
  for (const auto &value : range) {
    std::string current = name(value);
    if (current.empty() || !seen.insert(current).second)
      return current;
  }
  return std::nullopt;
}

std::map<std::string, ValueSort, std::less<>>
declarationMap(const std::vector<TypedDeclaration> &declarations) {
  std::map<std::string, ValueSort, std::less<>> result;
  for (const TypedDeclaration &declaration : declarations)
    result.emplace(declaration.name, declaration.sort);
  return result;
}

struct RuleEnvironment {
  const SchemaContext &context;
  const SoundnessRule &rule;
  std::map<std::string, ValueSort, std::less<>> parameters;
  std::map<std::string, ValueSort, std::less<>> resources;
  std::map<std::string, ValueSort, std::less<>> facts;
  std::map<std::string, const PremisePort *, std::less<>> premises;
};

bool isDefaultContractSelector(const ContractRoundSelector &selector) {
  return selector.kind == ContractRoundSelectorKind::AllContractRounds &&
         selector.roundKind.empty() && selector.position == 0;
}

bool isClosedContractSelector(const ContractRoundSelector &selector) {
  switch (selector.kind) {
  case ContractRoundSelectorKind::AllContractRounds:
    return selector.roundKind.empty() && selector.position == 0;
  case ContractRoundSelectorKind::RoundKind:
    return !selector.roundKind.empty() && selector.position == 0;
  case ContractRoundSelectorKind::RoundPosition:
    return selector.roundKind.empty();
  }
  return false;
}

bool isDefaultArtifactProjection(const ArtifactProjection &projection) {
  return projection.kind ==
             ArtifactProjectionKind::ConclusionReductionContract &&
         projection.resultSort == ValueSort::String &&
         projection.field.empty() && projection.inputIndex == 0 &&
         isDefaultContractSelector(projection.roundSelector) &&
         projection.aggregate == ProjectionAggregate::UniqueEqual;
}

bool hasDefaultLiteralPayload(const BindingValue &value) {
  const auto *text = std::get_if<std::string>(&value.literal);
  return text && text->empty();
}

RuleWfResult checkArtifactProjection(const ArtifactProjection &projection,
                                     const std::string &location) {
  auto inactiveBaseIsDefault = [&] {
    return projection.inputIndex == 0 &&
           isDefaultContractSelector(projection.roundSelector) &&
           projection.aggregate == ProjectionAggregate::UniqueEqual;
  };
  auto simpleField = [&] {
    return !projection.field.empty() && inactiveBaseIsDefault();
  };

  switch (projection.kind) {
  case ArtifactProjectionKind::ConclusionReductionContract:
    if (projection.resultSort != ValueSort::ReductionContract ||
        !projection.field.empty() || !inactiveBaseIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed conclusion-contract projection");
    return accepted();
  case ArtifactProjectionKind::ContractRoundAdjacency:
    if (projection.resultSort != ValueSort::RoundAdjacency ||
        !projection.field.empty() || !inactiveBaseIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed contract-round adjacency projection");
    return accepted();
  case ArtifactProjectionKind::ReductionInputCount:
    if (projection.resultSort != ValueSort::Integer ||
        !projection.field.empty() || !inactiveBaseIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed reduction-input-count projection");
    return accepted();
  case ArtifactProjectionKind::BoundRelationAnchorCount:
    if (projection.resultSort != ValueSort::Integer ||
        !projection.field.empty() || !inactiveBaseIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed bound-relation-anchor-count projection");
    return accepted();
  case ArtifactProjectionKind::CommittedArity:
    if (projection.resultSort != ValueSort::Integer ||
        !projection.field.empty() || !inactiveBaseIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed committed-arity projection");
    return accepted();
  case ArtifactProjectionKind::ReductionParameter:
    if (!simpleField() || (!isNumeric(projection.resultSort) &&
                           projection.resultSort != ValueSort::String &&
                           projection.resultSort != ValueSort::Boolean))
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed typed reduction-parameter projection");
    return accepted();
  case ArtifactProjectionKind::PathBindingField:
    if (!simpleField())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed typed path-binding projection");
    {
      static const std::map<std::string, ValueSort, std::less<>> fields = {
          {"sponge.alphabet_order", ValueSort::Integer},
          {"sponge.capacity", ValueSort::Integer},
          {"sponge.rate", ValueSort::Integer},
          {"codec_bias_max", ValueSort::Rational},
          {"codec_bias_sum", ValueSort::Rational},
      };
      auto field = fields.find(projection.field);
      if (field == fields.end() || field->second != projection.resultSort)
        return refuse(RuleWfRefusalCode::InvalidReference, location,
                      "unknown or ill-typed path-binding field");
    }
    return accepted();
  case ArtifactProjectionKind::ContractRoundFamilyField: {
    static const std::set<std::string> fields = {
        "RoundIndex",     "RoundKind",   "ChallengeSpace",
        "ChallengeCount", "RoundDegree", "ChallengeSpaceLog2"};
    if (!fields.count(projection.field) ||
        !isClosedContractSelector(projection.roundSelector) ||
        projection.inputIndex != 0)
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed contract-round-family projection");
    if (projection.aggregate != ProjectionAggregate::Count &&
        projection.aggregate != ProjectionAggregate::UniqueEqual)
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "unknown round-family projection aggregate");
    if (projection.aggregate == ProjectionAggregate::Count) {
      if (projection.resultSort != ValueSort::Integer)
        return refuse(RuleWfRefusalCode::InvalidReference, location,
                      "round-family Count must produce an integer");
    } else {
      ValueSort expected = projection.field == "RoundKind" ? ValueSort::String
                                                           : ValueSort::Integer;
      if (projection.resultSort != expected)
        return refuse(RuleWfRefusalCode::InvalidReference, location,
                      "round-family projection has the wrong result sort");
    }
    return accepted();
  }
  }
  return refuse(RuleWfRefusalCode::InvalidReference, location,
                "unknown artifact projection kind");
}

RuleWfResult checkBindingValue(const RuleEnvironment &env,
                               const BindingValue &value,
                               ValueSort expectedSort,
                               const std::string &location) {
  if (!validValueSort(value.sort) || !validValueSort(expectedSort) ||
      value.sort != expectedSort)
    return refuse(RuleWfRefusalCode::InvalidReference, location,
                  "binding value has the wrong declared sort");

  // These owned semantic facts have exactly one admitted source each.  In
  // particular, a same-sorted parameter or resource is not a substitute for
  // an authenticated artifact fact.
  if (expectedSort == ValueSort::ReductionContract &&
      (value.kind != BindingValueKind::SealedArtifactProjection ||
       value.artifactProjection.kind !=
           ArtifactProjectionKind::ConclusionReductionContract))
    return refuse(RuleWfRefusalCode::InvalidReference, location,
                  "reduction contract must come from the sealed conclusion "
                  "contract projection");
  if (expectedSort == ValueSort::RoundAdjacency &&
      (value.kind != BindingValueKind::SealedArtifactProjection ||
       value.artifactProjection.kind !=
           ArtifactProjectionKind::ContractRoundAdjacency))
    return refuse(RuleWfRefusalCode::InvalidReference, location,
                  "round adjacency must come from the sealed contract-round "
                  "adjacency projection");
  if (expectedSort == ValueSort::PathTransition &&
      value.kind != BindingValueKind::ApplicationPathTransition)
    return refuse(RuleWfRefusalCode::InvalidReference, location,
                  "path transition must be the selected application path "
                  "transition");

  auto inactiveIsDefault = [&] {
    return hasDefaultLiteralPayload(value) && value.reference.empty() &&
           value.premisePort.empty() &&
           isDefaultArtifactProjection(value.artifactProjection);
  };
  switch (value.kind) {
  case BindingValueKind::Literal:
    if (!value.reference.empty() || !value.premisePort.empty() ||
        !isDefaultArtifactProjection(value.artifactProjection))
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "literal carries inactive reference payload");
    if (value.sort == ValueSort::Integer || value.sort == ValueSort::Rational) {
      const auto *number = std::get_if<registry::Rational>(&value.literal);
      if (!number ||
          (value.sort == ValueSort::Integer && number->denStr() != "1"))
        return refuse(RuleWfRefusalCode::InvalidReference, location,
                      "numeric literal is not an exact value of its sort");
      return accepted();
    }
    if (value.sort == ValueSort::String &&
        std::holds_alternative<std::string>(value.literal))
      return accepted();
    if (value.sort == ValueSort::Boolean &&
        std::holds_alternative<bool>(value.literal))
      return accepted();
    if (value.sort == ValueSort::AlgebraInstance) {
      const auto *algebra = std::get_if<AlgebraInstanceValue>(&value.literal);
      if (algebra && !algebra->group.empty() && !algebra->fieldClass.empty() &&
          algebra->fieldOrder.denStr() == "1" &&
          algebra->fieldOrder.compare(registry::Rational::fromInteger(0)) > 0)
        return accepted();
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "algebra literal is not an exact positive-order carrier");
    }
    return refuse(RuleWfRefusalCode::InvalidReference, location,
                  "this semantic sort has no literal constructor");
  case BindingValueKind::SealedArtifactProjection:
    if (!hasDefaultLiteralPayload(value) || !value.reference.empty() ||
        !value.premisePort.empty())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "artifact projection carries inactive payload");
    if (value.artifactProjection.resultSort != value.sort)
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "artifact projection sort does not match its value");
    return checkArtifactProjection(value.artifactProjection,
                                   location + ".artifact_projection");
  case BindingValueKind::ConclusionSubject:
    if (value.sort != ValueSort::Subject || !inactiveIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed conclusion-subject value");
    return accepted();
  case BindingValueKind::ApplicationPathTransition:
    if (value.sort != ValueSort::PathTransition || !inactiveIsDefault())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed application path-transition value");
    return accepted();
  case BindingValueKind::ConclusionResource: {
    if (!hasDefaultLiteralPayload(value) || value.reference.empty() ||
        !value.premisePort.empty() ||
        !isDefaultArtifactProjection(value.artifactProjection))
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed conclusion-resource value");
    auto resource = env.resources.find(value.reference);
    if (resource == env.resources.end() || resource->second != value.sort)
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "unknown or ill-typed conclusion resource");
    return accepted();
  }
  case BindingValueKind::ResolvedParameter: {
    if (!hasDefaultLiteralPayload(value) || value.reference.empty() ||
        !value.premisePort.empty() ||
        !isDefaultArtifactProjection(value.artifactProjection))
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "malformed resolved-parameter value");
    auto parameter = env.parameters.find(value.reference);
    if (parameter == env.parameters.end() || parameter->second != value.sort)
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "unknown or ill-typed resolved parameter");
    return accepted();
  }
  }
  return refuse(RuleWfRefusalCode::InvalidReference, location,
                "unknown binding value kind");
}

enum class Integrality { Integer, HalfInteger, Unknown };
enum class ResourceShape { None, Monomial, Polynomial };

struct QuantityScope {
  std::set<std::string> roundCases;
  std::optional<std::string> boundCoordinatePort;
  std::optional<std::string> forbiddenPremisePort;
};

struct QuantityInfo {
  ValueSort sort = ValueSort::Rational;
  Integrality integrality = Integrality::Unknown;
  ResourceShape resourceShape = ResourceShape::None;
  std::optional<registry::Rational> constant;
  // Exact zero-degree component when it is statically knowable, even if the
  // whole expression also contains resource monomials.
  std::optional<registry::Rational> staticOffset;
};

bool isDefaultPremiseCoordinateSelector(
    const PremiseCoordinateSelector &selector) {
  return selector.kind == PremiseCoordinateSelectorKind::BoundCoordinate;
}

bool hasDefaultQuantityLeafPayload(const QuantityTemplate &quantity) {
  return quantity.literal.isZero() && quantity.name.empty() &&
         quantity.port.empty() && quantity.caseName.empty() &&
         quantity.contractRoundField == ContractRoundField::ChallengeSpace &&
         quantity.premiseCoordinateField == PremiseCoordinateField::Arity &&
         isDefaultPremiseCoordinateSelector(
             quantity.premiseCoordinateSelector) &&
         quantity.operands.empty();
}

bool isDefaultQuantity(const QuantityTemplate &quantity) {
  return quantity.kind == QuantityKind::RationalLiteral &&
         hasDefaultQuantityLeafPayload(quantity);
}

Integrality literalIntegrality(const registry::Rational &value) {
  if (value.denStr() == "1")
    return Integrality::Integer;
  if (value.denStr() == "2")
    return Integrality::HalfInteger;
  return Integrality::Unknown;
}

std::optional<int64_t> exactInt64(const registry::Rational &value) {
  if (value.denStr() != "1")
    return std::nullopt;
  auto converted = value.floorToInt();
  if (!converted) {
    llvm::consumeError(converted.takeError());
    return std::nullopt;
  }
  return *converted;
}

bool isPlusOrMinus(const registry::Rational &value, int64_t magnitude) {
  registry::Rational positive = registry::Rational::fromInteger(magnitude);
  registry::Rational negative = registry::Rational::fromInteger(-magnitude);
  return value.compare(positive) == 0 || value.compare(negative) == 0;
}

bool arithmeticPayloadIsClosed(const QuantityTemplate &quantity) {
  return quantity.literal.isZero() && quantity.name.empty() &&
         quantity.port.empty() && quantity.caseName.empty() &&
         quantity.contractRoundField == ContractRoundField::ChallengeSpace &&
         quantity.premiseCoordinateField == PremiseCoordinateField::Arity &&
         isDefaultPremiseCoordinateSelector(quantity.premiseCoordinateSelector);
}

std::optional<QuantityInfo> analyzeQuantity(const RuleEnvironment &env,
                                            const QuantityTemplate &quantity,
                                            const QuantityScope &scope,
                                            RuleWfResult &failure,
                                            const std::string &location) {
  auto fail = [&](std::string detail) -> std::optional<QuantityInfo> {
    failure =
        refuse(RuleWfRefusalCode::InvalidQuantity, location, std::move(detail));
    return std::nullopt;
  };
  auto numericNamed = [&](const auto &table,
                          const char *kind) -> std::optional<QuantityInfo> {
    if (!quantity.literal.isZero() || quantity.name.empty() ||
        !quantity.port.empty() || !quantity.caseName.empty() ||
        quantity.contractRoundField != ContractRoundField::ChallengeSpace ||
        quantity.premiseCoordinateField != PremiseCoordinateField::Arity ||
        !isDefaultPremiseCoordinateSelector(
            quantity.premiseCoordinateSelector) ||
        !quantity.operands.empty())
      return fail(std::string(kind) + " carries inactive payload");
    auto it = table.find(quantity.name);
    if (it == table.end() || !isNumeric(it->second))
      return fail(std::string("unknown or non-numeric ") + kind + " '" +
                  quantity.name + "'");
    QuantityInfo result;
    result.sort = it->second;
    result.integrality = it->second == ValueSort::Integer
                             ? Integrality::Integer
                             : Integrality::Unknown;
    return result;
  };

  switch (quantity.kind) {
  case QuantityKind::RationalLiteral: {
    if (!quantity.name.empty() || !quantity.port.empty() ||
        !quantity.caseName.empty() ||
        quantity.contractRoundField != ContractRoundField::ChallengeSpace ||
        quantity.premiseCoordinateField != PremiseCoordinateField::Arity ||
        !isDefaultPremiseCoordinateSelector(
            quantity.premiseCoordinateSelector) ||
        !quantity.operands.empty())
      return fail("rational literal carries inactive payload");
    QuantityInfo result;
    result.sort = quantity.literal.denStr() == "1" ? ValueSort::Integer
                                                   : ValueSort::Rational;
    result.integrality = literalIntegrality(quantity.literal);
    result.constant = quantity.literal;
    result.staticOffset = quantity.literal;
    return result;
  }
  case QuantityKind::Parameter:
    return numericNamed(env.parameters, "parameter");
  case QuantityKind::ArtifactFact:
    return numericNamed(env.facts, "artifact fact");
  case QuantityKind::ResourceVariable: {
    std::optional<QuantityInfo> result =
        numericNamed(env.resources, "resource variable");
    if (result)
      result->resourceShape = ResourceShape::Monomial;
    if (result)
      result->staticOffset = registry::Rational::fromInteger(0);
    return result;
  }
  case QuantityKind::ContractRoundFact: {
    if (!quantity.literal.isZero() || !quantity.name.empty() ||
        !quantity.port.empty() || quantity.caseName.empty() ||
        !scope.roundCases.count(quantity.caseName) ||
        quantity.premiseCoordinateField != PremiseCoordinateField::Arity ||
        !validContractRoundField(quantity.contractRoundField) ||
        !isDefaultPremiseCoordinateSelector(
            quantity.premiseCoordinateSelector) ||
        !quantity.operands.empty())
      return fail("contract-round fact escapes its lexical case or carries "
                  "inactive payload");
    QuantityInfo result;
    result.sort = ValueSort::Integer;
    result.integrality = Integrality::Integer;
    return result;
  }
  case QuantityKind::PremiseCoordinate: {
    if (!quantity.literal.isZero() || !quantity.name.empty() ||
        quantity.port.empty() || !quantity.caseName.empty() ||
        quantity.contractRoundField != ContractRoundField::ChallengeSpace ||
        !validPremiseCoordinateField(quantity.premiseCoordinateField) ||
        !quantity.operands.empty())
      return fail("premise-coordinate projection carries inactive payload");
    auto premise = env.premises.find(quantity.port);
    if (premise == env.premises.end() ||
        premise->second->expectedResult != ResultSchema::Extraction)
      return fail("premise-coordinate projection reads a non-extraction "
                  "premise");
    if (scope.forbiddenPremisePort &&
        *scope.forbiddenPremisePort == quantity.port)
      return fail("body-local quantity rereads its fixed premise");
    if (!scope.boundCoordinatePort ||
        *scope.boundCoordinatePort != quantity.port)
      return fail("bound-coordinate projection escapes its lexical binder");
    QuantityInfo result;
    result.sort = ValueSort::Integer;
    result.integrality = Integrality::Integer;
    return result;
  }
  case QuantityKind::Add:
  case QuantityKind::Mul:
    if (quantity.operands.empty())
      return fail("n-ary arithmetic requires a non-empty operand list");
    break;
  case QuantityKind::Sub:
  case QuantityKind::Div:
  case QuantityKind::Pow:
    if (quantity.operands.size() != 2)
      return fail("binary arithmetic requires exactly two operands");
    break;
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up:
    if (quantity.operands.size() != 1)
      return fail("dyadic exponentiation requires exactly one operand");
    break;
  default:
    return fail("unknown quantity kind");
  }
  if (!arithmeticPayloadIsClosed(quantity))
    return fail("arithmetic node carries inactive payload");

  std::vector<QuantityInfo> operands;
  operands.reserve(quantity.operands.size());
  for (size_t index = 0; index < quantity.operands.size(); ++index) {
    std::optional<QuantityInfo> operand =
        analyzeQuantity(env, quantity.operands[index], scope, failure,
                        location + ".operand[" + std::to_string(index) + "]");
    if (!operand)
      return std::nullopt;
    operands.push_back(std::move(*operand));
  }

  QuantityInfo result;
  bool allIntegerSorts =
      std::all_of(operands.begin(), operands.end(), [](const auto &operand) {
        return operand.sort == ValueSort::Integer;
      });
  result.sort =
      quantity.kind == QuantityKind::Add ||
              quantity.kind == QuantityKind::Sub ||
              quantity.kind == QuantityKind::Mul
          ? (allIntegerSorts ? ValueSort::Integer : ValueSort::Rational)
          : ValueSort::Rational;

  auto allConstants = [&] {
    return std::all_of(
        operands.begin(), operands.end(),
        [](const auto &operand) { return operand.constant.has_value(); });
  };
  auto combineAdditiveIntegrality = [&] {
    bool half = false;
    for (const QuantityInfo &operand : operands) {
      if (operand.integrality == Integrality::Unknown)
        return Integrality::Unknown;
      half |= operand.integrality == Integrality::HalfInteger;
    }
    return half ? Integrality::HalfInteger : Integrality::Integer;
  };

  switch (quantity.kind) {
  case QuantityKind::Add:
  case QuantityKind::Sub: {
    if (quantity.kind == QuantityKind::Sub &&
        operands[1].resourceShape != ResourceShape::None)
      return fail("subtraction may not introduce a negative resource "
                  "coefficient");
    result.integrality = combineAdditiveIntegrality();
    bool anyResource =
        std::any_of(operands.begin(), operands.end(), [](const auto &operand) {
          return operand.resourceShape != ResourceShape::None;
        });
    result.resourceShape =
        anyResource ? ResourceShape::Polynomial : ResourceShape::None;
    if (allConstants()) {
      registry::Rational value = *operands.front().constant;
      if (quantity.kind == QuantityKind::Add) {
        for (size_t index = 1; index < operands.size(); ++index)
          value = value.add(*operands[index].constant);
      } else {
        value = value.sub(*operands[1].constant);
      }
      result.constant = std::move(value);
    }
    if (std::all_of(operands.begin(), operands.end(), [](const auto &operand) {
          return operand.staticOffset.has_value();
        })) {
      registry::Rational offset = *operands.front().staticOffset;
      if (quantity.kind == QuantityKind::Add) {
        for (size_t index = 1; index < operands.size(); ++index)
          offset = offset.add(*operands[index].staticOffset);
      } else {
        offset = offset.sub(*operands[1].staticOffset);
      }
      result.staticOffset = std::move(offset);
    }
    return result;
  }
  case QuantityKind::Mul: {
    size_t resourceFactors = std::count_if(
        operands.begin(), operands.end(), [](const auto &operand) {
          return operand.resourceShape != ResourceShape::None;
        });
    if (resourceFactors > 1)
      return fail("a product contains multiple resource-valued factors");
    if (resourceFactors == 1)
      result.resourceShape =
          std::find_if(operands.begin(), operands.end(),
                       [](const auto &operand) {
                         return operand.resourceShape != ResourceShape::None;
                       })
              ->resourceShape;
    size_t halfFactors = std::count_if(
        operands.begin(), operands.end(), [](const auto &operand) {
          return operand.integrality == Integrality::HalfInteger;
        });
    bool hasUnknown =
        std::any_of(operands.begin(), operands.end(), [](const auto &operand) {
          return operand.integrality == Integrality::Unknown;
        });
    result.integrality =
        !hasUnknown && halfFactors == 0
            ? Integrality::Integer
            : (!hasUnknown && halfFactors == 1 ? Integrality::HalfInteger
                                               : Integrality::Unknown);
    if (allConstants()) {
      registry::Rational value = registry::Rational::fromInteger(1);
      for (const QuantityInfo &operand : operands)
        value = value.mul(*operand.constant);
      result.constant = std::move(value);
    } else if (result.resourceShape != ResourceShape::None) {
      registry::Rational knownCoefficient = registry::Rational::fromInteger(1);
      bool coefficientKnown = true;
      for (const QuantityInfo &operand : operands) {
        if (operand.resourceShape != ResourceShape::None)
          continue;
        if (!operand.constant) {
          coefficientKnown = false;
          break;
        }
        knownCoefficient = knownCoefficient.mul(*operand.constant);
      }
      if (coefficientKnown && knownCoefficient.isNegative())
        return fail("resource monomial has a static negative coefficient");
    }
    if (std::all_of(operands.begin(), operands.end(), [](const auto &operand) {
          return operand.staticOffset.has_value();
        })) {
      registry::Rational offset = registry::Rational::fromInteger(1);
      for (const QuantityInfo &operand : operands)
        offset = offset.mul(*operand.staticOffset);
      result.staticOffset = std::move(offset);
    }
    return result;
  }
  case QuantityKind::Div: {
    const QuantityInfo &numerator = operands[0];
    const QuantityInfo &denominator = operands[1];
    if (denominator.resourceShape != ResourceShape::None)
      return fail("a divisor may not depend on a resource variable");
    if (denominator.constant && denominator.constant->isZero())
      return fail("division by a static zero denominator");
    result.resourceShape = numerator.resourceShape;
    if (denominator.constant && isPlusOrMinus(*denominator.constant, 1))
      result.integrality = numerator.integrality;
    else if (denominator.constant && isPlusOrMinus(*denominator.constant, 2) &&
             numerator.integrality == Integrality::Integer)
      result.integrality = Integrality::HalfInteger;
    if (numerator.constant && denominator.constant) {
      auto quotient = numerator.constant->div(*denominator.constant);
      if (!quotient) {
        llvm::consumeError(quotient.takeError());
        return fail("division is outside the exact rational domain");
      }
      result.constant = std::move(*quotient);
    }
    if (numerator.staticOffset && denominator.constant) {
      auto quotient = numerator.staticOffset->div(*denominator.constant);
      if (!quotient) {
        llvm::consumeError(quotient.takeError());
        return fail("division is outside the exact rational domain");
      }
      result.staticOffset = std::move(*quotient);
    }
    if (result.resourceShape != ResourceShape::None && denominator.constant &&
        denominator.constant->isNegative())
      return fail("resource expression has a static negative divisor");
    return result;
  }
  case QuantityKind::Pow: {
    const QuantityInfo &base = operands[0];
    const QuantityInfo &exponent = operands[1];
    if (exponent.resourceShape != ResourceShape::None)
      return fail("power exponent may not depend on a resource variable");
    std::optional<int64_t> staticExponent;
    if (exponent.constant) {
      staticExponent = exactInt64(*exponent.constant);
      if (!staticExponent)
        return fail("power exponent is not a representable integer");
    } else if (exponent.integrality != Integrality::Integer) {
      return fail("power exponent is not structurally integer-valued");
    }
    if (base.resourceShape != ResourceShape::None) {
      if (base.resourceShape != ResourceShape::Monomial || !staticExponent ||
          *staticExponent <= 0)
        return fail("resource powers require one monomial and a static "
                    "positive integer exponent");
      result.resourceShape = ResourceShape::Monomial;
    }
    if (staticExponent) {
      if (*staticExponent < -4096 || *staticExponent > 4096)
        return fail("static power exponent exceeds the v0 exact range");
      if (*staticExponent == 0)
        result.integrality = Integrality::Integer;
      else if (*staticExponent > 0 && base.integrality == Integrality::Integer)
        result.integrality = Integrality::Integer;
      else if (*staticExponent == 1)
        result.integrality = base.integrality;
      if (base.constant) {
        auto powered = base.constant->pow(*staticExponent);
        if (!powered) {
          llvm::consumeError(powered.takeError());
          return fail("power is outside the exact rational domain");
        }
        result.constant = std::move(*powered);
      }
      if (base.staticOffset) {
        auto powered = base.staticOffset->pow(*staticExponent);
        if (!powered) {
          llvm::consumeError(powered.takeError());
          return fail("power is outside the exact rational domain");
        }
        result.staticOffset = std::move(*powered);
      }
    }
    return result;
  }
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up: {
    const QuantityInfo &exponent = operands.front();
    if (exponent.resourceShape != ResourceShape::None)
      return fail("dyadic exponent may not depend on a resource variable");
    std::optional<int64_t> staticExponent;
    if (exponent.constant) {
      if (quantity.kind == QuantityKind::Pow2) {
        staticExponent = exactInt64(*exponent.constant);
        if (!staticExponent)
          return fail("Pow2 exponent is not a representable integer");
      } else {
        if (exponent.constant->denStr() != "1" &&
            exponent.constant->denStr() != "2")
          return fail("Pow2Up exponent is not a half-integer");
        auto rounded = exponent.constant->ceilToInt();
        if (!rounded) {
          llvm::consumeError(rounded.takeError());
          return fail("Pow2Up exponent is not representable");
        }
        staticExponent = *rounded;
      }
    } else if (quantity.kind == QuantityKind::Pow2 &&
               exponent.integrality != Integrality::Integer) {
      return fail("Pow2 exponent is not structurally integer-valued");
    } else if (quantity.kind == QuantityKind::Pow2Up &&
               exponent.integrality == Integrality::Unknown) {
      return fail("Pow2Up exponent is not structurally half-integer-valued");
    }
    if (staticExponent) {
      if (*staticExponent < -4096 || *staticExponent > 4096)
        return fail("static dyadic exponent exceeds the v0 exact range");
      auto powered = registry::Rational::fromInteger(2).pow(*staticExponent);
      if (!powered) {
        llvm::consumeError(powered.takeError());
        return fail("dyadic power is outside the exact rational domain");
      }
      result.constant = std::move(*powered);
      result.staticOffset = result.constant;
      result.integrality =
          *staticExponent >= 0
              ? Integrality::Integer
              : (*staticExponent == -1 ? Integrality::HalfInteger
                                       : Integrality::Unknown);
    }
    return result;
  }
  case QuantityKind::RationalLiteral:
  case QuantityKind::Parameter:
  case QuantityKind::ArtifactFact:
  case QuantityKind::ContractRoundFact:
  case QuantityKind::PremiseCoordinate:
  case QuantityKind::ResourceVariable:
    break;
  }
  return fail("unknown quantity kind");
}

enum class QuantityDomain { NonNegative, PositiveInteger };

RuleWfResult checkQuantityDomain(const QuantityInfo &quantity,
                                 QuantityDomain domain,
                                 const std::string &location) {
  if (domain == QuantityDomain::PositiveInteger &&
      quantity.resourceShape != ResourceShape::None)
    return refuse(RuleWfRefusalCode::InvalidQuantity, location,
                  "positive structural sizes may not depend on a resource");
  if (quantity.constant) {
    registry::Rational zero = registry::Rational::fromInteger(0);
    int comparison = quantity.constant->compare(zero);
    if ((domain == QuantityDomain::NonNegative && comparison < 0) ||
        (domain == QuantityDomain::PositiveInteger && comparison <= 0))
      return refuse(RuleWfRefusalCode::InvalidQuantity, location,
                    domain == QuantityDomain::NonNegative
                        ? "quantity is statically negative"
                        : "quantity is statically non-positive");
    if (domain == QuantityDomain::PositiveInteger &&
        quantity.constant->denStr() != "1")
      return refuse(RuleWfRefusalCode::InvalidQuantity, location,
                    "quantity is statically non-integral");
  }
  if (domain == QuantityDomain::NonNegative && quantity.staticOffset &&
      quantity.staticOffset->isNegative())
    return refuse(RuleWfRefusalCode::InvalidQuantity, location,
                  "quantity has a statically negative constant coefficient");
  return accepted();
}

bool isResourceExpression(const QuantityTemplate &quantity) {
  switch (quantity.kind) {
  case QuantityKind::RationalLiteral:
  case QuantityKind::ResourceVariable:
    break;
  case QuantityKind::Add:
  case QuantityKind::Sub:
  case QuantityKind::Mul:
  case QuantityKind::Div:
  case QuantityKind::Pow:
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up:
    break;
  case QuantityKind::Parameter:
  case QuantityKind::ArtifactFact:
  case QuantityKind::ContractRoundFact:
  case QuantityKind::PremiseCoordinate:
    return false;
  default:
    return false;
  }
  return std::all_of(quantity.operands.begin(), quantity.operands.end(),
                     isResourceExpression);
}

bool isDefaultGame(const PrimitiveGameInstanceTemplate &game) {
  return game.gameRef.empty() && game.instanceArguments.empty();
}

struct BoundInfo {
  bool groundAfterApply = false;
};

struct BoundScope {
  QuantityScope quantity;
  std::optional<std::string> forbiddenPremisePort;
};

bool boundInactiveBaseIsDefault(const RuleBound &bound) {
  return isDefaultQuantity(bound.quantity) && bound.premisePort.empty() &&
         isDefaultGame(bound.game) && bound.gameResourceSubstitution.empty();
}

RuleWfResult analyzeBound(const RuleEnvironment &env, const RuleBound &bound,
                          const BoundScope &scope, const std::string &location,
                          BoundInfo &info) {
  auto requirePremiseResult = [&](ResultSchema result) -> RuleWfResult {
    if (scope.forbiddenPremisePort &&
        *scope.forbiddenPremisePort == bound.premisePort)
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "body-local bound rereads its fixed premise");
    auto it = env.premises.find(bound.premisePort);
    if (it == env.premises.end() || it->second->expectedResult != result)
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "premise projection has the wrong result schema");
    return accepted();
  };
  auto checkLeafInactive = [&]() -> RuleWfResult {
    if (!isDefaultQuantity(bound.quantity) || !isDefaultGame(bound.game) ||
        !bound.gameResourceSubstitution.empty() || !bound.operands.empty())
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "bound leaf carries inactive payload");
    return accepted();
  };

  switch (bound.kind) {
  case RuleBoundKind::Quantity: {
    if (!bound.premisePort.empty() || !isDefaultGame(bound.game) ||
        !bound.gameResourceSubstitution.empty() || !bound.operands.empty())
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "quantity bound carries inactive payload");
    RuleWfResult failure;
    std::optional<QuantityInfo> quantity = analyzeQuantity(
        env, bound.quantity, scope.quantity, failure, location + ".quantity");
    if (!quantity)
      return failure;
    RuleWfResult domain = checkQuantityDomain(
        *quantity, QuantityDomain::NonNegative, location + ".quantity");
    if (!domain.accepted())
      return domain;
    info.groundAfterApply = quantity->resourceShape == ResourceShape::None;
    return accepted();
  }
  case RuleBoundKind::ScalarBound: {
    if (bound.premisePort.empty())
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "premise projection has no premise");
    if (RuleWfResult shape = checkLeafInactive(); !shape.accepted())
      return shape;
    info.groundAfterApply = false;
    return requirePremiseResult(ResultSchema::Scalar);
  }
  case RuleBoundKind::PrimitiveAdvantage: {
    if (!isDefaultQuantity(bound.quantity) || !bound.premisePort.empty() ||
        bound.game.gameRef.empty() || !bound.operands.empty())
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "primitive advantage carries inactive payload");
    auto definition = env.context.primitiveGames.find(bound.game.gameRef);
    if (definition == env.context.primitiveGames.end() ||
        !validExactRef(definition->second.ref) ||
        definition->second.ref.id != bound.game.gameRef)
      return refuse(RuleWfRefusalCode::InvalidPrimitiveGame, location,
                    "unknown or inexact primitive game '" + bound.game.gameRef +
                        "'");
    if (definition->second.instanceArgumentTypes.size() !=
        bound.game.instanceArguments.size())
      return refuse(RuleWfRefusalCode::InvalidPrimitiveGame, location,
                    "primitive-game instance arity mismatch");
    for (size_t index = 0; index < bound.game.instanceArguments.size();
         ++index) {
      const ValueSort expectedSort =
          definition->second.instanceArgumentTypes[index];
      if (!validValueSort(expectedSort) ||
          bound.game.instanceArguments[index].sort != expectedSort)
        return refuse(RuleWfRefusalCode::InvalidPrimitiveGame, location,
                      "primitive-game instance argument sort mismatch");
      RuleWfResult argument = checkBindingValue(
          env, bound.game.instanceArguments[index], expectedSort,
          location + ".game_argument[" + std::to_string(index) + "]");
      if (!argument.accepted())
        return argument;
    }
    std::set<std::string> expected;
    for (const TypedDeclaration &resource : definition->second.resources) {
      if (resource.name.empty() || !expected.insert(resource.name).second ||
          !isNumeric(resource.sort))
        return refuse(RuleWfRefusalCode::InvalidPrimitiveGame, location,
                      "primitive game resources must be non-empty, unique, "
                      "and numeric");
    }
    std::set<std::string> actual;
    for (const auto &entry : bound.gameResourceSubstitution)
      actual.insert(entry.first);
    if (actual != expected)
      return refuse(RuleWfRefusalCode::InvalidResourceSubstitution, location,
                    "primitive-game resource substitution is not total");
    for (const auto &[name, expression] : bound.gameResourceSubstitution) {
      RuleWfResult failure;
      std::optional<QuantityInfo> quantity =
          analyzeQuantity(env, expression, scope.quantity, failure,
                          location + ".game_resource." + name);
      if (!quantity)
        return failure;
      RuleWfResult domain =
          checkQuantityDomain(*quantity, QuantityDomain::NonNegative,
                              location + ".game_resource." + name);
      if (!domain.accepted())
        return domain;
      auto declaration = std::find_if(definition->second.resources.begin(),
                                      definition->second.resources.end(),
                                      [&](const TypedDeclaration &candidate) {
                                        return candidate.name == name;
                                      });
      if (declaration == definition->second.resources.end() ||
          declaration->sort != quantity->sort)
        return refuse(RuleWfRefusalCode::InvalidResourceSubstitution, location,
                      "primitive-game resource sort mismatch");
    }
    info.groundAfterApply = false;
    return accepted();
  }
  case RuleBoundKind::Add:
  case RuleBoundKind::Max:
    if (!boundInactiveBaseIsDefault(bound) || bound.operands.empty())
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "bound aggregation has invalid active fields");
    break;
  case RuleBoundKind::Scale: {
    if (!bound.premisePort.empty() || !isDefaultGame(bound.game) ||
        !bound.gameResourceSubstitution.empty() || bound.operands.size() != 1)
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "bound scaling has invalid active fields");
    RuleWfResult failure;
    std::optional<QuantityInfo> scale = analyzeQuantity(
        env, bound.quantity, scope.quantity, failure, location + ".scale");
    if (!scale)
      return failure;
    if (scale->resourceShape != ResourceShape::None)
      return refuse(RuleWfRefusalCode::InvalidBound, location,
                    "bound coefficient may not depend on a resource");
    RuleWfResult domain = checkQuantityDomain(
        *scale, QuantityDomain::NonNegative, location + ".scale");
    if (!domain.accepted())
      return domain;
    break;
  }
  default:
    return refuse(RuleWfRefusalCode::InvalidBound, location,
                  "unknown rule-bound kind");
  }

  bool allGround = true;
  for (size_t index = 0; index < bound.operands.size(); ++index) {
    BoundInfo child;
    RuleWfResult result =
        analyzeBound(env, bound.operands[index], scope,
                     location + ".bound[" + std::to_string(index) + "]", child);
    if (!result.accepted())
      return result;
    allGround &= child.groundAfterApply;
  }
  if (bound.kind == RuleBoundKind::Max && !allGround)
    return refuse(RuleWfRefusalCode::InvalidBound, location,
                  "symbolic Max is outside the v0 normal form");
  info.groundAfterApply = allGround;
  return accepted();
}

RuleWfResult checkBound(const RuleEnvironment &env, const RuleBound &bound,
                        const BoundScope &scope, const std::string &location) {
  BoundInfo info;
  return analyzeBound(env, bound, scope, location, info);
}

RuleWfResult checkSelector(const ContractRoundSelector &selector,
                           const std::string &location) {
  if (!isClosedContractSelector(selector))
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract-round selector carries invalid active fields");
  return accepted();
}

bool validLabelProjection(ContractLabelProjection projection) {
  switch (projection) {
  case ContractLabelProjection::RoundIndex:
  case ContractLabelProjection::RoundKindOccurrence:
  case ContractLabelProjection::CaseName:
  case ContractLabelProjection::SiteQualifiedRoundIndex:
    return true;
  }
  return false;
}

std::string selectorKey(const ContractRoundSelector &selector) {
  switch (selector.kind) {
  case ContractRoundSelectorKind::AllContractRounds:
    return "all";
  case ContractRoundSelectorKind::RoundKind:
    return "kind:" + selector.roundKind;
  case ContractRoundSelectorKind::RoundPosition:
    return "position:" + std::to_string(selector.position);
  }
  return {};
}

RuleWfResult checkCoordinates(const RuleEnvironment &env,
                              const CoordinateSequence &sequence,
                              const std::string &location) {
  if (sequence.kind != CoordinateSequence::Kind::Explicit &&
      sequence.kind != CoordinateSequence::Kind::Contract)
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "unknown coordinate-sequence kind");
  if (sequence.kind == CoordinateSequence::Kind::Explicit) {
    if (!sequence.contractFactPort.empty() || !sequence.cases.empty())
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "explicit coordinate sequence carries contract payload");
    if (sequence.coordinates.empty())
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "explicit coordinate sequence is empty");
    if (duplicateName(
            sequence.coordinates,
            [](const CoordinateTemplate &value) { return value.label; }))
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "coordinate labels must be non-empty and unique");
    for (size_t index = 0; index < sequence.coordinates.size(); ++index) {
      RuleWfResult failure;
      std::optional<QuantityInfo> arity = analyzeQuantity(
          env, sequence.coordinates[index].arity, {}, failure,
          location + ".coordinate[" + std::to_string(index) + "].arity");
      if (!arity)
        return failure;
      RuleWfResult arityDomain = checkQuantityDomain(
          *arity, QuantityDomain::PositiveInteger,
          location + ".coordinate[" + std::to_string(index) + "].arity");
      if (!arityDomain.accepted())
        return arityDomain;
      if (sequence.coordinates[index].challengeSpace) {
        std::optional<QuantityInfo> space = analyzeQuantity(
            env, *sequence.coordinates[index].challengeSpace, {}, failure,
            location + ".coordinate[" + std::to_string(index) + "].space");
        if (!space)
          return failure;
        RuleWfResult spaceDomain = checkQuantityDomain(
            *space, QuantityDomain::PositiveInteger,
            location + ".coordinate[" + std::to_string(index) + "].space");
        if (!spaceDomain.accepted())
          return spaceDomain;
      }
    }
    return accepted();
  }

  if (!sequence.coordinates.empty())
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract coordinate sequence carries explicit payload");
  auto fact = env.facts.find(sequence.contractFactPort);
  if (fact == env.facts.end() || fact->second != ValueSort::ReductionContract ||
      sequence.cases.empty())
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract coordinate sequence has no typed contract fact");
  if (duplicateName(sequence.cases, [](const ContractCoordinateCase &value) {
        return value.caseName;
      }))
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract coordinate case names must be unique");
  if (sequence.cases.size() != 1 &&
      std::any_of(sequence.cases.begin(), sequence.cases.end(),
                  [](const ContractCoordinateCase &value) {
                    return value.selector.kind ==
                           ContractRoundSelectorKind::AllContractRounds;
                  }))
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "AllContractRounds must be the sole case");

  std::set<std::string> selectors;
  for (size_t index = 0; index < sequence.cases.size(); ++index) {
    const ContractCoordinateCase &value = sequence.cases[index];
    if (!validLabelProjection(value.labelProjection))
      return refuse(RuleWfRefusalCode::InvalidSequence,
                    location + ".case[" + std::to_string(index) + "]",
                    "unknown contract-coordinate label projection");
    if (!selectors.insert(selectorKey(value.selector)).second)
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "contract coordinate selectors overlap");
    RuleWfResult selector = checkSelector(
        value.selector, location + ".case[" + std::to_string(index) + "]");
    if (!selector.accepted())
      return selector;
    RuleWfResult failure;
    QuantityScope scope{{value.caseName}, std::nullopt, std::nullopt};
    std::optional<QuantityInfo> arity = analyzeQuantity(
        env, value.arity, scope, failure,
        location + ".case[" + std::to_string(index) + "].arity");
    if (!arity)
      return failure;
    RuleWfResult arityDomain = checkQuantityDomain(
        *arity, QuantityDomain::PositiveInteger,
        location + ".case[" + std::to_string(index) + "].arity");
    if (!arityDomain.accepted())
      return arityDomain;
    if (value.challengeSpace) {
      std::optional<QuantityInfo> space = analyzeQuantity(
          env, *value.challengeSpace, scope, failure,
          location + ".case[" + std::to_string(index) + "].space");
      if (!space)
        return failure;
      RuleWfResult spaceDomain = checkQuantityDomain(
          *space, QuantityDomain::PositiveInteger,
          location + ".case[" + std::to_string(index) + "].space");
      if (!spaceDomain.accepted())
        return spaceDomain;
    }
  }
  return accepted();
}

RuleWfResult checkRounds(const RuleEnvironment &env,
                         const RoundSequence &sequence,
                         const std::string &location) {
  if (sequence.kind != RoundSequence::Kind::Explicit &&
      sequence.kind != RoundSequence::Kind::Contract)
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "unknown round-sequence kind");
  if (sequence.kind == RoundSequence::Kind::Explicit) {
    if (!sequence.contractFactPort.empty() || !sequence.cases.empty())
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "explicit round sequence carries contract payload");
    if (sequence.rounds.empty())
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "explicit round sequence is empty");
    if (duplicateName(sequence.rounds, [](const RoundTemplate &value) {
          return value.roundIndex;
        }))
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "round indices must be non-empty and unique");
    for (size_t index = 0; index < sequence.rounds.size(); ++index) {
      RuleWfResult failure;
      std::optional<QuantityInfo> space = analyzeQuantity(
          env, sequence.rounds[index].challengeSpace, {}, failure,
          location + ".round[" + std::to_string(index) + "].space");
      if (!space)
        return failure;
      RuleWfResult spaceDomain = checkQuantityDomain(
          *space, QuantityDomain::PositiveInteger,
          location + ".round[" + std::to_string(index) + "].space");
      if (!spaceDomain.accepted())
        return spaceDomain;
      RuleWfResult bound =
          checkBound(env, sequence.rounds[index].bound, {},
                     location + ".round[" + std::to_string(index) + "].bound");
      if (!bound.accepted())
        return bound;
    }
    return accepted();
  }

  if (!sequence.rounds.empty())
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract round sequence carries explicit payload");
  auto fact = env.facts.find(sequence.contractFactPort);
  if (fact == env.facts.end() || fact->second != ValueSort::ReductionContract ||
      sequence.cases.empty())
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract round sequence has no typed contract fact");
  if (duplicateName(sequence.cases, [](const ContractRoundCase &value) {
        return value.caseName;
      }))
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "contract round case names must be unique");
  if (sequence.cases.size() != 1 &&
      std::any_of(sequence.cases.begin(), sequence.cases.end(),
                  [](const ContractRoundCase &value) {
                    return value.selector.kind ==
                           ContractRoundSelectorKind::AllContractRounds;
                  }))
    return refuse(RuleWfRefusalCode::InvalidSequence, location,
                  "AllContractRounds must be the sole case");
  std::set<std::string> selectors;
  for (size_t index = 0; index < sequence.cases.size(); ++index) {
    const ContractRoundCase &value = sequence.cases[index];
    if (!validLabelProjection(value.indexProjection))
      return refuse(RuleWfRefusalCode::InvalidSequence,
                    location + ".case[" + std::to_string(index) + "]",
                    "unknown contract-round index projection");
    if (!selectors.insert(selectorKey(value.selector)).second)
      return refuse(RuleWfRefusalCode::InvalidSequence, location,
                    "contract round selectors overlap");
    RuleWfResult selector = checkSelector(
        value.selector, location + ".case[" + std::to_string(index) + "]");
    if (!selector.accepted())
      return selector;
    RuleWfResult failure;
    QuantityScope quantityScope{{value.caseName}, std::nullopt, std::nullopt};
    std::optional<QuantityInfo> space = analyzeQuantity(
        env, value.challengeSpace, quantityScope, failure,
        location + ".case[" + std::to_string(index) + "].space");
    if (!space)
      return failure;
    RuleWfResult spaceDomain = checkQuantityDomain(
        *space, QuantityDomain::PositiveInteger,
        location + ".case[" + std::to_string(index) + "].space");
    if (!spaceDomain.accepted())
      return spaceDomain;
    BoundScope boundScope;
    boundScope.quantity = std::move(quantityScope);
    RuleWfResult bound =
        checkBound(env, value.bound, boundScope,
                   location + ".case[" + std::to_string(index) + "].bound");
    if (!bound.accepted())
      return bound;
  }
  return accepted();
}

RuleWfResult requirePort(const RuleEnvironment &env, const std::string &name,
                         const SecurityIndex &index,
                         const std::string &location) {
  auto it = env.premises.find(name);
  // A body reference names a premise by the index it concluded, so a
  // premise whose quantification is a variable matches whatever the
  // body asks for on that coordinate alone.
  std::optional<SecurityQuantification> unused;
  if (it == env.premises.end() ||
      !matchSecurityIndex(it->second->expectedIndex, index, unused) ||
      it->second->expectedResult != resultFor(index))
    return refuse(RuleWfRefusalCode::InvalidBodySignature, location,
                  "body premise has the wrong exact index signature");
  return accepted();
}

void collectQuantityParameters(const QuantityTemplate &quantity,
                               std::set<std::string> &out) {
  if (quantity.kind == QuantityKind::Parameter)
    out.insert(quantity.name);
  for (const QuantityTemplate &operand : quantity.operands)
    collectQuantityParameters(operand, out);
}

void collectValueParameters(const BindingValue &value,
                            std::set<std::string> &out) {
  if (value.kind == BindingValueKind::ResolvedParameter)
    out.insert(value.reference);
}

void collectBoundParameters(const RuleBound &bound,
                            std::set<std::string> &out) {
  collectQuantityParameters(bound.quantity, out);
  for (const BindingValue &argument : bound.game.instanceArguments)
    collectValueParameters(argument, out);
  for (const auto &[name, expression] : bound.gameResourceSubstitution) {
    (void)name;
    collectQuantityParameters(expression, out);
  }
  for (const RuleBound &operand : bound.operands)
    collectBoundParameters(operand, out);
}

void collectSequenceParameters(const CoordinateSequence &sequence,
                               std::set<std::string> &out) {
  for (const CoordinateTemplate &coordinate : sequence.coordinates) {
    collectQuantityParameters(coordinate.arity, out);
    if (coordinate.challengeSpace)
      collectQuantityParameters(*coordinate.challengeSpace, out);
  }
  for (const ContractCoordinateCase &entry : sequence.cases) {
    collectQuantityParameters(entry.arity, out);
    if (entry.challengeSpace)
      collectQuantityParameters(*entry.challengeSpace, out);
  }
}

void collectSequenceParameters(const RoundSequence &sequence,
                               std::set<std::string> &out) {
  for (const RoundTemplate &round : sequence.rounds) {
    collectQuantityParameters(round.challengeSpace, out);
    collectBoundParameters(round.bound, out);
  }
  for (const ContractRoundCase &entry : sequence.cases) {
    collectQuantityParameters(entry.challengeSpace, out);
    collectBoundParameters(entry.bound, out);
  }
}

/// Every value the rule body reads a primitive-game instance argument from.
///
/// A rule is generic over the occurrences it is applied at, so `RULE_WF`
/// cannot decide whether one of these is reachable; the binding names the
/// occurrence, so binding well-formedness can.  Without this the rule body is
/// the one place a value escapes the anchor law.
void collectGameArguments(const RuleBound &bound,
                          std::vector<const BindingValue *> &out) {
  for (const BindingValue &argument : bound.game.instanceArguments)
    out.push_back(&argument);
  for (const RuleBound &operand : bound.operands)
    collectGameArguments(operand, out);
}

void collectGameArguments(const RoundSequence &sequence,
                          std::vector<const BindingValue *> &out) {
  for (const RoundTemplate &round : sequence.rounds)
    collectGameArguments(round.bound, out);
  for (const ContractRoundCase &entry : sequence.cases)
    collectGameArguments(entry.bound, out);
}

void collectGameArguments(const RuleBody &body,
                          std::vector<const BindingValue *> &out) {
  std::visit(
      [&](const auto &value) {
        using Body = std::decay_t<decltype(value)>;
        if constexpr (std::is_same_v<Body, NativeRoundByRoundEntry>) {
          collectGameArguments(value.rounds, out);
        } else if constexpr (std::is_same_v<Body, RoundByRoundPreservation>) {
          collectGameArguments(value.appendedRounds, out);
        } else if constexpr (std::is_same_v<Body, ComputationalEntry>) {
          collectGameArguments(value.failureBound, out);
        } else if constexpr (std::is_same_v<Body, CompletenessEntry>) {
          collectGameArguments(value.bound, out);
        } else if constexpr (std::is_same_v<Body,
                                            SpecialSoundnessPreservation>) {
          collectGameArguments(value.conclusionFailureBound, out);
        } else if constexpr (std::is_same_v<Body,
                                            SpecialSoundnessToRoundByRound>) {
          collectGameArguments(value.perCoordinateBound, out);
        } else if constexpr (std::is_same_v<
                                 Body, StateRestorationToFiatShamirDuplex>) {
          collectGameArguments(value.localDuplexBound, out);
        }
      },
      body);
}

/// Every declared parameter the rule body itself reads.
void collectReadParameters(const RuleBody &body, std::set<std::string> &out) {
  std::visit(
      [&](const auto &value) {
        using Body = std::decay_t<decltype(value)>;
        if constexpr (std::is_same_v<Body, SpecialSoundnessEntry>) {
          collectSequenceParameters(value.coordinates, out);
        } else if constexpr (std::is_same_v<Body, NativeRoundByRoundEntry>) {
          collectSequenceParameters(value.rounds, out);
        } else if constexpr (std::is_same_v<Body, RoundByRoundPreservation>) {
          collectSequenceParameters(value.appendedRounds, out);
        } else if constexpr (std::is_same_v<Body, ComputationalEntry>) {
          collectSequenceParameters(value.coordinates, out);
          collectBoundParameters(value.failureBound, out);
        } else if constexpr (std::is_same_v<Body, CompletenessEntry>) {
          collectBoundParameters(value.bound, out);
        } else if constexpr (std::is_same_v<Body,
                                            SpecialSoundnessPreservation>) {
          collectSequenceParameters(value.appendedCoordinates, out);
          collectBoundParameters(value.conclusionFailureBound, out);
        } else if constexpr (std::is_same_v<Body, RoundScaling>) {
          collectQuantityParameters(value.scale, out);
        } else if constexpr (std::is_same_v<Body,
                                            SpecialSoundnessToRoundByRound>) {
          collectBoundParameters(value.perCoordinateBound, out);
        } else if constexpr (std::is_same_v<Body,
                                            RoundByRoundToStateRestoration>) {
          collectQuantityParameters(value.moveBudget, out);
        } else {
          collectBoundParameters(value.localDuplexBound, out);
        }
      },
      body);
}

} // namespace

bool detail::validSubjectSchema(const std::string &lookupRef,
                                const SubjectSchema &schema) {
  return validSubjectSchemaImpl(lookupRef, schema);
}

bool detail::validMachineDecider(const std::string &lookupRef,
                                 const MachineDeciderDefinition &definition) {
  return validMachineDeciderImpl(lookupRef, definition);
}


RuleWfResult checkRuleBindingWellFormed(const SchemaContext &context,
                                        const SoundnessRule &rule,
                                        const RuleBinding &binding) {
  RuleWfResult ruleWf = checkRuleWellFormed(context, rule);
  if (!ruleWf.accepted())
    return ruleWf;

  // A declared rule is a record, not an offer. Refusing here — rather than in
  // rule well-formedness — keeps the two questions apart: the declaration is
  // still judged well-formed, and only its reachability is denied.
  if (rule.status != RuleStatus::Admitted)
    return refuse(RuleWfRefusalCode::RuleNotBindable, "binding.rule_ref",
                  "the named rule is declared, so no binding may reach it");

  if (!validExactRef(binding.ref))
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.ref",
                  "binding reference and revision must be non-empty");
  if (binding.ruleRef != rule.ref)
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.rule_ref",
                  "binding does not name the exact rule revision");
  if (!validExactRef(binding.anchor.ref))
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.anchor.ref",
                  "protocol anchor reference and revision must be non-empty");
  switch (binding.anchor.kind) {
  case ProtocolAnchorKind::ReductionContract:
  case ProtocolAnchorKind::PathTransition:
    break;
  default:
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.anchor.kind",
                  "binding has an unknown protocol-anchor kind");
  }

  auto subject = context.subjectSchemas.find(binding.subjectSchema);
  if (subject == context.subjectSchemas.end() ||
      !detail::validSubjectSchema(binding.subjectSchema, subject->second))
    return refuse(RuleWfRefusalCode::UnknownSchema, "binding.subject_schema",
                  "binding conclusion subject schema is not admitted");
  if (subject->second.kind != SubjectSchemaKind::ProtocolClaim)
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.subject_schema",
                  "a direct application binding must conclude an exact "
                  "protocol-claim subject");

  RuleEnvironment env{context,
                      rule,
                      declarationMap(rule.parameters),
                      declarationMap(rule.resources),
                      declarationMap(rule.artifactFacts),
                      {}};
  for (const PremisePort &port : rule.premises)
    env.premises.emplace(port.name, &port);

  auto checkAnchorCompatibility =
      [&](const BindingValue &value,
          const std::string &location) -> RuleWfResult {
    if (value.kind == BindingValueKind::ApplicationPathTransition) {
      if (binding.anchor.kind != ProtocolAnchorKind::PathTransition)
        return refuse(RuleWfRefusalCode::InvalidBinding, location,
                      "path-transition occurrence requires a path anchor");
      return accepted();
    }
    if (value.kind != BindingValueKind::SealedArtifactProjection)
      return accepted();
    if (value.artifactProjection.kind ==
        ArtifactProjectionKind::PathBindingField) {
      if (binding.anchor.kind != ProtocolAnchorKind::PathTransition)
        return refuse(RuleWfRefusalCode::InvalidBinding, location,
                      "path projection requires a path anchor");
      return accepted();
    }
    // A fact about the whole artifact rather than one occurrence, so it
    // is readable from either anchor kind.
    if (value.artifactProjection.kind ==
        ArtifactProjectionKind::BoundRelationAnchorCount)
      return accepted();
    if (binding.anchor.kind != ProtocolAnchorKind::ReductionContract)
      return refuse(RuleWfRefusalCode::InvalidBinding, location,
                    "reduction projection requires a reduction anchor");
    return accepted();
  };

  auto checkBoundValue = [&](const BindingValue &value, ValueSort expectedSort,
                             const std::string &location) -> RuleWfResult {
    RuleWfResult valueWf =
        checkBindingValue(env, value, expectedSort, location);
    if (!valueWf.accepted())
      return valueWf;
    return checkAnchorCompatibility(value, location);
  };
  if (binding.parameterBindings.size() != rule.parameters.size())
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.parameters",
                  "parameter binding coverage is not exact");
  for (const TypedDeclaration &parameter : rule.parameters) {
    auto value = binding.parameterBindings.find(parameter.name);
    if (value == binding.parameterBindings.end())
      return refuse(RuleWfRefusalCode::InvalidBinding,
                    "binding.parameters." + parameter.name,
                    "parameter binding is missing");
    RuleWfResult valueWf = checkBoundValue(
        value->second, parameter.sort, "binding.parameters." + parameter.name);
    if (!valueWf.accepted())
      return valueWf;
  }

  if (binding.factBindings.size() != rule.artifactFacts.size())
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.facts",
                  "artifact-fact binding coverage is not exact");
  for (const TypedDeclaration &fact : rule.artifactFacts) {
    auto value = binding.factBindings.find(fact.name);
    if (value == binding.factBindings.end())
      return refuse(RuleWfRefusalCode::InvalidBinding,
                    "binding.facts." + fact.name,
                    "artifact-fact binding is missing");
    RuleWfResult valueWf =
        checkBoundValue(value->second, fact.sort, "binding.facts." + fact.name);
    if (!valueWf.accepted())
      return valueWf;
  }

  if (binding.premiseRelations.size() != rule.premises.size())
    return refuse(RuleWfRefusalCode::InvalidBinding,
                  "binding.premise_relations",
                  "premise-relation coverage is not exact");
  for (const PremisePort &premise : rule.premises) {
    auto relationIt = binding.premiseRelations.find(premise.name);
    if (relationIt == binding.premiseRelations.end())
      return refuse(RuleWfRefusalCode::InvalidBinding,
                    "binding.premise_relations." + premise.name,
                    "premise relation is missing");
    const SubjectRelation &relation = relationIt->second;
    std::string location = "binding.premise_relations." + premise.name;
    auto expectedSubject =
        context.subjectSchemas.find(premise.expectedSubjectSchema);
    if (expectedSubject == context.subjectSchemas.end())
      return refuse(RuleWfRefusalCode::UnknownSchema, location,
                    "premise subject schema is not admitted");
    auto noExternalPayload = [&] {
      return relation.externalSubjectSchema.empty() &&
             relation.externalArguments.empty();
    };
    switch (relation.kind) {
    case SubjectRelationKind::SameSubject:
      if (relation.selector != ConsumedClaimSelectorKind::ReductionInput ||
          !relation.inputIndices.empty() || !noExternalPayload() ||
          premise.expectedSubjectSchema != binding.subjectSchema)
        return refuse(RuleWfRefusalCode::InvalidSubjectRelation, location,
                      "SameSubject has invalid active fields or schema");
      break;
    case SubjectRelationKind::ConsumedClaim:
      if (binding.anchor.kind != ProtocolAnchorKind::ReductionContract ||
          relation.selector != ConsumedClaimSelectorKind::ReductionInput ||
          relation.inputIndices.size() != 1 || !noExternalPayload() ||
          expectedSubject->second.kind != SubjectSchemaKind::ProtocolClaim)
        return refuse(RuleWfRefusalCode::InvalidSubjectRelation, location,
                      "ConsumedClaim requires one reduction input and a "
                      "protocol-claim premise");
      break;
    case SubjectRelationKind::ConsumedClaimVector: {
      bool validSelector =
          (relation.selector == ConsumedClaimSelectorKind::AllReductionInputs &&
           relation.inputIndices.empty()) ||
          (relation.selector == ConsumedClaimSelectorKind::ReductionInputs &&
           !relation.inputIndices.empty());
      std::set<uint64_t> uniqueIndices(relation.inputIndices.begin(),
                                       relation.inputIndices.end());
      if (binding.anchor.kind != ProtocolAnchorKind::ReductionContract ||
          !validSelector ||
          uniqueIndices.size() != relation.inputIndices.size() ||
          !noExternalPayload() ||
          expectedSubject->second.kind !=
              SubjectSchemaKind::ConsumedClaimVector)
        return refuse(RuleWfRefusalCode::InvalidSubjectRelation, location,
                      "ConsumedClaimVector has an invalid selector, duplicate "
                      "input, or subject schema");
      break;
    }
    case SubjectRelationKind::ExactExternalSubject:
      if (relation.selector != ConsumedClaimSelectorKind::ReductionInput ||
          !relation.inputIndices.empty() ||
          relation.externalSubjectSchema != premise.expectedSubjectSchema ||
          expectedSubject->second.kind != SubjectSchemaKind::ExternalInstance ||
          relation.externalArguments.size() !=
              expectedSubject->second.argumentTypes.size())
        return refuse(RuleWfRefusalCode::InvalidSubjectRelation, location,
                      "ExactExternalSubject has an invalid schema or arity");
      for (size_t index = 0; index < relation.externalArguments.size();
           ++index) {
        const BindingValue &argument = relation.externalArguments[index];
        if (argument.sort != expectedSubject->second.argumentTypes[index])
          return refuse(RuleWfRefusalCode::InvalidSubjectRelation,
                        location + ".argument[" + std::to_string(index) + "]",
                        "external subject argument has the wrong sort");
        RuleWfResult argumentWf = checkBoundValue(
            argument, expectedSubject->second.argumentTypes[index],
            location + ".argument[" + std::to_string(index) + "]");
        if (!argumentWf.accepted())
          return argumentWf;
      }
      break;
    default:
      return refuse(RuleWfRefusalCode::InvalidSubjectRelation, location,
                    "premise relation has an unknown relation kind");
    }
  }

  if (binding.conditionArgumentBindings.size() != rule.machineConditions.size())
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.conditions",
                  "machine-condition binding coverage is not exact");
  for (const MachineConditionTemplate &condition : rule.machineConditions) {
    auto arguments = binding.conditionArgumentBindings.find(condition.slot);
    if (arguments == binding.conditionArgumentBindings.end() ||
        arguments->second.size() != condition.argumentTypes.size())
      return refuse(RuleWfRefusalCode::InvalidBinding,
                    "binding.conditions." + condition.slot,
                    "machine-condition binding is missing or has wrong arity");
    for (size_t index = 0; index < arguments->second.size(); ++index) {
      RuleWfResult valueWf = checkBoundValue(
          arguments->second[index], condition.argumentTypes[index],
          "binding.conditions." + condition.slot + "[" + std::to_string(index) +
              "]");
      if (!valueWf.accepted())
        return valueWf;
    }
  }

  if (binding.hypothesisArgumentBindings.size() !=
      rule.externalHypotheses.size())
    return refuse(RuleWfRefusalCode::InvalidBinding, "binding.hypotheses",
                  "external-hypothesis binding coverage is not exact");
  for (const ExternalHypothesisTemplate &hypothesis : rule.externalHypotheses) {
    auto arguments = binding.hypothesisArgumentBindings.find(hypothesis.slot);
    if (arguments == binding.hypothesisArgumentBindings.end() ||
        arguments->second.size() != hypothesis.argumentTypes.size())
      return refuse(RuleWfRefusalCode::InvalidBinding,
                    "binding.hypotheses." + hypothesis.slot,
                    "hypothesis binding is missing or has wrong arity");
    for (size_t index = 0; index < arguments->second.size(); ++index) {
      RuleWfResult valueWf = checkBoundValue(
          arguments->second[index], hypothesis.argumentTypes[index],
          "binding.hypotheses." + hypothesis.slot + "[" +
              std::to_string(index) + "]");
      if (!valueWf.accepted())
        return valueWf;
    }
  }

  // Primitive-game instance arguments are binding values like any other, and
  // the body is the one place they are typed without an occurrence in hand.
  // A rule is reusable across bindings whose anchors differ, so whether a
  // path field is reachable is a question only the binding can answer.
  {
    std::vector<const BindingValue *> gameArguments;
    collectGameArguments(rule.body, gameArguments);
    for (size_t index = 0; index < gameArguments.size(); ++index) {
      const std::string location =
          "binding.body.game_argument[" + std::to_string(index) + "]";
      RuleWfResult anchorWf =
          checkAnchorCompatibility(*gameArguments[index], location);
      if (!anchorWf.accepted())
        return anchorWf;
    }
  }

  // A declared parameter that nothing reads is not inert: it is bound, so it
  // demands a value from the caller, and it can carry the same quantity a
  // condition asserts as a separate literal with nothing tying the two
  // together. Requiring every parameter to be reached forces the one value to
  // have one source.
  std::set<std::string> readParameters;
  collectReadParameters(rule.body, readParameters);
  for (const ExactParameterPin &pin : rule.exactParameterPins)
    readParameters.insert(pin.parameter);
  for (const PremisePort &port : rule.premises)
    for (const auto &[name, expression] : port.resourceSubstitution) {
      (void)name;
      collectQuantityParameters(expression, readParameters);
    }
  auto collectFromArguments =
      [&](const std::map<std::string, std::vector<BindingValue>, std::less<>>
              &arguments) {
        for (const auto &[slot, values] : arguments) {
          (void)slot;
          for (const BindingValue &value : values) {
            if (value.kind == BindingValueKind::ResolvedParameter) {
              readParameters.insert(value.reference);
              continue;
            }
            // An argument equal to a parameter bound to something the artifact
            // supplies reads that parameter: both evaluate the same
            // projection, so it is one value spelled twice. Equality with a
            // literal-bound parameter does not count — two literals agree
            // today and diverge the moment one is edited, which is the whole
            // hazard.
            for (const auto &[name, bound] : binding.parameterBindings)
              if (bound.kind != BindingValueKind::Literal && value == bound)
                readParameters.insert(name);
          }
        }
      };
  collectFromArguments(binding.conditionArgumentBindings);
  collectFromArguments(binding.hypothesisArgumentBindings);
  for (const TypedDeclaration &parameter : rule.parameters)
    if (readParameters.count(parameter.name) == 0)
      return refuse(RuleWfRefusalCode::InvalidBinding, "binding.parameters",
                    "declared parameter '" + parameter.name +
                        "' is read by neither the rule body nor any condition "
                        "or hypothesis argument of this binding");
  return accepted();
}

bool operator==(const ContractRoundSelector &lhs,
                const ContractRoundSelector &rhs) {
  return lhs.kind == rhs.kind && lhs.roundKind == rhs.roundKind &&
         lhs.position == rhs.position;
}

bool operator==(const ArtifactProjection &lhs, const ArtifactProjection &rhs) {
  return lhs.kind == rhs.kind && lhs.resultSort == rhs.resultSort &&
         lhs.field == rhs.field && lhs.inputIndex == rhs.inputIndex &&
         lhs.roundSelector == rhs.roundSelector &&
         lhs.aggregate == rhs.aggregate;
}

bool operator==(const BindingValue &lhs, const BindingValue &rhs) {
  if (lhs.kind != rhs.kind || lhs.sort != rhs.sort ||
      lhs.reference != rhs.reference || lhs.premisePort != rhs.premisePort ||
      !(lhs.artifactProjection == rhs.artifactProjection))
    return false;
  if (lhs.literal.index() != rhs.literal.index())
    return false;
  if (const auto *number = std::get_if<registry::Rational>(&lhs.literal))
    return number->compare(std::get<registry::Rational>(rhs.literal)) == 0;
  if (const auto *algebra = std::get_if<AlgebraInstanceValue>(&lhs.literal))
    return *algebra == std::get<AlgebraInstanceValue>(rhs.literal);
  if (const auto *text = std::get_if<std::string>(&lhs.literal))
    return *text == std::get<std::string>(rhs.literal);
  return std::get<bool>(lhs.literal) == std::get<bool>(rhs.literal);
}

RuleWfResult checkRuleWellFormed(const SchemaContext &context,
                                 const SoundnessRule &rule) {
  if (!validExactRef(rule.ref))
    return refuse(RuleWfRefusalCode::InvalidReference, "rule.ref",
                  "rule reference and source revision must be non-empty");
  // A pattern whose quantification is a variable describes a set of
  // indices, and its literal quantification field carries no meaning,
  // so membership degenerates sensibly only for literal patterns. What
  // a pattern must satisfy is satisfiability: some admitted index
  // matches it, otherwise it can never be filled and the rule is dead
  // on arrival.
  auto admittedPattern = [&](const SecurityIndexPattern &pattern) {
    if (pattern.quantificationVariable.empty())
      return admittedIndex(context, pattern.index);
    return llvm::any_of(context.securityIndices,
                        [&](const SecurityIndex &candidate) {
                          std::optional<SecurityQuantification> unused;
                          return matchSecurityIndex(pattern, candidate, unused);
                        });
  };
  // A conclusion's variable restates what a premise bound; with no
  // premise naming it there is nothing to restate and the conclusion
  // denotes no index at all. The instantiated index is checked against
  // the admitted vocabulary where the conclusion is assembled, since
  // which index that is depends on the derivation.
  if (!rule.conclusionIndex.quantificationVariable.empty() &&
      llvm::none_of(rule.premises, [&](const PremisePort &port) {
        return port.expectedIndex.quantificationVariable ==
               rule.conclusionIndex.quantificationVariable;
      }))
    return refuse(RuleWfRefusalCode::InvalidIndex, "rule.conclusion_index",
                  "conclusion index variable is bound by no premise");
  // The variable is a rule-level device with one name: a premise binds
  // it and the conclusion restates it. A premise naming a variable the
  // conclusion does not restate binds a value the conclusion discards,
  // and a conclusion whose literal is stronger than the discarded value
  // would then claim more than any premise established. Refusing the
  // mismatch is also what keeps one binding slot correct: two premises
  // cannot name two variables.
  for (const PremisePort &port : rule.premises)
    if (!port.expectedIndex.quantificationVariable.empty() &&
        port.expectedIndex.quantificationVariable !=
            rule.conclusionIndex.quantificationVariable)
      return refuse(RuleWfRefusalCode::InvalidIndex,
                    "rule.premise." + port.name,
                    "premise index variable is not the one the conclusion "
                    "restates");
  if (!admittedPattern(rule.conclusionIndex))
    return refuse(RuleWfRefusalCode::InvalidIndex, "rule.conclusion_index",
                  "conclusion index is absent from the admitted vocabulary");

  auto checkDeclarations = [&](const std::vector<TypedDeclaration> &values,
                               const char *location) -> RuleWfResult {
    if (std::optional<std::string> duplicate = duplicateName(
            values, [](const TypedDeclaration &value) { return value.name; }))
      return refuse(RuleWfRefusalCode::DuplicateDeclaration, location,
                    "empty or duplicate declaration '" + *duplicate + "'");
    if (std::any_of(values.begin(), values.end(),
                    [](const TypedDeclaration &value) {
                      return !validValueSort(value.sort);
                    }))
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "declaration has an unknown value sort");
    return accepted();
  };
  for (const auto &[values, location] :
       {std::pair{&rule.parameters, "rule.parameters"},
        std::pair{&rule.resources, "rule.resources"},
        std::pair{&rule.artifactFacts, "rule.artifact_facts"}}) {
    RuleWfResult declarations = checkDeclarations(*values, location);
    if (!declarations.accepted())
      return declarations;
  }
  if (std::any_of(rule.resources.begin(), rule.resources.end(),
                  [](const TypedDeclaration &resource) {
                    return !isNumeric(resource.sort);
                  }))
    return refuse(RuleWfRefusalCode::InvalidReference, "rule.resources",
                  "rule resources must be numeric");
  if (std::optional<std::string> duplicate = duplicateName(
          rule.premises, [](const PremisePort &port) { return port.name; }))
    return refuse(RuleWfRefusalCode::DuplicateDeclaration, "rule.premises",
                  "empty or duplicate premise port '" + *duplicate + "'");

  RuleEnvironment env{context,
                      rule,
                      declarationMap(rule.parameters),
                      declarationMap(rule.resources),
                      declarationMap(rule.artifactFacts),
                      {}};
  for (const PremisePort &port : rule.premises)
    env.premises.emplace(port.name, &port);

  for (const PremisePort &port : rule.premises) {
    auto subject = context.subjectSchemas.find(port.expectedSubjectSchema);
    if (!admittedPattern(port.expectedIndex) ||
        !validResultSchema(port.expectedResult) ||
        port.expectedResult != resultFor(port.expectedIndex.index) ||
        subject == context.subjectSchemas.end() ||
        !detail::validSubjectSchema(port.expectedSubjectSchema,
                                    subject->second))
      return refuse(RuleWfRefusalCode::UnknownSchema,
                    "rule.premise." + port.name,
                    "premise index, result, or subject schema is invalid");
    RuleWfResult resources =
        checkDeclarations(port.expectedResources, "premise.resources");
    if (!resources.accepted())
      return resources;
    if (std::any_of(port.expectedResources.begin(),
                    port.expectedResources.end(),
                    [](const TypedDeclaration &resource) {
                      return !isNumeric(resource.sort);
                    }))
      return refuse(RuleWfRefusalCode::InvalidReference,
                    "rule.premise." + port.name + ".resources",
                    "premise resources must be numeric");
    for (PremiseResultConstraint constraint : port.resultConstraints) {
      if (constraint != PremiseResultConstraint::RequiresEmptyGameSupport &&
          constraint != PremiseResultConstraint::RequiresNoBoundResourceSupport)
        return refuse(RuleWfRefusalCode::InvalidBodySignature,
                      "rule.premise." + port.name,
                      "premise has an unknown result constraint");
    }
    std::set<std::string> expected;
    for (const TypedDeclaration &resource : port.expectedResources)
      expected.insert(resource.name);
    std::set<std::string> actual;
    for (const auto &entry : port.resourceSubstitution)
      actual.insert(entry.first);
    if (expected != actual)
      return refuse(RuleWfRefusalCode::InvalidResourceSubstitution,
                    "rule.premise." + port.name,
                    "premise resource substitution is not total");
    for (const auto &[name, expression] : port.resourceSubstitution) {
      if (!isResourceExpression(expression))
        return refuse(RuleWfRefusalCode::InvalidResourceSubstitution,
                      "rule.premise." + port.name + "." + name,
                      "premise resources may depend only on conclusion "
                      "resources and exact rational arithmetic");
      RuleWfResult failure;
      std::optional<QuantityInfo> quantity =
          analyzeQuantity(env, expression, {}, failure,
                          "rule.premise." + port.name + "." + name);
      if (!quantity)
        return failure;
      RuleWfResult domain =
          checkQuantityDomain(*quantity, QuantityDomain::NonNegative,
                              "rule.premise." + port.name + "." + name);
      if (!domain.accepted())
        return domain;
      auto expectedResource = std::find_if(
          port.expectedResources.begin(), port.expectedResources.end(),
          [&](const TypedDeclaration &declaration) {
            return declaration.name == name;
          });
      if (expectedResource == port.expectedResources.end() ||
          expectedResource->sort != quantity->sort)
        return refuse(RuleWfRefusalCode::InvalidResourceSubstitution,
                      "rule.premise." + port.name + "." + name,
                      "premise resource substitution changes its sort");
    }
  }

  if (std::optional<std::string> duplicate =
          duplicateName(rule.machineConditions,
                        [](const MachineConditionTemplate &condition) {
                          return condition.slot;
                        }))
    return refuse(RuleWfRefusalCode::DuplicateDeclaration,
                  "rule.machine_conditions",
                  "empty or duplicate condition slot '" + *duplicate + "'");
  for (const MachineConditionTemplate &condition : rule.machineConditions) {
    auto definition = context.machineDeciders.find(condition.predicateRef);
    if (definition == context.machineDeciders.end() ||
        !detail::validMachineDecider(condition.predicateRef,
                                     definition->second) ||
        std::any_of(condition.argumentTypes.begin(),
                    condition.argumentTypes.end(),
                    [](ValueSort sort) { return !validValueSort(sort); }) ||
        definition->second.argumentTypes != condition.argumentTypes)
      return refuse(RuleWfRefusalCode::InvalidCondition,
                    "rule.machine_condition." + condition.slot,
                    "unknown decider or argument signature mismatch");
  }

  if (std::optional<std::string> duplicate =
          duplicateName(rule.externalHypotheses,
                        [](const ExternalHypothesisTemplate &hypothesis) {
                          return hypothesis.slot;
                        }))
    return refuse(RuleWfRefusalCode::DuplicateDeclaration,
                  "rule.external_hypotheses",
                  "empty or duplicate hypothesis slot '" + *duplicate + "'");
  for (const ExternalHypothesisTemplate &hypothesis : rule.externalHypotheses) {
    auto definition = context.propositions.find(hypothesis.propositionRef);
    if (definition == context.propositions.end() ||
        !validExactRef(definition->second.ref) ||
        definition->second.ref.id != hypothesis.propositionRef ||
        std::any_of(hypothesis.argumentTypes.begin(),
                    hypothesis.argumentTypes.end(),
                    [](ValueSort sort) { return !validValueSort(sort); }) ||
        definition->second.argumentTypes != hypothesis.argumentTypes)
      return refuse(RuleWfRefusalCode::InvalidHypothesis,
                    "rule.external_hypothesis." + hypothesis.slot,
                    "unknown proposition or argument signature mismatch");
  }

  if (std::optional<std::string> duplicate = duplicateName(
          rule.exactParameterPins,
          [](const ExactParameterPin &pin) { return pin.parameter; }))
    return refuse(
        RuleWfRefusalCode::DuplicateDeclaration, "rule.exact_parameter_pins",
        "empty or duplicate exact parameter pin '" + *duplicate + "'");
  for (size_t index = 0; index < rule.exactParameterPins.size(); ++index) {
    const ExactParameterPin &pin = rule.exactParameterPins[index];
    const std::string location =
        "rule.exact_parameter_pins[" + std::to_string(index) + "]";
    auto parameter = env.parameters.find(pin.parameter);
    if (pin.parameter.empty() || parameter == env.parameters.end())
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "exact parameter pin names no declared parameter");
    if (pin.expected.kind != BindingValueKind::Literal ||
        pin.expected.sort != parameter->second)
      return refuse(RuleWfRefusalCode::InvalidReference, location,
                    "exact parameter pin has a nonliteral or ill-typed value");
    RuleWfResult expected = checkBindingValue(
        env, pin.expected, parameter->second, location + ".expected");
    if (!expected.accepted())
      return expected;
  }

  return std::visit(
      [&](const auto &body) -> RuleWfResult {
        using Body = std::decay_t<decltype(body)>;
        if constexpr (std::is_same_v<Body, SpecialSoundnessEntry>) {
          if (!rule.premises.empty() || rule.conclusionIndex.index.notion !=
                                            SecurityNotion::SpecialSoundness)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "SpecialSoundnessEntry has an invalid index "
                          "signature");
          return checkCoordinates(env, body.coordinates,
                                  "rule.body.coordinates");
        } else if constexpr (std::is_same_v<Body, NativeRoundByRoundEntry>) {
          if (!rule.premises.empty() ||
              rule.conclusionIndex.index.notion != SecurityNotion::RoundByRound)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "NativeRoundByRoundEntry has an invalid index "
                          "signature");
          return checkRounds(env, body.rounds, "rule.body.rounds");
        } else if constexpr (std::is_same_v<Body, ComputationalEntry>) {
          if (!rule.premises.empty() ||
              rule.conclusionIndex.index.notion !=
                  SecurityNotion::ComputationalSpecialSoundness)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "ComputationalEntry has an invalid index signature");
          RuleWfResult coordinates =
              checkCoordinates(env, body.coordinates, "rule.body.coordinates");
          if (!coordinates.accepted())
            return coordinates;
          return checkBound(env, body.failureBound, {},
                            "rule.body.failure_bound");
        } else if constexpr (std::is_same_v<Body, CompletenessEntry>) {
          if (!rule.premises.empty() ||
              rule.conclusionIndex.index.notion != SecurityNotion::Completeness)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "CompletenessEntry has an invalid index signature");
          return checkBound(env, body.bound, {}, "rule.body.bound");
        } else if constexpr (std::is_same_v<Body,
                                            SpecialSoundnessPreservation>) {
          if (rule.premises.size() != 1 ||
              rule.conclusionIndex.index.notion !=
                  SecurityNotion::ComputationalSpecialSoundness)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "SpecialSoundnessPreservation requires exactly one "
                          "special-soundness premise");
          SecurityIndex expected{SecurityNotion::SpecialSoundness,
                                 rule.conclusionIndex.index.track,
                                 {},
                                 {},
                                 rule.conclusionIndex.index.quantification};
          RuleWfResult port =
              requirePort(env, body.sourcePort, expected, "rule.body");
          if (!port.accepted())
            return port;
          RuleWfResult coordinates = checkCoordinates(
              env, body.appendedCoordinates, "rule.body.appended_coordinates");
          if (!coordinates.accepted())
            return coordinates;
          return checkBound(env, body.conclusionFailureBound, {},
                            "rule.body.conclusion_failure_bound");
        } else if constexpr (std::is_same_v<Body, RoundByRoundPreservation>) {
          if (rule.premises.size() != 1 ||
              rule.conclusionIndex.index.notion != SecurityNotion::RoundByRound)
            return refuse(
                RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                "RoundByRoundPreservation has an invalid index signature");
          // Unlike the special-soundness preservation beside it this body
          // cannot shift the notion, and concatenating two round sequences
          // priced under different variants would mean nothing, so the
          // premise index is the conclusion index exactly.
          RuleWfResult port = requirePort(
              env, body.sourcePort, rule.conclusionIndex.index, "rule.body");
          if (!port.accepted())
            return port;
          return checkRounds(env, body.appendedRounds,
                             "rule.body.appended_rounds");
        } else if constexpr (std::is_same_v<Body, RoundScaling>) {
          if (rule.premises.size() != 1 ||
              rule.conclusionIndex.index.notion != SecurityNotion::RoundByRound)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "RoundScaling has an invalid index signature");
          RuleWfResult port =
              requirePort(env, body.roundByRoundPort,
                          rule.conclusionIndex.index, "rule.body");
          if (!port.accepted())
            return port;
          if (body.selectedRound.kind == RoundSelectorKind::ByRoundIndex) {
            if (body.selectedRound.exactRoundIndex.empty() ||
                !body.selectedRound.adjacencyFactPort.empty())
              return refuse(RuleWfRefusalCode::InvalidBodySignature,
                            "rule.body",
                            "exact round selector has invalid active fields");
          } else if (body.selectedRound.kind ==
                     RoundSelectorKind::AdjacentPredecessorRound) {
            if (!body.selectedRound.exactRoundIndex.empty() ||
                body.selectedRound.adjacencyFactPort.empty())
              return refuse(
                  RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                  "adjacent round selector has invalid active fields");
            auto adjacency =
                env.facts.find(body.selectedRound.adjacencyFactPort);
            if (adjacency == env.facts.end() ||
                adjacency->second != ValueSort::RoundAdjacency)
              return refuse(
                  RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                  "adjacent selector lacks a typed authenticated fact port");
          } else {
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "unknown round-selector kind");
          }
          RuleWfResult failure;
          std::optional<QuantityInfo> scale =
              analyzeQuantity(env, body.scale, {}, failure, "rule.body.scale");
          if (!scale)
            return failure;
          if (scale->resourceShape != ResourceShape::None)
            return refuse(RuleWfRefusalCode::InvalidBodySignature,
                          "rule.body.scale",
                          "round scale may not depend on a resource");
          RuleWfResult scaleDomain = checkQuantityDomain(
              *scale, QuantityDomain::NonNegative, "rule.body.scale");
          if (!scaleDomain.accepted())
            return scaleDomain;
          return accepted();
        } else if constexpr (std::is_same_v<Body,
                                            SpecialSoundnessToRoundByRound>) {
          if (rule.premises.size() != 1 ||
              rule.conclusionIndex.index.notion != SecurityNotion::RoundByRound)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "SpecialSoundnessToRoundByRound has an invalid "
                          "index signature");
          SecurityIndex expected{SecurityNotion::SpecialSoundness,
                                 rule.conclusionIndex.index.track,
                                 {},
                                 {},
                                 rule.conclusionIndex.index.quantification};
          RuleWfResult port = requirePort(env, body.specialSoundnessPort,
                                          expected, "rule.body");
          if (!port.accepted())
            return port;
          BoundScope scope;
          scope.quantity.boundCoordinatePort = body.specialSoundnessPort;
          return checkBound(env, body.perCoordinateBound, scope,
                            "rule.body.per_coordinate_bound");
        } else if constexpr (std::is_same_v<Body,
                                            RoundByRoundToStateRestoration>) {
          if (rule.premises.size() != 1 || rule.conclusionIndex.index.notion !=
                                               SecurityNotion::StateRestoration)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "RoundByRoundToStateRestoration has an invalid "
                          "index signature");
          SecurityIndex expected{SecurityNotion::RoundByRound,
                                 rule.conclusionIndex.index.track,
                                 rule.conclusionIndex.index.variant,
                                 {},
                                 rule.conclusionIndex.index.quantification};
          RuleWfResult port =
              requirePort(env, body.roundByRoundPort, expected, "rule.body");
          if (!port.accepted())
            return port;
          const PremisePort &premise = *env.premises.at(body.roundByRoundPort);
          if (!premise.resultConstraints.count(
                  PremiseResultConstraint::RequiresEmptyGameSupport) ||
              !premise.resultConstraints.count(
                  PremiseResultConstraint::RequiresNoBoundResourceSupport))
            return refuse(RuleWfRefusalCode::MissingRbrToSrConstraint,
                          "rule.body",
                          "RBR-to-SR requires empty-game and ground-resource "
                          "premise constraints");
          RuleWfResult failure;
          std::optional<QuantityInfo> moveBudget = analyzeQuantity(
              env, body.moveBudget, {}, failure, "rule.body.move_budget");
          if (!moveBudget)
            return failure;
          RuleWfResult moveDomain =
              checkQuantityDomain(*moveBudget, QuantityDomain::NonNegative,
                                  "rule.body.move_budget");
          if (!moveDomain.accepted())
            return moveDomain;
          return accepted();
        } else {
          static_assert(
              std::is_same_v<Body, StateRestorationToFiatShamirDuplex>);
          if (rule.premises.size() != 1 ||
              rule.conclusionIndex.index.notion != SecurityNotion::FiatShamir)
            return refuse(RuleWfRefusalCode::InvalidBodySignature, "rule.body",
                          "StateRestorationToFiatShamirDuplex has an invalid "
                          "index signature");
          SecurityIndex expected{SecurityNotion::StateRestoration,
                                 rule.conclusionIndex.index.track,
                                 rule.conclusionIndex.index.variant,
                                 {},
                                 rule.conclusionIndex.index.quantification};
          RuleWfResult port = requirePort(env, body.stateRestorationPort,
                                          expected, "rule.body");
          if (!port.accepted())
            return port;
          BoundScope scope;
          scope.forbiddenPremisePort = body.stateRestorationPort;
          scope.quantity.forbiddenPremisePort = body.stateRestorationPort;
          return checkBound(env, body.localDuplexBound, scope,
                            "rule.body.local_duplex_bound");
        }
      },
      rule.body);
}

const char *ruleWfRefusalCodeName(RuleWfRefusalCode code) {
  switch (code) {
  case RuleWfRefusalCode::InvalidReference:
    return "invalid_reference";
  case RuleWfRefusalCode::DuplicateDeclaration:
    return "duplicate_declaration";
  case RuleWfRefusalCode::UnknownSchema:
    return "unknown_schema";
  case RuleWfRefusalCode::InvalidIndex:
    return "invalid_index";
  case RuleWfRefusalCode::InvalidBodySignature:
    return "invalid_body_signature";
  case RuleWfRefusalCode::InvalidQuantity:
    return "invalid_quantity";
  case RuleWfRefusalCode::InvalidBound:
    return "invalid_bound";
  case RuleWfRefusalCode::InvalidSequence:
    return "invalid_sequence";
  case RuleWfRefusalCode::InvalidPrimitiveGame:
    return "invalid_primitive_game";
  case RuleWfRefusalCode::InvalidCondition:
    return "invalid_condition";
  case RuleWfRefusalCode::InvalidHypothesis:
    return "invalid_hypothesis";
  case RuleWfRefusalCode::InvalidResourceSubstitution:
    return "invalid_resource_substitution";
  case RuleWfRefusalCode::MissingRbrToSrConstraint:
    return "missing_rbr_to_sr_constraint";
  case RuleWfRefusalCode::InvalidBinding:
    return "invalid_binding";
  case RuleWfRefusalCode::InvalidSubjectRelation:
    return "invalid_subject_relation";
  case RuleWfRefusalCode::RuleNotBindable:
    return "rule_not_bindable";
  }
  return "unknown";
}

const char *ruleStatusName(RuleStatus status) {
  switch (status) {
  case RuleStatus::Admitted:
    return "admitted";
  case RuleStatus::Declared:
    return "declared";
  }
  return "unknown";
}


} // namespace zkc::soundness
