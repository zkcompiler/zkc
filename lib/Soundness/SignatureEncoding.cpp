//===- SignatureEncoding.cpp - Canonical declaration bytes --------------===//
#include "zkc/Soundness/SignatureEncoding.h"

#include "zkc/Encoding/CanonicalJson.h"

#include <utility>

using llvm::json::Array;
using llvm::json::Object;
using llvm::json::Value;

namespace zkc::soundness {

namespace {

constexpr llvm::StringRef kRuleDomain = "zkc/soundness-rule\n";
constexpr llvm::StringRef kBindingDomain = "zkc/soundness-binding\n";
constexpr llvm::StringRef kSignatureDomain = "zkc/soundness-signature\n";

const char *valueSortName(ValueSort sort) {
  switch (sort) {
  case ValueSort::Integer:
    return "integer";
  case ValueSort::Rational:
    return "rational";
  case ValueSort::String:
    return "string";
  case ValueSort::Boolean:
    return "boolean";
  case ValueSort::Subject:
    return "subject";
  case ValueSort::ReductionContract:
    return "reduction_contract";
  case ValueSort::PathTransition:
    return "path_transition";
  case ValueSort::RoundAdjacency:
    return "round_adjacency";
  case ValueSort::AlgebraInstance:
    return "algebra_instance";
  case ValueSort::SrsInstance:
    return "srs_instance";
  case ValueSort::FriDomainInstance:
    return "fri_domain_instance";
  }
  return "unknown";
}

const char *securityNotionName(SecurityNotion notion) {
  switch (notion) {
  case SecurityNotion::SpecialSoundness:
    return "special_soundness";
  case SecurityNotion::ComputationalSpecialSoundness:
    return "computational_special_soundness";
  case SecurityNotion::RoundByRound:
    return "round_by_round";
  case SecurityNotion::StateRestoration:
    return "state_restoration";
  case SecurityNotion::FiatShamir:
    return "fiat_shamir";
  case SecurityNotion::Completeness:
    return "completeness";
  }
  return "unknown";
}

const char *securityTrackName(SecurityTrack track) {
  switch (track) {
  case SecurityTrack::Soundness:
    return "soundness";
  case SecurityTrack::Knowledge:
    return "knowledge";
  case SecurityTrack::Completeness:
    return "completeness";
  }
  return "soundness";
}

const char *resultSchemaName(ResultSchema schema) {
  switch (schema) {
  case ResultSchema::Extraction:
    return "extraction";
  case ResultSchema::Round:
    return "round";
  case ResultSchema::Scalar:
    return "scalar";
  }
  return "unknown";
}

const char *subjectSchemaKindName(SubjectSchemaKind kind) {
  switch (kind) {
  case SubjectSchemaKind::ProtocolClaim:
    return "protocol_claim";
  case SubjectSchemaKind::ConsumedClaimVector:
    return "consumed_claim_vector";
  case SubjectSchemaKind::ExternalInstance:
    return "external_instance";
  }
  return "unknown";
}

const char *quantityKindName(QuantityKind kind) {
  switch (kind) {
  case QuantityKind::RationalLiteral:
    return "rational_literal";
  case QuantityKind::Parameter:
    return "parameter";
  case QuantityKind::ArtifactFact:
    return "artifact_fact";
  case QuantityKind::ContractRoundFact:
    return "contract_round_fact";
  case QuantityKind::PremiseCoordinate:
    return "premise_coordinate";
  case QuantityKind::ResourceVariable:
    return "resource_variable";
  case QuantityKind::Add:
    return "add";
  case QuantityKind::Sub:
    return "sub";
  case QuantityKind::Mul:
    return "mul";
  case QuantityKind::Div:
    return "div";
  case QuantityKind::Pow:
    return "pow";
  case QuantityKind::Pow2:
    return "pow2";
  case QuantityKind::Pow2Up:
    return "pow2_up";
  }
  return "unknown";
}

const char *contractRoundFieldName(ContractRoundField field) {
  switch (field) {
  case ContractRoundField::ChallengeSpace:
    return "challenge_space";
  case ContractRoundField::ChallengeCount:
    return "challenge_count";
  case ContractRoundField::RoundDegree:
    return "round_degree";
  case ContractRoundField::ChallengeSpaceLog2:
    return "challenge_space_log2";
  }
  return "unknown";
}

const char *premiseCoordinateFieldName(PremiseCoordinateField field) {
  return field == PremiseCoordinateField::Arity ? "arity" : "challenge_space";
}

const char *contractLabelProjectionName(ContractLabelProjection projection) {
  switch (projection) {
  case ContractLabelProjection::RoundIndex:
    return "round_index";
  case ContractLabelProjection::RoundKindOccurrence:
    return "round_kind_occurrence";
  case ContractLabelProjection::CaseName:
    return "case_name";
  case ContractLabelProjection::SiteQualifiedRoundIndex:
    return "site_qualified_round_index";
  }
  return "unknown";
}

const char *bindingValueKindName(BindingValueKind kind) {
  switch (kind) {
  case BindingValueKind::Literal:
    return "literal";
  case BindingValueKind::SealedArtifactProjection:
    return "sealed_artifact_projection";
  case BindingValueKind::ConclusionSubject:
    return "conclusion_subject";
  case BindingValueKind::ApplicationPathTransition:
    return "application_path_transition";
  case BindingValueKind::ConclusionResource:
    return "conclusion_resource";
  case BindingValueKind::ResolvedParameter:
    return "resolved_parameter";
  }
  return "unknown";
}

const char *artifactProjectionKindName(ArtifactProjectionKind kind) {
  switch (kind) {
  case ArtifactProjectionKind::ConclusionReductionContract:
    return "conclusion_reduction_contract";
  case ArtifactProjectionKind::ContractRoundAdjacency:
    return "contract_round_adjacency";
  case ArtifactProjectionKind::ReductionInputCount:
    return "reduction_input_count";
  case ArtifactProjectionKind::ReductionParameter:
    return "reduction_parameter";
  case ArtifactProjectionKind::ContractRoundFamilyField:
    return "contract_round_family_field";
  case ArtifactProjectionKind::PathBindingField:
    return "path_binding_field";
  }
  return "unknown";
}

const char *subjectRelationKindName(SubjectRelationKind kind) {
  switch (kind) {
  case SubjectRelationKind::SameSubject:
    return "same_subject";
  case SubjectRelationKind::ConsumedClaim:
    return "consumed_claim";
  case SubjectRelationKind::ConsumedClaimVector:
    return "consumed_claim_vector";
  case SubjectRelationKind::ExactExternalSubject:
    return "exact_external_subject";
  }
  return "unknown";
}

const char *consumedClaimSelectorName(ConsumedClaimSelectorKind kind) {
  switch (kind) {
  case ConsumedClaimSelectorKind::ReductionInput:
    return "reduction_input";
  case ConsumedClaimSelectorKind::AllReductionInputs:
    return "all_reduction_inputs";
  case ConsumedClaimSelectorKind::ReductionInputs:
    return "reduction_inputs";
  }
  return "unknown";
}

const char *machineDeciderKindName(MachineDeciderKind kind) {
  switch (kind) {
  case MachineDeciderKind::OneMessageRole:
    return "one_message_role";
  case MachineDeciderKind::SpaceEmbeds:
    return "space_embeds";
  case MachineDeciderKind::BoundBites:
    return "bound_bites";
  case MachineDeciderKind::FieldClass:
    return "field_class";
  case MachineDeciderKind::SpaceCoversArity:
    return "space_covers_arity";
  case MachineDeciderKind::BatchArity:
    return "batch_arity";
  case MachineDeciderKind::SpaceCoversBatch:
    return "space_covers_batch";
  case MachineDeciderKind::SamePoint:
    return "same_point";
  case MachineDeciderKind::BatchAfterMaterial:
    return "batch_after_material";
  case MachineDeciderKind::FriShape:
    return "fri_shape";
  case MachineDeciderKind::JohnsonFoldParam:
    return "johnson_fold_param";
  case MachineDeciderKind::JohnsonSlack:
    return "johnson_slack";
  case MachineDeciderKind::JohnsonMultiplicity:
    return "johnson_multiplicity";
  case MachineDeciderKind::JohnsonDelta:
    return "johnson_delta";
  case MachineDeciderKind::UdrDomainFloor:
    return "udr_domain_floor";
  case MachineDeciderKind::UdrThetaWindow:
    return "udr_theta_window";
  case MachineDeciderKind::RandomWordsEtaFloor:
    return "random_words_eta_floor";
  case MachineDeciderKind::ThresholdDeltaWindow:
    return "threshold_delta_window";
  case MachineDeciderKind::PowPinned:
    return "pow_pinned";
  case MachineDeciderKind::PowAdjacent:
    return "pow_adjacent";
  case MachineDeciderKind::DuplexSpine:
    return "duplex_spine";
  case MachineDeciderKind::CodecBiasDeclared:
    return "codec_bias_declared";
  }
  return "unknown";
}

Value encodeExactRef(const ExactRef &ref) {
  return Object{{"id", ref.id}, {"source_revision", ref.sourceRevision}};
}

Value encodeTypedDeclarations(const std::vector<TypedDeclaration> &values) {
  Array items;
  for (const TypedDeclaration &value : values)
    items.push_back(
        Object{{"name", value.name}, {"sort", valueSortName(value.sort)}});
  return items;
}

Value encodeValueSorts(const std::vector<ValueSort> &sorts) {
  Array items;
  for (ValueSort sort : sorts)
    items.push_back(valueSortName(sort));
  return items;
}

Value encodeSecurityIndex(const SecurityIndex &index) {
  return Object{{"notion", securityNotionName(index.notion)},
                {"track", securityTrackName(index.track)},
                {"variant", index.variant},
                {"model", index.model}};
}

Value encodeRoundSelector(const ContractRoundSelector &selector) {
  switch (selector.kind) {
  case ContractRoundSelectorKind::AllContractRounds:
    return Object{{"kind", "all_contract_rounds"}};
  case ContractRoundSelectorKind::RoundKind:
    return Object{{"kind", "round_kind"}, {"round_kind", selector.roundKind}};
  case ContractRoundSelectorKind::RoundPosition:
    return Object{{"kind", "round_position"},
                  {"position", int64_t(selector.position)}};
  }
  return Object{{"kind", "unknown"}};
}

Value encodeArtifactProjection(const ArtifactProjection &projection) {
  Object document{{"kind", artifactProjectionKindName(projection.kind)},
                  {"result_sort", valueSortName(projection.resultSort)}};
  switch (projection.kind) {
  case ArtifactProjectionKind::ConclusionReductionContract:
  case ArtifactProjectionKind::ContractRoundAdjacency:
  case ArtifactProjectionKind::ReductionInputCount:
    break;
  case ArtifactProjectionKind::ReductionParameter:
  case ArtifactProjectionKind::PathBindingField:
    document["field"] = projection.field;
    break;
  case ArtifactProjectionKind::ContractRoundFamilyField:
    document["field"] = projection.field;
    document["round_selector"] = encodeRoundSelector(projection.roundSelector);
    document["aggregate"] = projection.aggregate == ProjectionAggregate::Count
                                ? "count"
                                : "unique_equal";
    break;
  }
  return document;
}

Value encodeBindingValue(const BindingValue &value) {
  Object document{{"kind", bindingValueKindName(value.kind)},
                  {"sort", valueSortName(value.sort)}};
  switch (value.kind) {
  case BindingValueKind::Literal:
    if (const auto *number = std::get_if<registry::Rational>(&value.literal))
      document["literal"] = number->str();
    else if (const auto *text = std::get_if<std::string>(&value.literal))
      document["literal"] = *text;
    else if (const auto *flag = std::get_if<bool>(&value.literal))
      document["literal"] = *flag;
    else if (const auto *algebra =
                 std::get_if<AlgebraInstanceValue>(&value.literal))
      document["literal"] = Object{{"group", algebra->group},
                                   {"field_class", algebra->fieldClass},
                                   {"field_order", algebra->fieldOrder.str()}};
    break;
  case BindingValueKind::SealedArtifactProjection:
    document["artifact_projection"] =
        encodeArtifactProjection(value.artifactProjection);
    break;
  case BindingValueKind::ConclusionSubject:
  case BindingValueKind::ApplicationPathTransition:
    break;
  case BindingValueKind::ConclusionResource:
  case BindingValueKind::ResolvedParameter:
    document["reference"] = value.reference;
    break;
  }
  return document;
}

Value encodeBindingValues(const std::vector<BindingValue> &values) {
  Array items;
  for (const BindingValue &value : values)
    items.push_back(encodeBindingValue(value));
  return items;
}

Value encodeQuantity(const QuantityTemplate &quantity) {
  Object document{{"kind", quantityKindName(quantity.kind)}};
  switch (quantity.kind) {
  case QuantityKind::RationalLiteral:
    document["literal"] = quantity.literal.str();
    break;
  case QuantityKind::Parameter:
  case QuantityKind::ArtifactFact:
  case QuantityKind::ResourceVariable:
    document["name"] = quantity.name;
    break;
  case QuantityKind::ContractRoundFact:
    document["case_name"] = quantity.caseName;
    document["field"] = contractRoundFieldName(quantity.contractRoundField);
    break;
  case QuantityKind::PremiseCoordinate: {
    document["port"] = quantity.port;
    document["field"] =
        premiseCoordinateFieldName(quantity.premiseCoordinateField);
    document["selector"] = Object{{"kind", "bound_coordinate"}};
    break;
  }
  case QuantityKind::Add:
  case QuantityKind::Sub:
  case QuantityKind::Mul:
  case QuantityKind::Div:
  case QuantityKind::Pow:
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up: {
    Array operands;
    for (const QuantityTemplate &operand : quantity.operands)
      operands.push_back(encodeQuantity(operand));
    document["operands"] = std::move(operands);
    break;
  }
  }
  return document;
}

Value encodeOptionalQuantity(const std::optional<QuantityTemplate> &quantity) {
  if (!quantity)
    return nullptr;
  return encodeQuantity(*quantity);
}

Value encodeQuantityMap(
    const std::map<std::string, QuantityTemplate, std::less<>> &quantities) {
  Object document;
  for (const auto &[name, quantity] : quantities)
    document[name] = encodeQuantity(quantity);
  return document;
}

Value encodeBound(const RuleBound &bound) {
  auto operands = [&] {
    Array items;
    for (const RuleBound &operand : bound.operands)
      items.push_back(encodeBound(operand));
    return items;
  };

  switch (bound.kind) {
  case RuleBoundKind::Quantity:
    return Object{{"kind", "quantity"},
                  {"quantity", encodeQuantity(bound.quantity)}};
  case RuleBoundKind::ScalarBound:
    return Object{{"kind", "scalar_bound"},
                  {"premise_port", bound.premisePort}};
  case RuleBoundKind::PrimitiveAdvantage:
    return Object{
        {"kind", "primitive_advantage"},
        {"game", Object{{"ref", bound.game.gameRef},
                        {"instance_arguments",
                         encodeBindingValues(bound.game.instanceArguments)}}},
        {"resource_substitution",
         encodeQuantityMap(bound.gameResourceSubstitution)}};
  case RuleBoundKind::Add:
    return Object{{"kind", "add"}, {"operands", operands()}};
  case RuleBoundKind::Max:
    return Object{{"kind", "max"}, {"operands", operands()}};
  case RuleBoundKind::Scale:
    return Object{{"kind", "scale"},
                  {"scale", encodeQuantity(bound.quantity)},
                  {"operands", operands()}};
  }
  return Object{{"kind", "unknown"}};
}

Value encodeCoordinateSequence(const CoordinateSequence &sequence) {
  if (sequence.kind == CoordinateSequence::Kind::Explicit) {
    Array coordinates;
    for (const CoordinateTemplate &coordinate : sequence.coordinates)
      coordinates.push_back(
          Object{{"label", coordinate.label},
                 {"arity", encodeQuantity(coordinate.arity)},
                 {"challenge_space",
                  encodeOptionalQuantity(coordinate.challengeSpace)}});
    return Object{{"kind", "explicit"},
                  {"coordinates", std::move(coordinates)}};
  }
  Array cases;
  for (const ContractCoordinateCase &entry : sequence.cases)
    cases.push_back(Object{
        {"case_name", entry.caseName},
        {"selector", encodeRoundSelector(entry.selector)},
        {"label_projection",
         contractLabelProjectionName(entry.labelProjection)},
        {"arity", encodeQuantity(entry.arity)},
        {"challenge_space", encodeOptionalQuantity(entry.challengeSpace)}});
  return Object{{"kind", "contract"},
                {"contract_fact_port", sequence.contractFactPort},
                {"cases", std::move(cases)}};
}

Value encodeRoundSequence(const RoundSequence &sequence) {
  if (sequence.kind == RoundSequence::Kind::Explicit) {
    Array rounds;
    for (const RoundTemplate &round : sequence.rounds)
      rounds.push_back(
          Object{{"round_index", round.roundIndex},
                 {"challenge_space", encodeQuantity(round.challengeSpace)},
                 {"bound", encodeBound(round.bound)}});
    return Object{{"kind", "explicit"}, {"rounds", std::move(rounds)}};
  }
  Array cases;
  for (const ContractRoundCase &entry : sequence.cases)
    cases.push_back(
        Object{{"case_name", entry.caseName},
               {"selector", encodeRoundSelector(entry.selector)},
               {"index_projection",
                contractLabelProjectionName(entry.indexProjection)},
               {"challenge_space", encodeQuantity(entry.challengeSpace)},
               {"bound", encodeBound(entry.bound)}});
  return Object{{"kind", "contract"},
                {"contract_fact_port", sequence.contractFactPort},
                {"cases", std::move(cases)}};
}

Value encodeRoundSelectorTemplate(const RoundSelectorTemplate &selector) {
  if (selector.kind == RoundSelectorKind::ByRoundIndex)
    return Object{{"kind", "by_round_index"},
                  {"round_index", selector.exactRoundIndex}};
  return Object{{"kind", "adjacent_predecessor_round"},
                {"adjacency_fact_port", selector.adjacencyFactPort}};
}

Value encodeBody(const RuleBody &body) {
  return std::visit(
      [](const auto &value) -> Value {
        using Body = std::decay_t<decltype(value)>;
        if constexpr (std::is_same_v<Body, SpecialSoundnessEntry>)
          return Object{
              {"kind", "special_soundness_entry"},
              {"coordinates", encodeCoordinateSequence(value.coordinates)}};
        else if constexpr (std::is_same_v<Body, NativeRoundByRoundEntry>)
          return Object{{"kind", "native_round_by_round_entry"},
                        {"rounds", encodeRoundSequence(value.rounds)}};
        else if constexpr (std::is_same_v<Body, ComputationalEntry>)
          return Object{
              {"kind", "computational_entry"},
              {"coordinates", encodeCoordinateSequence(value.coordinates)},
              {"failure_bound", encodeBound(value.failureBound)}};
        else if constexpr (std::is_same_v<Body, CompletenessEntry>)
          return Object{{"kind", "completeness_entry"},
                        {"bound", encodeBound(value.bound)}};
        else if constexpr (std::is_same_v<Body, SpecialSoundnessPreservation>)
          return Object{{"kind", "special_soundness_preservation"},
                        {"source_port", value.sourcePort},
                        {"appended_coordinates",
                         encodeCoordinateSequence(value.appendedCoordinates)},
                        {"conclusion_failure_bound",
                         encodeBound(value.conclusionFailureBound)}};
        else if constexpr (std::is_same_v<Body, RoundByRoundPreservation>)
          return Object{
              {"kind", "round_by_round_preservation"},
              {"source_port", value.sourcePort},
              {"appended_rounds", encodeRoundSequence(value.appendedRounds)}};
        else if constexpr (std::is_same_v<Body, RoundScaling>)
          return Object{{"kind", "round_scaling"},
                        {"round_by_round_port", value.roundByRoundPort},
                        {"selected_round",
                         encodeRoundSelectorTemplate(value.selectedRound)},
                        {"scale", encodeQuantity(value.scale)}};
        else if constexpr (std::is_same_v<Body, SpecialSoundnessToRoundByRound>)
          return Object{
              {"kind", "special_soundness_to_round_by_round"},
              {"special_soundness_port", value.specialSoundnessPort},
              {"per_coordinate_bound", encodeBound(value.perCoordinateBound)}};
        else if constexpr (std::is_same_v<Body, RoundByRoundToStateRestoration>)
          return Object{{"kind", "round_by_round_to_state_restoration"},
                        {"round_by_round_port", value.roundByRoundPort},
                        {"move_budget", encodeQuantity(value.moveBudget)}};
        else
          return Object{
              {"kind", "state_restoration_to_fiat_shamir_duplex"},
              {"state_restoration_port", value.stateRestorationPort},
              {"local_duplex_bound", encodeBound(value.localDuplexBound)}};
      },
      body);
}

Value encodePremises(const std::vector<PremisePort> &premises) {
  Array items;
  for (const PremisePort &port : premises) {
    Array constraints;
    for (PremiseResultConstraint constraint : port.resultConstraints)
      constraints.push_back(
          constraint == PremiseResultConstraint::RequiresEmptyGameSupport
              ? "requires_empty_game_support"
              : "requires_no_bound_resource_support");
    items.push_back(Object{
        {"name", port.name},
        {"expected_subject_schema", port.expectedSubjectSchema},
        {"expected_index", encodeSecurityIndex(port.expectedIndex)},
        {"expected_result", resultSchemaName(port.expectedResult)},
        {"expected_resources", encodeTypedDeclarations(port.expectedResources)},
        {"result_constraints", std::move(constraints)},
        {"resource_substitution",
         encodeQuantityMap(port.resourceSubstitution)}});
  }
  return items;
}

Value encodeSubjectRelation(const SubjectRelation &relation) {
  Object document{{"kind", subjectRelationKindName(relation.kind)}};
  switch (relation.kind) {
  case SubjectRelationKind::SameSubject:
    break;
  case SubjectRelationKind::ConsumedClaim:
  case SubjectRelationKind::ConsumedClaimVector: {
    document["selector"] = consumedClaimSelectorName(relation.selector);
    Array indices;
    for (uint64_t index : relation.inputIndices)
      indices.push_back(int64_t(index));
    document["input_indices"] = std::move(indices);
    break;
  }
  case SubjectRelationKind::ExactExternalSubject:
    document["external_subject_schema"] = relation.externalSubjectSchema;
    document["external_arguments"] =
        encodeBindingValues(relation.externalArguments);
    break;
  }
  return document;
}

Value encodeBindingValueMap(
    const std::map<std::string, BindingValue, std::less<>> &values) {
  Object document;
  for (const auto &[name, value] : values)
    document[name] = encodeBindingValue(value);
  return document;
}

Value encodeBindingValueListMap(
    const std::map<std::string, std::vector<BindingValue>, std::less<>>
        &values) {
  Object document;
  for (const auto &[name, list] : values)
    document[name] = encodeBindingValues(list);
  return document;
}

} // namespace

Value encodeRuleDocument(const SoundnessRule &rule) {
  Array conditions;
  for (const MachineConditionTemplate &condition : rule.machineConditions)
    conditions.push_back(
        Object{{"slot", condition.slot},
               {"predicate_ref", condition.predicateRef},
               {"argument_types", encodeValueSorts(condition.argumentTypes)}});

  Array hypotheses;
  for (const ExternalHypothesisTemplate &hypothesis : rule.externalHypotheses)
    hypotheses.push_back(
        Object{{"slot", hypothesis.slot},
               {"proposition_ref", hypothesis.propositionRef},
               {"argument_types", encodeValueSorts(hypothesis.argumentTypes)}});

  Array pins;
  for (const ExactParameterPin &pin : rule.exactParameterPins)
    pins.push_back(Object{{"parameter", pin.parameter},
                          {"expected", encodeBindingValue(pin.expected)}});

  return Object{{"id", rule.ref.id},
                {"status", ruleStatusName(rule.status)},
                {"parameters", encodeTypedDeclarations(rule.parameters)},
                {"resources", encodeTypedDeclarations(rule.resources)},
                {"premises", encodePremises(rule.premises)},
                {"artifact_facts", encodeTypedDeclarations(rule.artifactFacts)},
                {"machine_conditions", std::move(conditions)},
                {"external_hypotheses", std::move(hypotheses)},
                {"exact_parameter_pins", std::move(pins)},
                {"conclusion_index", encodeSecurityIndex(rule.conclusionIndex)},
                {"body", encodeBody(rule.body)}};
}

Value encodeBindingDocument(const RuleBinding &binding) {
  Object relations;
  for (const auto &[name, relation] : binding.premiseRelations)
    relations[name] = encodeSubjectRelation(relation);

  return Object{
      {"id", binding.ref.id},
      {"rule_ref", encodeExactRef(binding.ruleRef)},
      {"subject_schema", binding.subjectSchema},
      {"anchor",
       Object{{"kind", binding.anchor.kind == ProtocolAnchorKind::PathTransition
                           ? "path_transition"
                           : "reduction_contract"},
              {"ref", encodeExactRef(binding.anchor.ref)}}},
      {"premise_relations", std::move(relations)},
      {"parameter_bindings", encodeBindingValueMap(binding.parameterBindings)},
      {"fact_bindings", encodeBindingValueMap(binding.factBindings)},
      {"condition_argument_bindings",
       encodeBindingValueListMap(binding.conditionArgumentBindings)},
      {"hypothesis_argument_bindings",
       encodeBindingValueListMap(binding.hypothesisArgumentBindings)}};
}

Value encodeSchemaContextDocument(const SchemaContext &schemas) {
  Array indices;
  for (const SecurityIndex &index : schemas.securityIndices)
    indices.push_back(encodeSecurityIndex(index));

  Object subjects;
  for (const auto &[id, schema] : schemas.subjectSchemas)
    subjects[id] =
        Object{{"ref", schema.ref},
               {"kind", subjectSchemaKindName(schema.kind)},
               {"argument_types", encodeValueSorts(schema.argumentTypes)}};

  Object games;
  for (const auto &[id, game] : schemas.primitiveGames)
    games[id] = Object{{"ref", encodeExactRef(game.ref)},
                       {"instance_argument_types",
                        encodeValueSorts(game.instanceArgumentTypes)},
                       {"resources", encodeTypedDeclarations(game.resources)}};

  Object deciders;
  for (const auto &[id, decider] : schemas.machineDeciders)
    deciders[id] =
        Object{{"ref", encodeExactRef(decider.ref)},
               {"kind", machineDeciderKindName(decider.kind)},
               {"argument_types", encodeValueSorts(decider.argumentTypes)}};

  Object propositions;
  for (const auto &[id, proposition] : schemas.propositions)
    propositions[id] =
        Object{{"ref", encodeExactRef(proposition.ref)},
               {"argument_types", encodeValueSorts(proposition.argumentTypes)}};

  return Object{{"security_indices", std::move(indices)},
                {"subject_schemas", std::move(subjects)},
                {"primitive_games", std::move(games)},
                {"machine_deciders", std::move(deciders)},
                {"propositions", std::move(propositions)}};
}

llvm::Expected<std::string> ruleDigest(const SoundnessRule &rule) {
  return encoding::taggedSha256Ref(kRuleDomain, encodeRuleDocument(rule));
}

llvm::Expected<std::string> bindingDigest(const RuleBinding &binding) {
  return encoding::taggedSha256Ref(kBindingDomain,
                                   encodeBindingDocument(binding));
}

Value encodeSignatureDocument(const SoundnessCatalog &catalog) {
  Object rules;
  for (const auto &[id, rule] : catalog.rules)
    rules[id] = encodeRuleDocument(rule);
  Object bindings;
  for (const auto &[id, binding] : catalog.bindings)
    bindings[id] = encodeBindingDocument(binding);
  return Object{{"schemas", encodeSchemaContextDocument(catalog.schemas)},
                {"rules", std::move(rules)},
                {"bindings", std::move(bindings)}};
}

llvm::Expected<std::string> signatureDigest(const SoundnessCatalog &catalog) {
  return encoding::taggedSha256Ref(kSignatureDomain,
                                   encodeSignatureDocument(catalog));
}

} // namespace zkc::soundness
