//===- DerivationEncoding.cpp - Asking for a derivation as data ---------===//
#include "zkc/Soundness/DerivationEncoding.h"

#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Registry/RegistryFile.h"

#include <memory>
#include <utility>

using llvm::ArrayRef;
using llvm::Error;
using llvm::Expected;
using llvm::StringRef;
using llvm::Twine;
using llvm::json::Array;
using llvm::json::Object;
using llvm::json::Value;

namespace zkc::soundness {

namespace {

constexpr llvm::StringLiteral kRequestRegistry = "zkc.derivation_request";
constexpr llvm::StringLiteral kWitnessRegistry = "zkc.derivation_witness";
constexpr llvm::StringRef kJudgmentDomain = "zkc/derivation-judgment\n";

//===--------------------------------------------------------------------===//
// Encoding
//===--------------------------------------------------------------------===//

Value encodeRef(const ExactRef &ref) {
  return Object{{"id", ref.id}, {"source_revision", ref.sourceRevision}};
}

Value encodeClaim(const ClaimRef &claim) {
  return Object{{"claim_index", int64_t(claim.claimIndex)},
                {"descriptor_digest", claim.descriptorDigest}};
}

Value encodeClaims(const std::vector<ClaimRef> &claims) {
  Array items;
  for (const ClaimRef &claim : claims)
    items.push_back(encodeClaim(claim));
  return items;
}

Value encodeSite(const ApplicationSite &site) {
  if (const auto *reduction = std::get_if<ReductionOccurrence>(&site))
    return Object{
        {"kind", "reduction"},
        {"artifact_id", reduction->artifactId},
        {"owner_claim", encodeClaim(reduction->ownerClaim)},
        {"transformer_position", int64_t(reduction->transformerPosition)},
        {"output_index", int64_t(reduction->outputIndex)}};
  const auto &path = std::get<PathOccurrence>(site);
  return Object{{"kind", "path"},
                {"artifact_id", path.artifactId},
                {"claim", encodeClaim(path.claim)}};
}

Value encodeIndex(const SecurityIndex &index) {
  const char *notion = "unknown";
  switch (index.notion) {
  case SecurityNotion::SpecialSoundness:
    notion = "special_soundness";
    break;
  case SecurityNotion::ComputationalSpecialSoundness:
    notion = "computational_special_soundness";
    break;
  case SecurityNotion::RoundByRound:
    notion = "round_by_round";
    break;
  case SecurityNotion::StateRestoration:
    notion = "state_restoration";
    break;
  case SecurityNotion::FiatShamir:
    notion = "fiat_shamir";
    break;
  case SecurityNotion::Completeness:
    notion = "completeness";
    break;
  }
  const char *track = "soundness";
  if (index.track == SecurityTrack::Knowledge)
    track = "knowledge";
  else if (index.track == SecurityTrack::Completeness)
    track = "completeness";
  return Object{{"notion", notion},
                {"track", track},
                {"variant", index.variant},
                {"model", index.model}};
}

const char *sortName(ValueSort sort) {
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

Value encodeDeclarations(const std::vector<TypedDeclaration> &values) {
  Array items;
  for (const TypedDeclaration &value : values)
    items.push_back(
        Object{{"name", value.name}, {"sort", sortName(value.sort)}});
  return items;
}

Value encodeSubject(const SecuritySubject &subject);

Value encodeValue(const RuntimeValue &value) {
  Object document{{"sort", sortName(value.sort)}};
  if (const auto *number = std::get_if<registry::Rational>(&value.payload))
    document["value"] = number->str();
  else if (const auto *text = std::get_if<std::string>(&value.payload))
    document["value"] = *text;
  else if (const auto *flag = std::get_if<bool>(&value.payload))
    document["value"] = *flag;
  else if (const auto *nested =
               std::get_if<RuntimeValue::SubjectPtr>(&value.payload))
    document["value"] = *nested ? encodeSubject(**nested) : Value(nullptr);
  else if (const auto *algebra =
               std::get_if<AlgebraInstanceValue>(&value.payload))
    document["value"] = Object{{"group", algebra->group},
                               {"field_class", algebra->fieldClass},
                               {"field_order", algebra->fieldOrder.str()}};
  else if (const auto *srs = std::get_if<SrsInstanceValue>(&value.payload))
    document["value"] = encodeRef(srs->ref);
  else if (const auto *fri =
               std::get_if<FriDomainInstanceValue>(&value.payload))
    document["value"] = encodeRef(fri->ref);
  // The artifact supplies these; the exact reference determines the content
  // given the artifact the witness names, so restating the protocol inside a
  // judgment digest would add bytes and no information.
  else if (const auto *contract =
               std::get_if<ReductionContractValue>(&value.payload))
    document["value"] = encodeRef(contract->ref);
  else if (const auto *path = std::get_if<PathTransitionValue>(&value.payload))
    document["value"] = Object{{"ref", encodeRef(path->ref)},
                               {"artifact_id", path->artifactId},
                               {"claim", encodeClaim(path->claim)}};
  else if (const auto *adjacency =
               std::get_if<RoundAdjacencyValue>(&value.payload))
    document["value"] = Object{
        {"contract", encodeRef(adjacency->contractRef)},
        {"grinding_transformer_position",
         int64_t(adjacency->grindingTransformerPosition)},
        {"premise_claim", encodeClaim(adjacency->premiseClaim)},
        {"premise_transformer_position",
         int64_t(adjacency->premiseTransformerPosition)},
        {"pow_challenge_event_position",
         int64_t(adjacency->powChallengeEventPosition)},
        {"pin_check_event_position", int64_t(adjacency->pinCheckEventPosition)},
        {"successor_challenge_event_position",
         int64_t(adjacency->successorChallengeEventPosition)},
        {"premise_round_position", int64_t(adjacency->premiseRoundPosition)}};
  return document;
}

Value encodeValues(const std::vector<RuntimeValue> &values) {
  Array items;
  for (const RuntimeValue &value : values)
    items.push_back(encodeValue(value));
  return items;
}

Value encodeSubject(const SecuritySubject &subject) {
  if (const auto *claim = std::get_if<ProtocolClaimSubject>(&subject.payload))
    return Object{{"kind", "protocol_claim"},
                  {"artifact_id", claim->artifactId},
                  {"claim", encodeClaim(claim->claim)}};
  if (const auto *vector =
          std::get_if<ConsumedClaimVectorSubject>(&subject.payload))
    return Object{{"kind", "consumed_claim_vector"},
                  {"artifact_id", vector->artifactId},
                  {"consumer", encodeClaim(vector->consumer)},
                  {"ordered_sources", encodeClaims(vector->orderedSources)}};
  const auto &external = std::get<ExternalInstanceSubject>(subject.payload);
  return Object{{"kind", "external_instance"},
                {"schema_ref", external.schemaRef},
                {"arguments", encodeValues(external.arguments)}};
}

Value encodeQuantity(const ClosedQuantity &quantity) {
  Array terms;
  for (const ResourceMonomial &term : quantity.resourceTerms)
    terms.push_back(Object{{"coefficient", term.coefficient.str()},
                           {"resource", term.resource},
                           {"exponent", int64_t(term.exponent)}});
  return Object{{"constant", quantity.constant.str()},
                {"resource_terms", std::move(terms)}};
}

Value encodeBound(const ClosedBound &bound) {
  Array games;
  for (const PrimitiveGameTerm &term : bound.primitiveGameTerms) {
    Object substitution;
    for (const auto &[name, quantity] : term.resourceSubstitution)
      substitution[name] = encodeQuantity(quantity);
    games.push_back(Object{{"coefficient", term.coefficient.str()},
                           {"game", encodeRef(term.instance.ref)},
                           {"arguments", encodeValues(term.instance.arguments)},
                           {"resource_substitution", std::move(substitution)}});
  }
  return Object{{"quantity", encodeQuantity(bound.quantity)},
                {"primitive_game_terms", std::move(games)}};
}

Value encodeResult(const SecurityResult &result) {
  if (const auto *extraction = std::get_if<ExtractionResult>(&result)) {
    Array coordinates;
    for (const ExtractionCoordinate &coordinate : extraction->coordinates) {
      Object entry{{"label", coordinate.label},
                   {"arity", encodeQuantity(coordinate.arity)}};
      entry["challenge_space"] =
          coordinate.challengeSpace ? encodeQuantity(*coordinate.challengeSpace)
                                    : Value(nullptr);
      coordinates.push_back(std::move(entry));
    }
    Object document{{"kind", "extraction"},
                    {"coordinates", std::move(coordinates)}};
    document["failure_bound"] = extraction->failureBound
                                    ? encodeBound(*extraction->failureBound)
                                    : Value(nullptr);
    return document;
  }
  if (const auto *rounds = std::get_if<RoundResult>(&result)) {
    Array entries;
    for (const RoundResultEntry &round : rounds->rounds)
      entries.push_back(
          Object{{"round_index", round.roundIndex},
                 {"challenge_space", encodeQuantity(round.challengeSpace)},
                 {"bound", encodeBound(round.bound)}});
    return Object{{"kind", "round"}, {"rounds", std::move(entries)}};
  }
  const auto &scalar = std::get<ScalarResult>(result);
  return Object{{"kind", "scalar"}, {"bound", encodeBound(scalar.bound)}};
}

Value encodeJudgment(const SecurityJudgment &judgment) {
  Array hypotheses;
  for (const Hypothesis &hypothesis : judgment.hypotheses) {
    if (const auto *proposition =
            std::get_if<PropositionInstance>(&hypothesis)) {
      hypotheses.push_back(
          Object{{"kind", "proposition"},
                 {"ref", encodeRef(proposition->ref)},
                 {"arguments", encodeValues(proposition->arguments)}});
      continue;
    }
    const auto &assumed = std::get<AssumedJudgmentHolds>(hypothesis);
    hypotheses.push_back(
        Object{{"kind", "assumed_judgment"},
               {"judgment", assumed.assertedJudgment
                                ? encodeJudgment(*assumed.assertedJudgment)
                                : Value(nullptr)}});
  }
  return Object{
      {"subject", encodeSubject(judgment.subject)},
      {"index", encodeIndex(judgment.index)},
      {"result", encodeResult(judgment.result)},
      {"resource_variables", encodeDeclarations(judgment.resourceVariables)},
      {"hypotheses", std::move(hypotheses)}};
}

Value encodePlan(const DerivationPlan &plan) {
  if (const auto *assumption =
          std::get_if<ExternalJudgmentAssumption>(&plan.node))
    return Object{{"kind", "assume"},
                  {"judgment", encodeJudgment(assumption->assertedJudgment)}};
  const auto &apply = std::get<ApplyDerivationPlan>(plan.node);
  Object premises;
  for (const auto &[port, child] : apply.premises)
    premises[port] = child ? encodePlan(*child) : Value(nullptr);
  return Object{{"kind", "apply"},
                {"site", encodeSite(apply.site)},
                {"binding", apply.bindingRef.id},
                {"premises", std::move(premises)}};
}

Value encodeRequestBody(const DerivationRequest &request) {
  // Bindings are named by identifier, not by revision. The revision is a
  // computed digest, so writing it into a request would go stale; naming the
  // identifier also makes one request runnable against a second signature,
  // which is what comparing two analyses of one artifact requires.
  Array bindings;
  for (const ExactRef &ref : request.selectedBindingRefs)
    bindings.push_back(ref.id);

  Object resolved;
  for (const auto &[id, environment] : request.resolvedParameters) {
    Object values;
    for (const auto &[name, value] : environment.values)
      values[name] = encodeValue(value);
    resolved[id] = std::move(values);
  }

  return Object{
      {"selected_bindings", std::move(bindings)},
      {"resolved_parameters", std::move(resolved)},
      {"target",
       Object{{"subject", encodeSubject(request.target.subject)},
              {"index", encodeIndex(request.target.index)},
              {"resource_variables",
               encodeDeclarations(request.target.resourceVariables)}}},
      {"plan", encodePlan(request.plan)}};
}

//===--------------------------------------------------------------------===//
// Decoding
//===--------------------------------------------------------------------===//

class Reader {
public:
  Reader(registry::RegistryFile file, const SoundnessCatalog &catalog)
      : file(std::move(file)), catalog(catalog) {}

  /// Resolve a binding identifier to the exact revision this signature
  /// declares for it. A request that names one the signature does not have is
  /// a request about a different analysis, and saying so is better than
  /// deriving something else.
  Expected<ExactRef> binding(StringRef id, const Twine &context) const {
    auto found = catalog.bindings.find(id);
    if (found == catalog.bindings.end())
      return file.error(context + " names binding '" + id +
                        "', which this signature does not declare");
    return found->second.ref;
  }

  const registry::RegistryFile &registryFile() const { return file; }

  template <typename T> Expected<T> failed(const Twine &message) const {
    return file.error(message);
  }
  Error fail(const Twine &message) const { return file.error(message); }

  Error closed(const Object &object, llvm::ArrayRef<StringRef> allowed,
               const Twine &context) const {
    return file.requireClosedFields(object, allowed, context);
  }
  Expected<StringRef> string(const Object &object, StringRef key,
                             const Twine &context) const {
    return file.requireString(object, key, context);
  }
  std::string optionalString(const Object &object, StringRef key) const {
    std::optional<StringRef> value = object.getString(key);
    return value ? value->str() : std::string();
  }
  Expected<const Object *> object(const Object &parent, StringRef key,
                                  const Twine &context) const {
    const Object *value = parent.getObject(key);
    if (!value)
      return file.error(context + " needs an object '" + key + "'");
    return value;
  }
  Expected<const Array *> array(const Object &parent, StringRef key,
                                const Twine &context) const {
    const Array *value = parent.getArray(key);
    if (!value)
      return file.error(context + " needs an array '" + key + "'");
    return value;
  }
  Expected<uint64_t> count(const Object &parent, StringRef key,
                           const Twine &context) const {
    std::optional<int64_t> value = parent.getInteger(key);
    if (!value || *value < 0)
      return file.error(context + " needs a non-negative integer '" + key +
                        "'");
    return uint64_t(*value);
  }

private:
  registry::RegistryFile file;
  const SoundnessCatalog &catalog;
};

Expected<ExactRef> readRef(const Reader &reader, const Object &parent,
                           StringRef key, const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  if (Error err = reader.closed(**entry, {"id", "source_revision"}, where))
    return std::move(err);
  auto id = reader.string(**entry, "id", where);
  if (!id)
    return id.takeError();
  auto revision = reader.string(**entry, "source_revision", where);
  if (!revision)
    return revision.takeError();
  return ExactRef{id->str(), revision->str()};
}

Expected<ClaimRef> readClaim(const Reader &reader, const Object &parent,
                             StringRef key, const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  if (Error err =
          reader.closed(**entry, {"claim_index", "descriptor_digest"}, where))
    return std::move(err);
  auto index = reader.count(**entry, "claim_index", where);
  if (!index)
    return index.takeError();
  auto digest = reader.string(**entry, "descriptor_digest", where);
  if (!digest)
    return digest.takeError();
  return ClaimRef{*index, digest->str()};
}

Expected<ValueSort> readSort(const Reader &reader, StringRef text,
                             const Twine &context) {
  static const std::pair<StringRef, ValueSort> table[] = {
      {"integer", ValueSort::Integer},
      {"rational", ValueSort::Rational},
      {"string", ValueSort::String},
      {"boolean", ValueSort::Boolean},
      {"subject", ValueSort::Subject},
      {"reduction_contract", ValueSort::ReductionContract},
      {"path_transition", ValueSort::PathTransition},
      {"round_adjacency", ValueSort::RoundAdjacency},
      {"algebra_instance", ValueSort::AlgebraInstance},
      {"srs_instance", ValueSort::SrsInstance},
      {"fri_domain_instance", ValueSort::FriDomainInstance},
  };
  for (const auto &entry : table)
    if (entry.first == text)
      return entry.second;
  return reader.failed<ValueSort>(context + " has unknown sort '" + text + "'");
}

Expected<registry::Rational> readRational(const Reader &reader, StringRef text,
                                          const Twine &context) {
  auto slash = text.find('/');
  Expected<registry::Rational> value =
      slash == StringRef::npos
          ? registry::Rational::fromDecimal(text)
          : registry::Rational::fromDecimalPair(text.substr(0, slash),
                                                text.substr(slash + 1));
  if (!value) {
    llvm::consumeError(value.takeError());
    return reader.failed<registry::Rational>(
        context + " is not an exact decimal rational: '" + text + "'");
  }
  return value;
}

Expected<SecurityIndex> readIndex(const Reader &reader, const Object &parent,
                                  StringRef key, const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  if (Error err = reader.closed(**entry,
                                {"notion", "track", "variant", "model"}, where))
    return std::move(err);
  static const std::pair<StringRef, SecurityNotion> notions[] = {
      {"special_soundness", SecurityNotion::SpecialSoundness},
      {"computational_special_soundness",
       SecurityNotion::ComputationalSpecialSoundness},
      {"round_by_round", SecurityNotion::RoundByRound},
      {"state_restoration", SecurityNotion::StateRestoration},
      {"fiat_shamir", SecurityNotion::FiatShamir},
      {"completeness", SecurityNotion::Completeness},
  };
  auto notionText = reader.string(**entry, "notion", where);
  if (!notionText)
    return notionText.takeError();
  SecurityIndex index;
  bool found = false;
  for (const auto &candidate : notions)
    if (candidate.first == *notionText) {
      index.notion = candidate.second;
      found = true;
    }
  if (!found)
    return reader.failed<SecurityIndex>(where + " has unknown notion '" +
                                        *notionText + "'");
  auto trackText = reader.string(**entry, "track", where);
  if (!trackText)
    return trackText.takeError();
  if (*trackText == "knowledge")
    index.track = SecurityTrack::Knowledge;
  else if (*trackText == "soundness")
    index.track = SecurityTrack::Soundness;
  else if (*trackText == "completeness")
    index.track = SecurityTrack::Completeness;
  else
    return reader.failed<SecurityIndex>(where + " has unknown track '" +
                                        *trackText + "'");
  index.variant = reader.optionalString(**entry, "variant");
  index.model = reader.optionalString(**entry, "model");
  return index;
}

/// A caller may supply only values the artifact does not.  A reduction
/// contract, a path transition, a round adjacency and a subject are read off
/// the sealed protocol; accepting one here would let a request assert a
/// protocol fact instead of reading it.
Expected<RuntimeValue> readSuppliedValue(const Reader &reader,
                                         const Object &entry,
                                         const Twine &context) {
  if (Error err = reader.closed(entry, {"sort", "value"}, context))
    return std::move(err);
  auto sortText = reader.string(entry, "sort", context);
  if (!sortText)
    return sortText.takeError();
  auto sort = readSort(reader, *sortText, context);
  if (!sort)
    return sort.takeError();
  const Value *payload = entry.get("value");
  if (!payload)
    return reader.failed<RuntimeValue>(context + " needs a 'value'");

  switch (*sort) {
  case ValueSort::Integer:
  case ValueSort::Rational: {
    std::optional<StringRef> text = payload->getAsString();
    if (!text)
      return reader.failed<RuntimeValue>(context +
                                         " needs a decimal string value");
    auto number = readRational(reader, *text, context);
    if (!number)
      return number.takeError();
    return *sort == ValueSort::Integer ? RuntimeValue::integer(*number)
                                       : RuntimeValue::rational(*number);
  }
  case ValueSort::String: {
    std::optional<StringRef> text = payload->getAsString();
    if (!text)
      return reader.failed<RuntimeValue>(context + " needs a string value");
    return RuntimeValue::text(text->str());
  }
  case ValueSort::Boolean: {
    std::optional<bool> flag = payload->getAsBoolean();
    if (!flag)
      return reader.failed<RuntimeValue>(context + " needs a boolean value");
    return RuntimeValue::boolean(*flag);
  }
  case ValueSort::AlgebraInstance: {
    const Object *algebra = payload->getAsObject();
    if (!algebra)
      return reader.failed<RuntimeValue>(context +
                                         " needs an algebra-instance object");
    if (Error err = reader.closed(
            *algebra, {"group", "field_class", "field_order"}, context))
      return std::move(err);
    auto group = reader.string(*algebra, "group", context);
    if (!group)
      return group.takeError();
    auto fieldClass = reader.string(*algebra, "field_class", context);
    if (!fieldClass)
      return fieldClass.takeError();
    auto orderText = reader.string(*algebra, "field_order", context);
    if (!orderText)
      return orderText.takeError();
    auto order = readRational(reader, *orderText, context);
    if (!order)
      return order.takeError();
    return RuntimeValue::algebra(
        {group->str(), fieldClass->str(), std::move(*order)});
  }
  case ValueSort::SrsInstance:
  case ValueSort::FriDomainInstance: {
    const Object *wrapper = payload->getAsObject();
    if (!wrapper)
      return reader.failed<RuntimeValue>(context + " needs an exact reference");
    Object holder;
    holder["value"] = *payload;
    auto ref = readRef(reader, holder, "value", context);
    if (!ref)
      return ref.takeError();
    return *sort == ValueSort::SrsInstance
               ? RuntimeValue::srs(SrsInstanceValue{std::move(*ref)})
               : RuntimeValue::friDomain(
                     FriDomainInstanceValue{std::move(*ref)});
  }
  default:
    return reader.failed<RuntimeValue>(
        context + " has sort '" + *sortText +
        "', which the sealed protocol supplies and a request may not");
  }
}

Expected<SecuritySubject> readSubject(const Reader &reader,
                                      const Object &parent, StringRef key,
                                      const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();

  SecuritySubject subject;
  if (*kind == "protocol_claim") {
    if (Error err =
            reader.closed(**entry, {"kind", "artifact_id", "claim"}, where))
      return std::move(err);
    auto artifact = reader.string(**entry, "artifact_id", where);
    if (!artifact)
      return artifact.takeError();
    auto claim = readClaim(reader, **entry, "claim", where);
    if (!claim)
      return claim.takeError();
    subject.payload = ProtocolClaimSubject{artifact->str(), std::move(*claim)};
    return subject;
  }
  if (*kind == "consumed_claim_vector") {
    if (Error err = reader.closed(
            **entry, {"kind", "artifact_id", "consumer", "ordered_sources"},
            where))
      return std::move(err);
    auto artifact = reader.string(**entry, "artifact_id", where);
    if (!artifact)
      return artifact.takeError();
    auto consumer = readClaim(reader, **entry, "consumer", where);
    if (!consumer)
      return consumer.takeError();
    auto sources = reader.array(**entry, "ordered_sources", where);
    if (!sources)
      return sources.takeError();
    ConsumedClaimVectorSubject value{artifact->str(), std::move(*consumer), {}};
    for (size_t index = 0; index < (*sources)->size(); ++index) {
      Object holder;
      holder["source"] = (**sources)[index];
      auto claim = readClaim(reader, holder, "source", where);
      if (!claim)
        return claim.takeError();
      value.orderedSources.push_back(std::move(*claim));
    }
    subject.payload = std::move(value);
    return subject;
  }
  if (*kind == "external_instance") {
    if (Error err =
            reader.closed(**entry, {"kind", "schema_ref", "arguments"}, where))
      return std::move(err);
    auto schema = reader.string(**entry, "schema_ref", where);
    if (!schema)
      return schema.takeError();
    auto arguments = reader.array(**entry, "arguments", where);
    if (!arguments)
      return arguments.takeError();
    ExternalInstanceSubject value{schema->str(), {}};
    for (const Value &item : **arguments) {
      const Object *argument = item.getAsObject();
      if (!argument)
        return reader.failed<SecuritySubject>(where +
                                              " arguments must be objects");
      auto decoded = readSuppliedValue(reader, *argument, where + " argument");
      if (!decoded)
        return decoded.takeError();
      value.arguments.push_back(std::move(*decoded));
    }
    subject.payload = std::move(value);
    return subject;
  }
  return reader.failed<SecuritySubject>(where + " has unknown subject kind '" +
                                        *kind + "'");
}

Expected<ApplicationSite> readSite(const Reader &reader, const Object &parent,
                                   StringRef key, const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();
  auto artifact = reader.string(**entry, "artifact_id", where);
  if (!artifact)
    return artifact.takeError();

  if (*kind == "reduction") {
    if (Error err = reader.closed(**entry,
                                  {"kind", "artifact_id", "owner_claim",
                                   "transformer_position", "output_index"},
                                  where))
      return std::move(err);
    auto owner = readClaim(reader, **entry, "owner_claim", where);
    if (!owner)
      return owner.takeError();
    auto position = reader.count(**entry, "transformer_position", where);
    if (!position)
      return position.takeError();
    auto output = reader.count(**entry, "output_index", where);
    if (!output)
      return output.takeError();
    return ApplicationSite(ReductionOccurrence{
        artifact->str(), std::move(*owner), *position, *output});
  }
  if (*kind == "path") {
    if (Error err =
            reader.closed(**entry, {"kind", "artifact_id", "claim"}, where))
      return std::move(err);
    auto claim = readClaim(reader, **entry, "claim", where);
    if (!claim)
      return claim.takeError();
    return ApplicationSite(PathOccurrence{artifact->str(), std::move(*claim)});
  }
  return reader.failed<ApplicationSite>(where + " has unknown site kind '" +
                                        *kind + "'");
}

Expected<ClosedQuantity> readQuantity(const Reader &reader,
                                      const Object &parent, StringRef key,
                                      const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  if (Error err = reader.closed(**entry, {"constant", "resource_terms"}, where))
    return std::move(err);
  auto constantText = reader.string(**entry, "constant", where);
  if (!constantText)
    return constantText.takeError();
  auto constant = readRational(reader, *constantText, where);
  if (!constant)
    return constant.takeError();
  ClosedQuantity quantity;
  quantity.constant = std::move(*constant);
  auto terms = reader.array(**entry, "resource_terms", where);
  if (!terms)
    return terms.takeError();
  for (const Value &item : **terms) {
    const Object *term = item.getAsObject();
    if (!term)
      return reader.failed<ClosedQuantity>(where +
                                           " resource terms must be objects");
    if (Error err = reader.closed(
            *term, {"coefficient", "resource", "exponent"}, where))
      return std::move(err);
    auto coefficientText = reader.string(*term, "coefficient", where);
    if (!coefficientText)
      return coefficientText.takeError();
    auto coefficient = readRational(reader, *coefficientText, where);
    if (!coefficient)
      return coefficient.takeError();
    auto resource = reader.string(*term, "resource", where);
    if (!resource)
      return resource.takeError();
    auto exponent = reader.count(*term, "exponent", where);
    if (!exponent)
      return exponent.takeError();
    quantity.resourceTerms.push_back(
        ResourceMonomial{std::move(*coefficient), resource->str(), *exponent});
  }
  return quantity;
}

Expected<SecurityJudgment> readJudgment(const Reader &reader,
                                        const Object &parent, StringRef key,
                                        const Twine &context);

Expected<std::shared_ptr<const DerivationPlan>>
readPlanNode(const Reader &reader, const Object &entry, const Twine &context) {
  auto kind = reader.string(entry, "kind", context);
  if (!kind)
    return kind.takeError();

  auto plan = std::make_shared<DerivationPlan>();
  if (*kind == "assume") {
    if (Error err = reader.closed(entry, {"kind", "judgment"}, context))
      return std::move(err);
    auto judgment = readJudgment(reader, entry, "judgment", context);
    if (!judgment)
      return judgment.takeError();
    plan->node = ExternalJudgmentAssumption{std::move(*judgment)};
    return std::const_pointer_cast<const DerivationPlan>(plan);
  }
  if (*kind == "apply") {
    if (Error err = reader.closed(
            entry, {"kind", "site", "binding", "premises"}, context))
      return std::move(err);
    ApplyDerivationPlan apply;
    auto site = readSite(reader, entry, "site", context);
    if (!site)
      return site.takeError();
    apply.site = std::move(*site);
    auto bindingId = reader.string(entry, "binding", context);
    if (!bindingId)
      return bindingId.takeError();
    auto binding = reader.binding(*bindingId, context);
    if (!binding)
      return binding.takeError();
    apply.bindingRef = std::move(*binding);
    auto premises = reader.object(entry, "premises", context);
    if (!premises)
      return premises.takeError();
    for (const auto &field : **premises) {
      const Object *child = field.second.getAsObject();
      if (!child)
        return reader.failed<std::shared_ptr<const DerivationPlan>>(
            context + " premise '" + field.first.str() + "' must be an object");
      auto decoded = readPlanNode(
          reader, *child, Twine(context + " premise " + field.first.str()));
      if (!decoded)
        return decoded.takeError();
      apply.premises.emplace(field.first.str(), std::move(*decoded));
    }
    plan->node = std::move(apply);
    return std::const_pointer_cast<const DerivationPlan>(plan);
  }
  return reader.failed<std::shared_ptr<const DerivationPlan>>(
      context + " has unknown plan node kind '" + *kind + "'");
}

/// A request supplies an assumed judgment only in the shape an Assume leaf
/// needs: a subject, an index, and a result. Everything else about a judgment
/// is produced by the evaluator, so accepting it here would let a request
/// assert a conclusion.
Expected<SecurityJudgment> readJudgment(const Reader &reader,
                                        const Object &parent, StringRef key,
                                        const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  if (Error err = reader.closed(**entry, {"subject", "index", "result"}, where))
    return std::move(err);

  SecurityJudgment judgment;
  auto subject = readSubject(reader, **entry, "subject", where);
  if (!subject)
    return subject.takeError();
  judgment.subject = std::move(*subject);
  auto index = readIndex(reader, **entry, "index", where);
  if (!index)
    return index.takeError();
  judgment.index = std::move(*index);

  auto result = reader.object(**entry, "result", where);
  if (!result)
    return result.takeError();
  auto resultKind = reader.string(**result, "kind", where);
  if (!resultKind)
    return resultKind.takeError();

  if (*resultKind == "extraction") {
    if (Error err = reader.closed(**result, {"kind", "coordinates"}, where))
      return std::move(err);
    auto coordinates = reader.array(**result, "coordinates", where);
    if (!coordinates)
      return coordinates.takeError();
    ExtractionResult extraction;
    for (const Value &item : **coordinates) {
      const Object *coordinate = item.getAsObject();
      if (!coordinate)
        return reader.failed<SecurityJudgment>(where +
                                               " coordinates must be objects");
      if (Error err = reader.closed(
              *coordinate, {"label", "arity", "challenge_space"}, where))
        return std::move(err);
      auto label = reader.string(*coordinate, "label", where);
      if (!label)
        return label.takeError();
      auto arity = readQuantity(reader, *coordinate, "arity", where);
      if (!arity)
        return arity.takeError();
      ExtractionCoordinate value{label->str(), std::move(*arity), std::nullopt};
      if (coordinate->getObject("challenge_space")) {
        auto space =
            readQuantity(reader, *coordinate, "challenge_space", where);
        if (!space)
          return space.takeError();
        value.challengeSpace = std::move(*space);
      }
      extraction.coordinates.push_back(std::move(value));
    }
    judgment.result = std::move(extraction);
    return judgment;
  }
  return reader.failed<SecurityJudgment>(
      where + " supplies a '" + *resultKind +
      "' result; an assumed judgment carries an extraction result, and every "
      "other shape is produced by the evaluator");
}

Expected<DerivationRequest> readRequestBody(const Reader &reader,
                                            const Object &body) {
  DerivationRequest request;
  auto bindings = reader.array(body, "selected_bindings", "request");
  if (!bindings)
    return bindings.takeError();
  for (const Value &item : **bindings) {
    std::optional<StringRef> id = item.getAsString();
    if (!id)
      return reader.failed<DerivationRequest>(
          "request selected bindings must be identifiers");
    auto ref = reader.binding(*id, "request selected binding");
    if (!ref)
      return ref.takeError();
    request.selectedBindingRefs.push_back(std::move(*ref));
  }

  if (const Object *resolved = body.getObject("resolved_parameters")) {
    for (const auto &field : *resolved) {
      const Object *entry = field.second.getAsObject();
      if (!entry)
        return reader.failed<DerivationRequest>(
            "request resolved parameters must be objects");
      const std::string where =
          Twine("request resolved parameters '" + field.first.str() + "'")
              .str();
      ResolvedParameterEnvironment environment;
      auto ref = reader.binding(field.first, where);
      if (!ref)
        return ref.takeError();
      environment.bindingRef = std::move(*ref);
      const Object **values = &entry;
      for (const auto &value : **values) {
        const Object *supplied = value.second.getAsObject();
        if (!supplied)
          return reader.failed<DerivationRequest>(where +
                                                  " values must be objects");
        auto decoded = readSuppliedValue(reader, *supplied,
                                         where + " " + value.first.str());
        if (!decoded)
          return decoded.takeError();
        environment.values.emplace(value.first.str(), std::move(*decoded));
      }
      request.resolvedParameters.emplace(field.first.str(),
                                         std::move(environment));
    }
  }

  auto target = reader.object(body, "target", "request");
  if (!target)
    return target.takeError();
  if (Error err =
          reader.closed(**target, {"subject", "index", "resource_variables"},
                        "request target"))
    return std::move(err);
  auto subject = readSubject(reader, **target, "subject", "request target");
  if (!subject)
    return subject.takeError();
  request.target.subject = std::move(*subject);
  auto index = readIndex(reader, **target, "index", "request target");
  if (!index)
    return index.takeError();
  request.target.index = std::move(*index);
  auto resources =
      reader.array(**target, "resource_variables", "request target");
  if (!resources)
    return resources.takeError();
  for (const Value &item : **resources) {
    const Object *declaration = item.getAsObject();
    if (!declaration)
      return reader.failed<DerivationRequest>(
          "request target resource variables must be objects");
    if (Error err = reader.closed(*declaration, {"name", "sort"},
                                  "request target resource"))
      return std::move(err);
    auto name = reader.string(*declaration, "name", "request target resource");
    if (!name)
      return name.takeError();
    auto sortText =
        reader.string(*declaration, "sort", "request target resource");
    if (!sortText)
      return sortText.takeError();
    auto sort = readSort(reader, *sortText, "request target resource");
    if (!sort)
      return sort.takeError();
    request.target.resourceVariables.push_back(
        TypedDeclaration{name->str(), *sort});
  }

  auto plan = reader.object(body, "plan", "request");
  if (!plan)
    return plan.takeError();
  auto root = readPlanNode(reader, **plan, "request plan");
  if (!root)
    return root.takeError();
  request.plan = **root;
  return request;
}

} // namespace

Expected<DerivationRequest>
parseDerivationRequest(StringRef json, StringRef source,
                       const SoundnessCatalog &catalog) {
  auto parsed = registry::RegistryFile::parse(json, source, kRequestRegistry,
                                              "derivation");
  if (!parsed)
    return parsed.takeError();
  Reader reader(std::move(*parsed), catalog);
  const Object &body = reader.registryFile().payload();
  if (Error err = reader.closed(
          body, {"selected_bindings", "resolved_parameters", "target", "plan"},
          "request"))
    return std::move(err);
  return readRequestBody(reader, body);
}

Value encodeJudgmentDocument(const SecurityJudgment &judgment) {
  return encodeJudgment(judgment);
}

namespace {

/// Drop every bound, at every depth.  An assumed premise carries a whole
/// nested judgment, so this has to reach inside one rather than clearing a
/// key at the top.
void dropResults(Value &value) {
  if (Object *object = value.getAsObject()) {
    object->erase("result");
    for (auto &entry : *object)
      dropResults(entry.second);
    return;
  }
  if (Array *array = value.getAsArray())
    for (Value &element : *array)
      dropResults(element);
}

Value encodeSkeletonNode(const EvaluatedDerivation &node) {
  if (const auto *assumption = std::get_if<EvaluatedAssumption>(&node.node)) {
    Value conclusion = encodeJudgment(assumption->conclusion);
    dropResults(conclusion);
    return Object{{"conclusion", std::move(conclusion)}, {"kind", "assumed"}};
  }
  const auto &application = std::get<EvaluatedApplication>(node.node);
  Object premises;
  for (const auto &[port, premise] : application.premises)
    premises[port] = premise ? encodeSkeletonNode(*premise) : Value(nullptr);
  Value conclusion = encodeJudgment(application.conclusion);
  dropResults(conclusion);
  return Object{{"binding", encodeRef(application.bindingRef)},
                {"conclusion", std::move(conclusion)},
                {"kind", "applied"},
                {"premises", std::move(premises)},
                {"site", encodeSite(application.site)}};
}

} // namespace

Value encodeDerivationSkeleton(const DerivationResult &result) {
  return Object{
      {"artifact_id", result.artifactId},
      {"root", encodeSkeletonNode(result.root)},
      {"target", Object{{"index", encodeIndex(result.target.index)},
                        {"resource_variables",
                         encodeDeclarations(result.target.resourceVariables)},
                        {"subject", encodeSubject(result.target.subject)}}}};
}

Expected<std::string> judgmentDigest(const SecurityJudgment &judgment) {
  return encoding::taggedSha256Ref(kJudgmentDomain, encodeJudgment(judgment));
}

Expected<Value>
encodeWitness(StringRef artifactId, StringRef signatureDigest,
              const DerivationRequest &request, const DerivationResult &result,
              ArrayRef<PreservationObligation> preservation,
              ArrayRef<std::pair<std::string, bool>> subjectAnchorGrounding) {
  const SecurityJudgment *conclusion = nullptr;
  if (const auto *application =
          std::get_if<EvaluatedApplication>(&result.root.node))
    conclusion = &application->conclusion;
  else
    conclusion = &std::get<EvaluatedAssumption>(result.root.node).conclusion;

  auto digest = judgmentDigest(*conclusion);
  if (!digest)
    return digest.takeError();

  // What a reader has to act on: the bound, and the obligations the conclusion
  // inherited. Everything else is for the checker, which re-derives.
  Array obligations;
  for (const Hypothesis &hypothesis : conclusion->hypotheses) {
    if (const auto *proposition = std::get_if<PropositionInstance>(&hypothesis))
      obligations.push_back(proposition->ref.id);
    else
      obligations.push_back("assumed judgment");
  }

  Array preserved;
  for (const PreservationObligation &obligation : preservation)
    preserved.push_back(
        Object{{"property", obligation.property},
               {"family", encodeRef(obligation.familyRef)},
               {"application_index", int64_t(obligation.applicationIndex)}});

  // Whether each anchor of the target claim is tied through a material
  // binding to a transcript position, or stands as its authors' declaration.
  // Artifact-derived, so a checker recomputes and compares it.
  Object grounding;
  for (const auto &[anchor, grounded] : subjectAnchorGrounding)
    grounding[anchor] = grounded ? "grounded" : "declared";

  return Object{{"registry", kWitnessRegistry},
                {"derivation", encodeRequestBody(request)},
                // Beside the conclusion rather than inside it: what a transform
                // claimed to preserve is not what the derivation established.
                {"preservation_obligations", std::move(preserved)},
                {"subject_anchor_grounding", std::move(grounding)},
                // What the derivation was about, under which analysis, and what
                // it gave. A checker re-runs it and compares the last of the
                // three; it does not read the conclusion below and believe it.
                {"identity", Object{{"artifact_id", artifactId},
                                    {"signature_digest", signatureDigest},
                                    {"judgment_digest", *digest}}},
                {"conclusion",
                 Object{{"index", encodeIndex(conclusion->index)},
                        {"result", encodeResult(conclusion->result)},
                        {"resource_variables",
                         encodeDeclarations(conclusion->resourceVariables)},
                        {"qualitative_obligations", std::move(obligations)}}}};
}

Expected<WitnessClaim> parseWitness(StringRef json, StringRef source,
                                    const SoundnessCatalog &catalog) {
  auto parsed = registry::RegistryFile::parse(
      json, source, kWitnessRegistry, "derivation",
      {"identity", "conclusion", "preservation_obligations",
       "subject_anchor_grounding"});
  if (!parsed)
    return parsed.takeError();
  Reader reader(std::move(*parsed), catalog);

  const Object *identity = reader.registryFile().extra("identity");
  if (!identity)
    return reader.failed<WitnessClaim>("'identity' must be an object");
  if (Error err = reader.closed(
          *identity, {"artifact_id", "signature_digest", "judgment_digest"},
          "identity"))
    return std::move(err);

  WitnessClaim claim;
  auto artifact = reader.string(*identity, "artifact_id", "identity");
  if (!artifact)
    return artifact.takeError();
  claim.artifactId = artifact->str();
  auto signature = reader.string(*identity, "signature_digest", "identity");
  if (!signature)
    return signature.takeError();
  claim.signatureDigest = signature->str();
  auto judgment = reader.string(*identity, "judgment_digest", "identity");
  if (!judgment)
    return judgment.takeError();
  claim.judgmentDigest = judgment->str();

  if (reader.registryFile().hasExtra("preservation_obligations")) {
    const llvm::json::Array *preserved =
        reader.registryFile().extraArray("preservation_obligations");
    if (!preserved)
      return reader.failed<WitnessClaim>(
          "'preservation_obligations' must be a list");
    for (const Value &entry : *preserved) {
      const Object *item = entry.getAsObject();
      if (!item)
        return reader.failed<WitnessClaim>(
            "a preservation obligation must be an object");
      if (Error err =
              reader.closed(*item, {"property", "family", "application_index"},
                            "preservation obligation"))
        return std::move(err);
      PreservationObligation obligation;
      auto property =
          reader.string(*item, "property", "preservation obligation");
      if (!property)
        return property.takeError();
      obligation.property = property->str();
      const Object *family = item->getObject("family");
      if (!family)
        return reader.failed<WitnessClaim>(
            "a preservation obligation needs a 'family' object");
      if (Error err = reader.closed(*family, {"id", "source_revision"},
                                    "preservation obligation family"))
        return std::move(err);
      auto id = reader.string(*family, "id", "preservation obligation family");
      if (!id)
        return id.takeError();
      auto revision = reader.string(*family, "source_revision",
                                    "preservation obligation family");
      if (!revision)
        return revision.takeError();
      obligation.familyRef = ExactRef{id->str(), revision->str()};
      std::optional<int64_t> index = item->getInteger("application_index");
      if (!index || *index < 0)
        return reader.failed<WitnessClaim>(
            "a preservation obligation needs a non-negative application index");
      obligation.applicationIndex = uint64_t(*index);
      claim.preservation.push_back(std::move(obligation));
    }
  }

  if (reader.registryFile().hasExtra("subject_anchor_grounding")) {
    const Object *grounding =
        reader.registryFile().extraObject("subject_anchor_grounding");
    if (!grounding)
      return reader.failed<WitnessClaim>(
          "'subject_anchor_grounding' must be an object");
    for (const auto &entry : *grounding) {
      auto spelling = entry.getSecond().getAsString();
      if (!spelling || (*spelling != "grounded" && *spelling != "declared"))
        return reader.failed<WitnessClaim>(
            "an anchor grounding is either 'grounded' or 'declared'");
      claim.subjectAnchorGrounding.emplace_back(entry.getFirst().str(),
                                                spelling->str());
    }
    llvm::sort(claim.subjectAnchorGrounding);
  }

  const Object &body = reader.registryFile().payload();
  if (Error err = reader.closed(
          body, {"selected_bindings", "resolved_parameters", "target", "plan"},
          "witness derivation"))
    return std::move(err);
  auto request = readRequestBody(reader, body);
  if (!request)
    return request.takeError();
  claim.request = std::move(*request);
  return claim;
}

} // namespace zkc::soundness
