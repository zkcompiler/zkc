//===- ProtocolVocabulary.cpp - Cross-admitted protocol vocabulary -------===//

#include "zkc/Registry/ProtocolVocabulary.h"

#include "zkc/ChallengeShape.h"
#include "zkc/Encoding/CanonicalJson.h"
#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/RegistryBase.h"
#include "zkc/Registry/RegistryFile.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/MemoryBuffer.h"
#include <set>

using namespace llvm;
using namespace zkc::registry;

namespace {

template <typename T>
const T *lookup(const std::map<std::string, T, std::less<>> &entries,
                StringRef id) {
  auto it = entries.find(id);
  return it == entries.end() ? nullptr : &it->second;
}

Error requireUnique(const RegistryFile &file, ArrayRef<std::string> values,
                    const Twine &context) {
  StringSet<> seen;
  for (const std::string &value : values)
    if (!seen.insert(value).second)
      return file.error(context + " repeats '" + value + "'");
  return Error::success();
}

Expected<uint64_t> requireBoundedPositive(const RegistryFile &file,
                                          const json::Object &object,
                                          StringRef field,
                                          const Twine &context) {
  std::optional<int64_t> value = object.getInteger(field);
  if (!value || *value < 1 ||
      static_cast<uint64_t>(*value) > zkc::challenge::kMaxCount)
    return file.error(context + " needs a positive integer '" + field +
                      "' (at most 2^20)");
  return static_cast<uint64_t>(*value);
}

Expected<uint64_t> requireNonNegative(const RegistryFile &file,
                                      const json::Object &object,
                                      StringRef field, const Twine &context) {
  std::optional<int64_t> value = object.getInteger(field);
  if (!value || *value < 0)
    return file.error(context + " needs a non-negative integer '" + field +
                      "'");
  return static_cast<uint64_t>(*value);
}

Expected<std::string> canonicalBytes(const json::Value &value) {
  std::string bytes;
  raw_string_ostream os(bytes);
  if (Error error = zkc::encoding::writeCanonicalJson(value, os))
    return std::move(error);
  return bytes;
}

json::Object profileDigestObject(
    const ReductionContract &contract,
    const std::map<std::string, ClaimProfile, std::less<>> &profiles) {
  std::set<std::string, std::less<>> ids;
  for (const VocabularyConsumePattern &pattern : contract.consumes)
    ids.insert(pattern.profile);
  for (const ReductionOutputConstructor &output : contract.outputs)
    ids.insert(output.profile);
  json::Object result;
  for (const std::string &id : ids)
    result[id] = profiles.find(id)->second.digest;
  return result;
}

Expected<std::string> digestReductionContract(
    const ReductionContract &contract,
    const std::map<std::string, ClaimProfile, std::less<>> &profiles,
    const std::map<std::string, CheckContract, std::less<>> &checkContracts) {
  json::Object checkDigests;
  for (const auto &[role, slot] : contract.checks)
    checkDigests[role] = checkContracts.find(slot.contract)->second.digest;
  json::Object preimage{
      {"check_contract_digests", std::move(checkDigests)},
      {"content", contract.toCanonicalJson()},
      {"profile_digests", profileDigestObject(contract, profiles)}};
  return RegistryFile::digestEntry("zkc/reduction-contract\n",
                                   json::Value(std::move(preimage)));
}

Expected<std::string>
digestRule(const TerminalRule &rule,
           const std::map<std::string, ClaimProfile, std::less<>> &profiles,
           const std::map<std::string, CheckContract, std::less<>> &contracts,
           const std::map<std::string, ReductionContract, std::less<>>
               &reductionContracts) {
  json::Object checkDigests;
  for (const auto &[role, contract] : rule.checks)
    checkDigests[role] = contracts.find(contract)->second.digest;
  json::Object preimage{
      {"claim_profile_digest", profiles.find(rule.claimProfile)->second.digest},
      {"check_contract_digests", std::move(checkDigests)},
      {"content", rule.toCanonicalJson()}};
  if (rule.producer)
    preimage["producer_contract_digest"] =
        reductionContracts.find(rule.producer->contract)->second.digest;
  return RegistryFile::digestEntry("zkc/terminal-rule\n",
                                   json::Value(std::move(preimage)));
}

/// The admitted origins, in one place: the refusal names the same list the
/// predicate tests, so the two cannot disagree about what is admitted.
///
/// Naming the set is the point. A relation-derived commitment and a
/// preprocessed index are the same object with different provenance, so they
/// arrive as values of one field rather than as sibling mechanisms each
/// minting its own shape.
constexpr llvm::StringLiteral kValueOrigins[] = {
    "preprocessed", "prover_message", "relation_derived"};

bool admittedOrigin(StringRef origin) {
  return llvm::is_contained(kValueOrigins, origin);
}

Expected<ValueProfile> parseValueProfile(const RegistryFile &file, StringRef id,
                                         const json::Value &value) {
  auto error = [&](const Twine &message) {
    return file.error("value profile '" + id + "' " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return error("must map to an object");
  const std::string where = ("value profile '" + id + "'").str();
  if (Error e = file.requireClosedFields(
          *object, {"element_class", "origin", "arity_log2", "binding_route"},
          where))
    return std::move(e);

  ValueProfile profile;
  if (Error e = file.requireStringField(*object, "element_class", where,
                                        profile.elementClass))
    return std::move(e);
  if (Error e =
          file.requireStringField(*object, "origin", where, profile.origin))
    return std::move(e);
  if (!admittedOrigin(profile.origin))
    return error("names origin '" + profile.origin + "', which is not one of " +
                 llvm::join(llvm::ArrayRef(kValueOrigins), ", "));
  if (Error e = file.requireStringField(*object, "binding_route", where,
                                        profile.bindingRoute))
    return std::move(e);
  const json::Value *arity = object->get("arity_log2");
  std::optional<int64_t> arityValue = arity ? arity->getAsInteger() : std::nullopt;
  // Bounded on both sides: a negative arity is not a count, and the bound
  // keeps `2^arity` inside the exact integer domain every quantity here
  // travels in.
  if (!arityValue || *arityValue < 0 || *arityValue > 64)
    return error("needs an 'arity_log2' integer in 0..64");
  profile.arityLog2 = *arityValue;

  auto digest = RegistryFile::digestEntry("zkc/value-profile\n",
                                          profile.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  profile.digest = std::move(*digest);
  return profile;
}

Expected<ClaimProfile> parseProfile(const RegistryFile &file, StringRef id,
                                    const json::Value &value) {
  auto error = [&](const Twine &message) {
    return file.error("claim profile '" + id + "' " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return error("must map to an object");
  if (Error e = file.requireClosedFields(*object, {"kind", "anchors"},
                                         "claim profile '" + id + "'"))
    return std::move(e);

  ClaimProfile profile;
  if (Error e = file.requireStringField(
          *object, "kind", "claim profile '" + id + "'", profile.kind))
    return std::move(e);
  auto anchors =
      file.requireStringList(*object, "anchors", "claim profile '" + id + "'");
  if (!anchors)
    return anchors.takeError();
  if (Error e =
          requireUnique(file, *anchors, "claim profile '" + id + "' anchors"))
    return std::move(e);
  llvm::sort(*anchors);
  profile.anchors = std::move(*anchors);
  auto digest = RegistryFile::digestEntry("zkc/claim-profile\n",
                                          profile.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  profile.digest = std::move(*digest);
  return profile;
}

Expected<OperandMultiplicity> parseMultiplicity(const RegistryFile &file,
                                                const json::Value &value,
                                                const Twine &context,
                                                StringSet<> &captures) {
  const json::Object *object = value.getAsObject();
  if (!object)
    return file.error(context + " multiplicity must be an object");
  OperandMultiplicity result;
  if (object->size() == 1 && object->get("exact")) {
    auto count = requireBoundedPositive(file, *object, "exact", context);
    if (!count)
      return count.takeError();
    result.kind = OperandMultiplicityKind::Exact;
    result.value = *count;
    return result;
  }
  if (object->size() == 2 && object->get("capture") && object->get("min")) {
    auto capture = file.requireString(*object, "capture", context);
    if (!capture)
      return capture.takeError();
    auto minimum = requireBoundedPositive(file, *object, "min", context);
    if (!minimum)
      return minimum.takeError();
    // With no upper bounds, two independent captures make the same total
    // operand count admit multiple segmentations for sufficiently large
    // inputs. One captured cardinality may be reused by any number of
    // same_as segments and is uniquely solved from the total count.
    if (captures.contains(*capture))
      return file.error(context + " repeats count capture '" + *capture + "'");
    if (!captures.empty())
      return file.error(context +
                        " introduces a second independent count capture");
    captures.insert(*capture);
    result.kind = OperandMultiplicityKind::Capture;
    result.name = capture->str();
    result.value = *minimum;
    return result;
  }
  if (object->size() == 1 && object->get("same_as")) {
    auto capture = file.requireString(*object, "same_as", context);
    if (!capture)
      return capture.takeError();
    if (!captures.contains(*capture))
      return file.error(context + " references unbound count capture '" +
                        *capture + "'");
    result.kind = OperandMultiplicityKind::SameAs;
    result.name = capture->str();
    return result;
  }
  return file.error(context +
                    " multiplicity must be exact(n), capture(name,min), or "
                    "same_as(name)");
}

Expected<std::vector<CheckOperandSegment>>
parseCheckOperands(const RegistryFile &file, const json::Array &operands,
                   ArrayRef<std::string> parameters,
                   ArrayRef<std::string> semanticParameters,
                   const Twine &context) {
  StringSet<> allRoles;
  for (const std::string &name : parameters)
    allRoles.insert(name);
  for (const std::string &name : semanticParameters)
    if (!allRoles.insert(name).second)
      return file.error(context +
                        " parameter and semantic-parameter names must be "
                        "disjoint");

  std::vector<CheckOperandSegment> result;
  StringSet<> captures;
  for (const auto &[index, member] : llvm::enumerate(operands)) {
    const json::Object *operand = member.getAsObject();
    std::string operandContext = (context + " operand " + Twine(index)).str();
    if (!operand)
      return file.error(operandContext + " must be an object");
    if (Error e = file.requireClosedFields(
            *operand, {"role", "class", "multiplicity"}, operandContext))
      return std::move(e);
    CheckOperandSegment segment;
    if (Error e = file.requireStringField(*operand, "role", operandContext,
                                          segment.role))
      return std::move(e);
    if (Error e = file.requireStringField(*operand, "class", operandContext,
                                          segment.valueClass))
      return std::move(e);
    if (segment.valueClass == "chal")
      return file.error(operandContext +
                        " 'class' must be a semantic payload class, not the "
                        "retired producer pseudo-class 'chal'");
    if (!allRoles.insert(segment.role).second)
      return file.error(
          context + " parameter, semantic-parameter, and operand roles must be "
                    "disjoint and unique");
    const json::Value *multiplicity = operand->get("multiplicity");
    if (!multiplicity)
      return file.error(operandContext + " needs 'multiplicity'");
    auto parsed =
        parseMultiplicity(file, *multiplicity, operandContext, captures);
    if (!parsed)
      return parsed.takeError();
    segment.multiplicity = std::move(*parsed);
    result.push_back(std::move(segment));
  }
  return result;
}

Expected<CheckPredicateSpec> parsePredicateSpec(const RegistryFile &file,
                                                StringRef digestKey,
                                                const json::Value &value) {
  const std::string context = ("predicate spec '" + digestKey + "'").str();
  if (!zkc::encoding::isSha256Ref(digestKey))
    return file.error(context +
                      " key must be a canonical sha256 content digest");
  const json::Object *object = value.getAsObject();
  if (!object)
    return file.error(context + " must map to an object");
  if (Error e = file.requireClosedFields(
          *object, {"format", "title", "references", "entrypoints"}, context))
    return std::move(e);
  if (object->getString("format") !=
      std::optional<StringRef>("zkc-check-predicate-spec"))
    return file.error(context + " must use format zkc-check-predicate-spec");

  CheckPredicateSpec spec;
  if (Error e = file.requireStringField(*object, "title", context, spec.title))
    return std::move(e);
  if (object->get("references")) {
    auto references = file.requireStringList(*object, "references", context);
    if (!references)
      return references.takeError();
    if (references->empty())
      return file.error(context + " 'references' must be absent or non-empty");
    if (Error e = requireUnique(file, *references, context + " references"))
      return std::move(e);
    spec.references = std::move(*references);
  }

  const json::Object *entrypoints = object->getObject("entrypoints");
  if (!entrypoints || entrypoints->empty())
    return file.error(context + " needs a non-empty object 'entrypoints'");
  for (const auto &member : *entrypoints) {
    StringRef name(member.first);
    if (Error e = requireEntryName(file, "predicate entrypoint", name))
      return e;
    const std::string entryContext =
        (context + " entrypoint '" + name + "'").str();
    const json::Object *body = member.second.getAsObject();
    if (!body)
      return file.error(entryContext + " must be an object");
    if (Error e = file.requireClosedFields(
            *body,
            {"acceptance", "parameters", "semantic_parameters", "operands"},
            entryContext))
      return std::move(e);

    CheckPredicateEntrypoint entrypoint;
    auto acceptance = file.requireStringList(*body, "acceptance", entryContext);
    if (!acceptance)
      return acceptance.takeError();
    if (acceptance->empty())
      return file.error(entryContext +
                        " needs at least one normative acceptance clause");
    if (Error e =
            requireUnique(file, *acceptance, entryContext + " acceptance"))
      return std::move(e);
    entrypoint.acceptance = std::move(*acceptance);
    auto parameters = file.requireStringList(*body, "parameters", entryContext);
    if (!parameters)
      return parameters.takeError();
    auto semantic =
        file.requireStringList(*body, "semantic_parameters", entryContext);
    if (!semantic)
      return semantic.takeError();
    if (Error e =
            requireUnique(file, *parameters, entryContext + " parameters"))
      return std::move(e);
    if (Error e = requireUnique(file, *semantic,
                                entryContext + " semantic parameters"))
      return std::move(e);
    llvm::sort(*parameters);
    llvm::sort(*semantic);
    entrypoint.parameters = std::move(*parameters);
    entrypoint.semanticParameters = std::move(*semantic);
    const json::Array *operands = body->getArray("operands");
    if (!operands)
      return file.error(entryContext + " needs an array 'operands'");
    auto parsedOperands =
        parseCheckOperands(file, *operands, entrypoint.parameters,
                           entrypoint.semanticParameters, entryContext);
    if (!parsedOperands)
      return parsedOperands.takeError();
    entrypoint.operands = std::move(*parsedOperands);
    spec.entrypoints.try_emplace(name.str(), std::move(entrypoint));
  }

  auto digest = RegistryFile::digestEntry("zkc/check-predicate-spec\n",
                                          spec.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  if (*digest != digestKey)
    return file.error(context +
                      " key does not match its canonical content "
                      "digest (derived " +
                      *digest + ")");
  spec.digest = std::move(*digest);
  return spec;
}

bool sameMultiplicity(const OperandMultiplicity &left,
                      const OperandMultiplicity &right) {
  return left.kind == right.kind && left.value == right.value &&
         left.name == right.name;
}

bool sameOperand(const CheckOperandSegment &left,
                 const CheckOperandSegment &right) {
  return left.role == right.role && left.valueClass == right.valueClass &&
         sameMultiplicity(left.multiplicity, right.multiplicity);
}

Expected<CheckContract> parseContract(
    const RegistryFile &file, StringRef id, const json::Value &value,
    const std::map<std::string, CheckPredicateSpec, std::less<>> &specs) {
  auto error = [&](const Twine &message) {
    return file.error("check contract '" + id + "' " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return error("must map to an object");
  if (Error e = file.requireClosedFields(*object,
                                         {"mode", "predicate", "parameters",
                                          "semantic_parameters", "operands"},
                                         "check contract '" + id + "'"))
    return std::move(e);

  CheckContract contract;
  auto mode =
      file.requireString(*object, "mode", "check contract '" + id + "'");
  if (!mode)
    return mode.takeError();
  if (*mode == "opaque")
    contract.mode = CheckMode::Opaque;
  else if (*mode == "transparent")
    contract.mode = CheckMode::Transparent;
  else
    return error("mode must be \"opaque\" or \"transparent\"");

  const json::Object *predicate = object->getObject("predicate");
  if (!predicate)
    return error("needs an object 'predicate'");
  auto format = file.requireString(*predicate, "format",
                                   "check contract '" + id + "' predicate");
  if (!format)
    return format.takeError();
  if (*format == "zkc-transparent-expression") {
    if (Error e = file.requireClosedFields(
            *predicate, {"format"}, "check contract '" + id + "' predicate"))
      return std::move(e);
    if (contract.mode != CheckMode::Transparent)
      return error("opaque mode requires an opaque predicate-spec descriptor");
    contract.predicate.format = CheckPredicateFormat::TransparentExpressionV1;
  } else if (*format == "zkc-opaque-predicate-spec") {
    if (Error e = file.requireClosedFields(
            *predicate, {"format", "content_digest", "entrypoint"},
            "check contract '" + id + "' predicate"))
      return std::move(e);
    if (contract.mode != CheckMode::Opaque)
      return error(
          "transparent mode requires the transparent-expression descriptor");
    if (Error e =
            file.requireStringField(*predicate, "content_digest",
                                    "check contract '" + id + "' predicate",
                                    contract.predicate.contentDigest))
      return std::move(e);
    if (!zkc::encoding::isSha256Ref(contract.predicate.contentDigest))
      return error("predicate content_digest must be a canonical sha256 "
                   "reference");
    if (Error e = file.requireStringField(
            *predicate, "entrypoint", "check contract '" + id + "' predicate",
            contract.predicate.entrypoint))
      return std::move(e);
    if (contract.predicate.entrypoint.empty() ||
        !zkc::encoding::inEncodingDomain(contract.predicate.entrypoint))
      return error("predicate entrypoint must be non-empty printable ASCII");
    contract.predicate.format = CheckPredicateFormat::OpaquePredicateSpecV1;
  } else {
    return error("predicate format is not admitted");
  }

  auto parameters = file.requireStringList(*object, "parameters",
                                           "check contract '" + id + "'");
  if (!parameters)
    return parameters.takeError();
  auto semantic = file.requireStringList(*object, "semantic_parameters",
                                         "check contract '" + id + "'");
  if (!semantic)
    return semantic.takeError();
  if (Error e = requireUnique(file, *parameters,
                              "check contract '" + id + "' parameters"))
    return std::move(e);
  if (Error e = requireUnique(
          file, *semantic, "check contract '" + id + "' semantic parameters"))
    return std::move(e);
  llvm::sort(*parameters);
  llvm::sort(*semantic);
  contract.parameters = std::move(*parameters);
  contract.semanticParameters = std::move(*semantic);

  const json::Array *operands = object->getArray("operands");
  if (!operands)
    return error("needs an array 'operands'");
  auto parsedOperands = parseCheckOperands(file, *operands, contract.parameters,
                                           contract.semanticParameters,
                                           "check contract '" + id + "'");
  if (!parsedOperands)
    return parsedOperands.takeError();
  contract.operands = std::move(*parsedOperands);

  if (contract.mode == CheckMode::Opaque) {
    auto spec = specs.find(contract.predicate.contentDigest);
    if (spec == specs.end())
      return error("predicate content_digest does not resolve in the closed "
                   "predicate_specs section");
    auto entrypoint =
        spec->second.entrypoints.find(contract.predicate.entrypoint);
    if (entrypoint == spec->second.entrypoints.end())
      return error("predicate entrypoint does not resolve in its cited spec");
    const CheckPredicateEntrypoint &abi = entrypoint->second;
    bool operandsMatch = abi.operands.size() == contract.operands.size();
    if (operandsMatch)
      for (size_t i = 0; i < abi.operands.size(); ++i)
        operandsMatch &= sameOperand(abi.operands[i], contract.operands[i]);
    if (abi.parameters != contract.parameters ||
        abi.semanticParameters != contract.semanticParameters || !operandsMatch)
      return error("ABI does not exactly match predicate spec entrypoint '" +
                   contract.predicate.entrypoint + "'");
  }

  auto digest = RegistryFile::digestEntry("zkc/check-contract\n",
                                          contract.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  contract.digest = std::move(*digest);
  return contract;
}

Expected<std::vector<HoleSegment>>
parseHoleSegments(const RegistryFile &file, const json::Array &segments,
                  const Twine &context) {
  std::vector<HoleSegment> parsed;
  llvm::StringSet<> roles;
  for (const auto &[index, value] : llvm::enumerate(segments)) {
    std::string where = (context + " segment #" + Twine(index)).str();
    const json::Object *object = value.getAsObject();
    if (!object)
      return file.error(where + " must be an object");
    HoleSegment segment;
    auto sort = file.requireString(*object, "sort", where);
    if (!sort)
      return sort.takeError();
    if (*sort == "value") {
      if (Error e = file.requireClosedFields(
              *object, {"sort", "role", "class", "count"}, where))
        return std::move(e);
      segment.sort = HoleSegmentSort::Value;
      if (Error e = file.requireStringField(*object, "class", where,
                                            segment.typeClass))
        return std::move(e);
      if (Error e =
              file.requireStringField(*object, "count", where, segment.count))
        return std::move(e);
      if (!zkc::challenge::parseCount(segment.count))
        return file.error(where + " count must be a canonical decimal from "
                                  "1 through 2^20");
    } else if (*sort == "handle") {
      if (Error e = file.requireClosedFields(*object, {"sort", "role", "class"},
                                             where))
        return std::move(e);
      segment.sort = HoleSegmentSort::Handle;
      if (Error e = file.requireStringField(*object, "class", where,
                                            segment.typeClass))
        return std::move(e);
    } else if (*sort == "sponge") {
      if (Error e = file.requireClosedFields(*object, {"sort", "role"}, where))
        return std::move(e);
      segment.sort = HoleSegmentSort::Sponge;
    } else {
      return file.error(where +
                        " sort must be \"value\", \"handle\", or \"sponge\"");
    }
    if (Error e = file.requireStringField(*object, "role", where, segment.role))
      return std::move(e);
    if (segment.role.empty() || !zkc::encoding::inEncodingDomain(segment.role))
      return file.error(where + " role must be non-empty printable ASCII");
    if (!roles.insert(segment.role).second)
      return file.error(where + " role duplicates an earlier segment");
    if (segment.sort != HoleSegmentSort::Sponge &&
        (segment.typeClass.empty() ||
         !zkc::encoding::inEncodingDomain(segment.typeClass)))
      return file.error(where + " class must be non-empty printable ASCII");
    parsed.push_back(std::move(segment));
  }
  return parsed;
}

Expected<HoleContract> parseHoleContract(const RegistryFile &file, StringRef id,
                                         const json::Value &value) {
  auto error = [&](const Twine &message) {
    return file.error("hole contract '" + id + "' " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return error("must map to an object");
  if (Error e = file.requireClosedFields(
          *object,
          {"kind", "operands", "results", "parameters", "semantic_parameters"},
          "hole contract '" + id + "'"))
    return std::move(e);

  HoleContract contract;
  auto kind = file.requireString(*object, "kind", "hole contract '" + id + "'");
  if (!kind)
    return kind.takeError();
  bool knownKind = *kind == "commit" || *kind == "extend" ||
                   *kind == "evaluate" || *kind == "fold" || *kind == "open" ||
                   *kind == "pow_search";
  if (!knownKind)
    return error("kind must be one of commit | extend | evaluate | fold | "
                 "open | pow_search");
  contract.kind = std::string(*kind);

  const json::Array *operands = object->getArray("operands");
  if (!operands)
    return error("needs an array 'operands'");
  auto parsedOperands =
      parseHoleSegments(file, *operands, "hole contract '" + id + "' operand");
  if (!parsedOperands)
    return parsedOperands.takeError();
  contract.operands = std::move(*parsedOperands);

  const json::Array *results = object->getArray("results");
  if (!results)
    return error("needs an array 'results'");
  auto parsedResults =
      parseHoleSegments(file, *results, "hole contract '" + id + "' result");
  if (!parsedResults)
    return parsedResults.takeError();
  contract.results = std::move(*parsedResults);
  if (contract.results.empty())
    return error("declares at least one result");

  // The transcript peek is the pow_search kind's exclusive license:
  // exactly one sponge operand and one sponge result there, none
  // anywhere else (docs/spec/vocabularies.md §5.1).
  auto countSponges = [](ArrayRef<HoleSegment> segments) {
    return llvm::count_if(segments, [](const HoleSegment &segment) {
      return segment.sort == HoleSegmentSort::Sponge;
    });
  };
  int64_t spongeIns = countSponges(contract.operands);
  int64_t spongeOuts = countSponges(contract.results);
  if (contract.kind == "pow_search") {
    if (spongeIns != 1 || spongeOuts != 1)
      return error("pow_search declares exactly one sponge operand and one "
                   "sponge result");
  } else if (spongeIns || spongeOuts) {
    return error("only a pow_search hole declares sponge segments");
  }

  auto parameters = file.requireStringList(*object, "parameters",
                                           "hole contract '" + id + "'");
  if (!parameters)
    return parameters.takeError();
  auto semantic = file.requireStringList(*object, "semantic_parameters",
                                         "hole contract '" + id + "'");
  if (!semantic)
    return semantic.takeError();
  if (Error e = requireUnique(file, *parameters,
                              "hole contract '" + id + "' parameters"))
    return std::move(e);
  if (Error e = requireUnique(file, *semantic,
                              "hole contract '" + id + "' semantic parameters"))
    return std::move(e);
  StringSet<> parameterNames;
  for (const std::string &name : *parameters)
    parameterNames.insert(name);
  for (const std::string &name : *semantic)
    if (!parameterNames.insert(name).second)
      return error("parameter and semantic-parameter names must be disjoint");
  llvm::sort(*parameters);
  llvm::sort(*semantic);
  contract.parameters = std::move(*parameters);
  contract.semanticParameters = std::move(*semantic);

  auto digest = RegistryFile::digestEntry("zkc/hole-contract\n",
                                          contract.toCanonicalJson());
  if (!digest)
    return digest.takeError();
  contract.digest = std::move(*digest);
  return contract;
}

Error validateExpr(const RegistryFile &file, const json::Value &value,
                   const StringSet<> &operandRoles, const Twine &context,
                   unsigned depth);

Error validateCanonicalAtom(const RegistryFile &file, const json::Value &value,
                            const Twine &context, unsigned depth = 0) {
  if (depth > zkc::encoding::kMaxAttrDepth)
    return file.error(context + " exceeds the canonical value depth limit");
  if (auto string = value.getAsString()) {
    if (!zkc::encoding::inEncodingDomain(*string))
      return file.error(context + " contains a non-printable string");
    return Error::success();
  }
  if (value.getAsInteger())
    return Error::success();
  if (const json::Array *array = value.getAsArray()) {
    for (const auto &[index, member] : llvm::enumerate(*array))
      if (Error e = validateCanonicalAtom(
              file, member, context + "[" + Twine(index) + "]", depth + 1))
        return e;
    return Error::success();
  }
  if (const json::Object *object = value.getAsObject()) {
    for (const auto &member : *object) {
      StringRef key(member.first);
      if (key.empty() || !zkc::encoding::inEncodingDomain(key))
        return file.error(context +
                          " contains an invalid canonical object key");
      if (Error e = validateCanonicalAtom(file, member.second,
                                          context + "." + key, depth + 1))
        return e;
    }
    return Error::success();
  }
  return file.error(context +
                    " must use the canonical kernel value domain (string, "
                    "integer, array, or object)");
}

const VocabularyDepSlot *findDepSlot(const ReductionContract &contract,
                                     StringRef role) {
  for (const VocabularyDepSlot &slot : contract.depSlots)
    if (slot.role == role)
      return &slot;
  return nullptr;
}

const VocabularyMessageRole *findMessageRole(const ReductionContract &contract,
                                             StringRef role) {
  for (const VocabularyRound &round : contract.rounds)
    for (const VocabularyMessageRole &message : round.messages)
      if (message.role == role)
        return &message;
  return nullptr;
}

Expected<MaterialOrder> parseMaterialOrder(const RegistryFile &file,
                                           const json::Object &object,
                                           const Twine &context) {
  auto order = file.requireString(object, "order", context);
  if (!order)
    return order.takeError();
  if (*order == "operand")
    return MaterialOrder::Operand;
  if (*order == "canonical_unique")
    return MaterialOrder::CanonicalUnique;
  return file.error(context +
                    " order must be \"operand\" or \"canonical_unique\"");
}

uint64_t guaranteedInputCount(const ReductionContract &contract) {
  return contract.consumes.front().isVariadic() ? contract.consumes.front().min
                                                : contract.consumes.size();
}

const ClaimProfile *inputProfileAt(
    const ReductionContract &contract, uint64_t input,
    const std::map<std::string, ClaimProfile, std::less<>> &profiles) {
  const VocabularyConsumePattern &pattern =
      contract.consumes.front().isVariadic() ? contract.consumes.front()
                                             : contract.consumes[input];
  return lookup(profiles, pattern.profile);
}

Expected<MaterialExpr> parseMaterialExpr(
    const RegistryFile &file, const json::Value &value,
    const ReductionContract &contract,
    const std::map<std::string, ClaimProfile, std::less<>> &profiles,
    const Twine &context, unsigned depth, uint64_t &nodeCount) {
  if (depth >= zkc::encoding::kMaxAttrDepth)
    return file.error(context + " exceeds the material-expression depth limit");
  if (++nodeCount > zkc::challenge::kMaxCount)
    return file.error(context + " exceeds the material-expression node limit");
  const json::Object *object = value.getAsObject();
  if (!object)
    return file.error(context + " must be a tagged expression object");
  auto kind = file.requireString(*object, "kind", context);
  if (!kind)
    return kind.takeError();

  auto closed = [&](ArrayRef<StringRef> fields) -> Error {
    return file.requireClosedFields(*object, fields, context);
  };
  auto stringField = [&](StringRef field, std::string &out) -> Error {
    return file.requireStringField(*object, field, context, out);
  };
  auto inputIndex = [&]() -> Expected<uint64_t> {
    auto input = requireNonNegative(file, *object, "input", context);
    if (!input)
      return input.takeError();
    if (*input >= guaranteedInputCount(contract))
      return file.error(context + " references an input not guaranteed by "
                                  "the consume pattern");
    return *input;
  };
  auto hasInputAnchor = [&](uint64_t input, StringRef anchor) {
    const ClaimProfile *profile = inputProfileAt(contract, input, profiles);
    return llvm::is_contained(profile->anchors, anchor);
  };

  MaterialExpr expr;
  if (*kind == "literal_ref") {
    if (Error e = closed({"kind", "value"}))
      return std::move(e);
    if (Error e = stringField("value", expr.name))
      return std::move(e);
    if (!zkc::encoding::isSha256Ref(expr.name))
      return file.error(context + " value " +
                        zkc::encoding::kSha256RefMessage);
    expr.kind = MaterialExprKind::LiteralRef;
    expr.sort = MaterialExprSort::Ref;
  } else if (*kind == "input_anchor") {
    if (Error e = closed({"kind", "input", "anchor"}))
      return std::move(e);
    auto input = inputIndex();
    if (!input)
      return input.takeError();
    expr.index = *input;
    if (Error e = stringField("anchor", expr.name))
      return std::move(e);
    if (!hasInputAnchor(expr.index, expr.name))
      return file.error(context + " references an unknown input anchor");
    expr.kind = MaterialExprKind::InputAnchor;
    expr.sort = MaterialExprSort::Ref;
  } else if (*kind == "dependency") {
    if (Error e = closed({"kind", "role"}))
      return std::move(e);
    if (Error e = stringField("role", expr.name))
      return std::move(e);
    if (!findDepSlot(contract, expr.name))
      return file.error(context + " references an unknown dependency role");
    expr.kind = MaterialExprKind::Dependency;
    expr.sort = MaterialExprSort::Ref;
  } else if (*kind == "message") {
    if (Error e = closed({"kind", "role", "occurrence"}))
      return std::move(e);
    if (Error e = stringField("role", expr.name))
      return std::move(e);
    auto occurrence = requireNonNegative(file, *object, "occurrence", context);
    if (!occurrence)
      return occurrence.takeError();
    const VocabularyMessageRole *message = findMessageRole(contract, expr.name);
    if (!message)
      return file.error(context + " references an unknown message occurrence");
    if (message->multiplicity.isDynamic())
      return file.error(context +
                        " cannot select one occurrence from a dynamic "
                        "message role; use a messages expression");
    if (*occurrence >= message->multiplicity.exact)
      return file.error(context + " references an unknown message occurrence");
    expr.index = *occurrence;
    expr.kind = MaterialExprKind::Message;
    expr.sort = MaterialExprSort::Ref;
  } else if (*kind == "parameter_ref" || *kind == "parameter_refs" ||
             *kind == "parameter_atom") {
    if (Error e = closed({"kind", "name"}))
      return std::move(e);
    if (Error e = stringField("name", expr.name))
      return std::move(e);
    auto parameter = contract.parameters.find(expr.name);
    if (parameter == contract.parameters.end())
      return file.error(context + " references an unknown reduction parameter");
    ReductionParameterSort required = ReductionParameterSort::Atom;
    if (*kind == "parameter_ref") {
      expr.kind = MaterialExprKind::ParameterRef;
      expr.sort = MaterialExprSort::Ref;
      required = ReductionParameterSort::MaterialRef;
    } else if (*kind == "parameter_refs") {
      expr.kind = MaterialExprKind::ParameterRefs;
      expr.sort = MaterialExprSort::Refs;
      required = ReductionParameterSort::MaterialRefVector;
    } else {
      expr.kind = MaterialExprKind::ParameterAtom;
      expr.sort = MaterialExprSort::Atom;
    }
    if (parameter->second != required)
      return file.error(context + " uses a reduction parameter at the wrong "
                                  "material sort");
  } else if (*kind == "construct") {
    if (Error e = closed({"kind", "tag", "args"}))
      return std::move(e);
    if (Error e = stringField("tag", expr.name))
      return std::move(e);
    const json::Array *args = object->getArray("args");
    if (!args)
      return file.error(context + " needs an array 'args'");
    for (const auto &[index, argument] : llvm::enumerate(*args)) {
      auto parsed = parseMaterialExpr(file, argument, contract, profiles,
                                      context + " arg " + Twine(index),
                                      depth + 1, nodeCount);
      if (!parsed)
        return parsed.takeError();
      expr.arguments.push_back(std::move(*parsed));
    }
    expr.kind = MaterialExprKind::Construct;
    expr.sort = MaterialExprSort::Ref;
  } else if (*kind == "input_anchors") {
    if (Error e = closed({"kind", "anchor", "order"}))
      return std::move(e);
    if (Error e = stringField("anchor", expr.name))
      return std::move(e);
    for (const VocabularyConsumePattern &pattern : contract.consumes)
      if (!llvm::is_contained(lookup(profiles, pattern.profile)->anchors,
                              expr.name))
        return file.error(context + " references an anchor not shared by all "
                                    "input profiles");
    auto order = parseMaterialOrder(file, *object, context);
    if (!order)
      return order.takeError();
    expr.order = *order;
    expr.kind = MaterialExprKind::InputAnchors;
    expr.sort = MaterialExprSort::Refs;
  } else if (*kind == "messages") {
    if (Error e = closed({"kind", "role"}))
      return std::move(e);
    if (Error e = stringField("role", expr.name))
      return std::move(e);
    if (!findMessageRole(contract, expr.name))
      return file.error(context + " references an unknown message role");
    expr.kind = MaterialExprKind::Messages;
    expr.sort = MaterialExprSort::Refs;
  } else if (*kind == "list") {
    if (Error e = closed({"kind", "items"}))
      return std::move(e);
    const json::Array *items = object->getArray("items");
    if (!items)
      return file.error(context + " needs an array 'items'");
    for (const auto &[index, item] : llvm::enumerate(*items)) {
      auto parsed = parseMaterialExpr(file, item, contract, profiles,
                                      context + " item " + Twine(index),
                                      depth + 1, nodeCount);
      if (!parsed)
        return parsed.takeError();
      if (parsed->sort != MaterialExprSort::Ref)
        return file.error(context + " list items must have ref sort");
      expr.arguments.push_back(std::move(*parsed));
    }
    expr.kind = MaterialExprKind::List;
    expr.sort = MaterialExprSort::Refs;
  } else if (*kind == "input_descriptor") {
    if (Error e = closed({"kind", "input"}))
      return std::move(e);
    auto input = inputIndex();
    if (!input)
      return input.takeError();
    expr.index = *input;
    expr.kind = MaterialExprKind::InputDescriptor;
    expr.sort = MaterialExprSort::Claim;
  } else if (*kind == "input_descriptors") {
    if (Error e = closed({"kind", "order"}))
      return std::move(e);
    auto order = parseMaterialOrder(file, *object, context);
    if (!order)
      return order.takeError();
    expr.order = *order;
    expr.kind = MaterialExprKind::InputDescriptors;
    expr.sort = MaterialExprSort::Claims;
  } else if (*kind == "literal") {
    if (Error e = closed({"kind", "value"}))
      return std::move(e);
    const json::Value *literal = object->get("value");
    if (!literal)
      return file.error(context + " needs 'value'");
    if (Error e = validateCanonicalAtom(file, *literal, context + " value"))
      return std::move(e);
    expr.literal = *literal;
    expr.kind = MaterialExprKind::Literal;
    expr.sort = MaterialExprSort::Atom;
  } else {
    return file.error(context + " has unknown material-expression kind '" +
                      *kind + "'");
  }
  return expr;
}

const CheckOperandSegment *findOperand(const CheckContract &contract,
                                       StringRef role) {
  for (const CheckOperandSegment &operand : contract.operands)
    if (operand.role == role)
      return &operand;
  return nullptr;
}

Expected<MessageMultiplicity> parseMessageMultiplicity(const RegistryFile &file,
                                                       const json::Value &value,
                                                       bool hasVariadicConsume,
                                                       const Twine &context) {
  std::string where = context.str();
  const json::Object *object = value.getAsObject();
  if (!object || object->size() != 1)
    return file.error(Twine(where) +
                      " count must be exactly one of {\"exact\":N} or "
                      "{\"same_as\":\"consumed_claims\"}");

  MessageMultiplicity result;
  if (object->get("exact")) {
    auto exact =
        requireBoundedPositive(file, *object, "exact", Twine(where) + " count");
    if (!exact)
      return exact.takeError();
    result.exact = *exact;
    return result;
  }
  if (object->get("same_as")) {
    auto source =
        file.requireString(*object, "same_as", Twine(where) + " count");
    if (!source)
      return source.takeError();
    if (*source != "consumed_claims")
      return file.error(Twine(where) +
                        " count same_as must name \"consumed_claims\"");
    if (!hasVariadicConsume)
      return file.error(Twine(where) +
                        " count may use consumed_claims only on a contract "
                        "with exactly one variadic consume pattern");
    result.kind = MessageMultiplicityKind::ConsumedClaims;
    return result;
  }
  return file.error(Twine(where) +
                    " count must be exactly one of {\"exact\":N} or "
                    "{\"same_as\":\"consumed_claims\"}");
}

Expected<ReductionContract> parseReductionContract(
    const RegistryFile &file, StringRef id, const json::Value &value,
    const std::map<std::string, ClaimProfile, std::less<>> &profiles,
    const std::map<std::string, CheckContract, std::less<>> &checkContracts) {
  auto error = [&](const Twine &message) {
    return file.error("reduction contract '" + id + "': " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return error("must map to an object");
  if (Error e = file.requireClosedFields(*object,
                                         {"consumes", "dep_slots", "rounds",
                                          "parameters", "checks", "constraints",
                                          "outputs"},
                                         "reduction contract '" + id + "'"))
    return std::move(e);

  ReductionContract contract;

  const json::Array *consumes = object->getArray("consumes");
  if (!consumes || consumes->empty())
    return error("needs a non-empty array 'consumes'");
  for (const auto &[index, member] : llvm::enumerate(*consumes)) {
    VocabularyConsumePattern pattern;
    if (auto profile = member.getAsString()) {
      pattern.profile = profile->str();
    } else if (const json::Object *variadic = member.getAsObject()) {
      std::string context =
          ("reduction contract '" + id + "' consumes[" + Twine(index) + "]")
              .str();
      if (Error e =
              file.requireClosedFields(*variadic, {"profile", "min"}, context))
        return std::move(e);
      if (Error e = file.requireStringField(*variadic, "profile", context,
                                            pattern.profile))
        return std::move(e);
      auto minimum = requireBoundedPositive(file, *variadic, "min", context);
      if (!minimum)
        return minimum.takeError();
      pattern.min = *minimum;
    } else {
      return error("consumes entries must be profile ids or {profile,min} "
                   "patterns");
    }
    if (!profiles.count(pattern.profile))
      return error("consumes unknown claim profile '" + pattern.profile + "'");
    contract.consumes.push_back(std::move(pattern));
  }
  for (const VocabularyConsumePattern &pattern : contract.consumes)
    if (pattern.isVariadic() && contract.consumes.size() != 1)
      return error("a variadic consumes pattern must be the contract's only "
                   "entry");

  const json::Array *depSlots = object->getArray("dep_slots");
  if (!depSlots)
    return error("needs an array 'dep_slots'");
  StringSet<> roles;
  for (const auto &[index, member] : llvm::enumerate(*depSlots)) {
    const json::Object *slot = member.getAsObject();
    std::string context =
        ("reduction contract '" + id + "' dep slot " + Twine(index)).str();
    if (!slot)
      return file.error(context + " must be an object");
    if (Error e = file.requireClosedFields(*slot, {"role", "source", "class"},
                                           context))
      return std::move(e);
    VocabularyDepSlot parsed;
    if (Error e = file.requireStringField(*slot, "role", context, parsed.role))
      return std::move(e);
    auto source = file.requireString(*slot, "source", context);
    if (!source)
      return source.takeError();
    if (*source == "any")
      parsed.source = VocabularyDepSource::Any;
    else if (*source == "public_bind")
      parsed.source = VocabularyDepSource::PublicBind;
    else if (*source == "prover_slot")
      parsed.source = VocabularyDepSource::ProverSlot;
    else if (*source == "challenge_capability")
      parsed.source = VocabularyDepSource::ChallengeCapability;
    else
      return file.error(context +
                        " 'source' must be any, public_bind, prover_slot, or "
                        "challenge_capability");
    if (Error e = file.requireStringField(*slot, "class", context,
                                          parsed.payloadClass))
      return std::move(e);
    if (parsed.payloadClass == "chal")
      return file.error(context +
                        " 'class' must be a semantic payload class, not the "
                        "retired producer pseudo-class 'chal'");
    if (!roles.insert(parsed.role).second)
      return error("role '" + parsed.role + "' is declared twice");
    contract.depSlots.push_back(std::move(parsed));
  }

  const json::Array *rounds = object->getArray("rounds");
  if (!rounds)
    return error("needs an array 'rounds'");
  if (rounds->empty())
    return error("needs a non-empty array 'rounds': a contract with no "
                 "interaction rounds states no local transition to judge "
                 "or price");
  StringSet<> roundChallengeUses;
  for (const auto &[index, member] : llvm::enumerate(*rounds)) {
    const json::Object *round = member.getAsObject();
    std::string context =
        ("reduction contract '" + id + "' round " + Twine(index)).str();
    if (!round)
      return file.error(context + " must be an object");
    if (Error e = file.requireClosedFields(
            *round, {"challenge_use", "messages", "kind"}, context))
      return std::move(e);
    VocabularyRound parsed;
    const json::Object *challengeUse = round->getObject("challenge_use");
    if (!challengeUse)
      return file.error(context + " needs an object 'challenge_use'");
    if (Error e = file.requireClosedFields(*challengeUse, {"role", "count"},
                                           context + " challenge_use"))
      return std::move(e);
    if (Error e = file.requireStringField(*challengeUse, "role",
                                          context + " challenge_use",
                                          parsed.challengeUse.role))
      return std::move(e);
    const VocabularyDepSlot *challengeSlot =
        findDepSlot(contract, parsed.challengeUse.role);
    if (!challengeSlot)
      return file.error(context + " challenge_use must name a dependency slot");
    if (!roundChallengeUses.insert(parsed.challengeUse.role).second)
      return error("challenge-use role '" + parsed.challengeUse.role +
                   "' heads more than one round");
    if (const json::Value *count = challengeUse->get("count")) {
      auto amount = count->getAsInteger();
      if (!amount || *amount < 2 ||
          static_cast<uint64_t>(*amount) > zkc::challenge::kMaxCount)
        return file.error(context +
                          " challenge_use 'count' must be an integer from 2 "
                          "through 2^20 (omit it for a scalar use)");
      parsed.challengeUse.count = static_cast<uint64_t>(*amount);
    }
    if (round->get("kind"))
      if (Error e =
              file.requireStringField(*round, "kind", context, parsed.kind))
        return std::move(e);
    const json::Array *messages = round->getArray("messages");
    if (!messages)
      return file.error(context + " needs an array 'messages'");
    for (const auto &[messageIndex, messageValue] :
         llvm::enumerate(*messages)) {
      const json::Object *message = messageValue.getAsObject();
      std::string messageContext =
          (Twine(context) + " message " + Twine(messageIndex)).str();
      if (!message)
        return file.error(messageContext + " must be an object");
      if (Error e = file.requireClosedFields(*message, {"role", "count"},
                                             messageContext))
        return std::move(e);
      VocabularyMessageRole role;
      if (Error e = file.requireStringField(*message, "role", messageContext,
                                            role.role))
        return std::move(e);
      const json::Value *count = message->get("count");
      if (!count)
        return file.error(messageContext + " needs 'count'");
      auto multiplicity =
          parseMessageMultiplicity(file, *count,
                                   contract.consumes.size() == 1 &&
                                       contract.consumes.front().isVariadic(),
                                   messageContext);
      if (!multiplicity)
        return multiplicity.takeError();
      if (!roles.insert(role.role).second)
        return error("role '" + role.role + "' is declared twice");
      role.multiplicity = *multiplicity;
      parsed.messages.push_back(std::move(role));
    }
    contract.rounds.push_back(std::move(parsed));
  }

  const json::Object *parameters = object->getObject("parameters");
  if (!parameters)
    return error("needs an object 'parameters'");
  for (const auto &member : *parameters) {
    StringRef name(member.first);
    if (Error e = requireEntryName(file, "reduction parameter", name))
      return std::move(e);
    if (!roles.insert(name).second)
      return error("dependency, message, parameter, and check roles must be "
                   "disjoint and unique");
    auto sort = member.second.getAsString();
    if (!sort)
      return error("parameter '" + name + "' needs a sort string");
    ReductionParameterSort parsed;
    if (*sort == "atom")
      parsed = ReductionParameterSort::Atom;
    else if (*sort == "material_ref")
      parsed = ReductionParameterSort::MaterialRef;
    else if (*sort == "material_ref_vector")
      parsed = ReductionParameterSort::MaterialRefVector;
    else
      return error("parameter '" + name +
                   "' sort must be atom, material_ref, or "
                   "material_ref_vector");
    contract.parameters[name.str()] = parsed;
  }

  const json::Object *checks = object->getObject("checks");
  if (!checks)
    return error("needs an object 'checks'");
  for (const auto &member : *checks) {
    StringRef role(member.first);
    if (Error e = requireEntryName(file, "reduction check role", role))
      return std::move(e);
    if (!roles.insert(role).second)
      return error("dependency, message, parameter, and check roles must be "
                   "disjoint and unique");
    std::string context =
        ("reduction contract '" + id + "' check '" + role + "'").str();
    const json::Object *slotObject = member.second.getAsObject();
    if (!slotObject)
      return file.error(context + " must be an object");
    if (Error e = file.requireClosedFields(
            *slotObject,
            {"contract", "parameters", "transparent_predicate", "attachments"},
            context))
      return std::move(e);
    BodyCheckSlot slot;
    if (Error e = file.requireStringField(*slotObject, "contract", context,
                                          slot.contract))
      return std::move(e);
    const CheckContract *checkContract = lookup(checkContracts, slot.contract);
    if (!checkContract)
      return file.error(context + " references unknown check contract '" +
                        slot.contract + "'");

    const json::Object *slotParameters = slotObject->getObject("parameters");
    if (!slotParameters)
      return file.error(context + " needs an object 'parameters'");
    if (slotParameters->size() != checkContract->parameters.size())
      return file.error(context +
                        " parameters must match the check contract exactly");
    for (const std::string &name : checkContract->parameters) {
      const json::Value *parameter = slotParameters->get(name);
      if (!parameter)
        return file.error(context +
                          " parameters must match the check contract exactly");
      if (Error e = validateCanonicalAtom(
              file, *parameter, context + " parameter '" + name + "'"))
        return std::move(e);
      slot.parameters.insert_or_assign(name, *parameter);
    }
    for (const auto &parameter : *slotParameters)
      if (!llvm::is_contained(checkContract->parameters,
                              StringRef(parameter.first)))
        return file.error(context +
                          " parameters must match the check contract exactly");

    const json::Value *predicate = slotObject->get("transparent_predicate");
    if (checkContract->isTransparent() != (predicate != nullptr))
      return file.error(context +
                        " must define a predicate exactly for transparent "
                        "check contracts");
    if (predicate) {
      StringSet<> operandRoles;
      for (const CheckOperandSegment &operand : checkContract->operands)
        operandRoles.insert(operand.role);
      const json::Array *root = predicate->getAsArray();
      if (!root || root->size() != 3 || (*root)[0].getAsString() != "eq")
        return file.error(context +
                          " transparent predicate must be a binary equality");
      if (Error e = validateExpr(file, *predicate, operandRoles,
                                 context + " transparent predicate", 0))
        return std::move(e);
      slot.transparentPredicate = *predicate;
    }

    const json::Array *attachments = slotObject->getArray("attachments");
    if (!attachments)
      return file.error(context + " needs an array 'attachments'");
    StringSet<> encodedAttachments;
    StringSet<> targets;
    StringSet<> semanticCoverage;
    std::vector<std::pair<std::string, ReductionCheckAttachment>> admitted;
    for (const auto &[index, attachmentValue] : llvm::enumerate(*attachments)) {
      std::string attachmentContext =
          (Twine(context) + " attachment " + Twine(index)).str();
      const json::Object *attachmentObject = attachmentValue.getAsObject();
      if (!attachmentObject)
        return file.error(attachmentContext + " must be an object");
      if (Error e = file.requireClosedFields(*attachmentObject,
                                             {"kind", "source", "target_role"},
                                             attachmentContext))
        return std::move(e);
      auto attachmentKind =
          file.requireString(*attachmentObject, "kind", attachmentContext);
      if (!attachmentKind)
        return attachmentKind.takeError();
      ReductionCheckAttachment attachment;
      MaterialExprSort requiredSort = MaterialExprSort::Ref;
      bool semanticTarget = false;
      bool singletonTarget = false;
      if (*attachmentKind == "semantic_parameter") {
        attachment.kind = ReductionCheckAttachmentKind::SemanticParameter;
        semanticTarget = true;
      } else if (*attachmentKind == "material_ref_equality") {
        attachment.kind = ReductionCheckAttachmentKind::MaterialRefEquality;
        singletonTarget = true;
      } else if (*attachmentKind == "value_identity") {
        attachment.kind = ReductionCheckAttachmentKind::ValueIdentity;
        singletonTarget = true;
      } else if (*attachmentKind == "material_ref_vector_equality") {
        attachment.kind =
            ReductionCheckAttachmentKind::MaterialRefVectorEquality;
        requiredSort = MaterialExprSort::Refs;
      } else if (*attachmentKind == "common_material_ref_equality") {
        attachment.kind =
            ReductionCheckAttachmentKind::CommonMaterialRefEquality;
        requiredSort = MaterialExprSort::Refs;
        singletonTarget = true;
      } else if (*attachmentKind == "value_identity_vector") {
        attachment.kind = ReductionCheckAttachmentKind::ValueIdentityVector;
      } else if (*attachmentKind == "value_identity_list") {
        attachment.kind = ReductionCheckAttachmentKind::ValueIdentityList;
        requiredSort = MaterialExprSort::Refs;
      } else {
        return file.error(attachmentContext +
                          " has unknown check-attachment kind '" +
                          *attachmentKind + "'");
      }
      if (Error e =
              file.requireStringField(*attachmentObject, "target_role",
                                      attachmentContext, attachment.targetRole))
        return std::move(e);
      if (!targets.insert(attachment.targetRole).second)
        return file.error(context + " constrains one check target twice");

      const json::Value *source = attachmentObject->get("source");
      if (!source)
        return file.error(attachmentContext + " needs 'source'");
      uint64_t nodeCount = 0;
      auto parsedSource =
          parseMaterialExpr(file, *source, contract, profiles,
                            attachmentContext + " source", 0, nodeCount);
      if (!parsedSource)
        return parsedSource.takeError();
      if (parsedSource->sort != requiredSort)
        return file.error(attachmentContext + " source has the wrong sort");
      if (attachment.kind == ReductionCheckAttachmentKind::ValueIdentity &&
          parsedSource->kind != MaterialExprKind::Dependency &&
          parsedSource->kind != MaterialExprKind::Message)
        return file.error(attachmentContext +
                          " value_identity source must be dependency or "
                          "message");
      // The whole-vector identity: one counted source value binds one
      // counted operand segment, count for count — the kernel-level
      // statement that the sampled or absorbed vector is the vector the
      // check consumes (docs/spec/carrier.md §7). The source is a
      // counted challenge dependency or a counted round message; the
      // scalar case keeps its own kind, so one realized identity never
      // has two content spellings.
      if (attachment.kind == ReductionCheckAttachmentKind::ValueIdentityVector) {
        uint64_t sourceCount = 0;
        if (parsedSource->kind == MaterialExprKind::Dependency) {
          for (const VocabularyRound &round : contract.rounds)
            if (round.challengeUse.role == parsedSource->name)
              sourceCount =
                  round.challengeUse.count ? round.challengeUse.count : 1;
        } else if (parsedSource->kind == MaterialExprKind::Message) {
          // A dynamic multiplicity has no static count to agree on;
          // only exact message roles carry the vector identity.
          for (const VocabularyRound &round : contract.rounds)
            for (const VocabularyMessageRole &message : round.messages)
              if (message.role == parsedSource->name &&
                  !message.multiplicity.isDynamic())
                sourceCount = message.multiplicity.exact;
        } else {
          return file.error(attachmentContext +
                            " value_identity_vector source must be a "
                            "dependency or message");
        }
        const CheckOperandSegment *operand =
            findOperand(*checkContract, attachment.targetRole);
        if (!operand)
          return file.error(attachmentContext +
                            " references an unknown check operand role");
        if (operand->multiplicity.kind != OperandMultiplicityKind::Exact ||
            sourceCount < 2 ||
            operand->multiplicity.value != sourceCount)
          return file.error(attachmentContext +
                            " value_identity_vector requires a counted "
                            "dependency or message source whose count "
                            "equals the target segment's");
      }
      // The positional list identity: an ordered list of local-value
      // selectors binds a multi-element segment element for element —
      // how per-round scalars (the betas, the round roots) enter one
      // counted role.
      if (attachment.kind == ReductionCheckAttachmentKind::ValueIdentityList) {
        if (parsedSource->kind != MaterialExprKind::List)
          return file.error(attachmentContext +
                            " value_identity_list source must be a list");
        for (const MaterialExpr &item : parsedSource->arguments)
          if (item.kind != MaterialExprKind::Dependency &&
              item.kind != MaterialExprKind::Message)
            return file.error(attachmentContext +
                              " value_identity_list items must be "
                              "dependency or message selectors");
        const CheckOperandSegment *operand =
            findOperand(*checkContract, attachment.targetRole);
        if (!operand)
          return file.error(attachmentContext +
                            " references an unknown check operand role");
        if (operand->multiplicity.kind != OperandMultiplicityKind::Exact ||
            operand->multiplicity.value != parsedSource->arguments.size())
          return file.error(attachmentContext +
                            " value_identity_list length must equal the "
                            "target segment's count");
      }
      attachment.source = std::move(*parsedSource);

      if (semanticTarget) {
        if (!llvm::is_contained(checkContract->semanticParameters,
                                attachment.targetRole))
          return file.error(attachmentContext +
                            " references an unknown semantic parameter");
        semanticCoverage.insert(attachment.targetRole);
      } else {
        const CheckOperandSegment *operand =
            findOperand(*checkContract, attachment.targetRole);
        if (!operand)
          return file.error(attachmentContext +
                            " references an unknown check operand role");
        if (singletonTarget &&
            (operand->multiplicity.kind != OperandMultiplicityKind::Exact ||
             operand->multiplicity.value != 1))
          return file.error(attachmentContext +
                            " requires an exactly-one operand target");
      }
      auto bytes = canonicalBytes(attachment.toCanonicalJson());
      if (!bytes)
        return bytes.takeError();
      if (!encodedAttachments.insert(*bytes).second)
        return file.error(context + " repeats an attachment");
      admitted.emplace_back(std::move(*bytes), std::move(attachment));
    }
    if (semanticCoverage.size() != checkContract->semanticParameters.size())
      return file.error(context + " does not cover every semantic parameter");
    for (const std::string &name : checkContract->semanticParameters)
      if (!semanticCoverage.contains(name))
        return file.error(context + " does not cover every semantic parameter");
    llvm::sort(admitted, [](const auto &left, const auto &right) {
      return left.first < right.first;
    });
    for (auto &entry : admitted)
      slot.attachments.push_back(std::move(entry.second));
    contract.checks[role.str()] = std::move(slot);
  }

  const json::Array *constraints = object->getArray("constraints");
  if (!constraints)
    return error("needs an array 'constraints'");
  StringSet<> encodedConstraints;
  std::vector<std::pair<std::string, MaterialConstraint>> admittedConstraints;
  for (const auto &[index, member] : llvm::enumerate(*constraints)) {
    std::string context =
        ("reduction contract '" + id + "' constraint " + Twine(index)).str();
    const json::Object *constraintObject = member.getAsObject();
    if (!constraintObject)
      return file.error(context + " must be an object");
    if (Error e = file.requireClosedFields(*constraintObject,
                                           {"kind", "left", "right"}, context))
      return std::move(e);
    auto kind = file.requireString(*constraintObject, "kind", context);
    if (!kind)
      return kind.takeError();
    if (*kind != "equal")
      return file.error(context + " kind must be \"equal\"");
    const json::Value *left = constraintObject->get("left");
    const json::Value *right = constraintObject->get("right");
    if (!left || !right)
      return file.error(context + " needs 'left' and 'right'");
    uint64_t nodeCount = 0;
    auto parsedLeft = parseMaterialExpr(file, *left, contract, profiles,
                                        context + " left", 0, nodeCount);
    if (!parsedLeft)
      return parsedLeft.takeError();
    auto parsedRight = parseMaterialExpr(file, *right, contract, profiles,
                                         context + " right", 0, nodeCount);
    if (!parsedRight)
      return parsedRight.takeError();
    if (parsedLeft->sort != parsedRight->sort)
      return file.error(context + " compares expressions of different sorts");
    auto leftBytes = canonicalBytes(parsedLeft->toCanonicalJson());
    auto rightBytes = canonicalBytes(parsedRight->toCanonicalJson());
    if (!leftBytes)
      return leftBytes.takeError();
    if (!rightBytes)
      return rightBytes.takeError();
    if (*leftBytes == *rightBytes)
      return file.error(context + " is tautological");
    MaterialConstraint constraint{std::move(*parsedLeft),
                                  std::move(*parsedRight)};
    if (*rightBytes < *leftBytes)
      std::swap(constraint.left, constraint.right);
    auto bytes = canonicalBytes(constraint.toCanonicalJson());
    if (!bytes)
      return bytes.takeError();
    if (!encodedConstraints.insert(*bytes).second)
      return error("repeats a material constraint");
    admittedConstraints.emplace_back(std::move(*bytes), std::move(constraint));
  }
  llvm::sort(admittedConstraints, [](const auto &left, const auto &right) {
    return left.first < right.first;
  });
  for (auto &entry : admittedConstraints)
    contract.constraints.push_back(std::move(entry.second));

  const json::Array *outputs = object->getArray("outputs");
  if (!outputs || outputs->empty())
    return error("needs a non-empty array 'outputs'");
  // Exactly one, and the reason is on the judgment side rather than here: a
  // derivation site names one output position, so a contract producing several
  // would offer one site per output and every conclusion would carry the whole
  // reduction's error. Nothing constrains the other direction, so the
  // over-count would be admitted in silence. Ranging a conclusion over the
  // whole output tensor is the alternative and it needs a subject this model
  // does not have (docs/spec/kernel.md §4 and docs/spec/vocabularies.md §4).
  if (outputs->size() != 1)
    return error("produces " + Twine(outputs->size()) +
                 " claims; a reduction contract produces exactly one, because "
                 "a derivation site names one output position");
  for (const auto &[index, member] : llvm::enumerate(*outputs)) {
    std::string context =
        ("reduction contract '" + id + "' output " + Twine(index)).str();
    const json::Object *outputObject = member.getAsObject();
    if (!outputObject)
      return file.error(context + " must be an object");
    if (Error e = file.requireClosedFields(*outputObject,
                                           {"profile", "anchors"}, context))
      return std::move(e);
    ReductionOutputConstructor output;
    if (Error e = file.requireStringField(*outputObject, "profile", context,
                                          output.profile))
      return std::move(e);
    const ClaimProfile *profile = lookup(profiles, output.profile);
    if (!profile)
      return file.error(context + " references unknown claim profile '" +
                        output.profile + "'");
    // The faithfulness gate: an anchorless profile is one constant descriptor
    // in every artifact, so with descriptors as the claim graph's objects an
    // anchorless output composes with every consumer at the link boundary --
    // a discrete-log conclusion fusing with a sumcheck source.  A profile a
    // reduction produces must therefore say what its claims are about.  An
    // anchorless *source* profile stays legal: an entry claim's anchors are
    // declared by its author, and requiring them here would refuse nothing
    // (docs/spec/vocabularies.md §3).
    if (profile->anchors.empty())
      return file.error(context + " produces anchorless profile '" +
                        output.profile +
                        "'; a produced claim descriptor must say what it is "
                        "about, or every consumer composes with it");
    const json::Object *anchors = outputObject->getObject("anchors");
    if (!anchors)
      return file.error(context + " needs an object 'anchors'");
    if (anchors->size() != profile->anchors.size())
      return file.error(context +
                        " anchors must match the output profile exactly");
    for (const std::string &anchor : profile->anchors) {
      const json::Value *anchorExpr = anchors->get(anchor);
      if (!anchorExpr)
        return file.error(context +
                          " anchors must match the output profile exactly");
      uint64_t nodeCount = 0;
      auto parsed =
          parseMaterialExpr(file, *anchorExpr, contract, profiles,
                            context + " anchor '" + anchor + "'", 0, nodeCount);
      if (!parsed)
        return parsed.takeError();
      if (parsed->sort != MaterialExprSort::Ref)
        return file.error(context + " anchor expressions must have ref sort");
      output.anchors.emplace(anchor, std::move(*parsed));
    }
    for (const auto &anchor : *anchors)
      if (!llvm::is_contained(profile->anchors, StringRef(anchor.first)))
        return file.error(context +
                          " anchors must match the output profile exactly");
    contract.outputs.push_back(std::move(output));
  }

  auto digest = digestReductionContract(contract, profiles, checkContracts);
  if (!digest)
    return digest.takeError();
  contract.digest = std::move(*digest);
  return contract;
}

Expected<AttachmentSource> parseSource(const RegistryFile &file,
                                       const json::Value &value,
                                       const Twine &context) {
  const json::Object *object = value.getAsObject();
  if (!object)
    return file.error(context + " source must be an object");
  auto kind = file.requireString(*object, "kind", context + " source");
  if (!kind)
    return kind.takeError();
  AttachmentSource source;
  if (*kind == "claim_anchor") {
    if (Error e = file.requireClosedFields(*object, {"kind", "anchor"},
                                           context + " source"))
      return std::move(e);
    source.kind = AttachmentSourceKind::ClaimAnchor;
    if (Error e = file.requireStringField(*object, "anchor",
                                          context + " source", source.anchor))
      return std::move(e);
  } else if (*kind == "producer_input_anchor") {
    if (Error e = file.requireClosedFields(*object, {"kind", "input", "anchor"},
                                           context + " source"))
      return std::move(e);
    source.kind = AttachmentSourceKind::ProducerInputAnchor;
    auto input =
        requireNonNegative(file, *object, "input", context + " source");
    if (!input)
      return input.takeError();
    source.index = *input;
    if (Error e = file.requireStringField(*object, "anchor",
                                          context + " source", source.anchor))
      return std::move(e);
  } else if (*kind == "producer_inputs_anchor") {
    if (Error e = file.requireClosedFields(*object, {"kind", "anchor"},
                                           context + " source"))
      return std::move(e);
    source.kind = AttachmentSourceKind::ProducerInputsAnchor;
    if (Error e = file.requireStringField(*object, "anchor",
                                          context + " source", source.anchor))
      return std::move(e);
  } else if (*kind == "producer_input_descriptors") {
    if (Error e =
            file.requireClosedFields(*object, {"kind"}, context + " source"))
      return std::move(e);
    source.kind = AttachmentSourceKind::ProducerInputDescriptors;
  } else if (*kind == "producer_dependency") {
    if (Error e = file.requireClosedFields(*object, {"kind", "role"},
                                           context + " source"))
      return std::move(e);
    source.kind = AttachmentSourceKind::ProducerDependency;
    if (Error e = file.requireStringField(*object, "role", context + " source",
                                          source.role))
      return std::move(e);
  } else if (*kind == "producer_message") {
    if (Error e = file.requireClosedFields(*object, {"kind", "role", "index"},
                                           context + " source"))
      return std::move(e);
    source.kind = AttachmentSourceKind::ProducerMessage;
    if (Error e = file.requireStringField(*object, "role", context + " source",
                                          source.role))
      return std::move(e);
    auto index =
        requireNonNegative(file, *object, "index", context + " source");
    if (!index)
      return index.takeError();
    source.index = *index;
  } else {
    return file.error(context + " has unknown attachment source kind '" +
                      *kind + "'");
  }
  return source;
}

Expected<TerminalAttachment> parseAttachment(const RegistryFile &file,
                                             const json::Value &value,
                                             const Twine &context) {
  const json::Object *object = value.getAsObject();
  if (!object)
    return file.error(context + " must be an object");
  auto kind = file.requireString(*object, "kind", context);
  if (!kind)
    return kind.takeError();
  TerminalAttachment attachment;
  SmallVector<StringRef, 5> fields;
  if (*kind == "semantic_parameter") {
    attachment.kind = TerminalAttachmentKind::SemanticParameter;
    fields = {"kind", "source", "check", "role"};
  } else if (*kind == "material_ref_equality") {
    attachment.kind = TerminalAttachmentKind::MaterialRefEquality;
    fields = {"kind", "source", "check", "role"};
  } else if (*kind == "value_identity") {
    attachment.kind = TerminalAttachmentKind::ValueIdentity;
    fields = {"kind", "source", "check", "role"};
  } else if (*kind == "material_ref_vector_equality") {
    attachment.kind = TerminalAttachmentKind::MaterialRefVectorEquality;
    fields = {"kind", "source", "check", "role"};
  } else if (*kind == "common_material_ref_equality") {
    attachment.kind = TerminalAttachmentKind::CommonMaterialRefEquality;
    fields = {"kind", "source", "check", "role", "claim_anchor"};
  } else if (*kind == "descriptor_digest") {
    attachment.kind = TerminalAttachmentKind::DescriptorDigest;
    fields = {"kind", "source", "anchor"};
  } else {
    return file.error(context + " has unknown attachment kind '" + *kind + "'");
  }
  if (Error e = file.requireClosedFields(*object, fields, context))
    return std::move(e);
  const json::Value *source = object->get("source");
  if (!source)
    return file.error(context + " needs 'source'");
  auto parsedSource = parseSource(file, *source, context);
  if (!parsedSource)
    return parsedSource.takeError();
  attachment.source = std::move(*parsedSource);

  if (attachment.kind == TerminalAttachmentKind::DescriptorDigest) {
    if (Error e = file.requireStringField(*object, "anchor", context,
                                          attachment.claimAnchor))
      return std::move(e);
  } else {
    if (Error e = file.requireStringField(*object, "check", context,
                                          attachment.checkRole))
      return std::move(e);
    if (Error e = file.requireStringField(*object, "role", context,
                                          attachment.targetRole))
      return std::move(e);
    if (attachment.kind == TerminalAttachmentKind::CommonMaterialRefEquality)
      if (Error e = file.requireStringField(*object, "claim_anchor", context,
                                            attachment.claimAnchor))
        return std::move(e);
  }
  return attachment;
}

Error validateExpr(const RegistryFile &file, const json::Value &value,
                   const StringSet<> &operandRoles, const Twine &context,
                   unsigned depth = 0) {
  if (depth >= zkc::encoding::kMaxAttrDepth)
    return file.error(context + " exceeds the expression depth limit");
  const json::Array *expr = value.getAsArray();
  if (!expr || expr->empty())
    return file.error(context + " must be a non-empty expression array");
  auto op = (*expr)[0].getAsString();
  if (!op || op->empty() || !zkc::encoding::inEncodingDomain(*op))
    return file.error(context + " needs a printable-ASCII operator");
  if (*op == "role") {
    if (expr->size() != 2 && expr->size() != 3)
      return file.error(context + " has an invalid role leaf");
    auto role = (*expr)[1].getAsString();
    if (!role || !operandRoles.contains(*role))
      return file.error(context + " references an unknown operand role");
    if (expr->size() == 3) {
      auto index = (*expr)[2].getAsInteger();
      if (!index || *index < 0)
        return file.error(context + " has an invalid role index");
    }
    return Error::success();
  }
  if (*op == "const") {
    if (expr->size() != 2)
      return file.error(context + " has an invalid constant leaf");
    if (auto string = (*expr)[1].getAsString()) {
      if (string->empty() || !zkc::encoding::inEncodingDomain(*string))
        return file.error(context + " has an invalid constant string");
      return Error::success();
    }
    if ((*expr)[1].getAsInteger())
      return Error::success();
    return file.error(context + " constants must be strings or integers");
  }
  if (expr->size() < 2)
    return file.error(context + " has an empty operator");
  for (const json::Value &child : llvm::drop_begin(*expr))
    if (Error e = validateExpr(file, child, operandRoles, context, depth + 1))
      return e;
  return Error::success();
}

bool profileHasAnchor(const ClaimProfile &profile, StringRef anchor) {
  return llvm::is_contained(profile.anchors, anchor);
}

Error validateProducerSource(
    const RegistryFile &file, const AttachmentSource &source,
    const ReductionContract &contract,
    const std::map<std::string, ClaimProfile, std::less<>> &profiles,
    const Twine &context) {
  auto consumedHasAnchor = [&](const VocabularyConsumePattern &pattern) {
    return profileHasAnchor(*lookup(profiles, pattern.profile), source.anchor);
  };
  switch (source.kind) {
  case AttachmentSourceKind::ProducerInputAnchor:
    if (contract.consumes.front().isVariadic()) {
      if (!consumedHasAnchor(contract.consumes.front()))
        return file.error(context + " references an unknown producer input "
                                    "anchor");
    } else {
      if (source.index >= contract.consumes.size())
        return file.error(context + " references an unknown producer input");
      if (!consumedHasAnchor(contract.consumes[source.index]))
        return file.error(context + " references an unknown producer input "
                                    "anchor");
    }
    break;
  case AttachmentSourceKind::ProducerInputsAnchor:
    for (const VocabularyConsumePattern &pattern : contract.consumes)
      if (!consumedHasAnchor(pattern))
        return file.error(context + " references an anchor not shared by all "
                                    "producer inputs");
    break;
  case AttachmentSourceKind::ProducerDependency:
    if (!llvm::any_of(contract.depSlots, [&](const VocabularyDepSlot &slot) {
          return slot.role == source.role;
        }))
      return file.error(context + " references an unknown producer dependency");
    break;
  case AttachmentSourceKind::ProducerMessage: {
    const VocabularyMessageRole *message = nullptr;
    for (const VocabularyRound &round : contract.rounds)
      for (const VocabularyMessageRole &candidate : round.messages)
        if (candidate.role == source.role)
          message = &candidate;
    if (!message)
      return file.error(context + " references an unknown producer message");
    if (message->multiplicity.isDynamic())
      return file.error(context +
                        " cannot select one producer message from a dynamic "
                        "message role");
    if (source.index >= message->multiplicity.exact)
      return file.error(context + " references an unknown producer message");
    break;
  }
  case AttachmentSourceKind::ProducerInputDescriptors:
    break;
  case AttachmentSourceKind::ClaimAnchor:
    llvm_unreachable("claim source is not a producer source");
  }
  return Error::success();
}

Expected<TerminalRule>
parseRule(const RegistryFile &file, StringRef id, const json::Value &value,
          const std::map<std::string, ClaimProfile, std::less<>> &profiles,
          const std::map<std::string, CheckContract, std::less<>> &contracts,
          const std::map<std::string, ReductionContract, std::less<>>
              &reductionContracts) {
  auto error = [&](const Twine &message) {
    return file.error("terminal rule '" + id + "' " + message);
  };
  const json::Object *object = value.getAsObject();
  if (!object)
    return error("must map to an object");
  if (Error e =
          file.requireClosedFields(*object,
                                   {"claim_profile", "producer", "checks",
                                    "attachments", "transparent_predicates"},
                                   "terminal rule '" + id + "'"))
    return std::move(e);

  TerminalRule rule;
  if (Error e = file.requireStringField(*object, "claim_profile",
                                        "terminal rule '" + id + "'",
                                        rule.claimProfile))
    return std::move(e);
  const ClaimProfile *claimProfile = lookup(profiles, rule.claimProfile);
  if (!claimProfile)
    return error("references unknown claim profile '" + rule.claimProfile +
                 "'");

  const ReductionContract *producerContract = nullptr;
  if (const json::Value *producerValue = object->get("producer")) {
    const json::Object *producer = producerValue->getAsObject();
    if (!producer)
      return error("producer must be an object");
    if (Error e =
            file.requireClosedFields(*producer, {"contract", "output"},
                                     "terminal rule '" + id + "' producer"))
      return std::move(e);
    TerminalProducerPin pin;
    if (Error e = file.requireStringField(*producer, "contract",
                                          "terminal rule '" + id + "' producer",
                                          pin.contract))
      return std::move(e);
    auto output = requireNonNegative(file, *producer, "output",
                                     "terminal rule '" + id + "' producer");
    if (!output)
      return output.takeError();
    pin.output = *output;
    producerContract = lookup(reductionContracts, pin.contract);
    if (!producerContract || pin.output >= producerContract->outputs.size())
      return error("has an invalid producer pin");
    if (producerContract->outputs[pin.output].profile != rule.claimProfile)
      return error("producer output disagrees with its claim profile");
    rule.producer = std::move(pin);
  }

  const json::Object *checks = object->getObject("checks");
  if (!checks || checks->empty())
    return error("checks must be a non-empty object");
  for (const auto &entry : *checks) {
    StringRef role(entry.first);
    if (Error e = requireEntryName(file, "terminal check role", role))
      return std::move(e);
    auto contractId = entry.second.getAsString();
    if (!contractId || contractId->empty() ||
        !zkc::encoding::inEncodingDomain(*contractId))
      return error("check role '" + role + "' needs a contract id");
    if (!lookup(contracts, *contractId))
      return error("references unknown check contract '" + *contractId + "'");
    rule.checks[role.str()] = contractId->str();
  }

  const json::Object *predicates = object->getObject("transparent_predicates");
  if (!predicates)
    return error("needs an object 'transparent_predicates'");
  std::set<std::string, std::less<>> transparentRoles;
  for (const auto &[role, contractId] : rule.checks)
    if (lookup(contracts, contractId)->isTransparent())
      transparentRoles.insert(role);
  if (predicates->size() != transparentRoles.size())
    return error("must define exactly its transparent predicates");
  for (const auto &entry : *predicates) {
    StringRef role(entry.first);
    if (!transparentRoles.count(role.str()))
      return error("must define exactly its transparent predicates");
    const CheckContract *contract =
        lookup(contracts, rule.checks.find(role)->second);
    StringSet<> operandRoles;
    for (const CheckOperandSegment &operand : contract->operands)
      operandRoles.insert(operand.role);
    const json::Array *root = entry.second.getAsArray();
    if (!root || root->size() != 3 || (*root)[0].getAsString() != "eq")
      return error("transparent predicate '" + role +
                   "' must be a binary equality");
    if (Error e = validateExpr(file, entry.second, operandRoles,
                               "terminal rule '" + id +
                                   "' transparent predicate '" + role + "'"))
      return std::move(e);
    rule.transparentPredicates.insert_or_assign(role.str(), entry.second);
  }

  const json::Array *attachments = object->getArray("attachments");
  if (!attachments || attachments->empty())
    return error("attachments must be a non-empty array");
  StringSet<> encodedAttachments;
  std::vector<std::pair<std::string, TerminalAttachment>> admittedAttachments;
  std::set<std::pair<std::string, std::string>> targets;
  StringSet<> coveredAnchors;
  // A producer-pinned rule receives an already reconstructed descriptor from
  // ReductionClosure. Terminal closure must connect the closing check, not
  // re-derive the same output anchors through a second attachment language.
  if (producerContract)
    for (const std::string &anchor : claimProfile->anchors)
      coveredAnchors.insert(anchor);
  StringSet<> targetedChecks;
  std::map<std::string, StringSet<>, std::less<>> semanticCoverage;
  for (const auto &[index, member] : llvm::enumerate(*attachments)) {
    std::string context =
        ("terminal rule '" + id + "' attachment " + Twine(index)).str();
    auto attachment = parseAttachment(file, member, context);
    if (!attachment)
      return attachment.takeError();
    auto bytes = canonicalBytes(attachment->toCanonicalJson());
    if (!bytes)
      return bytes.takeError();
    if (!encodedAttachments.insert(*bytes).second)
      return error("repeats an attachment");

    bool producerSource =
        attachment->source.kind != AttachmentSourceKind::ClaimAnchor;
    if (producerSource) {
      if (!producerContract)
        return file.error(context + " requires a producer-pinned rule");
      if (Error e = validateProducerSource(
              file, attachment->source, *producerContract, profiles, context))
        return std::move(e);
    } else {
      if (!profileHasAnchor(*claimProfile, attachment->source.anchor))
        return file.error(context + " references an unknown claim anchor");
      coveredAnchors.insert(attachment->source.anchor);
    }

    switch (attachment->kind) {
    case TerminalAttachmentKind::SemanticParameter:
      if (attachment->source.kind != AttachmentSourceKind::ClaimAnchor &&
          attachment->source.kind != AttachmentSourceKind::ProducerInputAnchor)
        return file.error(context + " has an incompatible attachment source");
      break;
    case TerminalAttachmentKind::MaterialRefEquality:
      if (attachment->source.kind != AttachmentSourceKind::ClaimAnchor &&
          attachment->source.kind != AttachmentSourceKind::ProducerInputAnchor)
        return file.error(context + " has an incompatible attachment source");
      break;
    case TerminalAttachmentKind::ValueIdentity:
      if (attachment->source.kind != AttachmentSourceKind::ProducerDependency &&
          attachment->source.kind != AttachmentSourceKind::ProducerMessage)
        return file.error(context + " has an incompatible attachment source");
      break;
    case TerminalAttachmentKind::MaterialRefVectorEquality:
      if (attachment->source.kind != AttachmentSourceKind::ProducerInputsAnchor)
        return file.error(context + " has an incompatible attachment source");
      break;
    case TerminalAttachmentKind::CommonMaterialRefEquality:
      if (attachment->source.kind != AttachmentSourceKind::ProducerInputsAnchor)
        return file.error(context + " has an incompatible attachment source");
      if (!profileHasAnchor(*claimProfile, attachment->claimAnchor))
        return file.error(context + " references an unknown common claim "
                                    "anchor");
      coveredAnchors.insert(attachment->claimAnchor);
      break;
    case TerminalAttachmentKind::DescriptorDigest:
      if (attachment->source.kind !=
          AttachmentSourceKind::ProducerInputDescriptors)
        return file.error(context + " has an incompatible attachment source");
      if (!profileHasAnchor(*claimProfile, attachment->claimAnchor))
        return file.error(context + " references an unknown output anchor");
      coveredAnchors.insert(attachment->claimAnchor);
      admittedAttachments.emplace_back(std::move(*bytes),
                                       std::move(*attachment));
      continue;
    }

    auto check = rule.checks.find(attachment->checkRole);
    if (check == rule.checks.end())
      return file.error(context + " references an unknown terminal check role");
    const CheckContract *contract = lookup(contracts, check->second);
    targetedChecks.insert(attachment->checkRole);
    auto target = std::make_pair(attachment->checkRole, attachment->targetRole);
    if (!targets.insert(target).second)
      return error("constrains one check role twice");
    if (attachment->kind == TerminalAttachmentKind::SemanticParameter) {
      if (!llvm::is_contained(contract->semanticParameters,
                              attachment->targetRole))
        return file.error(context +
                          " references an unknown semantic parameter");
      semanticCoverage[attachment->checkRole].insert(attachment->targetRole);
    } else if (!llvm::any_of(contract->operands,
                             [&](const CheckOperandSegment &operand) {
                               return operand.role == attachment->targetRole;
                             })) {
      return file.error(context + " references an unknown operand role");
    }
    admittedAttachments.emplace_back(std::move(*bytes), std::move(*attachment));
  }

  if (coveredAnchors.size() != claimProfile->anchors.size())
    return error("does not cover exactly its claim anchors");
  for (const std::string &anchor : claimProfile->anchors)
    if (!coveredAnchors.contains(anchor))
      return error("does not cover exactly its claim anchors");
  for (const auto &[role, contractId] : rule.checks) {
    const CheckContract *contract = lookup(contracts, contractId);
    if (!targetedChecks.contains(role))
      return error("contains an unattached terminal check role '" + role + "'");
    const StringSet<> &covered = semanticCoverage[role];
    if (covered.size() != contract->semanticParameters.size())
      return error("does not cover every semantic parameter");
    for (const std::string &parameter : contract->semanticParameters)
      if (!covered.contains(parameter))
        return error("does not cover every semantic parameter");
  }

  // Attachments form a set of named relations. Normalize them by their
  // canonical bytes so author order cannot perturb rule or artifact identity.
  llvm::sort(admittedAttachments, [](const auto &left, const auto &right) {
    return left.first < right.first;
  });
  for (auto &entry : admittedAttachments)
    rule.attachments.push_back(std::move(entry.second));

  auto digest = digestRule(rule, profiles, contracts, reductionContracts);
  if (!digest)
    return digest.takeError();
  rule.digest = std::move(*digest);
  return rule;
}

/// The vocabulary's envelope carries seven named sections, so it walks
/// them itself rather than through RegistryBase::parse. The walk is the
/// shared one — same name gate, same order — with the one thing these
/// call sites all want added: the admitted entry lands in the section's
/// map.
template <typename Entry, typename Parse>
Error parseEntries(const RegistryFile &file, StringRef section,
                   const json::Object &object,
                   std::map<std::string, Entry, std::less<>> &out,
                   Parse &&parse) {
  return parseSection(file, object, section,
                      [&](const RegistryFile &, StringRef id,
                          const json::Value &value) -> Error {
                        auto entry = parse(id, value);
                        if (!entry)
                          return entry.takeError();
                        out[id.str()] = std::move(*entry);
                        return Error::success();
                      });
}

} // namespace

json::Value ClaimProfile::toCanonicalJson() const {
  return json::Object{{"anchors", json::Array(anchors)}, {"kind", kind}};
}

json::Value ValueProfile::toCanonicalJson() const {
  return json::Object{{"arity_log2", arityLog2},
                      {"binding_route", bindingRoute},
                      {"element_class", elementClass},
                      {"origin", origin}};
}

json::Value OperandMultiplicity::toCanonicalJson() const {
  switch (kind) {
  case OperandMultiplicityKind::Exact:
    return json::Object{{"exact", static_cast<int64_t>(value)}};
  case OperandMultiplicityKind::Capture:
    return json::Object{{"capture", name},
                        {"min", static_cast<int64_t>(value)}};
  case OperandMultiplicityKind::SameAs:
    return json::Object{{"same_as", name}};
  }
  llvm_unreachable("unknown operand multiplicity");
}

json::Value CheckOperandSegment::toCanonicalJson() const {
  return json::Object{{"class", valueClass},
                      {"multiplicity", multiplicity.toCanonicalJson()},
                      {"role", role}};
}

json::Value CheckPredicateEntrypoint::toCanonicalJson() const {
  json::Array operandJson;
  for (const CheckOperandSegment &operand : operands)
    operandJson.push_back(operand.toCanonicalJson());
  return json::Object{{"acceptance", json::Array(acceptance)},
                      {"operands", std::move(operandJson)},
                      {"parameters", json::Array(parameters)},
                      {"semantic_parameters", json::Array(semanticParameters)}};
}

json::Value CheckPredicateSpec::toCanonicalJson() const {
  json::Object entrypointJson;
  for (const auto &[name, entrypoint] : entrypoints)
    entrypointJson[name] = entrypoint.toCanonicalJson();
  json::Object body{{"entrypoints", std::move(entrypointJson)},
                    {"format", "zkc-check-predicate-spec"},
                    {"title", title}};
  if (references)
    body["references"] = json::Array(*references);
  return body;
}

json::Value CheckPredicateDescriptor::toCanonicalJson() const {
  if (format == CheckPredicateFormat::TransparentExpressionV1)
    return json::Object{{"format", "zkc-transparent-expression"}};
  return json::Object{{"content_digest", contentDigest},
                      {"entrypoint", entrypoint},
                      {"format", "zkc-opaque-predicate-spec"}};
}

json::Value CheckContract::toCanonicalJson() const {
  json::Array operandJson;
  for (const CheckOperandSegment &operand : operands)
    operandJson.push_back(operand.toCanonicalJson());
  return json::Object{
      {"mode", mode == CheckMode::Opaque ? "opaque" : "transparent"},
      {"operands", std::move(operandJson)},
      {"parameters", json::Array(parameters)},
      {"predicate", predicate.toCanonicalJson()},
      {"semantic_parameters", json::Array(semanticParameters)}};
}

json::Value HoleSegment::toCanonicalJson() const {
  json::Object body{{"role", role}};
  switch (sort) {
  case HoleSegmentSort::Value:
    body["sort"] = "value";
    body["class"] = typeClass;
    body["count"] = count;
    break;
  case HoleSegmentSort::Handle:
    body["sort"] = "handle";
    body["class"] = typeClass;
    break;
  case HoleSegmentSort::Sponge:
    body["sort"] = "sponge";
    break;
  }
  return body;
}

json::Value HoleContract::toCanonicalJson() const {
  json::Array operandJson, resultJson;
  for (const HoleSegment &operand : operands)
    operandJson.push_back(operand.toCanonicalJson());
  for (const HoleSegment &result : results)
    resultJson.push_back(result.toCanonicalJson());
  return json::Object{{"kind", kind},
                      {"operands", std::move(operandJson)},
                      {"parameters", json::Array(parameters)},
                      {"results", std::move(resultJson)},
                      {"semantic_parameters", json::Array(semanticParameters)}};
}

json::Value MessageMultiplicity::toCanonicalJson() const {
  if (kind == MessageMultiplicityKind::ConsumedClaims)
    return json::Object{{"same_as", "consumed_claims"}};
  return json::Object{{"exact", static_cast<int64_t>(exact)}};
}

json::Value VocabularyChallengeUse::toCanonicalJson() const {
  json::Object body{{"role", role}};
  if (count)
    body["count"] = static_cast<int64_t>(count);
  return body;
}

json::Value MaterialExpr::toCanonicalJson() const {
  auto orderName = [&]() -> StringRef {
    return order == MaterialOrder::Operand ? "operand" : "canonical_unique";
  };
  switch (kind) {
  case MaterialExprKind::LiteralRef:
    return json::Object{{"kind", "literal_ref"}, {"value", name}};
  case MaterialExprKind::InputAnchor:
    return json::Object{{"anchor", name},
                        {"input", static_cast<int64_t>(index)},
                        {"kind", "input_anchor"}};
  case MaterialExprKind::Dependency:
    return json::Object{{"kind", "dependency"}, {"role", name}};
  case MaterialExprKind::Message:
    return json::Object{{"kind", "message"},
                        {"occurrence", static_cast<int64_t>(index)},
                        {"role", name}};
  case MaterialExprKind::ParameterRef:
    return json::Object{{"kind", "parameter_ref"}, {"name", name}};
  case MaterialExprKind::Construct: {
    json::Array args;
    for (const MaterialExpr &argument : arguments)
      args.push_back(argument.toCanonicalJson());
    return json::Object{
        {"args", std::move(args)}, {"kind", "construct"}, {"tag", name}};
  }
  case MaterialExprKind::InputAnchors:
    return json::Object{
        {"anchor", name}, {"kind", "input_anchors"}, {"order", orderName()}};
  case MaterialExprKind::Messages:
    return json::Object{{"kind", "messages"}, {"role", name}};
  case MaterialExprKind::ParameterRefs:
    return json::Object{{"kind", "parameter_refs"}, {"name", name}};
  case MaterialExprKind::List: {
    json::Array items;
    for (const MaterialExpr &item : arguments)
      items.push_back(item.toCanonicalJson());
    return json::Object{{"items", std::move(items)}, {"kind", "list"}};
  }
  case MaterialExprKind::InputDescriptor:
    return json::Object{{"input", static_cast<int64_t>(index)},
                        {"kind", "input_descriptor"}};
  case MaterialExprKind::InputDescriptors:
    return json::Object{{"kind", "input_descriptors"}, {"order", orderName()}};
  case MaterialExprKind::ParameterAtom:
    return json::Object{{"kind", "parameter_atom"}, {"name", name}};
  case MaterialExprKind::Literal:
    return json::Object{{"kind", "literal"}, {"value", literal}};
  }
  llvm_unreachable("unknown material-expression kind");
}

json::Value ReductionCheckAttachment::toCanonicalJson() const {
  StringRef kindName;
  switch (kind) {
  case ReductionCheckAttachmentKind::SemanticParameter:
    kindName = "semantic_parameter";
    break;
  case ReductionCheckAttachmentKind::MaterialRefEquality:
    kindName = "material_ref_equality";
    break;
  case ReductionCheckAttachmentKind::ValueIdentity:
    kindName = "value_identity";
    break;
  case ReductionCheckAttachmentKind::MaterialRefVectorEquality:
    kindName = "material_ref_vector_equality";
    break;
  case ReductionCheckAttachmentKind::CommonMaterialRefEquality:
    kindName = "common_material_ref_equality";
    break;
  case ReductionCheckAttachmentKind::ValueIdentityVector:
    kindName = "value_identity_vector";
    break;
  case ReductionCheckAttachmentKind::ValueIdentityList:
    kindName = "value_identity_list";
    break;
  }
  return json::Object{{"kind", kindName},
                      {"source", source.toCanonicalJson()},
                      {"target_role", targetRole}};
}

json::Value BodyCheckSlot::toCanonicalJson() const {
  json::Object parameterJson;
  for (const auto &[name, value] : parameters)
    parameterJson[name] = value;
  json::Array attachmentJson;
  for (const ReductionCheckAttachment &attachment : attachments)
    attachmentJson.push_back(attachment.toCanonicalJson());
  json::Object body{{"attachments", std::move(attachmentJson)},
                    {"contract", contract},
                    {"parameters", std::move(parameterJson)}};
  if (transparentPredicate)
    body["transparent_predicate"] = *transparentPredicate;
  return body;
}

json::Value MaterialConstraint::toCanonicalJson() const {
  return json::Object{{"kind", "equal"},
                      {"left", left.toCanonicalJson()},
                      {"right", right.toCanonicalJson()}};
}

json::Value ReductionOutputConstructor::toCanonicalJson() const {
  json::Object anchorJson;
  for (const auto &[name, expr] : anchors)
    anchorJson[name] = expr.toCanonicalJson();
  return json::Object{{"anchors", std::move(anchorJson)}, {"profile", profile}};
}

json::Value ReductionContract::toCanonicalJson() const {
  json::Array consumesJson, depSlotsJson, roundsJson;
  for (const VocabularyConsumePattern &pattern : consumes) {
    if (pattern.isVariadic())
      consumesJson.push_back(
          json::Object{{"min", static_cast<int64_t>(pattern.min)},
                       {"profile", pattern.profile}});
    else
      consumesJson.push_back(pattern.profile);
  }
  for (const VocabularyDepSlot &slot : depSlots) {
    StringRef source;
    switch (slot.source) {
    case VocabularyDepSource::Any:
      source = "any";
      break;
    case VocabularyDepSource::PublicBind:
      source = "public_bind";
      break;
    case VocabularyDepSource::ProverSlot:
      source = "prover_slot";
      break;
    case VocabularyDepSource::ChallengeCapability:
      source = "challenge_capability";
      break;
    }
    json::Object body{
        {"class", slot.payloadClass}, {"role", slot.role}, {"source", source}};
    depSlotsJson.push_back(std::move(body));
  }
  for (const VocabularyRound &round : rounds) {
    json::Array messages;
    for (const VocabularyMessageRole &message : round.messages)
      messages.push_back(
          json::Object{{"count", message.multiplicity.toCanonicalJson()},
                       {"role", message.role}});
    json::Object body{{"challenge_use", round.challengeUse.toCanonicalJson()},
                      {"messages", std::move(messages)}};
    if (!round.kind.empty())
      body["kind"] = round.kind;
    roundsJson.push_back(std::move(body));
  }
  json::Object parameterJson;
  for (const auto &[name, sort] : parameters) {
    StringRef sortName;
    switch (sort) {
    case ReductionParameterSort::Atom:
      sortName = "atom";
      break;
    case ReductionParameterSort::MaterialRef:
      sortName = "material_ref";
      break;
    case ReductionParameterSort::MaterialRefVector:
      sortName = "material_ref_vector";
      break;
    }
    parameterJson[name] = sortName;
  }
  json::Object checkJson;
  for (const auto &[role, slot] : checks)
    checkJson[role] = slot.toCanonicalJson();
  json::Array constraintJson;
  for (const MaterialConstraint &constraint : constraints)
    constraintJson.push_back(constraint.toCanonicalJson());
  json::Array outputJson;
  for (const ReductionOutputConstructor &output : outputs)
    outputJson.push_back(output.toCanonicalJson());
  return json::Object{{"checks", std::move(checkJson)},
                      {"constraints", std::move(constraintJson)},
                      {"consumes", std::move(consumesJson)},
                      {"dep_slots", std::move(depSlotsJson)},
                      {"outputs", std::move(outputJson)},
                      {"parameters", std::move(parameterJson)},
                      {"rounds", std::move(roundsJson)}};
}

json::Value AttachmentSource::toCanonicalJson() const {
  switch (kind) {
  case AttachmentSourceKind::ClaimAnchor:
    return json::Object{{"anchor", anchor}, {"kind", "claim_anchor"}};
  case AttachmentSourceKind::ProducerInputAnchor:
    return json::Object{{"anchor", anchor},
                        {"input", static_cast<int64_t>(index)},
                        {"kind", "producer_input_anchor"}};
  case AttachmentSourceKind::ProducerInputsAnchor:
    return json::Object{{"anchor", anchor}, {"kind", "producer_inputs_anchor"}};
  case AttachmentSourceKind::ProducerInputDescriptors:
    return json::Object{{"kind", "producer_input_descriptors"}};
  case AttachmentSourceKind::ProducerDependency:
    return json::Object{{"kind", "producer_dependency"}, {"role", role}};
  case AttachmentSourceKind::ProducerMessage:
    return json::Object{{"index", static_cast<int64_t>(index)},
                        {"kind", "producer_message"},
                        {"role", role}};
  }
  llvm_unreachable("unknown attachment source");
}

json::Value TerminalAttachment::toCanonicalJson() const {
  switch (kind) {
  case TerminalAttachmentKind::SemanticParameter:
    return json::Object{{"check", checkRole},
                        {"kind", "semantic_parameter"},
                        {"role", targetRole},
                        {"source", source.toCanonicalJson()}};
  case TerminalAttachmentKind::MaterialRefEquality:
    return json::Object{{"check", checkRole},
                        {"kind", "material_ref_equality"},
                        {"role", targetRole},
                        {"source", source.toCanonicalJson()}};
  case TerminalAttachmentKind::ValueIdentity:
    return json::Object{{"check", checkRole},
                        {"kind", "value_identity"},
                        {"role", targetRole},
                        {"source", source.toCanonicalJson()}};
  case TerminalAttachmentKind::MaterialRefVectorEquality:
    return json::Object{{"check", checkRole},
                        {"kind", "material_ref_vector_equality"},
                        {"role", targetRole},
                        {"source", source.toCanonicalJson()}};
  case TerminalAttachmentKind::CommonMaterialRefEquality:
    return json::Object{{"check", checkRole},
                        {"claim_anchor", claimAnchor},
                        {"kind", "common_material_ref_equality"},
                        {"role", targetRole},
                        {"source", source.toCanonicalJson()}};
  case TerminalAttachmentKind::DescriptorDigest:
    return json::Object{{"anchor", claimAnchor},
                        {"kind", "descriptor_digest"},
                        {"source", source.toCanonicalJson()}};
  }
  llvm_unreachable("unknown terminal attachment");
}

json::Value TerminalRule::toCanonicalJson() const {
  json::Object checksJson;
  for (const auto &[role, contract] : checks)
    checksJson[role] = contract;
  json::Array attachmentJson;
  for (const TerminalAttachment &attachment : attachments)
    attachmentJson.push_back(attachment.toCanonicalJson());
  json::Object predicatesJson;
  for (const auto &[role, predicate] : transparentPredicates)
    predicatesJson[role] = predicate;
  json::Object body{{"attachments", std::move(attachmentJson)},
                    {"checks", std::move(checksJson)},
                    {"claim_profile", claimProfile},
                    {"transparent_predicates", std::move(predicatesJson)}};
  if (producer)
    body["producer"] =
        json::Object{{"contract", producer->contract},
                     {"output", static_cast<int64_t>(producer->output)}};
  return body;
}

Expected<ProtocolVocabulary> ProtocolVocabulary::loadFromFile(StringRef path) {
  auto buffer = RegistryFile::readFile(path);
  if (!buffer)
    return buffer.takeError();
  return parse((*buffer)->getBuffer(), path);
}

Expected<ProtocolVocabulary> ProtocolVocabulary::parse(StringRef json,
                                                       StringRef sourceName) {
  auto file = RegistryFile::parse(
      json, sourceName, "zkc.protocol_vocabulary", "claim_profiles",
      {"predicate_specs", "check_contracts", "hole_contracts",
       "reduction_contracts", "terminal_rules", "value_profiles"});
  if (!file)
    return file.takeError();
  const json::Object *predicateSpecs = file->extra("predicate_specs");
  const json::Object *contracts = file->extra("check_contracts");
  const json::Object *holeContracts = file->extra("hole_contracts");
  const json::Object *reductionContracts = file->extra("reduction_contracts");
  const json::Object *rules = file->extra("terminal_rules");
  const json::Object *valueProfiles = file->extra("value_profiles");
  if (!predicateSpecs)
    return file->error("'predicate_specs' must be an object");
  if (!contracts)
    return file->error("'check_contracts' must be an object");
  if (!holeContracts)
    return file->error("'hole_contracts' must be an object");
  if (!reductionContracts)
    return file->error("'reduction_contracts' must be an object");
  if (!rules)
    return file->error("'terminal_rules' must be an object");
  if (!valueProfiles)
    return file->error("'value_profiles' must be an object");

  ProtocolVocabulary vocabulary;
  if (Error e = parseEntries(*file, "claim profile", file->payload(),
                             vocabulary.profiles_,
                             [&](StringRef id, const json::Value &value) {
                               return parseProfile(*file, id, value);
                             }))
    return std::move(e);
  if (Error e = parseEntries(*file, "value profile", *valueProfiles,
                             vocabulary.valueProfiles_,
                             [&](StringRef id, const json::Value &value) {
                               return parseValueProfile(*file, id, value);
                             }))
    return std::move(e);
  if (Error e = parseEntries(*file, "predicate spec", *predicateSpecs,
                             vocabulary.predicateSpecs_,
                             [&](StringRef id, const json::Value &value) {
                               return parsePredicateSpec(*file, id, value);
                             }))
    return std::move(e);
  if (Error e = parseEntries(
          *file, "check contract", *contracts, vocabulary.checkContracts_,
          [&](StringRef id, const json::Value &value) {
            return parseContract(*file, id, value, vocabulary.predicateSpecs_);
          }))
    return std::move(e);
  if (Error e = parseEntries(*file, "hole contract", *holeContracts,
                             vocabulary.holeContracts_,
                             [&](StringRef id, const json::Value &value) {
                               return parseHoleContract(*file, id, value);
                             }))
    return std::move(e);
  StringSet<> citedPredicateSpecs;
  for (const auto &[id, contract] : vocabulary.checkContracts_)
    if (contract.mode == CheckMode::Opaque)
      citedPredicateSpecs.insert(contract.predicate.contentDigest);
  for (const auto &[digest, spec] : vocabulary.predicateSpecs_)
    if (!citedPredicateSpecs.contains(digest))
      return file->error("predicate spec '" + digest +
                         "' is not cited by any opaque check contract");
  if (Error e = parseEntries(*file, "reduction contract", *reductionContracts,
                             vocabulary.reductionContracts_,
                             [&](StringRef id, const json::Value &value) {
                               return parseReductionContract(
                                   *file, id, value, vocabulary.profiles_,
                                   vocabulary.checkContracts_);
                             }))
    return std::move(e);
  if (Error e = parseEntries(*file, "terminal rule", *rules, vocabulary.rules_,
                             [&](StringRef id, const json::Value &value) {
                               return parseRule(*file, id, value,
                                                vocabulary.profiles_,
                                                vocabulary.checkContracts_,
                                                vocabulary.reductionContracts_);
                             }))
    return std::move(e);

  return vocabulary;
}

const ClaimProfile *ProtocolVocabulary::lookupProfile(StringRef id) const {
  return lookup(profiles_, id);
}

const ValueProfile *
ProtocolVocabulary::lookupValueProfile(StringRef id) const {
  return lookup(valueProfiles_, id);
}


const CheckContract *
ProtocolVocabulary::lookupCheckContract(StringRef id) const {
  return lookup(checkContracts_, id);
}

const HoleContract *ProtocolVocabulary::lookupHoleContract(StringRef id) const {
  return lookup(holeContracts_, id);
}

const ReductionContract *
ProtocolVocabulary::lookupReductionContract(StringRef id) const {
  return lookup(reductionContracts_, id);
}

const TerminalRule *ProtocolVocabulary::lookupRule(StringRef id) const {
  return lookup(rules_, id);
}

json::Value ProtocolVocabulary::toCanonicalJson() const {
  json::Object profileJson, predicateSpecJson, checkContractJson,
      holeContractJson, reductionContractJson, ruleJson, valueProfileJson;
  for (const auto &[id, profile] : profiles_)
    profileJson[id] = profile.toCanonicalJson();
  for (const auto &[id, profile] : valueProfiles_)
    valueProfileJson[id] = profile.toCanonicalJson();
  for (const auto &[digest, spec] : predicateSpecs_)
    predicateSpecJson[digest] = spec.toCanonicalJson();
  for (const auto &[id, contract] : checkContracts_)
    checkContractJson[id] = contract.toCanonicalJson();
  for (const auto &[id, contract] : holeContracts_)
    holeContractJson[id] = contract.toCanonicalJson();
  for (const auto &[id, contract] : reductionContracts_)
    reductionContractJson[id] = contract.toCanonicalJson();
  for (const auto &[id, rule] : rules_)
    ruleJson[id] = rule.toCanonicalJson();
  return json::Object{{"check_contracts", std::move(checkContractJson)},
                      {"claim_profiles", std::move(profileJson)},
                      {"hole_contracts", std::move(holeContractJson)},
                      {"predicate_specs", std::move(predicateSpecJson)},
                      {"reduction_contracts", std::move(reductionContractJson)},
                      {"registry", "zkc.protocol_vocabulary"},
                      {"terminal_rules", std::move(ruleJson)},
                      {"value_profiles", std::move(valueProfileJson)}};
}
