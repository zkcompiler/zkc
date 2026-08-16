//===- SignatureFile.cpp - Reading a signature ---------------------------===//
#include "zkc/Soundness/SignatureFile.h"

#include "zkc/Encoding/EncodingDomain.h"
#include "zkc/Registry/RegistryFile.h"
#include "zkc/Soundness/SignatureEncoding.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <optional>
#include <string>
#include <utility>
#include <vector>

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

constexpr llvm::StringLiteral kRegistryName = "zkc.soundness_signature";

/// Reading state: the parsed file plus the diagnostics that name it.
class Reader {
public:
  explicit Reader(registry::RegistryFile file) : file(std::move(file)) {}

  const registry::RegistryFile &registryFile() const { return file; }

  Error fail(const Twine &message) const { return file.error(message); }

  template <typename T> Expected<T> failed(const Twine &message) const {
    return file.error(message);
  }

  Error closed(const Object &object, ArrayRef<StringRef> allowed,
               const Twine &context) const {
    return file.requireClosedFields(object, allowed, context);
  }

  Expected<StringRef> string(const Object &object, StringRef key,
                             const Twine &context) const {
    return file.requireString(object, key, context);
  }

  /// A string field that is allowed to be absent or empty.  Absent means
  /// empty; present-but-not-a-string does not, because reading a number as
  /// the empty string would make an author's mistake look like a decision
  /// they made deliberately.
  Expected<std::string> optionalString(const Object &object, StringRef key,
                                       const Twine &context) const {
    const llvm::json::Value *value = object.get(key);
    if (!value)
      return std::string();
    std::optional<StringRef> text = value->getAsString();
    if (!text)
      return failed<std::string>(context + " needs a string '" + key + "'");
    if (!text->empty() && !encoding::inEncodingDomain(*text))
      return failed<std::string>(context +
                                 " needs an empty or printable-ASCII "
                                 "string '" +
                                 key + "'");
    return text->str();
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

private:
  registry::RegistryFile file;
};

template <typename T>
Expected<T> lookupEnum(const Reader &reader, StringRef text,
                       ArrayRef<std::pair<StringRef, T>> table,
                       const Twine &what) {
  for (const auto &entry : table)
    if (entry.first == text)
      return entry.second;
  return reader.template failed<T>(what + " has unknown value '" + text + "'");
}

Expected<ValueSort> readValueSort(const Reader &reader, StringRef text,
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
  return lookupEnum<ValueSort>(reader, text, table, context + " sort");
}

Expected<std::vector<ValueSort>> readValueSorts(const Reader &reader,
                                                const Object &parent,
                                                StringRef key,
                                                const Twine &context) {
  auto items = reader.array(parent, key, context);
  if (!items)
    return items.takeError();
  std::vector<ValueSort> sorts;
  for (const Value &item : **items) {
    std::optional<StringRef> text = item.getAsString();
    if (!text)
      return reader.failed<std::vector<ValueSort>>(context + " '" + key +
                                                   "' entries must be strings");
    auto sort = readValueSort(reader, *text, context);
    if (!sort)
      return sort.takeError();
    sorts.push_back(*sort);
  }
  return sorts;
}

Expected<std::vector<TypedDeclaration>>
readTypedDeclarations(const Reader &reader, const Object &parent, StringRef key,
                      const Twine &context) {
  auto items = reader.array(parent, key, context);
  if (!items)
    return items.takeError();
  std::vector<TypedDeclaration> declarations;
  for (const Value &item : **items) {
    const Object *entry = item.getAsObject();
    if (!entry)
      return reader.failed<std::vector<TypedDeclaration>>(
          context + " '" + key + "' entries must be objects");
    if (Error err =
            reader.closed(*entry, {"name", "sort"}, context + " " + key))
      return std::move(err);
    auto name = reader.string(*entry, "name", context + " " + key);
    if (!name)
      return name.takeError();
    auto sortText = reader.string(*entry, "sort", context + " " + key);
    if (!sortText)
      return sortText.takeError();
    auto sort = readValueSort(reader, *sortText, context + " " + key);
    if (!sort)
      return sort.takeError();
    declarations.push_back(TypedDeclaration{name->str(), *sort});
  }
  return declarations;
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

Expected<SecurityIndex> readSecurityIndex(const Reader &reader,
                                          const Object &parent, StringRef key,
                                          const Twine &context) {
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
  static const std::pair<StringRef, SecurityTrack> tracks[] = {
      {"soundness", SecurityTrack::Soundness},
      {"knowledge", SecurityTrack::Knowledge},
      {"completeness", SecurityTrack::Completeness},
  };

  auto notionText = reader.string(**entry, "notion", where);
  if (!notionText)
    return notionText.takeError();
  auto notion = lookupEnum<SecurityNotion>(reader, *notionText, notions,
                                           where + " notion");
  if (!notion)
    return notion.takeError();
  auto trackText = reader.string(**entry, "track", where);
  if (!trackText)
    return trackText.takeError();
  auto track =
      lookupEnum<SecurityTrack>(reader, *trackText, tracks, where + " track");
  if (!track)
    return track.takeError();

  SecurityIndex index;
  index.notion = *notion;
  index.track = *track;
  auto variant = reader.optionalString(**entry, "variant", where);
  if (!variant)
    return variant.takeError();
  auto model = reader.optionalString(**entry, "model", where);
  if (!model)
    return model.takeError();
  index.variant = std::move(*variant);
  index.model = std::move(*model);
  return index;
}

Expected<ContractRoundSelector> readRoundSelector(const Reader &reader,
                                                  const Object &parent,
                                                  StringRef key,
                                                  const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();

  ContractRoundSelector selector;
  if (*kind == "all_contract_rounds") {
    if (Error err = reader.closed(**entry, {"kind"}, where))
      return std::move(err);
    selector.kind = ContractRoundSelectorKind::AllContractRounds;
    return selector;
  }
  if (*kind == "round_kind") {
    if (Error err = reader.closed(**entry, {"kind", "round_kind"}, where))
      return std::move(err);
    auto roundKind = reader.string(**entry, "round_kind", where);
    if (!roundKind)
      return roundKind.takeError();
    selector.kind = ContractRoundSelectorKind::RoundKind;
    selector.roundKind = roundKind->str();
    return selector;
  }
  if (*kind == "round_position") {
    if (Error err = reader.closed(**entry, {"kind", "position"}, where))
      return std::move(err);
    std::optional<int64_t> position = (*entry)->getInteger("position");
    if (!position || *position < 0)
      return reader.failed<ContractRoundSelector>(
          where + " needs a non-negative integer 'position'");
    selector.kind = ContractRoundSelectorKind::RoundPosition;
    selector.position = uint64_t(*position);
    return selector;
  }
  return reader.failed<ContractRoundSelector>(where +
                                              " has unknown round-selector "
                                              "kind '" +
                                              *kind + "'");
}

Expected<ArtifactProjection> readArtifactProjection(const Reader &reader,
                                                    const Object &entry,
                                                    const Twine &context) {
  auto kindText = reader.string(entry, "kind", context);
  if (!kindText)
    return kindText.takeError();
  static const std::pair<StringRef, ArtifactProjectionKind> kinds[] = {
      {"conclusion_reduction_contract",
       ArtifactProjectionKind::ConclusionReductionContract},
      {"contract_round_adjacency",
       ArtifactProjectionKind::ContractRoundAdjacency},
      {"reduction_input_count", ArtifactProjectionKind::ReductionInputCount},
      {"reduction_parameter", ArtifactProjectionKind::ReductionParameter},
      {"contract_round_family_field",
       ArtifactProjectionKind::ContractRoundFamilyField},
      {"path_binding_field", ArtifactProjectionKind::PathBindingField},
  };
  auto kind =
      lookupEnum<ArtifactProjectionKind>(reader, *kindText, kinds, context);
  if (!kind)
    return kind.takeError();
  auto sortText = reader.string(entry, "result_sort", context);
  if (!sortText)
    return sortText.takeError();
  auto sort = readValueSort(reader, *sortText, context + " result");
  if (!sort)
    return sort.takeError();

  ArtifactProjection projection;
  projection.kind = *kind;
  projection.resultSort = *sort;
  switch (*kind) {
  case ArtifactProjectionKind::ConclusionReductionContract:
  case ArtifactProjectionKind::ContractRoundAdjacency:
  case ArtifactProjectionKind::ReductionInputCount:
    if (Error err = reader.closed(entry, {"kind", "result_sort"}, context))
      return std::move(err);
    return projection;
  case ArtifactProjectionKind::ReductionParameter:
  case ArtifactProjectionKind::PathBindingField: {
    if (Error err =
            reader.closed(entry, {"kind", "result_sort", "field"}, context))
      return std::move(err);
    auto field = reader.string(entry, "field", context);
    if (!field)
      return field.takeError();
    projection.field = field->str();
    return projection;
  }
  case ArtifactProjectionKind::ContractRoundFamilyField: {
    if (Error err = reader.closed(
            entry,
            {"kind", "result_sort", "field", "round_selector", "aggregate"},
            context))
      return std::move(err);
    auto field = reader.string(entry, "field", context);
    if (!field)
      return field.takeError();
    projection.field = field->str();
    auto selector = readRoundSelector(reader, entry, "round_selector", context);
    if (!selector)
      return selector.takeError();
    projection.roundSelector = std::move(*selector);
    auto aggregate = reader.string(entry, "aggregate", context);
    if (!aggregate)
      return aggregate.takeError();
    if (*aggregate == "count")
      projection.aggregate = ProjectionAggregate::Count;
    else if (*aggregate == "unique_equal")
      projection.aggregate = ProjectionAggregate::UniqueEqual;
    else
      return reader.failed<ArtifactProjection>(
          context + " has unknown aggregate '" + *aggregate + "'");
    return projection;
  }
  }
  return reader.failed<ArtifactProjection>(context +
                                           " has an unhandled projection kind");
}

Expected<BindingValue> readBindingValue(const Reader &reader,
                                        const Object &entry,
                                        const Twine &context) {
  auto kindText = reader.string(entry, "kind", context);
  if (!kindText)
    return kindText.takeError();
  static const std::pair<StringRef, BindingValueKind> kinds[] = {
      {"literal", BindingValueKind::Literal},
      {"sealed_artifact_projection",
       BindingValueKind::SealedArtifactProjection},
      {"conclusion_subject", BindingValueKind::ConclusionSubject},
      {"application_path_transition",
       BindingValueKind::ApplicationPathTransition},
      {"conclusion_resource", BindingValueKind::ConclusionResource},
      {"resolved_parameter", BindingValueKind::ResolvedParameter},
  };
  auto kind = lookupEnum<BindingValueKind>(reader, *kindText, kinds, context);
  if (!kind)
    return kind.takeError();
  auto sortText = reader.string(entry, "sort", context);
  if (!sortText)
    return sortText.takeError();
  auto sort = readValueSort(reader, *sortText, context);
  if (!sort)
    return sort.takeError();

  BindingValue value;
  value.kind = *kind;
  value.sort = *sort;

  switch (*kind) {
  case BindingValueKind::Literal: {
    if (Error err = reader.closed(entry, {"kind", "sort", "literal"}, context))
      return std::move(err);
    const Value *literal = entry.get("literal");
    if (!literal)
      return reader.failed<BindingValue>(context + " needs a 'literal'");
    switch (*sort) {
    case ValueSort::Integer:
    case ValueSort::Rational: {
      std::optional<StringRef> text = literal->getAsString();
      if (!text)
        return reader.failed<BindingValue>(
            context + " needs a decimal string 'literal' for its numeric sort");
      auto number = readRational(reader, *text, context + " literal");
      if (!number)
        return number.takeError();
      value.literal = std::move(*number);
      return value;
    }
    case ValueSort::String: {
      std::optional<StringRef> text = literal->getAsString();
      if (!text)
        return reader.failed<BindingValue>(context +
                                           " needs a string 'literal'");
      value.literal = text->str();
      return value;
    }
    case ValueSort::Boolean: {
      std::optional<bool> flag = literal->getAsBoolean();
      if (!flag)
        return reader.failed<BindingValue>(context +
                                           " needs a boolean 'literal'");
      value.literal = *flag;
      return value;
    }
    case ValueSort::AlgebraInstance: {
      const Object *algebra = literal->getAsObject();
      if (!algebra)
        return reader.failed<BindingValue>(
            context + " needs an object 'literal' for an algebra instance");
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
      auto order = readRational(reader, *orderText, context + " field order");
      if (!order)
        return order.takeError();
      value.literal = AlgebraInstanceValue{group->str(), fieldClass->str(),
                                           std::move(*order)};
      return value;
    }
    default:
      return reader.failed<BindingValue>(context +
                                         " has no literal constructor for its "
                                         "sort");
    }
  }
  case BindingValueKind::SealedArtifactProjection: {
    if (Error err = reader.closed(
            entry, {"kind", "sort", "artifact_projection"}, context))
      return std::move(err);
    auto projectionEntry = reader.object(entry, "artifact_projection", context);
    if (!projectionEntry)
      return projectionEntry.takeError();
    auto projection = readArtifactProjection(reader, **projectionEntry,
                                             context + " projection");
    if (!projection)
      return projection.takeError();
    value.artifactProjection = std::move(*projection);
    return value;
  }
  case BindingValueKind::ConclusionSubject:
  case BindingValueKind::ApplicationPathTransition:
    if (Error err = reader.closed(entry, {"kind", "sort"}, context))
      return std::move(err);
    return value;
  case BindingValueKind::ConclusionResource:
  case BindingValueKind::ResolvedParameter: {
    if (Error err =
            reader.closed(entry, {"kind", "sort", "reference"}, context))
      return std::move(err);
    auto reference = reader.string(entry, "reference", context);
    if (!reference)
      return reference.takeError();
    value.reference = reference->str();
    return value;
  }
  }
  return reader.failed<BindingValue>(context + " has an unhandled value kind");
}

Expected<std::vector<BindingValue>> readBindingValues(const Reader &reader,
                                                      const Object &parent,
                                                      StringRef key,
                                                      const Twine &context) {
  auto items = reader.array(parent, key, context);
  if (!items)
    return items.takeError();
  std::vector<BindingValue> values;
  for (const Value &item : **items) {
    const Object *entry = item.getAsObject();
    if (!entry)
      return reader.failed<std::vector<BindingValue>>(
          context + " '" + key + "' entries must be objects");
    auto value = readBindingValue(reader, *entry, context + " " + key);
    if (!value)
      return value.takeError();
    values.push_back(std::move(*value));
  }
  return values;
}

Expected<QuantityTemplate>
readQuantity(const Reader &reader, const Object &entry, const Twine &context) {
  auto kindText = reader.string(entry, "kind", context);
  if (!kindText)
    return kindText.takeError();
  static const std::pair<StringRef, QuantityKind> kinds[] = {
      {"rational_literal", QuantityKind::RationalLiteral},
      {"parameter", QuantityKind::Parameter},
      {"artifact_fact", QuantityKind::ArtifactFact},
      {"contract_round_fact", QuantityKind::ContractRoundFact},
      {"premise_coordinate", QuantityKind::PremiseCoordinate},
      {"resource_variable", QuantityKind::ResourceVariable},
      {"add", QuantityKind::Add},
      {"sub", QuantityKind::Sub},
      {"mul", QuantityKind::Mul},
      {"div", QuantityKind::Div},
      {"pow", QuantityKind::Pow},
      {"pow2", QuantityKind::Pow2},
      {"pow2_up", QuantityKind::Pow2Up},
  };
  auto kind = lookupEnum<QuantityKind>(reader, *kindText, kinds, context);
  if (!kind)
    return kind.takeError();

  QuantityTemplate quantity;
  quantity.kind = *kind;
  switch (*kind) {
  case QuantityKind::RationalLiteral: {
    if (Error err = reader.closed(entry, {"kind", "literal"}, context))
      return std::move(err);
    auto text = reader.string(entry, "literal", context);
    if (!text)
      return text.takeError();
    auto number = readRational(reader, *text, context + " literal");
    if (!number)
      return number.takeError();
    quantity.literal = std::move(*number);
    return quantity;
  }
  case QuantityKind::Parameter:
  case QuantityKind::ArtifactFact:
  case QuantityKind::ResourceVariable: {
    if (Error err = reader.closed(entry, {"kind", "name"}, context))
      return std::move(err);
    auto name = reader.string(entry, "name", context);
    if (!name)
      return name.takeError();
    quantity.name = name->str();
    return quantity;
  }
  case QuantityKind::ContractRoundFact: {
    if (Error err =
            reader.closed(entry, {"kind", "case_name", "field"}, context))
      return std::move(err);
    auto caseName = reader.string(entry, "case_name", context);
    if (!caseName)
      return caseName.takeError();
    quantity.caseName = caseName->str();
    static const std::pair<StringRef, ContractRoundField> fields[] = {
        {"challenge_space", ContractRoundField::ChallengeSpace},
        {"challenge_count", ContractRoundField::ChallengeCount},
        {"round_degree", ContractRoundField::RoundDegree},
        {"challenge_space_log2", ContractRoundField::ChallengeSpaceLog2},
    };
    auto fieldText = reader.string(entry, "field", context);
    if (!fieldText)
      return fieldText.takeError();
    auto field = lookupEnum<ContractRoundField>(reader, *fieldText, fields,
                                                context + " field");
    if (!field)
      return field.takeError();
    quantity.contractRoundField = *field;
    return quantity;
  }
  case QuantityKind::PremiseCoordinate: {
    if (Error err = reader.closed(entry, {"kind", "port", "field", "selector"},
                                  context))
      return std::move(err);
    auto port = reader.string(entry, "port", context);
    if (!port)
      return port.takeError();
    quantity.port = port->str();
    auto fieldText = reader.string(entry, "field", context);
    if (!fieldText)
      return fieldText.takeError();
    if (*fieldText == "arity")
      quantity.premiseCoordinateField = PremiseCoordinateField::Arity;
    else if (*fieldText == "challenge_space")
      quantity.premiseCoordinateField = PremiseCoordinateField::ChallengeSpace;
    else
      return reader.failed<QuantityTemplate>(
          context + " has unknown premise-coordinate field '" + *fieldText +
          "'");
    auto selector = reader.object(entry, "selector", context);
    if (!selector)
      return selector.takeError();
    auto selectorKind =
        reader.string(**selector, "kind", context + " selector");
    if (!selectorKind)
      return selectorKind.takeError();
    if (*selectorKind == "bound_coordinate") {
      if (Error err =
              reader.closed(**selector, {"kind"}, context + " selector"))
        return std::move(err);
      quantity.premiseCoordinateSelector.kind =
          PremiseCoordinateSelectorKind::BoundCoordinate;
      return quantity;
    }
    return reader.failed<QuantityTemplate>(
        context + " has unknown coordinate selector '" + *selectorKind + "'");
  }
  case QuantityKind::Add:
  case QuantityKind::Sub:
  case QuantityKind::Mul:
  case QuantityKind::Div:
  case QuantityKind::Pow:
  case QuantityKind::Pow2:
  case QuantityKind::Pow2Up: {
    if (Error err = reader.closed(entry, {"kind", "operands"}, context))
      return std::move(err);
    auto operands = reader.array(entry, "operands", context);
    if (!operands)
      return operands.takeError();
    for (const Value &item : **operands) {
      const Object *operandEntry = item.getAsObject();
      if (!operandEntry)
        return reader.failed<QuantityTemplate>(context +
                                               " operands must be objects");
      auto operand = readQuantity(reader, *operandEntry, context + " operand");
      if (!operand)
        return operand.takeError();
      quantity.operands.push_back(std::move(*operand));
    }
    return quantity;
  }
  }
  return reader.failed<QuantityTemplate>(context + " has an unhandled kind");
}

Expected<std::optional<QuantityTemplate>>
readOptionalQuantity(const Reader &reader, const Object &parent, StringRef key,
                     const Twine &context) {
  const Value *value = parent.get(key);
  if (!value)
    return reader.failed<std::optional<QuantityTemplate>>(
        context + " needs a '" + key + "' (null when absent)");
  if (value->getAsNull())
    return std::optional<QuantityTemplate>();
  const Object *entry = value->getAsObject();
  if (!entry)
    return reader.failed<std::optional<QuantityTemplate>>(
        context + " '" + key + "' must be an object or null");
  auto quantity = readQuantity(reader, *entry, context + " " + key);
  if (!quantity)
    return quantity.takeError();
  return std::optional<QuantityTemplate>(std::move(*quantity));
}

Expected<std::map<std::string, QuantityTemplate, std::less<>>>
readQuantityMap(const Reader &reader, const Object &parent, StringRef key,
                const Twine &context) {
  using Map = std::map<std::string, QuantityTemplate, std::less<>>;
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  Map quantities;
  for (const auto &field : **entry) {
    const Object *value = field.second.getAsObject();
    if (!value)
      return reader.failed<Map>(context + " '" + key +
                                "' entries must be objects");
    auto quantity =
        readQuantity(reader, *value, context + " " + key + " entry");
    if (!quantity)
      return quantity.takeError();
    quantities.emplace(field.first.str(), std::move(*quantity));
  }
  return quantities;
}

Expected<RuleBound> readBound(const Reader &reader, const Object &entry,
                              const Twine &context) {
  auto kindText = reader.string(entry, "kind", context);
  if (!kindText)
    return kindText.takeError();

  auto readOperands = [&](RuleBound &bound) -> Error {
    auto operands = reader.array(entry, "operands", context);
    if (!operands)
      return operands.takeError();
    for (const Value &item : **operands) {
      const Object *operandEntry = item.getAsObject();
      if (!operandEntry)
        return reader.fail(context + " operands must be objects");
      auto operand = readBound(reader, *operandEntry, context + " operand");
      if (!operand)
        return operand.takeError();
      bound.operands.push_back(std::move(*operand));
    }
    return Error::success();
  };
  auto readQuantityField = [&](StringRef key, RuleBound &bound) -> Error {
    auto quantityEntry = reader.object(entry, key, context);
    if (!quantityEntry)
      return quantityEntry.takeError();
    auto quantity = readQuantity(reader, **quantityEntry, context + " " + key);
    if (!quantity)
      return quantity.takeError();
    bound.quantity = std::move(*quantity);
    return Error::success();
  };
  auto readPremisePort = [&](RuleBound &bound) -> Error {
    auto port = reader.string(entry, "premise_port", context);
    if (!port)
      return port.takeError();
    bound.premisePort = port->str();
    return Error::success();
  };

  RuleBound bound;
  if (*kindText == "quantity") {
    if (Error err = reader.closed(entry, {"kind", "quantity"}, context))
      return std::move(err);
    bound.kind = RuleBoundKind::Quantity;
    if (Error err = readQuantityField("quantity", bound))
      return std::move(err);
    return bound;
  }
  if (*kindText == "scalar_bound") {
    if (Error err = reader.closed(entry, {"kind", "premise_port"}, context))
      return std::move(err);
    bound.kind = RuleBoundKind::ScalarBound;
    if (Error err = readPremisePort(bound))
      return std::move(err);
    return bound;
  }
  if (*kindText == "primitive_advantage") {
    if (Error err = reader.closed(
            entry, {"kind", "game", "resource_substitution"}, context))
      return std::move(err);
    bound.kind = RuleBoundKind::PrimitiveAdvantage;
    auto game = reader.object(entry, "game", context);
    if (!game)
      return game.takeError();
    if (Error err = reader.closed(**game, {"ref", "instance_arguments"},
                                  context + " game"))
      return std::move(err);
    auto ref = reader.string(**game, "ref", context + " game");
    if (!ref)
      return ref.takeError();
    bound.game.gameRef = ref->str();
    auto arguments = readBindingValues(reader, **game, "instance_arguments",
                                       context + " game");
    if (!arguments)
      return arguments.takeError();
    bound.game.instanceArguments = std::move(*arguments);
    auto substitution =
        readQuantityMap(reader, entry, "resource_substitution", context);
    if (!substitution)
      return substitution.takeError();
    bound.gameResourceSubstitution = std::move(*substitution);
    return bound;
  }
  if (*kindText == "add" || *kindText == "max") {
    if (Error err = reader.closed(entry, {"kind", "operands"}, context))
      return std::move(err);
    bound.kind = *kindText == "add" ? RuleBoundKind::Add : RuleBoundKind::Max;
    if (Error err = readOperands(bound))
      return std::move(err);
    return bound;
  }
  if (*kindText == "scale") {
    if (Error err =
            reader.closed(entry, {"kind", "scale", "operands"}, context))
      return std::move(err);
    bound.kind = RuleBoundKind::Scale;
    if (Error err = readQuantityField("scale", bound))
      return std::move(err);
    if (Error err = readOperands(bound))
      return std::move(err);
    return bound;
  }
  return reader.failed<RuleBound>(context + " has unknown bound kind '" +
                                  *kindText + "'");
}

Expected<ContractLabelProjection> readLabelProjection(const Reader &reader,
                                                      const Object &parent,
                                                      StringRef key,
                                                      const Twine &context) {
  static const std::pair<StringRef, ContractLabelProjection> table[] = {
      {"round_index", ContractLabelProjection::RoundIndex},
      {"round_kind_occurrence", ContractLabelProjection::RoundKindOccurrence},
      {"case_name", ContractLabelProjection::CaseName},
      {"site_qualified_round_index",
       ContractLabelProjection::SiteQualifiedRoundIndex},
  };
  auto text = reader.string(parent, key, context);
  if (!text)
    return text.takeError();
  return lookupEnum<ContractLabelProjection>(reader, *text, table,
                                             context + " " + key);
}

Expected<CoordinateSequence> readCoordinateSequence(const Reader &reader,
                                                    const Object &parent,
                                                    StringRef key,
                                                    const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();

  CoordinateSequence sequence;
  if (*kind == "explicit") {
    if (Error err = reader.closed(**entry, {"kind", "coordinates"}, where))
      return std::move(err);
    sequence.kind = CoordinateSequence::Kind::Explicit;
    auto items = reader.array(**entry, "coordinates", where);
    if (!items)
      return items.takeError();
    for (const Value &item : **items) {
      const Object *coordinateEntry = item.getAsObject();
      if (!coordinateEntry)
        return reader.failed<CoordinateSequence>(
            where + " coordinates must be objects");
      if (Error err = reader.closed(
              *coordinateEntry, {"label", "arity", "challenge_space"}, where))
        return std::move(err);
      CoordinateTemplate coordinate;
      auto label = reader.string(*coordinateEntry, "label", where);
      if (!label)
        return label.takeError();
      coordinate.label = label->str();
      auto arityEntry = reader.object(*coordinateEntry, "arity", where);
      if (!arityEntry)
        return arityEntry.takeError();
      auto arity = readQuantity(reader, **arityEntry, where + " arity");
      if (!arity)
        return arity.takeError();
      coordinate.arity = std::move(*arity);
      auto space = readOptionalQuantity(reader, *coordinateEntry,
                                        "challenge_space", where);
      if (!space)
        return space.takeError();
      coordinate.challengeSpace = std::move(*space);
      sequence.coordinates.push_back(std::move(coordinate));
    }
    return sequence;
  }
  if (*kind == "contract") {
    if (Error err = reader.closed(
            **entry, {"kind", "contract_fact_port", "cases"}, where))
      return std::move(err);
    sequence.kind = CoordinateSequence::Kind::Contract;
    auto port = reader.string(**entry, "contract_fact_port", where);
    if (!port)
      return port.takeError();
    sequence.contractFactPort = port->str();
    auto items = reader.array(**entry, "cases", where);
    if (!items)
      return items.takeError();
    for (const Value &item : **items) {
      const Object *caseEntry = item.getAsObject();
      if (!caseEntry)
        return reader.failed<CoordinateSequence>(where +
                                                 " cases must be objects");
      if (Error err =
              reader.closed(*caseEntry,
                            {"case_name", "selector", "label_projection",
                             "arity", "challenge_space"},
                            where))
        return std::move(err);
      ContractCoordinateCase entry2;
      auto caseName = reader.string(*caseEntry, "case_name", where);
      if (!caseName)
        return caseName.takeError();
      entry2.caseName = caseName->str();
      auto selector = readRoundSelector(reader, *caseEntry, "selector", where);
      if (!selector)
        return selector.takeError();
      entry2.selector = std::move(*selector);
      auto projection =
          readLabelProjection(reader, *caseEntry, "label_projection", where);
      if (!projection)
        return projection.takeError();
      entry2.labelProjection = *projection;
      auto arityEntry = reader.object(*caseEntry, "arity", where);
      if (!arityEntry)
        return arityEntry.takeError();
      auto arity = readQuantity(reader, **arityEntry, where + " arity");
      if (!arity)
        return arity.takeError();
      entry2.arity = std::move(*arity);
      // A contract-derived coordinate resolves against a round that has a
      // challenge space, so the case reads one. Only an explicit coordinate
      // may omit it, and a rule that turns coordinates into rounds requires
      // every source coordinate to carry one (docs/spec/soundness.md §5.1).
      auto spaceEntry = reader.object(*caseEntry, "challenge_space", where);
      if (!spaceEntry)
        return spaceEntry.takeError();
      auto space =
          readQuantity(reader, **spaceEntry, where + " challenge space");
      if (!space)
        return space.takeError();
      entry2.challengeSpace = std::move(*space);
      sequence.cases.push_back(std::move(entry2));
    }
    return sequence;
  }
  return reader.failed<CoordinateSequence>(
      where + " has unknown coordinate-sequence kind '" + *kind + "'");
}

Expected<RoundSequence> readRoundSequence(const Reader &reader,
                                          const Object &parent, StringRef key,
                                          const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();

  RoundSequence sequence;
  if (*kind == "explicit") {
    if (Error err = reader.closed(**entry, {"kind", "rounds"}, where))
      return std::move(err);
    sequence.kind = RoundSequence::Kind::Explicit;
    auto items = reader.array(**entry, "rounds", where);
    if (!items)
      return items.takeError();
    for (const Value &item : **items) {
      const Object *roundEntry = item.getAsObject();
      if (!roundEntry)
        return reader.failed<RoundSequence>(where + " rounds must be objects");
      if (Error err = reader.closed(
              *roundEntry, {"round_index", "challenge_space", "bound"}, where))
        return std::move(err);
      RoundTemplate round;
      auto index = reader.string(*roundEntry, "round_index", where);
      if (!index)
        return index.takeError();
      round.roundIndex = index->str();
      auto spaceEntry = reader.object(*roundEntry, "challenge_space", where);
      if (!spaceEntry)
        return spaceEntry.takeError();
      auto space =
          readQuantity(reader, **spaceEntry, where + " challenge space");
      if (!space)
        return space.takeError();
      round.challengeSpace = std::move(*space);
      auto boundEntry = reader.object(*roundEntry, "bound", where);
      if (!boundEntry)
        return boundEntry.takeError();
      auto bound = readBound(reader, **boundEntry, where + " bound");
      if (!bound)
        return bound.takeError();
      round.bound = std::move(*bound);
      sequence.rounds.push_back(std::move(round));
    }
    return sequence;
  }
  if (*kind == "contract") {
    if (Error err = reader.closed(
            **entry, {"kind", "contract_fact_port", "cases"}, where))
      return std::move(err);
    sequence.kind = RoundSequence::Kind::Contract;
    auto port = reader.string(**entry, "contract_fact_port", where);
    if (!port)
      return port.takeError();
    sequence.contractFactPort = port->str();
    auto items = reader.array(**entry, "cases", where);
    if (!items)
      return items.takeError();
    for (const Value &item : **items) {
      const Object *caseEntry = item.getAsObject();
      if (!caseEntry)
        return reader.failed<RoundSequence>(where + " cases must be objects");
      if (Error err =
              reader.closed(*caseEntry,
                            {"case_name", "selector", "index_projection",
                             "challenge_space", "bound"},
                            where))
        return std::move(err);
      ContractRoundCase entry2;
      auto caseName = reader.string(*caseEntry, "case_name", where);
      if (!caseName)
        return caseName.takeError();
      entry2.caseName = caseName->str();
      auto selector = readRoundSelector(reader, *caseEntry, "selector", where);
      if (!selector)
        return selector.takeError();
      entry2.selector = std::move(*selector);
      auto projection =
          readLabelProjection(reader, *caseEntry, "index_projection", where);
      if (!projection)
        return projection.takeError();
      entry2.indexProjection = *projection;
      auto spaceEntry = reader.object(*caseEntry, "challenge_space", where);
      if (!spaceEntry)
        return spaceEntry.takeError();
      auto space =
          readQuantity(reader, **spaceEntry, where + " challenge space");
      if (!space)
        return space.takeError();
      entry2.challengeSpace = std::move(*space);
      auto boundEntry = reader.object(*caseEntry, "bound", where);
      if (!boundEntry)
        return boundEntry.takeError();
      auto bound = readBound(reader, **boundEntry, where + " bound");
      if (!bound)
        return bound.takeError();
      entry2.bound = std::move(*bound);
      sequence.cases.push_back(std::move(entry2));
    }
    return sequence;
  }
  return reader.failed<RoundSequence>(
      where + " has unknown round-sequence kind '" + *kind + "'");
}

Expected<RoundSelectorTemplate>
readRoundSelectorTemplate(const Reader &reader, const Object &parent,
                          StringRef key, const Twine &context) {
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " " + key).str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();

  RoundSelectorTemplate selector;
  if (*kind == "by_round_index") {
    if (Error err = reader.closed(**entry, {"kind", "round_index"}, where))
      return std::move(err);
    selector.kind = RoundSelectorKind::ByRoundIndex;
    auto index = reader.string(**entry, "round_index", where);
    if (!index)
      return index.takeError();
    selector.exactRoundIndex = index->str();
    return selector;
  }
  if (*kind == "adjacent_predecessor_round") {
    if (Error err =
            reader.closed(**entry, {"kind", "adjacency_fact_port"}, where))
      return std::move(err);
    selector.kind = RoundSelectorKind::AdjacentPredecessorRound;
    auto port = reader.string(**entry, "adjacency_fact_port", where);
    if (!port)
      return port.takeError();
    selector.adjacencyFactPort = port->str();
    return selector;
  }
  return reader.failed<RoundSelectorTemplate>(
      where + " has unknown round-selector kind '" + *kind + "'");
}

Expected<RuleBody> readBody(const Reader &reader, const Object &parent,
                            const Twine &context) {
  auto entry = reader.object(parent, "body", context);
  if (!entry)
    return entry.takeError();
  const std::string where = Twine(context + " body").str();
  auto kind = reader.string(**entry, "kind", where);
  if (!kind)
    return kind.takeError();

  auto boundField = [&](StringRef key) -> Expected<RuleBound> {
    auto boundEntry = reader.object(**entry, key, where);
    if (!boundEntry)
      return boundEntry.takeError();
    return readBound(reader, **boundEntry, where + " " + key);
  };
  auto quantityField = [&](StringRef key) -> Expected<QuantityTemplate> {
    auto quantityEntry = reader.object(**entry, key, where);
    if (!quantityEntry)
      return quantityEntry.takeError();
    return readQuantity(reader, **quantityEntry, where + " " + key);
  };
  auto portField = [&](StringRef key) -> Expected<std::string> {
    auto port = reader.string(**entry, key, where);
    if (!port)
      return port.takeError();
    return port->str();
  };

  if (*kind == "special_soundness_entry") {
    if (Error err = reader.closed(**entry, {"kind", "coordinates"}, where))
      return std::move(err);
    auto coordinates =
        readCoordinateSequence(reader, **entry, "coordinates", where);
    if (!coordinates)
      return coordinates.takeError();
    return RuleBody(SpecialSoundnessEntry{std::move(*coordinates)});
  }
  if (*kind == "native_round_by_round_entry") {
    if (Error err = reader.closed(**entry, {"kind", "rounds"}, where))
      return std::move(err);
    auto rounds = readRoundSequence(reader, **entry, "rounds", where);
    if (!rounds)
      return rounds.takeError();
    return RuleBody(NativeRoundByRoundEntry{std::move(*rounds)});
  }
  if (*kind == "computational_entry") {
    if (Error err = reader.closed(
            **entry, {"kind", "coordinates", "failure_bound"}, where))
      return std::move(err);
    auto coordinates =
        readCoordinateSequence(reader, **entry, "coordinates", where);
    if (!coordinates)
      return coordinates.takeError();
    auto failure = boundField("failure_bound");
    if (!failure)
      return failure.takeError();
    return RuleBody(
        ComputationalEntry{std::move(*coordinates), std::move(*failure)});
  }
  if (*kind == "completeness_entry") {
    if (Error err = reader.closed(**entry, {"kind", "bound"}, where))
      return std::move(err);
    auto bound = boundField("bound");
    if (!bound)
      return bound.takeError();
    return RuleBody(CompletenessEntry{std::move(*bound)});
  }
  if (*kind == "special_soundness_preservation") {
    if (Error err =
            reader.closed(**entry,
                          {"kind", "source_port", "appended_coordinates",
                           "conclusion_failure_bound"},
                          where))
      return std::move(err);
    auto sourcePort = portField("source_port");
    if (!sourcePort)
      return sourcePort.takeError();
    auto appended =
        readCoordinateSequence(reader, **entry, "appended_coordinates", where);
    if (!appended)
      return appended.takeError();
    auto failure = boundField("conclusion_failure_bound");
    if (!failure)
      return failure.takeError();
    return RuleBody(SpecialSoundnessPreservation{
        std::move(*sourcePort), std::move(*appended), std::move(*failure)});
  }
  if (*kind == "round_by_round_preservation") {
    if (Error err = reader.closed(
            **entry, {"kind", "source_port", "appended_rounds"}, where))
      return std::move(err);
    auto sourcePort = portField("source_port");
    if (!sourcePort)
      return sourcePort.takeError();
    auto appended =
        readRoundSequence(reader, **entry, "appended_rounds", where);
    if (!appended)
      return appended.takeError();
    return RuleBody(
        RoundByRoundPreservation{std::move(*sourcePort), std::move(*appended)});
  }
  if (*kind == "round_scaling") {
    if (Error err = reader.closed(
            **entry, {"kind", "round_by_round_port", "selected_round", "scale"},
            where))
      return std::move(err);
    auto port = portField("round_by_round_port");
    if (!port)
      return port.takeError();
    auto selected =
        readRoundSelectorTemplate(reader, **entry, "selected_round", where);
    if (!selected)
      return selected.takeError();
    auto scale = quantityField("scale");
    if (!scale)
      return scale.takeError();
    return RuleBody(RoundScaling{std::move(*port), std::move(*selected),
                                 std::move(*scale)});
  }
  if (*kind == "special_soundness_to_round_by_round") {
    if (Error err = reader.closed(
            **entry, {"kind", "special_soundness_port", "per_coordinate_bound"},
            where))
      return std::move(err);
    auto port = portField("special_soundness_port");
    if (!port)
      return port.takeError();
    auto bound = boundField("per_coordinate_bound");
    if (!bound)
      return bound.takeError();
    return RuleBody(
        SpecialSoundnessToRoundByRound{std::move(*port), std::move(*bound)});
  }
  if (*kind == "round_by_round_to_state_restoration") {
    if (Error err = reader.closed(
            **entry, {"kind", "round_by_round_port", "move_budget"}, where))
      return std::move(err);
    auto port = portField("round_by_round_port");
    if (!port)
      return port.takeError();
    auto budget = quantityField("move_budget");
    if (!budget)
      return budget.takeError();
    return RuleBody(
        RoundByRoundToStateRestoration{std::move(*port), std::move(*budget)});
  }
  if (*kind == "state_restoration_to_fiat_shamir_duplex") {
    if (Error err = reader.closed(
            **entry, {"kind", "state_restoration_port", "local_duplex_bound"},
            where))
      return std::move(err);
    auto port = portField("state_restoration_port");
    if (!port)
      return port.takeError();
    auto bound = boundField("local_duplex_bound");
    if (!bound)
      return bound.takeError();
    return RuleBody(StateRestorationToFiatShamirDuplex{std::move(*port),
                                                       std::move(*bound)});
  }
  return reader.failed<RuleBody>(where + " has unknown body kind '" + *kind +
                                 "'");
}

Expected<std::vector<PremisePort>>
readPremises(const Reader &reader, const Object &parent, const Twine &context) {
  auto items = reader.array(parent, "premises", context);
  if (!items)
    return items.takeError();
  std::vector<PremisePort> premises;
  for (const Value &item : **items) {
    const Object *entry = item.getAsObject();
    if (!entry)
      return reader.failed<std::vector<PremisePort>>(
          context + " premises must be objects");
    if (Error err =
            reader.closed(*entry,
                          {"name", "expected_subject_schema", "expected_index",
                           "expected_result", "expected_resources",
                           "result_constraints", "resource_substitution"},
                          context + " premise"))
      return std::move(err);
    PremisePort port;
    auto name = reader.string(*entry, "name", context + " premise");
    if (!name)
      return name.takeError();
    port.name = name->str();
    auto schema =
        reader.string(*entry, "expected_subject_schema", context + " premise");
    if (!schema)
      return schema.takeError();
    port.expectedSubjectSchema = schema->str();
    auto index = readSecurityIndex(reader, *entry, "expected_index",
                                   context + " premise");
    if (!index)
      return index.takeError();
    port.expectedIndex = std::move(*index);

    static const std::pair<StringRef, ResultSchema> schemas[] = {
        {"extraction", ResultSchema::Extraction},
        {"round", ResultSchema::Round},
        {"scalar", ResultSchema::Scalar},
    };
    auto resultText =
        reader.string(*entry, "expected_result", context + " premise");
    if (!resultText)
      return resultText.takeError();
    auto result = lookupEnum<ResultSchema>(reader, *resultText, schemas,
                                           context + " premise result");
    if (!result)
      return result.takeError();
    port.expectedResult = *result;

    auto resources = readTypedDeclarations(reader, *entry, "expected_resources",
                                           context + " premise");
    if (!resources)
      return resources.takeError();
    port.expectedResources = std::move(*resources);

    auto constraints =
        reader.array(*entry, "result_constraints", context + " premise");
    if (!constraints)
      return constraints.takeError();
    for (const Value &constraint : **constraints) {
      std::optional<StringRef> text = constraint.getAsString();
      if (!text)
        return reader.failed<std::vector<PremisePort>>(
            context + " premise result constraints must be strings");
      if (*text == "requires_empty_game_support")
        port.resultConstraints.insert(
            PremiseResultConstraint::RequiresEmptyGameSupport);
      else if (*text == "requires_no_bound_resource_support")
        port.resultConstraints.insert(
            PremiseResultConstraint::RequiresNoBoundResourceSupport);
      else
        return reader.failed<std::vector<PremisePort>>(
            context + " premise has unknown result constraint '" + *text + "'");
    }

    auto substitution = readQuantityMap(reader, *entry, "resource_substitution",
                                        context + " premise");
    if (!substitution)
      return substitution.takeError();
    port.resourceSubstitution = std::move(*substitution);
    premises.push_back(std::move(port));
  }
  return premises;
}

Expected<SoundnessRule> readRule(const Reader &reader, StringRef id,
                                 const Object &entry) {
  const std::string context = Twine("rule '" + id + "'").str();
  if (Error err = reader.closed(
          entry,
          {"id", "status", "parameters", "resources", "premises",
           "artifact_facts", "machine_conditions", "external_hypotheses",
           "exact_parameter_pins", "conclusion_index", "body"},
          context))
    return std::move(err);

  SoundnessRule rule;
  auto declaredId = reader.string(entry, "id", context);
  if (!declaredId)
    return declaredId.takeError();
  if (*declaredId != id)
    return reader.failed<SoundnessRule>(context +
                                        " does not carry its own identifier");
  rule.ref.id = id.str();

  auto statusText = reader.string(entry, "status", context);
  if (!statusText)
    return statusText.takeError();
  if (*statusText == "admitted")
    rule.status = RuleStatus::Admitted;
  else if (*statusText == "declared")
    rule.status = RuleStatus::Declared;
  else
    return reader.failed<SoundnessRule>(context + " has unknown status '" +
                                        *statusText + "'");

  auto parameters = readTypedDeclarations(reader, entry, "parameters", context);
  if (!parameters)
    return parameters.takeError();
  rule.parameters = std::move(*parameters);
  auto resources = readTypedDeclarations(reader, entry, "resources", context);
  if (!resources)
    return resources.takeError();
  rule.resources = std::move(*resources);
  auto premises = readPremises(reader, entry, context);
  if (!premises)
    return premises.takeError();
  rule.premises = std::move(*premises);
  auto facts = readTypedDeclarations(reader, entry, "artifact_facts", context);
  if (!facts)
    return facts.takeError();
  rule.artifactFacts = std::move(*facts);

  auto conditions = reader.array(entry, "machine_conditions", context);
  if (!conditions)
    return conditions.takeError();
  for (const Value &item : **conditions) {
    const Object *conditionEntry = item.getAsObject();
    if (!conditionEntry)
      return reader.failed<SoundnessRule>(
          context + " machine conditions must be objects");
    if (Error err = reader.closed(*conditionEntry,
                                  {"slot", "predicate_ref", "argument_types"},
                                  context + " machine condition"))
      return std::move(err);
    MachineConditionTemplate condition;
    auto slot =
        reader.string(*conditionEntry, "slot", context + " machine condition");
    if (!slot)
      return slot.takeError();
    condition.slot = slot->str();
    auto predicate = reader.string(*conditionEntry, "predicate_ref",
                                   context + " machine condition");
    if (!predicate)
      return predicate.takeError();
    condition.predicateRef = predicate->str();
    auto types = readValueSorts(reader, *conditionEntry, "argument_types",
                                context + " machine condition");
    if (!types)
      return types.takeError();
    condition.argumentTypes = std::move(*types);
    rule.machineConditions.push_back(std::move(condition));
  }

  auto hypotheses = reader.array(entry, "external_hypotheses", context);
  if (!hypotheses)
    return hypotheses.takeError();
  for (const Value &item : **hypotheses) {
    const Object *hypothesisEntry = item.getAsObject();
    if (!hypothesisEntry)
      return reader.failed<SoundnessRule>(
          context + " external hypotheses must be objects");
    if (Error err = reader.closed(*hypothesisEntry,
                                  {"slot", "proposition_ref", "argument_types"},
                                  context + " external hypothesis"))
      return std::move(err);
    ExternalHypothesisTemplate hypothesis;
    auto slot = reader.string(*hypothesisEntry, "slot",
                              context + " external hypothesis");
    if (!slot)
      return slot.takeError();
    hypothesis.slot = slot->str();
    auto proposition = reader.string(*hypothesisEntry, "proposition_ref",
                                     context + " external hypothesis");
    if (!proposition)
      return proposition.takeError();
    hypothesis.propositionRef = proposition->str();
    auto types = readValueSorts(reader, *hypothesisEntry, "argument_types",
                                context + " external hypothesis");
    if (!types)
      return types.takeError();
    hypothesis.argumentTypes = std::move(*types);
    rule.externalHypotheses.push_back(std::move(hypothesis));
  }

  auto pins = reader.array(entry, "exact_parameter_pins", context);
  if (!pins)
    return pins.takeError();
  for (const Value &item : **pins) {
    const Object *pinEntry = item.getAsObject();
    if (!pinEntry)
      return reader.failed<SoundnessRule>(context +
                                          " parameter pins must be objects");
    if (Error err = reader.closed(*pinEntry, {"parameter", "expected"},
                                  context + " parameter pin"))
      return std::move(err);
    ExactParameterPin pin;
    auto parameter =
        reader.string(*pinEntry, "parameter", context + " parameter pin");
    if (!parameter)
      return parameter.takeError();
    pin.parameter = parameter->str();
    auto expectedEntry =
        reader.object(*pinEntry, "expected", context + " parameter pin");
    if (!expectedEntry)
      return expectedEntry.takeError();
    auto expected =
        readBindingValue(reader, **expectedEntry, context + " parameter pin");
    if (!expected)
      return expected.takeError();
    pin.expected = std::move(*expected);
    rule.exactParameterPins.push_back(std::move(pin));
  }

  auto conclusion =
      readSecurityIndex(reader, entry, "conclusion_index", context);
  if (!conclusion)
    return conclusion.takeError();
  rule.conclusionIndex = std::move(*conclusion);

  auto body = readBody(reader, entry, context);
  if (!body)
    return body.takeError();
  rule.body = std::move(*body);

  // The revision is the declaration's content digest, so it is computed here
  // rather than written in the file: a hand-maintained digest can go stale,
  // and a stale exact reference is exactly what the pin exists to prevent.
  auto digest = ruleDigest(rule);
  if (!digest)
    return digest.takeError();
  rule.ref.sourceRevision = std::move(*digest);
  return rule;
}

Expected<ExactRef> readExactRef(const Reader &reader, const Object &parent,
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

Expected<SubjectRelation> readSubjectRelation(const Reader &reader,
                                              const Object &entry,
                                              const Twine &context) {
  auto kindText = reader.string(entry, "kind", context);
  if (!kindText)
    return kindText.takeError();

  SubjectRelation relation;
  if (*kindText == "same_subject") {
    if (Error err = reader.closed(entry, {"kind"}, context))
      return std::move(err);
    relation.kind = SubjectRelationKind::SameSubject;
    return relation;
  }
  if (*kindText == "consumed_claim" || *kindText == "consumed_claim_vector") {
    if (Error err = reader.closed(entry, {"kind", "selector", "input_indices"},
                                  context))
      return std::move(err);
    relation.kind = *kindText == "consumed_claim"
                        ? SubjectRelationKind::ConsumedClaim
                        : SubjectRelationKind::ConsumedClaimVector;
    static const std::pair<StringRef, ConsumedClaimSelectorKind> selectors[] = {
        {"reduction_input", ConsumedClaimSelectorKind::ReductionInput},
        {"all_reduction_inputs", ConsumedClaimSelectorKind::AllReductionInputs},
        {"reduction_inputs", ConsumedClaimSelectorKind::ReductionInputs},
    };
    auto selectorText = reader.string(entry, "selector", context);
    if (!selectorText)
      return selectorText.takeError();
    auto selector = lookupEnum<ConsumedClaimSelectorKind>(
        reader, *selectorText, selectors, context + " selector");
    if (!selector)
      return selector.takeError();
    relation.selector = *selector;
    auto indices = reader.array(entry, "input_indices", context);
    if (!indices)
      return indices.takeError();
    for (const Value &item : **indices) {
      std::optional<int64_t> index = item.getAsInteger();
      if (!index || *index < 0)
        return reader.failed<SubjectRelation>(
            context + " input indices must be non-negative integers");
      relation.inputIndices.push_back(uint64_t(*index));
    }
    return relation;
  }
  if (*kindText == "exact_external_subject") {
    if (Error err = reader.closed(
            entry, {"kind", "external_subject_schema", "external_arguments"},
            context))
      return std::move(err);
    relation.kind = SubjectRelationKind::ExactExternalSubject;
    auto schema = reader.string(entry, "external_subject_schema", context);
    if (!schema)
      return schema.takeError();
    relation.externalSubjectSchema = schema->str();
    auto arguments =
        readBindingValues(reader, entry, "external_arguments", context);
    if (!arguments)
      return arguments.takeError();
    relation.externalArguments = std::move(*arguments);
    return relation;
  }
  return reader.failed<SubjectRelation>(
      context + " has unknown subject-relation kind '" + *kindText + "'");
}

Expected<std::map<std::string, BindingValue, std::less<>>>
readBindingValueMap(const Reader &reader, const Object &parent, StringRef key,
                    const Twine &context) {
  using Map = std::map<std::string, BindingValue, std::less<>>;
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  Map values;
  for (const auto &field : **entry) {
    const Object *value = field.second.getAsObject();
    if (!value)
      return reader.failed<Map>(context + " '" + key +
                                "' entries must be objects");
    auto decoded =
        readBindingValue(reader, *value, context + " " + key + " entry");
    if (!decoded)
      return decoded.takeError();
    values.emplace(field.first.str(), std::move(*decoded));
  }
  return values;
}

Expected<std::map<std::string, std::vector<BindingValue>, std::less<>>>
readBindingValueListMap(const Reader &reader, const Object &parent,
                        StringRef key, const Twine &context) {
  using Map = std::map<std::string, std::vector<BindingValue>, std::less<>>;
  auto entry = reader.object(parent, key, context);
  if (!entry)
    return entry.takeError();
  Map values;
  for (const auto &field : **entry) {
    if (!field.second.getAsArray())
      return reader.failed<Map>(context + " '" + key +
                                "' entries must be arrays");
    auto decoded =
        readBindingValues(reader, **entry, field.first, context + " " + key);
    if (!decoded)
      return decoded.takeError();
    values.emplace(field.first.str(), std::move(*decoded));
  }
  return values;
}

Expected<RuleBinding>
readBinding(const Reader &reader, StringRef id, const Object &entry,
            const std::map<std::string, SoundnessRule, std::less<>> &rules) {
  const std::string context = Twine("binding '" + id + "'").str();
  if (Error err = reader.closed(entry,
                                {"id", "rule", "subject_schema", "anchor",
                                 "premise_relations", "parameter_bindings",
                                 "fact_bindings", "condition_argument_bindings",
                                 "hypothesis_argument_bindings"},
                                context))
    return std::move(err);

  RuleBinding binding;
  auto declaredId = reader.string(entry, "id", context);
  if (!declaredId)
    return declaredId.takeError();
  if (*declaredId != id)
    return reader.failed<RuleBinding>(context +
                                      " does not carry its own identifier");
  binding.ref.id = id.str();

  auto ruleId = reader.string(entry, "rule", context);
  if (!ruleId)
    return ruleId.takeError();
  auto rule = rules.find(*ruleId);
  if (rule == rules.end())
    return reader.failed<RuleBinding>(context + " names no rule '" + *ruleId +
                                      "' in this signature");
  binding.ruleRef = rule->second.ref;

  auto schema = reader.string(entry, "subject_schema", context);
  if (!schema)
    return schema.takeError();
  binding.subjectSchema = schema->str();

  auto anchor = reader.object(entry, "anchor", context);
  if (!anchor)
    return anchor.takeError();
  if (Error err = reader.closed(**anchor, {"kind", "ref"}, context + " anchor"))
    return std::move(err);
  auto anchorKind = reader.string(**anchor, "kind", context + " anchor");
  if (!anchorKind)
    return anchorKind.takeError();
  if (*anchorKind == "reduction_contract")
    binding.anchor.kind = ProtocolAnchorKind::ReductionContract;
  else if (*anchorKind == "path_transition")
    binding.anchor.kind = ProtocolAnchorKind::PathTransition;
  else
    return reader.failed<RuleBinding>(context + " has unknown anchor kind '" +
                                      *anchorKind + "'");
  auto anchorRef = readExactRef(reader, **anchor, "ref", context + " anchor");
  if (!anchorRef)
    return anchorRef.takeError();
  binding.anchor.ref = std::move(*anchorRef);

  auto relations = reader.object(entry, "premise_relations", context);
  if (!relations)
    return relations.takeError();
  for (const auto &field : **relations) {
    const Object *value = field.second.getAsObject();
    if (!value)
      return reader.failed<RuleBinding>(context +
                                        " premise relations must be objects");
    auto relation =
        readSubjectRelation(reader, *value, context + " premise relation");
    if (!relation)
      return relation.takeError();
    binding.premiseRelations.emplace(field.first.str(), std::move(*relation));
  }

  auto parameters =
      readBindingValueMap(reader, entry, "parameter_bindings", context);
  if (!parameters)
    return parameters.takeError();
  binding.parameterBindings = std::move(*parameters);
  auto facts = readBindingValueMap(reader, entry, "fact_bindings", context);
  if (!facts)
    return facts.takeError();
  binding.factBindings = std::move(*facts);
  auto conditions = readBindingValueListMap(
      reader, entry, "condition_argument_bindings", context);
  if (!conditions)
    return conditions.takeError();
  binding.conditionArgumentBindings = std::move(*conditions);
  auto hypotheses = readBindingValueListMap(
      reader, entry, "hypothesis_argument_bindings", context);
  if (!hypotheses)
    return hypotheses.takeError();
  binding.hypothesisArgumentBindings = std::move(*hypotheses);

  auto digest = bindingDigest(binding);
  if (!digest)
    return digest.takeError();
  binding.ref.sourceRevision = std::move(*digest);
  return binding;
}

Expected<SchemaContext> readSchemas(const Reader &reader,
                                    const Object &schemas) {
  const std::string context = Twine("schemas").str();
  if (Error err =
          reader.closed(schemas,
                        {"security_indices", "subject_schemas",
                         "primitive_games", "machine_deciders", "propositions"},
                        context))
    return std::move(err);

  SchemaContext result;

  auto indices = reader.array(schemas, "security_indices", context);
  if (!indices)
    return indices.takeError();
  for (size_t index = 0; index < (*indices)->size(); ++index) {
    Object wrapper;
    wrapper["index"] = (**indices)[index];
    auto parsed = readSecurityIndex(reader, wrapper, "index",
                                    context + " security index");
    if (!parsed)
      return parsed.takeError();
    result.securityIndices.push_back(std::move(*parsed));
  }

  auto subjects = reader.object(schemas, "subject_schemas", context);
  if (!subjects)
    return subjects.takeError();
  for (const auto &field : **subjects) {
    const Object *entry = field.second.getAsObject();
    if (!entry)
      return reader.failed<SchemaContext>(context +
                                          " subject schemas must be objects");
    const std::string where =
        Twine(context + " subject schema '" + field.first.str() + "'").str();
    if (Error err =
            reader.closed(*entry, {"ref", "kind", "argument_types"}, where))
      return std::move(err);
    SubjectSchema schema;
    auto ref = reader.string(*entry, "ref", where);
    if (!ref)
      return ref.takeError();
    if (*ref != field.first.str())
      return reader.failed<SchemaContext>(where +
                                          " does not carry its own identifier");
    schema.ref = ref->str();
    static const std::pair<StringRef, SubjectSchemaKind> kinds[] = {
        {"protocol_claim", SubjectSchemaKind::ProtocolClaim},
        {"consumed_claim_vector", SubjectSchemaKind::ConsumedClaimVector},
        {"external_instance", SubjectSchemaKind::ExternalInstance},
    };
    auto kindText = reader.string(*entry, "kind", where);
    if (!kindText)
      return kindText.takeError();
    auto kind = lookupEnum<SubjectSchemaKind>(reader, *kindText, kinds, where);
    if (!kind)
      return kind.takeError();
    schema.kind = *kind;
    auto types = readValueSorts(reader, *entry, "argument_types", where);
    if (!types)
      return types.takeError();
    schema.argumentTypes = std::move(*types);
    result.subjectSchemas.emplace(field.first.str(), std::move(schema));
  }

  auto games = reader.object(schemas, "primitive_games", context);
  if (!games)
    return games.takeError();
  for (const auto &field : **games) {
    const Object *entry = field.second.getAsObject();
    if (!entry)
      return reader.failed<SchemaContext>(context +
                                          " primitive games must be objects");
    const std::string where =
        Twine(context + " primitive game '" + field.first.str() + "'").str();
    if (Error err = reader.closed(
            *entry, {"ref", "instance_argument_types", "resources"}, where))
      return std::move(err);
    PrimitiveGameDefinition game;
    auto ref = readExactRef(reader, *entry, "ref", where);
    if (!ref)
      return ref.takeError();
    if (ref->id != field.first.str())
      return reader.failed<SchemaContext>(where +
                                          " does not carry its own identifier");
    game.ref = std::move(*ref);
    auto types =
        readValueSorts(reader, *entry, "instance_argument_types", where);
    if (!types)
      return types.takeError();
    game.instanceArgumentTypes = std::move(*types);
    auto resources = readTypedDeclarations(reader, *entry, "resources", where);
    if (!resources)
      return resources.takeError();
    game.resources = std::move(*resources);
    result.primitiveGames.emplace(field.first.str(), std::move(game));
  }

  auto deciders = reader.object(schemas, "machine_deciders", context);
  if (!deciders)
    return deciders.takeError();
  static const std::pair<StringRef, MachineDeciderKind> deciderKinds[] = {
      {"one_message_role", MachineDeciderKind::OneMessageRole},
      {"space_embeds", MachineDeciderKind::SpaceEmbeds},
      {"bound_bites", MachineDeciderKind::BoundBites},
      {"field_class", MachineDeciderKind::FieldClass},
      {"space_covers_arity", MachineDeciderKind::SpaceCoversArity},
      {"batch_arity", MachineDeciderKind::BatchArity},
      {"space_covers_batch", MachineDeciderKind::SpaceCoversBatch},
      {"same_point", MachineDeciderKind::SamePoint},
      {"batch_after_material", MachineDeciderKind::BatchAfterMaterial},
      {"fri_rate_below_one", MachineDeciderKind::FriRateBelowOne},
      {"johnson_fold_param", MachineDeciderKind::JohnsonFoldParam},
      {"johnson_slack", MachineDeciderKind::JohnsonSlack},
      {"johnson_multiplicity", MachineDeciderKind::JohnsonMultiplicity},
      {"johnson_delta", MachineDeciderKind::JohnsonDelta},
      {"udr_domain_floor", MachineDeciderKind::UdrDomainFloor},
      {"udr_theta_window", MachineDeciderKind::UdrThetaWindow},
      {"random_words_eta_floor", MachineDeciderKind::RandomWordsEtaFloor},
      {"threshold_delta_window", MachineDeciderKind::ThresholdDeltaWindow},
      {"pow_pinned", MachineDeciderKind::PowPinned},
      {"pow_adjacent", MachineDeciderKind::PowAdjacent},
      {"duplex_spine", MachineDeciderKind::DuplexSpine},
      {"codec_bias_declared", MachineDeciderKind::CodecBiasDeclared},
  };
  for (const auto &field : **deciders) {
    const Object *entry = field.second.getAsObject();
    if (!entry)
      return reader.failed<SchemaContext>(context +
                                          " machine deciders must be objects");
    const std::string where =
        Twine(context + " machine decider '" + field.first.str() + "'").str();
    if (Error err =
            reader.closed(*entry, {"ref", "kind", "argument_types"}, where))
      return std::move(err);
    MachineDeciderDefinition decider;
    auto ref = readExactRef(reader, *entry, "ref", where);
    if (!ref)
      return ref.takeError();
    if (ref->id != field.first.str())
      return reader.failed<SchemaContext>(where +
                                          " does not carry its own identifier");
    decider.ref = std::move(*ref);
    auto kindText = reader.string(*entry, "kind", where);
    if (!kindText)
      return kindText.takeError();
    auto kind =
        lookupEnum<MachineDeciderKind>(reader, *kindText, deciderKinds, where);
    if (!kind)
      return kind.takeError();
    decider.kind = *kind;
    auto types = readValueSorts(reader, *entry, "argument_types", where);
    if (!types)
      return types.takeError();
    decider.argumentTypes = std::move(*types);
    result.machineDeciders.emplace(field.first.str(), std::move(decider));
  }

  auto propositions = reader.object(schemas, "propositions", context);
  if (!propositions)
    return propositions.takeError();
  for (const auto &field : **propositions) {
    const Object *entry = field.second.getAsObject();
    if (!entry)
      return reader.failed<SchemaContext>(context +
                                          " propositions must be objects");
    const std::string where =
        Twine(context + " proposition '" + field.first.str() + "'").str();
    if (Error err = reader.closed(*entry, {"ref", "argument_types"}, where))
      return std::move(err);
    PropositionSchema proposition;
    auto ref = readExactRef(reader, *entry, "ref", where);
    if (!ref)
      return ref.takeError();
    if (ref->id != field.first.str())
      return reader.failed<SchemaContext>(where +
                                          " does not carry its own identifier");
    proposition.ref = std::move(*ref);
    auto types = readValueSorts(reader, *entry, "argument_types", where);
    if (!types)
      return types.takeError();
    proposition.argumentTypes = std::move(*types);
    result.propositions.emplace(field.first.str(), std::move(proposition));
  }

  return result;
}

Expected<DeclarationAnnotation>
readAnnotation(const Reader &reader, StringRef id, const Object &entry) {
  const std::string context = Twine("annotation '" + id + "'").str();
  if (Error err =
          reader.closed(entry,
                        {"statement", "loss_display", "status_rationale",
                         "notes", "citations", "statement_basis",
                         "formalization", "formalization_absence"},
                        context))
    return std::move(err);

  DeclarationAnnotation annotation;
  auto statementText = reader.optionalString(entry, "statement", context);
  if (!statementText)
    return statementText.takeError();
  annotation.statement = std::move(*statementText);
  auto lossDisplayText = reader.optionalString(entry, "loss_display", context);
  if (!lossDisplayText)
    return lossDisplayText.takeError();
  annotation.lossDisplay = std::move(*lossDisplayText);
  auto statusRationaleText =
      reader.optionalString(entry, "status_rationale", context);
  if (!statusRationaleText)
    return statusRationaleText.takeError();
  annotation.statusRationale = std::move(*statusRationaleText);
  auto notesText = reader.optionalString(entry, "notes", context);
  if (!notesText)
    return notesText.takeError();
  annotation.notes = std::move(*notesText);

  if (entry.get("citations")) {
    auto citations =
        reader.registryFile().requireStringList(entry, "citations", context);
    if (!citations)
      return citations.takeError();
    annotation.citations = std::move(*citations);
  }

  // A present field of the wrong shape refuses; getArray alone would treat
  // it as absent, and a silently skipped authority field is a lenient path.
  if (const llvm::json::Value *basisValue = entry.get("statement_basis")) {
    if (!basisValue->getAsArray())
      return reader.failed<DeclarationAnnotation>(
          context + " statement basis must be a list");
  }
  if (const llvm::json::Value *receiptsValue = entry.get("formalization")) {
    if (!receiptsValue->getAsArray())
      return reader.failed<DeclarationAnnotation>(
          context + " formalization must be a list");
  }

  if (const Array *basis = entry.getArray("statement_basis")) {
    for (const Value &item : *basis) {
      const Object *anchorEntry = item.getAsObject();
      if (!anchorEntry)
        return reader.failed<DeclarationAnnotation>(
            context + " statement basis entries must be objects");
      if (Error err = reader.closed(*anchorEntry,
                                    {"source", "revision", "anchor"}, context))
        return std::move(err);
      SourceAnchor anchor;
      auto _sourceText = reader.optionalString(*anchorEntry, "source", context);
      if (!_sourceText)
        return _sourceText.takeError();
      anchor.source = std::move(*_sourceText);
      auto _revisionText =
          reader.optionalString(*anchorEntry, "revision", context);
      if (!_revisionText)
        return _revisionText.takeError();
      anchor.revision = std::move(*_revisionText);
      auto _anchorText = reader.optionalString(*anchorEntry, "anchor", context);
      if (!_anchorText)
        return _anchorText.takeError();
      anchor.anchor = std::move(*_anchorText);
      annotation.statementBasis.push_back(std::move(anchor));
    }
  }

  if (const Array *receipts = entry.getArray("formalization")) {
    for (const Value &item : *receipts) {
      const Object *receiptEntry = item.getAsObject();
      if (!receiptEntry)
        return reader.failed<DeclarationAnnotation>(
            context + " formalization entries must be objects");
      if (Error err = reader.closed(*receiptEntry,
                                    {"repository", "revision", "declaration",
                                     "statement", "axioms", "state", "covers",
                                     "does_not_cover", "unmatched_obligations"},
                                    context))
        return std::move(err);
      FormalizationReceipt receipt;
      auto _repositoryText =
          reader.optionalString(*receiptEntry, "repository", context);
      if (!_repositoryText)
        return _repositoryText.takeError();
      receipt.repository = std::move(*_repositoryText);
      auto _revisionText =
          reader.optionalString(*receiptEntry, "revision", context);
      if (!_revisionText)
        return _revisionText.takeError();
      receipt.revision = std::move(*_revisionText);
      auto _declarationText =
          reader.optionalString(*receiptEntry, "declaration", context);
      if (!_declarationText)
        return _declarationText.takeError();
      receipt.declaration = std::move(*_declarationText);
      auto _statementText =
          reader.optionalString(*receiptEntry, "statement", context);
      if (!_statementText)
        return _statementText.takeError();
      receipt.statement = std::move(*_statementText);
      auto _coversText =
          reader.optionalString(*receiptEntry, "covers", context);
      if (!_coversText)
        return _coversText.takeError();
      receipt.covers = std::move(*_coversText);
      auto _doesnotcoverText =
          reader.optionalString(*receiptEntry, "does_not_cover", context);
      if (!_doesnotcoverText)
        return _doesnotcoverText.takeError();
      receipt.doesNotCover = std::move(*_doesnotcoverText);

      static const std::pair<StringRef, FormalizationState> states[] = {
          {"mechanized", FormalizationState::Mechanized},
          {"proof_incomplete", FormalizationState::ProofIncomplete},
          {"subject_incomplete", FormalizationState::SubjectIncomplete},
      };
      auto stateText = reader.string(*receiptEntry, "state", context);
      if (!stateText)
        return stateText.takeError();
      auto state = lookupEnum<FormalizationState>(reader, *stateText, states,
                                                  context + " state");
      if (!state)
        return state.takeError();
      receipt.state = *state;

      // Present and possibly empty: an absent list would be indistinguishable
      // from a list nobody filled in, and the empty list is the claim that no
      // axiom was admitted.
      if (!receiptEntry->getArray("axioms"))
        return reader.failed<DeclarationAnnotation>(
            context + " formalization needs an 'axioms' array, empty when the "
                      "dependency closure admits none");
      auto axioms = reader.registryFile().requireStringList(*receiptEntry,
                                                            "axioms", context);
      if (!axioms)
        return axioms.takeError();
      receipt.axioms = std::move(*axioms);

      if (receiptEntry->get("unmatched_obligations")) {
        auto unmatched = reader.registryFile().requireStringList(
            *receiptEntry, "unmatched_obligations", context);
        if (!unmatched)
          return unmatched.takeError();
        receipt.unmatchedObligations = std::move(*unmatched);
      }
      annotation.formalization.push_back(std::move(receipt));
    }
  }

  if (const llvm::json::Value *absenceValue =
          entry.get("formalization_absence")) {
    const Object *absenceEntry = absenceValue->getAsObject();
    if (!absenceEntry)
      return reader.failed<DeclarationAnnotation>(
          context + " formalization absence must be an object");
    if (Error err = reader.closed(
            *absenceEntry, {"repository", "revision", "wanted", "demand"},
            context))
      return std::move(err);
    FormalizationAbsence absence;
    for (auto [key, field] : {std::pair<StringRef, std::string *>{
                                  "repository", &absence.repository},
                              {"revision", &absence.revision},
                              {"wanted", &absence.wanted},
                              {"demand", &absence.demand}}) {
      // reader.string already refuses an empty or non-printable value, so
      // the record cannot avoid saying what was looked for and where the
      // demand is written down.
      auto text = reader.string(*absenceEntry, key, context);
      if (!text)
        return text.takeError();
      *field = std::move(*text);
    }
    annotation.formalizationAbsence = std::move(absence);
  }

  return annotation;
}

} // namespace

Expected<Signature> parseSignature(StringRef json, StringRef sourceName) {
  auto parsed =
      registry::RegistryFile::parse(json, sourceName, kRegistryName, "rules",
                                    {"schemas", "bindings", "annotations"});
  if (!parsed)
    return parsed.takeError();
  Reader reader(std::move(*parsed));

  const Object *root = reader.registryFile().extra("schemas");
  if (!root)
    return reader.failed<Signature>("'schemas' must be an object");
  auto schemas = readSchemas(reader, *root);
  if (!schemas)
    return schemas.takeError();

  std::map<std::string, SoundnessRule, std::less<>> rules;
  for (const auto &field : reader.registryFile().payload()) {
    const Object *entry = field.second.getAsObject();
    if (!entry)
      return reader.failed<Signature>("rule '" + field.first.str() +
                                      "' must be an object");
    auto rule = readRule(reader, field.first, *entry);
    if (!rule)
      return rule.takeError();
    rules.emplace(field.first.str(), std::move(*rule));
  }

  // Every section a signature declares is written, empty if it has nothing
  // to say. An omitted one and one written as the wrong shape are both
  // authoring mistakes, and reading either as "no bindings" would drop the
  // whole executable set while still minting a digest for the result.
  for (StringRef section : {"bindings", "annotations"})
    if (!reader.registryFile().extra(section))
      return reader.failed<Signature>("'" + section.str() +
                                      "' must be an object");

  std::map<std::string, RuleBinding, std::less<>> bindings;
  if (const Object *entries = reader.registryFile().extra("bindings")) {
    for (const auto &field : *entries) {
      const Object *entry = field.second.getAsObject();
      if (!entry)
        return reader.failed<Signature>("binding '" + field.first.str() +
                                        "' must be an object");
      auto binding = readBinding(reader, field.first, *entry, rules);
      if (!binding)
        return binding.takeError();
      bindings.emplace(field.first.str(), std::move(*binding));
    }
  }

  std::map<std::string, DeclarationAnnotation, std::less<>> annotations;
  if (const Object *entries = reader.registryFile().extra("annotations")) {
    for (const auto &field : *entries) {
      const Object *entry = field.second.getAsObject();
      if (!entry)
        return reader.failed<Signature>("annotation '" + field.first.str() +
                                        "' must be an object");
      auto annotation = readAnnotation(reader, field.first, *entry);
      if (!annotation)
        return annotation.takeError();
      annotations.emplace(field.first.str(), std::move(*annotation));
    }
  }

  auto catalog = freezeSoundnessCatalog(std::move(*schemas), std::move(rules),
                                        std::move(bindings));
  if (!catalog)
    return catalog.takeError();
  return freezeSignature(std::move(*catalog), std::move(annotations));
}

Expected<Signature> loadSignatureFromFile(StringRef path) {
  auto buffer = registry::RegistryFile::readFile(path);
  if (!buffer)
    return buffer.takeError();
  return parseSignature((*buffer)->getBuffer(), path);
}

} // namespace zkc::soundness
