#include "OracleDefinitions.h"
#include "llvm/ADT/STLExtras.h"
#include <set>
using namespace llvm;
namespace zkc::language::detail {
std::shared_ptr<OracleDefinition>
closeOracleDefinition(Semantics &types, const OracleDefinition &source,
                      const Substitution &bindings, Span span) {
  if (!types.charge(source.sourceBounds.size() + source.resultShape.size() +
                        source.predicates.size() + 1,
                    span))
    return {};
  auto result = std::make_shared<OracleDefinition>(source);
  auto close = [&](Type &type, Span at) {
    auto closed = types.substitute(type, bindings, at);
    if (!closed)
      return false;
    if (types.symbolic(*closed))
      return types.fail("source.oracle-specialization",
                        "oracle metadata retains an open static term", at);
    type = std::move(*closed);
    return true;
  };
  if (!close(result->queryParameter.type, result->queryParameter.span) ||
      !close(result->answer, span))
    return {};
  for (auto &bound : result->sourceBounds)
    if (!close(bound.maximum, bound.span))
      return {};
  for (auto &shape : result->resultShape)
    if (!close(shape.maximum, shape.span))
      return {};
  return result;
}
bool checkOracleDefinition(Semantics &types, ArrayRef<Declaration> declarations,
                           const Declaration &decl) {
  auto refuse = [&](Span span, StringRef message) {
    return types.fail("source.oracle-specialization", message, span);
  };
  if (!decl.oracleDefinition || decl.outputs.size() != 1 ||
      decl.outputs.front().type.kind != Type::Kind::Oracle ||
      decl.outputs.front().type.arguments.size() != 1)
    return refuse(decl.span, "oracle constructor result differs");
  const auto &definition = *decl.oracleDefinition;
  if (!definition.sourceCount || definition.sourceCount > decl.inputs.size() ||
      definition.admissibility.index >= declarations.size() ||
      !definition.queryParameter.roles.empty() ||
      definition.queryParameter.oracle)
    return refuse(decl.span, "oracle metadata signature differs");
  auto query = types.associated(decl.outputs.front().type.arguments.front(),
                                "Query", decl.span);
  auto answer = types.associated(decl.outputs.front().type.arguments.front(),
                                 "Answer", decl.span);
  if (!query || !answer)
    return false;
  if (*query != definition.queryParameter.type || *answer != definition.answer)
    return refuse(decl.span, "oracle query/answer metadata differs");
  const auto &predicate = declarations[definition.admissibility.index];
  if (!predicate.oraclePredicateOwner ||
      predicate.oraclePredicateOwner->index != decl.id.index ||
      predicate.kind != Declaration::Kind::Relation || !predicate.relation ||
      predicate.relation->kind != RelationDefinition::Kind::Formula ||
      predicate.inputs.size() != decl.inputs.size() ||
      predicate.outputs.size() != 1 ||
      predicate.outputs.front().type != Type{} || !predicate.body ||
      predicate.body->mode != Body::Mode::Math ||
      predicate.body->inputs != decl.inputs.size() ||
      predicate.body->values.size() < decl.inputs.size())
    return refuse(decl.span, "oracle predicate identity or signature differs");
  for (unsigned i = 0; i < decl.inputs.size(); ++i) {
    const auto &port = decl.inputs[i];
    auto expected = std::optional<Type>(port.type);
    if (i < definition.sourceCount) {
      if (port.type.kind != Type::Kind::Oracle ||
          port.type.arguments.size() != 1)
        return refuse(port.span, "oracle direct source prefix differs");
      expected =
          types.associated(port.type.arguments.front(), "Data", port.span);
    } else if (isLogicalValue(port.type))
      return refuse(port.span, "logical handle appears after oracle captures");
    if (!expected || predicate.inputs[i].type != *expected ||
        predicate.body->values[i].type != *expected)
      return refuse(port.span,
                    "oracle predicate source/capture substitution differs");
  }
  std::set<unsigned> boundedSources;
  for (const auto &bound : definition.sourceBounds)
    if (bound.source >= definition.sourceCount || bound.dimension != "rows" ||
        bound.maximum.kind != Type::Kind::Natural ||
        !boundedSources.insert(bound.source).second)
      return refuse(bound.span, "oracle source bound differs");
  for (unsigned i = 0; i < definition.sourceCount; ++i) {
    const auto &kind = decl.inputs[i].type.arguments.front();
    if (kind.domain == "table" &&
        ((kind.arguments.size() == 1) != bool(boundedSources.count(i))))
      return refuse(decl.inputs[i].span,
                    "closed source row-bound coverage differs");
  }
  std::set<std::string> resultDimensions;
  for (const auto &shape : definition.resultShape)
    if (shape.input < definition.sourceCount ||
        shape.input >= decl.inputs.size() ||
        decl.inputs[shape.input].type.kind != Type::Kind::Index ||
        shape.dimension != "rows" ||
        shape.maximum.kind != Type::Kind::Natural ||
        !resultDimensions.insert(shape.dimension).second)
      return refuse(shape.span, "oracle result shape capture differs");
  const auto &resultKind = decl.outputs.front().type.arguments.front();
  if (resultKind.domain == "table" && ((resultKind.arguments.size() == 1) !=
                                       bool(resultDimensions.count("rows"))))
    return refuse(decl.span, "closed result row-shape coverage differs");
  for (unsigned i = 0; i < definition.predicates.size(); ++i) {
    const auto &clause = definition.predicates[i];
    if (clause.ordinal != i ||
        clause.condition.index >= predicate.body->values.size() ||
        predicate.body->values[clause.condition.index].type != Type{})
      return refuse(clause.span, "oracle requires clause substitution differs");
  }
  if (!decl.body || decl.body->inputs != decl.inputs.size() + 1 ||
      decl.body->values.size() < decl.body->inputs)
    return refuse(decl.span, "oracle has no query body");
  for (unsigned i = 0; i < decl.inputs.size(); ++i)
    if (decl.body->values[i].type != decl.inputs[i].type ||
        decl.body->values[i].oracleHolder)
      return refuse(decl.inputs[i].span,
                    "oracle query source/capture ABI differs");
  if (decl.body->values[decl.inputs.size()].type !=
          definition.queryParameter.type ||
      decl.body->values[decl.inputs.size()].oracleHolder)
    return refuse(decl.span, "oracle query parameter ABI differs");
  return checkOracleQueryBody(types, declarations, decl, *decl.body);
}
bool checkOracleMetadataSubstitution(Semantics &types,
                                     const Declaration &original,
                                     const Declaration &closed,
                                     const Substitution &bindings,
                                     ArrayRef<Declaration> declarations) {
  auto refuse = [&] {
    return types.fail("source.oracle-specialization",
                      "closed oracle metadata differs from checked source",
                      closed.span);
  };
  if (bool(original.oracleDefinition) != bool(closed.oracleDefinition))
    return refuse();
  if (!original.oracleDefinition)
    return true;
  auto expected = closeOracleDefinition(types, *original.oracleDefinition,
                                        bindings, original.span);
  if (!expected)
    return false;
  const auto &actual = *closed.oracleDefinition;
  auto sameSpan = [](Span a, Span b) {
    return a.source.index == b.source.index && a.begin == b.begin &&
           a.end == b.end;
  };
  if (expected->sourceCount != actual.sourceCount ||
      expected->queryParameter.name != actual.queryParameter.name ||
      expected->queryParameter.type != actual.queryParameter.type ||
      !sameSpan(expected->queryParameter.span, actual.queryParameter.span) ||
      expected->answer != actual.answer ||
      expected->sourceBounds.size() != actual.sourceBounds.size() ||
      expected->resultShape.size() != actual.resultShape.size() ||
      expected->predicates.size() != actual.predicates.size() ||
      actual.admissibility.index >= declarations.size())
    return refuse();
  const auto &predicate = declarations[actual.admissibility.index];
  if (!predicate.origin ||
      predicate.origin->index != expected->admissibility.index ||
      predicate.staticArguments != closed.staticArguments)
    return refuse();
  for (unsigned i = 0; i < actual.sourceBounds.size(); ++i) {
    const auto &a = expected->sourceBounds[i], &b = actual.sourceBounds[i];
    if (a.source != b.source || a.dimension != b.dimension ||
        a.maximum != b.maximum || !sameSpan(a.span, b.span))
      return refuse();
  }
  for (unsigned i = 0; i < actual.resultShape.size(); ++i) {
    const auto &a = expected->resultShape[i], &b = actual.resultShape[i];
    if (a.input != b.input || a.dimension != b.dimension ||
        a.maximum != b.maximum || !sameSpan(a.span, b.span))
      return refuse();
  }
  for (unsigned i = 0; i < actual.predicates.size(); ++i) {
    const auto &a = expected->predicates[i], &b = actual.predicates[i];
    if (a.label != b.label || a.ordinal != b.ordinal ||
        a.condition.index != b.condition.index || !sameSpan(a.span, b.span))
      return refuse();
  }
  return checkOracleDefinition(types, declarations, closed);
}
} // namespace zkc::language::detail
