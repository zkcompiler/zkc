#include "OracleInspection.h"
#include "State.h"
#include "zkc/Language/Companions.h"
using namespace llvm;
namespace zkc::language::detail {
Expected<json::Object>
oracleAdmissibilityCompanions(ArrayRef<Declaration> declarations,
                              const Declaration &decl, Work &work) {
  const auto &owner = decl.origin ? declarations[decl.origin->index] : decl;
  auto identity = companionIdentity(owner.qualifiedName, {},
                                    ObligationRole::OracleAdmissibility, {}, 0,
                                    work.limits);
  if (!identity)
    return identity.takeError();
  if (auto error = work.charge(1 + identity->size()))
    return std::move(error);
  json::Object result{{"template", std::move(*identity)},
                      {"instance", nullptr}};
  if (decl.origin) {
    auto selected = companionIdentity(owner.qualifiedName, decl.symbol,
                                      ObligationRole::OracleAdmissibility, {},
                                      0, work.limits);
    if (!selected)
      return selected.takeError();
    if (auto error = work.charge(1 + selected->size()))
      return std::move(error);
    result["instance"] = std::move(*selected);
  }
  return result;
}
Expected<json::Object>
describeOracleDefinition(ArrayRef<Declaration> declarations,
                         const Declaration &decl, Work &work) {
  const auto &definition = *decl.oracleDefinition;
  if (auto error = work.charge(
          definition.predicates.size() + definition.sourceBounds.size() +
          definition.resultShape.size() + decl.inputs.size() +
          (decl.body ? decl.body->operations.size() : 0) + 1))
    return std::move(error);
  auto companions = oracleAdmissibilityCompanions(declarations, decl, work);
  if (!companions)
    return companions.takeError();
  json::Array bounds, shapes, clauses, queries;
  for (const auto &bound : definition.sourceBounds)
    bounds.push_back(json::Object{{"source", bound.source},
                                  {"dimension", bound.dimension},
                                  {"maximum", spelling(bound.maximum)}});
  for (const auto &shape : definition.resultShape)
    shapes.push_back(json::Object{{"dimension", shape.dimension},
                                  {"input", shape.input},
                                  {"maximum", spelling(shape.maximum)}});
  for (const auto &clause : definition.predicates)
    clauses.push_back(
        json::Object{{"ordinal", clause.ordinal},
                     {"label", clause.label ? json::Value(*clause.label)
                                            : json::Value(nullptr)},
                     {"condition", clause.condition.index},
                     {"begin", clause.span.begin},
                     {"end", clause.span.end}});
  if (decl.body)
    for (const auto &operation : decl.body->operations)
      if (const auto *query = std::get_if<OracleSourceQuery>(&operation.action))
        queries.push_back(
            json::Object{{"source", query->source},
                         {"position", query->position.index},
                         {"answer", operation.results.front().index},
                         {"site", operation.site ? json::Value(*operation.site)
                                                 : json::Value(nullptr)}});
  const auto &predicate = declarations[definition.admissibility.index];
  json::Array predicateInputs;
  for (const auto &input : predicate.inputs)
    predicateInputs.push_back(
        json::Object{{"name", input.name}, {"type", spelling(input.type)}});
  return json::Object{
      {"source_count", definition.sourceCount},
      {"query_parameter",
       json::Object{{"name", definition.queryParameter.name},
                    {"type", spelling(definition.queryParameter.type)},
                    {"input", unsigned(decl.inputs.size())}}},
      {"answer", spelling(definition.answer)},
      {"admissibility", predicate.qualifiedName},
      {"admissibility_id", definition.admissibility.index},
      {"admissibility_symbol", formulaSymbol(predicate)},
      {"admissibility_companions", std::move(*companions)},
      {"admissibility_inputs", std::move(predicateInputs)},
      {"predicates", std::move(clauses)},
      {"source_bounds", std::move(bounds)},
      {"result_shape", std::move(shapes)},
      {"queries", std::move(queries)}};
}
} // namespace zkc::language::detail
