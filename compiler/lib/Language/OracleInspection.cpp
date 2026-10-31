#include "OracleInspection.h"
using namespace llvm;
namespace zkc::language::detail {
json::Object describeOracleDefinition(ArrayRef<Declaration> declarations,
                                      const Declaration &decl) {
  const auto &definition = *decl.oracleDefinition;
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
      {"admissibility_inputs", std::move(predicateInputs)},
      {"predicates", std::move(clauses)},
      {"source_bounds", std::move(bounds)},
      {"result_shape", std::move(shapes)},
      {"queries", std::move(queries)}};
}
} // namespace zkc::language::detail
