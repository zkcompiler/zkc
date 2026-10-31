#include "LayoutReader.h"
using namespace llvm;
namespace zkc::language::detail {
Error LayoutReader::oracleDefinitionBody(Id suite, SyntaxDeclaration &decl) {
  std::optional<Id> query;
  std::vector<Id> predicates;
  for (auto item : children(suite)) {
    if (auto error = charge(item))
      return error;
    if (kind(item) == K::QueryBody && !query)
      query = item;
    else if (kind(item) == K::Requires && !query)
      predicates.push_back(item);
    else
      return fail(item,
                  "oracle definition needs requires clauses followed by "
                  "exactly one query suite",
                  "source.oracle-definition");
  }
  if (!query)
    return fail(suite, "oracle definition has no query suite",
                "source.oracle-query");
  auto parameterList = first(*query, K::Parameters);
  auto querySuite = first(*query, K::Suite);
  if (!parameterList || !querySuite || children(*parameterList).size() != 1)
    return fail(*query, "query needs exactly one typed parameter",
                "source.oracle-query");
  auto parameter = port(children(*parameterList).front());
  if (!parameter)
    return parameter.takeError();
  decl.oracleDefinition->queryParameter = std::move(*parameter);
  // Root body index zero is always the query.
  if (auto error = body(*querySuite, decl))
    return error;
  for (auto item : predicates) {
    auto nodes = parts(item, 1, 2);
    if (!nodes)
      return nodes.takeError();
    SyntaxOraclePredicate predicate;
    predicate.span = span(item);
    if (nodes->size() == 2) {
      auto label = name(nodes->front());
      if (!label)
        return label.takeError();
      predicate.label = std::move(*label);
    }
    auto condition = [&]() -> Expected<uint32_t> {
      if (kind(nodes->back()) != K::Suite)
        return expression(nodes->back(), decl);
      auto formula = parts(nodes->back(), 1, 1);
      if (!formula)
        return formula.takeError();
      return expression(formula->front(), decl);
    }();
    if (!condition)
      return condition.takeError();
    predicate.condition = *condition;
    decl.oracleDefinition->predicates.push_back(std::move(predicate));
  }
  decl.deferredBody.reset();
  return Error::success();
}
} // namespace zkc::language::detail
