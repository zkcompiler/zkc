#include "BodyCheck.h"
#include "BodySummary.h"
#include "OracleDefinitions.h"
#include "llvm/ADT/STLExtras.h"
#include <set>
using namespace llvm;
namespace zkc::language::detail {
bool BodyChecker::oracleStatement(const Statement &source) {
  return ((source.kind == Statement::Kind::Let ||
           source.kind == Statement::Kind::Expression) &&
          !source.mutableBinding && !source.exchange && !source.roles &&
          !source.owner) ||
         fail("source.oracle-body",
              "query suites allow immutable bindings and total mathematics",
              source.span);
}
bool BodyChecker::oracleExpression(const Expression &expr) {
  using K = Expression::Kind;
  switch (expr.kind) {
  case K::Name:
  case K::Decimal:
  case K::Boolean:
  case K::And:
  case K::Or:
  case K::Call:
  case K::NotationCall:
  case K::Subscript:
  case K::Intrinsic:
  case K::Tuple:
  case K::Array:
  case K::Record:
  case K::Projection:
  case K::OracleQuery:
    return !expr.roles ||
           fail("source.oracle-body", "query expressions have no participants",
                expr.span);
  default:
    return fail(
        "source.oracle-body",
        "query suites cannot read shape/data or execute local, control, "
        "service or guard actions",
        expr.span);
  }
}
std::optional<ValueId> BodyChecker::oracleSourceQuery(const Expression &expr,
                                                      unsigned depth) {
  if (expr.kind != Expression::Kind::OracleQuery || expr.children.size() != 2) {
    fail("source.oracle-body", "only direct source queries are allowed",
         expr.span);
    return {};
  }
  auto handle = expression(expr.children.front(), {}, depth + 1);
  if (!handle)
    return {};
  auto source = *handle;
  // Immutable aliases are identity projections. No derived or assembled
  // handle can acquire a constructor source index.
  while (source.index >= body.inputs) {
    const Projection *alias = nullptr;
    for (const auto &operation : body.operations) {
      if (!checker.types.charge(1, expr.span))
        return {};
      if (llvm::any_of(operation.results, [&](ValueId value) {
            return value.index == source.index;
          })) {
        alias = std::get_if<Projection>(&operation.action);
        break;
      }
    }
    if (!alias || !alias->path.empty()) {
      fail("source.oracle-source", "query must select a direct source alias",
           expr.span);
      return {};
    }
    source = alias->input;
  }
  if (source.index >= decl.oracleDefinition->sourceCount) {
    fail("source.oracle-source",
         "query must select the constructor source prefix", expr.span);
    return {};
  }
  const auto &kind = decl.inputs[source.index].type.arguments.front();
  auto query = checker.types.associated(kind, "Query", expr.span);
  auto answer = checker.types.associated(kind, "Answer", expr.span);
  if (!query || !answer)
    return {};
  auto position = expression(expr.children.back(), *query, depth + 1);
  if (!position || !use(*handle, expr.span) || !use(*position, expr.span))
    return {};
  auto dependencies = combine({source, *position}, expr.span);
  return dependencies ? emit(OracleSourceQuery{source.index, *position},
                             *answer, *dependencies, expr.span)
                      : std::nullopt;
}
std::optional<ValueId>
BodyChecker::oraclePredicateProjection(const Expression &expr, unsigned depth) {
  using K = Expression::Kind;
  if ((expr.kind != K::OracleRows && expr.kind != K::OracleContents) ||
      expr.children.size() != 1) {
    fail("source.oracle-predicate",
         "predicate can only project source Data or rows", expr.span);
    return {};
  }
  const auto &selected = syntax.expressions[expr.children.front()];
  auto binding = selected.binding
                     ? llvm::find(syntax.inputBindings, *selected.binding)
                     : syntax.inputBindings.end();
  const auto &definition =
      *checker.output.declarations[decl.oraclePredicateOwner->index]
           .oracleDefinition;
  if (selected.kind != K::Name || binding == syntax.inputBindings.end() ||
      unsigned(binding - syntax.inputBindings.begin()) >=
          definition.sourceCount) {
    fail("source.oracle-predicate",
         "predicate projection must select a direct source", expr.span);
    return {};
  }
  auto value = expression(expr.children.front(), {}, depth + 1);
  if (!value)
    return {};
  if (expr.kind == K::OracleContents)
    return value;
  const auto &data = body.values[value->index].type;
  if (data.kind != Type::Kind::Builtin || data.domain != "vector" ||
      data.arguments.size() != 1) {
    fail("source.oracle-projection",
         "rows projection requires field table Data", expr.span);
    return {};
  }
  if (!use(*value, expr.span))
    return {};
  return emit(
      MathValue{
          MathematicalIdentity::VectorLength, {*value}, {}, data.arguments},
      Type(Type::Kind::Index), components(*value), expr.span);
}
bool Checker::oracleBody(Declaration &decl, Body &result, unsigned depth) {
  const auto &source = *sources[decl.id.index];
  BodyChecker check(*this, decl, source, result, depth);
  for (unsigned i = 0; i < decl.inputs.size(); ++i)
    if (!check.addInput(source.inputBindings[i], decl.inputs[i].type, {i},
                        decl.inputs[i].span))
      return false;
  const auto &query = decl.oracleDefinition->queryParameter;
  if (!source.oracleDefinition->queryBinding ||
      !check.addInput(*source.oracleDefinition->queryBinding, query.type,
                      {static_cast<unsigned>(decl.inputs.size())}, query.span))
    return false;
  std::vector<Port> answer{
      {"result", decl.oracleDefinition->answer, {}, decl.outputs.front().span}};
  return check.run(source.bodies.front(), answer, false) &&
         checkOracleQueryBody(types, output.declarations, decl, result);
}
bool checkOracleQueryBody(Semantics &types, ArrayRef<Declaration> declarations,
                          const Declaration &decl, const Body &body) {
  if (!decl.oracleDefinition || body.mode != Body::Mode::Oracle ||
      body.inputs != decl.inputs.size() + 1 ||
      body.values.size() < body.inputs || body.results.size() != 1 ||
      body.results.front().index >= body.values.size() ||
      body.values[body.results.front().index].type !=
          decl.oracleDefinition->answer)
    return types.fail("source.oracle-query",
                      "query signature differs from definition", decl.span);
  if (!types.charge(body.values.size() + body.inputs + 1, decl.span))
    return false;
  std::vector<std::optional<unsigned>> aliases(body.values.size());
  for (unsigned i = 0; i < decl.oracleDefinition->sourceCount; ++i)
    aliases[i] = i;
  for (const auto &value : body.values)
    if (!isLogicalValue(value.type) &&
        !types.mathematicalData(value.type, value.span, &decl))
      return false;
  std::set<std::string> sites;
  std::vector<Dependencies> inputs;
  for (unsigned i = 0; i < body.inputs; ++i)
    inputs.push_back({{i}, false});
  auto summary = summarizeBody(types, declarations, body, {}, inputs, {});
  if (!summary)
    return false;
  for (const auto &op : body.operations) {
    if (!types.charge(1, op.span))
      return false;
    for (auto result : op.results) {
      if (result.index >= body.values.size())
        return types.fail("source.oracle-body",
                          "query result is outside its body", op.span);
      if (!isLogicalValue(body.values[result.index].type))
        continue;
      const auto *projection = std::get_if<Projection>(&op.action);
      if (!projection || !projection->path.empty() ||
          projection->input.index >= aliases.size() ||
          !aliases[projection->input.index] ||
          body.values[result.index].type !=
              decl.inputs[*aliases[projection->input.index]].type)
        return types.fail("source.oracle-source",
                          "query may only alias its direct source handles",
                          op.span);
      aliases[result.index] = aliases[projection->input.index];
    }
    if (const auto *query = std::get_if<OracleSourceQuery>(&op.action)) {
      if (query->source >= decl.oracleDefinition->sourceCount ||
          query->position.index >= summary->values.size() ||
          op.results.size() != 1 ||
          op.results.front().index >= body.values.size())
        return types.fail("source.oracle-source",
                          "invalid direct source selection", op.span);
      if (!op.site || !sites.insert(*op.site).second)
        return types.fail("source.site",
                          "source query needs a unique occurrence site",
                          op.span);
      const auto &kind = decl.inputs[query->source].type.arguments.front();
      auto expectedQuery = types.associated(kind, "Query", op.span);
      auto expectedAnswer = types.associated(kind, "Answer", op.span);
      if (!expectedQuery || !expectedAnswer ||
          body.values[query->position.index].type != *expectedQuery ||
          body.values[op.results.front().index].type != *expectedAnswer)
        return types.fail("source.oracle-query",
                          "source query signature differs", op.span);
      const auto &position = summary->values[query->position.index];
      if (position.parameterized ||
          llvm::any_of(position.inputs,
                       [&](unsigned input) { return input >= body.inputs; }))
        return types.fail("source.oracle-adaptive",
                          "source query position depends on a query answer",
                          op.span);
    } else if (const auto *call = std::get_if<HelperCall>(&op.action)) {
      if (call->callee.index >= declarations.size() || call->owner ||
          declarations[call->callee.index].kind != Declaration::Kind::Math)
        return types.fail("source.oracle-body",
                          "query helper must be mathematical", op.span);
    } else if (!std::holds_alternative<MathValue>(op.action) &&
               !std::holds_alternative<HelperCall>(op.action) &&
               !std::holds_alternative<Construct>(op.action) &&
               !std::holds_alternative<Projection>(op.action) &&
               !std::holds_alternative<FiniteApplication>(op.action) &&
               !std::holds_alternative<FiniteComputation>(op.action))
      return types.fail("source.oracle-body", "forbidden action in query body",
                        op.span);
  }
  return true;
}
} // namespace zkc::language::detail
