#include "OracleDefinitions.h"
#include "Checker.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
#include <functional>
#include <set>
using namespace llvm;
namespace zkc::language::detail {
bool checkOraclePredicateReferences(Semantics &types, const Declaration &,
                                    const SyntaxDeclaration &syntax,
                                    unsigned sourceCount) {
  using K = Expression::Kind;
  std::function<bool(uint32_t, bool, unsigned)> expression;
  std::function<bool(uint32_t, unsigned)> body;
  body = [&](uint32_t region, unsigned depth) {
    const auto &source = syntax.bodies[region];
    for (const auto &statement : source.statements)
      if (!expression(statement.expression, false, depth + 1))
        return false;
    for (const auto &[name, value] : source.results)
      if (!expression(value, false, depth + 1))
        return false;
    return true;
  };
  expression = [&](uint32_t id, bool projection, unsigned depth) {
    const auto &expr = syntax.expressions[id];
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "oracle predicate depth exceeded",
                        expr.span);
    if (!types.charge(1, expr.span))
      return false;
    if (expr.kind == K::Name && expr.binding) {
      auto input = llvm::find(syntax.inputBindings, *expr.binding);
      if (input != syntax.inputBindings.end() &&
          unsigned(input - syntax.inputBindings.begin()) < sourceCount &&
          !projection)
        return types.fail(
            "source.oracle-predicate",
            "source handles require an explicit data or rows projection",
            expr.span);
    }
    const bool projects =
        expr.kind == K::OracleContents || expr.kind == K::OracleRows;
    for (auto child : expr.children)
      if (!expression(child, projects, depth + 1))
        return false;
    for (auto region : expr.regions)
      if (!body(region, depth + 1))
        return false;
    return true;
  };
  return body(0, 1);
}
bool Checker::prepareOraclePredicates() {
  // Declaration collection already allocated the child and its stable ID.
  // Authored clauses and declared source bounds share one Formula predicate.
  // Checking uses its separate Data ABI; bounds are not erased metadata.
  for (auto &decl : output.declarations) {
    if (decl.kind != Declaration::Kind::Oracle)
      continue;
    auto &source = *sources[decl.id.index];
    if (!source.oracleDefinition || source.bodies.empty())
      return types.fail("source.oracle-definition",
                        "oracle definition needs exactly one query body",
                        decl.span);
    auto predicate = llvm::find_if(decl.members, [&](DeclarationId member) {
      return sources[member.index]->oraclePredicate;
    });
    if (predicate == decl.members.end())
      return types.fail("source.oracle-predicate",
                        "missing predicate declaration", decl.span);
    auto &target = *sources[predicate->index];
    if (!types.charge(source.expressions.size() + source.bodies.size() + 1,
                      decl.span))
      return false;
    target.expressions = source.expressions;
    target.bodies = source.bodies;
    target.layoutSyntax = source.layoutSyntax;
    target.inputs = source.inputs;
    target.inputOrder = source.inputOrder;
    for (auto &port : target.inputs)
      port.purpose = RelationPurpose::Parameter;
    SyntaxBody root;
    root.span = decl.span;
    root.returned = true;
    root.notationEnvironment = source.bodies.front().notationEnvironment;
    std::optional<uint32_t> conjunction;
    auto append = [&](Expression expression) {
      auto index = uint32_t(target.expressions.size());
      target.expressions.push_back(std::move(expression));
      return index;
    };
    auto conjoin = [&](uint32_t condition, Span span) {
      if (!conjunction) {
        conjunction = condition;
        return;
      }
      Expression both;
      both.kind = Expression::Kind::And;
      both.children = {*conjunction, condition};
      both.span = span;
      conjunction = append(std::move(both));
    };
    for (const auto &clause : source.oracleDefinition->predicates) {
      if (!types.charge(1, clause.span))
        return false;
      conjoin(clause.condition, clause.span);
    }
    for (const auto &shape : source.oracleShapes) {
      if (shape.value)
        continue;
      if (!types.charge(8, shape.span))
        return false;
      Expression handle;
      handle.kind = Expression::Kind::Name;
      handle.text = shape.port;
      handle.span = shape.span;
      Expression rows;
      rows.kind = Expression::Kind::OracleRows;
      rows.children = {append(std::move(handle))};
      rows.span = shape.span;
      auto count = append(std::move(rows));
      Expression bound;
      bound.kind = Expression::Kind::Intrinsic;
      bound.text = "index.constant";
      bound.arguments = {shape.bound};
      bound.span = shape.span;
      auto maximum = append(std::move(bound));
      Expression less;
      less.kind = Expression::Kind::Intrinsic;
      less.text = "index.less";
      less.children = {count, maximum};
      less.span = shape.span;
      auto below = append(std::move(less));
      Expression equal;
      equal.kind = Expression::Kind::Intrinsic;
      equal.text = "index.equal";
      equal.children = {count, maximum};
      equal.span = shape.span;
      auto atBound = append(std::move(equal));
      Expression within;
      within.kind = Expression::Kind::Or;
      within.children = {below, atBound};
      within.span = shape.span;
      conjoin(append(std::move(within)), shape.span);
    }
    if (!conjunction) {
      Expression truth;
      truth.kind = Expression::Kind::Boolean;
      truth.text = "true";
      truth.span = decl.span;
      conjunction = target.expressions.size();
      target.expressions.push_back(std::move(truth));
    }
    root.results.emplace_back("result", *conjunction);
    target.bodies.front() = std::move(root);
  }
  return true;
}
bool Checker::oracleSignature(Declaration &decl, unsigned depth) {
  const auto &source = *sources[decl.id.index];
  if (!source.oracleDefinition || decl.outputs.size() != 1 ||
      decl.outputs.front().type.kind != Type::Kind::Oracle ||
      decl.outputs.front().type.arguments.size() != 1 || !decl.roles.empty() ||
      !decl.services.empty() || !decl.scopedInputs.empty() ||
      !decl.domainInputs.empty() || decl.effectAllowance ||
      !decl.dataPreconditions.empty() ||
      llvm::any_of(source.inputs, [](const SyntaxPort &port) {
        return port.scoped || port.domain || port.binding;
      }))
    return types.fail("source.oracle-signature",
                      "oracle constructor needs direct sources, mathematical "
                      "captures and one Oracle result without roles or effects",
                      decl.span);
  auto definition = std::make_shared<OracleDefinition>();
  definition->sourceCount = 0;
  while (definition->sourceCount < decl.inputs.size() &&
         decl.inputs[definition->sourceCount].type.kind == Type::Kind::Oracle)
    ++definition->sourceCount;
  if (!definition->sourceCount)
    return types.fail(
        "source.oracle-signature",
        "oracle constructor needs a nonempty direct source prefix", decl.span);
  for (unsigned i = definition->sourceCount; i < decl.inputs.size(); ++i)
    if (isLogicalValue(decl.inputs[i].type))
      return types.fail("source.oracle-signature",
                        "oracle sources must form a contiguous direct prefix",
                        decl.inputs[i].span);
    else if (!types.mathematicalData(decl.inputs[i].type, decl.inputs[i].span,
                                     &decl))
      return false;
  const auto &query = source.oracleDefinition->queryParameter;
  auto queryType = type(decl, query.type, depth + 1);
  auto kind = decl.outputs.front().type.arguments.front();
  auto expectedQuery = types.associated(kind, "Query", query.span);
  auto answer = types.associated(kind, "Answer", query.span);
  if (!queryType || !expectedQuery || !answer)
    return false;
  if (*queryType != *expectedQuery || query.name.empty() ||
      !query.roles.empty() || query.oracleHolder || query.scoped ||
      query.domain)
    return types.fail("source.oracle-query",
                      "query parameter must have the result kind's Query type",
                      query.span);
  definition->queryParameter = {query.name, *queryType, {}, query.span};
  definition->answer = *answer;
  if (!types.mathematicalData(*queryType, query.span, &decl) ||
      !types.mathematicalData(*answer, query.span, &decl))
    return false;
  for (auto member : decl.members)
    if (sources[member.index]->oraclePredicate)
      definition->admissibility = member;
  std::set<std::string> labels;
  for (const auto &[ordinal, predicate] :
       llvm::enumerate(source.oracleDefinition->predicates)) {
    if (predicate.label && !labels.insert(*predicate.label).second)
      return types.fail("source.oracle-predicate", "duplicate requires label",
                        predicate.span);
    definition->predicates.push_back(
        {predicate.label, unsigned(ordinal), ValueId{0}, predicate.span});
  }
  std::set<std::string> dimensions;
  for (const auto &shape : source.oracleShapes) {
    if (shape.dimension != "rows" ||
        !dimensions.insert(shape.port + "." + shape.dimension).second)
      return types.fail("source.oracle-shape", "invalid or duplicate dimension",
                        shape.span);
    auto maximum = type(decl, shape.bound, depth + 1);
    if (!maximum)
      return false;
    if (maximum->kind != Type::Kind::Natural)
      return types.fail("source.oracle-shape", "shape bound must be static Nat",
                        shape.span);
    auto input = llvm::find_if(
        decl.inputs, [&](const Port &port) { return port.name == shape.port; });
    if (!shape.value) {
      if (input == decl.inputs.end() ||
          unsigned(input - decl.inputs.begin()) >= definition->sourceCount)
        return types.fail("source.oracle-shape",
                          "source bound must select a direct source",
                          shape.span);
      const auto &sourceKind = input->type.arguments.front();
      if (sourceKind.symbolic || sourceKind.domain != "table" ||
          sourceKind.arguments.size() != 1)
        return types.fail("source.oracle-shape",
                          "source row bounds require an unsized table kind",
                          shape.span);
      definition->sourceBounds.push_back(
          {static_cast<unsigned>(input - decl.inputs.begin()), shape.dimension,
           *maximum, shape.span});
    } else {
      if (shape.port != decl.outputs.front().name || kind.symbolic ||
          kind.domain != "table" || kind.arguments.size() != 1)
        return types.fail("source.oracle-shape",
                          "result shape must select the unsized result table",
                          shape.span);
      auto capture = llvm::find_if(decl.inputs, [&](const Port &port) {
        return port.name == *shape.value;
      });
      if (capture == decl.inputs.end() ||
          unsigned(capture - decl.inputs.begin()) < definition->sourceCount ||
          capture->type.kind != Type::Kind::Index)
        return types.fail("source.oracle-shape",
                          "result rows must select an index capture",
                          shape.span);
      definition->resultShape.push_back(
          {shape.dimension, unsigned(capture - decl.inputs.begin()), *maximum,
           shape.span});
    }
  }
  // An unsized constructor must publish its shape carrier and source bounds.
  for (unsigned i = 0; i < definition->sourceCount; ++i) {
    const auto &sourceKind = decl.inputs[i].type.arguments.front();
    if (!sourceKind.symbolic && sourceKind.arguments.size() == 1 &&
        llvm::none_of(definition->sourceBounds,
                      [&](const auto &bound) { return bound.source == i; }))
      return types.fail("source.oracle-shape",
                        "unsized source needs a row bound",
                        decl.inputs[i].span);
  }
  if (!kind.symbolic && kind.arguments.size() == 1 &&
      definition->resultShape.empty())
    return types.fail("source.oracle-shape",
                      "unsized result needs captured rows",
                      decl.outputs.front().span);
  decl.oracleDefinition = std::move(definition);
  return true;
}
bool Checker::oraclePredicateSignature(Declaration &decl) {
  const auto &owner = output.declarations[decl.parent->index];
  if (!owner.oracleDefinition)
    return types.fail("source.oracle-predicate",
                      "predicate has no oracle owner", decl.span);
  decl.oraclePredicateOwner = owner.id;
  decl.inputs = owner.inputs;
  decl.inputOrder = owner.inputOrder;
  for (unsigned i = 0; i < owner.oracleDefinition->sourceCount; ++i) {
    auto data = types.associated(owner.inputs[i].type.arguments.front(), "Data",
                                 decl.inputs[i].span);
    if (!data)
      return false;
    decl.inputs[i].type = std::move(*data);
  }
  decl.outputs = {{"result", Type{}, {}, decl.span}};
  decl.relation->purposes.assign(decl.inputs.size(),
                                 RelationPurpose::Parameter);
  for (const auto &port : decl.inputs)
    if (!types.relationData(decl, port.type, port.span))
      return false;
  return true;
}
bool Checker::retainOraclePredicates(Declaration &predicate, const Body &body) {
  auto &owner = output.declarations[predicate.oraclePredicateOwner->index];
  auto definition = std::make_shared<OracleDefinition>(*owner.oracleDefinition);
  const auto &clauses = sources[owner.id.index]->oracleDefinition->predicates;
  if (clauses.size() != definition->predicates.size())
    return types.fail("source.oracle-predicate", "requires inventory differs",
                      owner.span);
  for (unsigned i = 0; i < clauses.size(); ++i) {
    auto found = body.expressionValues.find(clauses[i].condition);
    if (found == body.expressionValues.end() ||
        body.values[found->second.index].type.kind != Type::Kind::Boolean)
      return types.fail("source.oracle-predicate", "requires was not checked",
                        clauses[i].span);
    definition->predicates[i].condition = found->second;
  }
  owner.oracleDefinition = std::move(definition);
  return true;
}
} // namespace zkc::language::detail
