#include "Reductions.h"
#include "BodyCheck.h"
#include "zkc/Language/Builtins.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
bool reductionTarget(Semantics &types, const Declaration &callee,
                     const CallableReference &target, ArrayRef<Type> arguments,
                     Span span) {
  auto refuse = [&] {
    return types.fail(
        "source.reduction-target",
        "a reduction requires a static defined local Vector<F> -> F callable",
        span);
  };
  if (target.component || callee.abstract ||
      callee.kind != Declaration::Kind::Local || callee.inputs.size() != 1 ||
      callee.outputs.size() != 1 || !callee.services.empty() ||
      arguments.size() != callee.parameters.size())
    return refuse();
  auto substitution = types.substitution(callee, arguments);
  auto input = types.substitute(callee.inputs.front().type, substitution, span);
  auto output =
      types.substitute(callee.outputs.front().type, substitution, span);
  return input && output &&
         ((output->kind == Type::Kind::Field &&
           input->kind == Type::Kind::Builtin && input->domain == "vector" &&
           input->arguments == std::vector<Type>{*output}) ||
          refuse());
}

bool checkReductionRing(Semantics &types, ArrayRef<Declaration> declarations,
                        const Body &body, const Type &field, Span span) {
  std::set<std::string> admitted, active;
  std::function<bool(const Body &, const Substitution &, unsigned)> visit;
  auto refuse = [&](Span at) {
    return types.fail("source.reduction-body",
                      "every scalar-body operation and concrete helper must "
                      "belong to the same field ring",
                      at, {span});
  };
  visit = [&](const Body &current, const Substitution &substitution,
              unsigned depth) {
    if (depth > types.work.limits.callDepth)
      return types.fail("source.limit", "reduction ring helper depth exceeded",
                        span);
    if (current.mode != Body::Mode::Math || current.stopped ||
        current.mayStop || current.opaque || !current.services.empty() ||
        current.results.size() != 1)
      return refuse(span);
    for (const auto &value : current.values) {
      auto closed = types.substitute(value.type, substitution, value.span);
      if (!closed || *closed != field)
        return types.diagnostic ? false : refuse(value.span);
    }
    for (const auto &operation : current.operations) {
      if (!types.charge(1, operation.span))
        return false;
      if (auto math = std::get_if<MathValue>(&operation.action)) {
        using I = MathematicalIdentity;
        if (math->identity != I::FieldConstant &&
            math->identity != I::FieldAdd &&
            math->identity != I::FieldSubtract &&
            math->identity != I::FieldMultiply)
          return refuse(operation.span);
        if (math->staticArguments.size() > 1 || !math->parameters.empty() ||
            math->operands.size() !=
                (math->identity == I::FieldConstant ? 0u : 2u) ||
            operation.results.size() != 1)
          return refuse(operation.span);
        for (const auto &argument : math->staticArguments) {
          auto scalar =
              types.substitute(argument, substitution, operation.span);
          if (!scalar || *scalar != field)
            return types.diagnostic ? false : refuse(operation.span);
        }
      } else if (auto alias = std::get_if<Projection>(&operation.action)) {
        if (!alias->path.empty())
          return refuse(operation.span);
      } else if (auto call = std::get_if<HelperCall>(&operation.action)) {
        if (call->component || call->callee.index >= declarations.size())
          return refuse(operation.span);
        const auto &callee = declarations[call->callee.index];
        if (callee.kind != Declaration::Kind::Math || callee.abstract ||
            !callee.body || callee.inputs.size() != call->operands.size() ||
            callee.outputs.size() != 1 ||
            callee.parameters.size() != call->arguments.size())
          return refuse(operation.span);
        std::vector<Type> arguments;
        std::string key = std::to_string(call->callee.index);
        for (const auto &argument : call->arguments) {
          auto value = types.substitute(argument, substitution, operation.span);
          if (!value)
            return false;
          frame(key, typeIdentity(*value));
          arguments.push_back(*value);
        }
        auto bindings = types.substitution(callee, arguments);
        for (auto ports : {ArrayRef(callee.inputs), ArrayRef(callee.outputs)})
          for (const auto &port : ports) {
            auto type = types.substitute(port.type, bindings, port.span);
            if (!type || *type != field)
              return types.diagnostic ? false : refuse(port.span);
          }
        if (!admitted.count(key)) {
          if (!active.insert(key).second)
            return refuse(operation.span);
          if (!visit(*callee.body, bindings, depth + 1))
            return false;
          active.erase(key);
          admitted.insert(std::move(key));
        }
      } else
        return refuse(operation.span);
    }
    return true;
  };
  return field.kind == Type::Kind::Field && visit(body, {}, 1);
}

std::optional<ValueId> BodyChecker::reduction(const Expression &expr,
                                              unsigned depth) {
  if (!local()) {
    fail("source.mode", "finite reductions require local mode", expr.span);
    return {};
  }
  // Component members need a separate self-capture contract. The first profile
  // keeps generated helpers static in their original module.
  if (decl.parent) {
    fail("source.reduction-body",
         "reduction helpers require a module-level enclosing function",
         expr.span);
    return {};
  }
  const auto expressionId = uint32_t(&expr - syntax.expressions.data());
  const auto vector = inferredType(expressionId);
  if (!vector || vector->kind != Type::Kind::Builtin ||
      vector->domain != "vector" || vector->arguments.size() != 1 ||
      vector->arguments.front().kind != Type::Kind::Field) {
    fail("source.reduction-body",
         "reduction rows must be vectors of one scalar field", expr.span);
    return {};
  }
  const auto field = vector->arguments.front();
  const auto &region = syntax.bodies[expr.regions.front()];
  auto source = std::make_shared<ReductionSource>();
  source->owner = decl.id;
  source->expression = expressionId;
  std::vector<ValueId> operands;
  for (auto collection : expr.children) {
    auto value = expression(collection, *vector, depth + 1);
    if (!value || !use(*value, syntax.expressions[collection].span))
      return {};
    operands.push_back(*value);
  }
  source->collections = operands;
  // Snapshot the lexical value environment after evaluating collections, before
  // introducing row bindings. Independent validation reconstructs free names.
  for (const auto &[binding, state] : bindings) {
    if (!checker.types.charge(1, expr.span))
      return {};
    if (state.value)
      source->environment.emplace(binding, *state.value);
  }
  std::set<BindingId> introduced;
  for (const auto &row : expr.index.children)
    if (row.binding)
      introduced.insert(*row.binding);
  std::vector<uint32_t> references, visited;
  std::function<bool(uint32_t, unsigned)> scanExpression;
  std::function<bool(uint32_t, unsigned)> scanBody;
  scanBody = [&](uint32_t id, unsigned level) {
    const auto &block = syntax.bodies[id];
    if (block.stopped)
      return fail("source.reduction-body", "a scalar binder body must be total",
                  block.span);
    for (const auto &statement : block.statements) {
      if (statement.mutableBinding ||
          (statement.kind != Statement::Kind::Let &&
           statement.kind != Statement::Kind::Expression) ||
          (statement.kind == Statement::Kind::Let &&
           statement.pattern.kind != Pattern::Kind::Name &&
           statement.pattern.kind != Pattern::Kind::Ignore))
        return fail(
            "source.reduction-body",
            "scalar bodies admit immutable scalar lets and ring expressions",
            statement.span);
      if (statement.pattern.binding)
        introduced.insert(*statement.pattern.binding);
      if (!scanExpression(statement.expression, level + 1))
        return false;
    }
    for (const auto &result : block.results)
      if (!scanExpression(result.second, level + 1))
        return false;
    return true;
  };
  scanExpression = [&](uint32_t id, unsigned level) {
    const auto &value = syntax.expressions[id];
    if (level > checker.work.limits.expressionDepth)
      return fail("source.limit", "reduction capture depth exceeded",
                  value.span);
    if (!checker.types.charge(1, value.span))
      return false;
    using K = Expression::Kind;
    if (value.kind != K::Name && value.kind != K::Decimal &&
        value.kind != K::Call && value.kind != K::NotationCall &&
        value.kind != K::Intrinsic && value.kind != K::Block)
      return fail("source.reduction-body",
                  "expression is outside the scalar ring profile", value.span);
    visited.push_back(id);
    if (value.binding)
      references.push_back(id);
    for (auto child : value.children)
      if (!scanExpression(child, level + 1))
        return false;
    for (auto block : value.regions)
      if (!scanBody(block, level + 1))
        return false;
    return true;
  };
  if (!scanBody(expr.regions.front(), 1))
    return {};
  llvm::sort(references, [&](auto left, auto right) {
    return syntax.expressions[left].span.begin <
           syntax.expressions[right].span.begin;
  });
  std::vector<std::pair<BindingId, Span>> captures;
  std::set<BindingId> captured;
  for (auto id : references) {
    const auto &reference = syntax.expressions[id];
    const auto binding = *reference.binding;
    if (introduced.count(binding) || !captured.insert(binding).second)
      continue;
    auto found = bindings.find(binding);
    const auto &original = syntax.bindings[binding.index];
    if (original.mutableBinding || original.service ||
        found == bindings.end() || !found->second.value ||
        found->second.type != field) {
      fail("source.reduction-capture",
           "captures must be whole immutable scalars in the row field",
           reference.span);
      return {};
    }
    auto permissions = checker.types.permissions(field, reference.span, &decl);
    if (!permissions || !permissions->copy || !permissions->drop) {
      if (!checker.types.diagnostic)
        fail("source.reduction-capture", "captures require Copy and Drop",
             reference.span);
      return {};
    }
    captures.emplace_back(binding, reference.span);
  }
  if (!checker.types.accept(checker.work.count(
          checker.work.declarations, checker.work.limits.declarations,
          "generated reduction declaration count", expr.span)))
    return {};
  Declaration helper{};
  helper.id = {uint32_t(checker.output.declarations.size() +
                        checker.pendingReductions.size())};
  helper.kind = Declaration::Kind::Math;
  helper.module = decl.module;
  helper.parent = decl.id;
  helper.anonymous = true;
  helper.generatedReduction =
      GeneratedReduction{decl.id, expr.reductionOrdinal};
  helper.name = "reduction<" + std::to_string(expr.reductionOrdinal) + ">";
  helper.qualifiedName = decl.qualifiedName + "::" + helper.name;
  helper.span = region.span;
  std::string identity;
  frame(identity, "generated-reduction");
  frame(identity, decl.qualifiedName);
  frame(identity, std::to_string(expr.reductionOrdinal));
  helper.symbol = "zki_" + digest(identity);
  Body scalar;
  scalar.mode = Body::Mode::Math;
  BodyChecker nested(checker, decl, syntax, scalar, callDepth + 1);
  nested.inference = inference;
  std::map<uint32_t, ValueId> expressionValues;
  nested.reductionValues = &expressionValues;
  ReductionBinding evidence{uint32_t(checker.reductionSources.size()), {}, {}};
  for (unsigned i = 0; i < expr.index.children.size(); ++i) {
    const auto &row = expr.index.children[i];
    helper.inputs.push_back({row.name, field, {}, row.span});
    evidence.inputs.push_back(row.binding ? std::optional(row.binding->index)
                                          : std::nullopt);
    if (row.binding) {
      if (!nested.addInput(*row.binding, field, {i}, row.span))
        return {};
    } else if (!nested.input(field, {i}, row.span))
      return {};
  }
  for (auto [binding, at] : captures) {
    auto value = fresh(*bindings.at(binding).value, at);
    if (!value)
      return {};
    operands.push_back(*value);
    auto index = unsigned(helper.inputs.size());
    const auto &original = syntax.bindings[binding.index];
    helper.inputs.push_back({original.name, field, {}, original.span});
    evidence.inputs.push_back(binding.index);
    if (!nested.addInput(binding, field, {index}, original.span))
      return {};
  }
  auto result = nested.tail(region, field);
  if (!result || !nested.use(*result, region.span) ||
      !nested.finish(region.span))
    return {};
  scalar.results.push_back(*result);
  if (!checkReductionRing(checker.types, checker.output.declarations, scalar,
                          field, expr.span))
    return {};
  helper.outputs.push_back({"result", field, {}, region.span});
  helper.body = std::make_shared<Body>(std::move(scalar));
  source->helper = helper.id;
  evidence.expressions.assign(expressionValues.begin(), expressionValues.end());
  // Retain only solved facts for this scalar body and its enclosing reducer.
  visited.push_back(expressionId);
  visited.push_back(expr.reducerExpression);
  for (auto id : visited) {
    if (!checker.types.charge(1, syntax.expressions[id].span))
      return {};
    if (auto it = inference->expressions.find(id);
        it != inference->expressions.end()) {
      if (!checker.types.chargeType(it->second, expr.span))
        return {};
      source->inference.expressions.emplace(*it);
    }
    if (auto it = inference->callees.find(id); it != inference->callees.end())
      source->inference.callees.emplace(*it);
    if (auto it = inference->arguments.find(id);
        it != inference->arguments.end()) {
      for (const auto &argument : it->second)
        if (!checker.types.chargeType(argument, expr.span))
          return {};
      source->inference.arguments.emplace(*it);
    }
    if (auto it = inference->operators.find(id);
        it != inference->operators.end()) {
      for (const auto &member : it->second.family)
        if (!checker.types.charge(member.size() + 1, expr.span))
          return {};
      source->inference.operators.emplace(*it);
    }
    if (auto it = inference->inputs.find(id); it != inference->inputs.end()) {
      if (!checker.types.charge(it->second.size(), expr.span))
        return {};
      source->inference.inputs.emplace(*it);
    }
  }
  auto helperId = helper.id;
  checker.pendingReductions.push_back(
      {std::move(helper), inference->reductionHeights.at(expressionId)});
  checker.reductionSources.push_back(std::move(source));
  std::vector<Type> arguments;
  for (const auto &parameter : decl.parameters)
    arguments.push_back(parameterType(parameter));
  std::vector<bool> mapped(operands.size(), false);
  std::fill_n(mapped.begin(), expr.children.size(), true);
  body.mayStop = true;
  auto value = emit(BulkApplication{helperId, operands, arguments, mapped},
                    *vector, {}, expr.span);
  if (value)
    body.operations.back().reduction = std::move(evidence);
  return value;
}

bool Checker::finalizeReductions() {
  // All authored checks and lazy signature consumers have finished. No source
  // name lookup can reach a pending helper; only BulkApplication stores its ID.
  for (auto &pending : pendingReductions) {
    auto &helper = pending.declaration;
    const auto &owner =
        output.declarations[helper.generatedReduction->enclosing.index];
    if (!types.charge(owner.parameters.size() + owner.bounds.size() +
                          owner.permissionBounds.size() +
                          owner.capabilityBounds.size() + 1,
                      helper.span))
      return false;
    for (const auto &parameter : owner.parameters)
      if (!types.chargeType(parameterType(parameter), helper.span))
        return false;
    for (const auto &bound : owner.bounds)
      if (!types.charge(bound.lhs.spelling().size() +
                            bound.rhs.spelling().size(),
                        helper.span))
        return false;
    for (const auto &bound : owner.permissionBounds)
      if (!types.chargeType(bound.type, helper.span))
        return false;
    for (const auto &bound : owner.capabilityBounds) {
      if (!types.charge(bound.predicate.size() + 1, helper.span))
        return false;
      for (const auto &argument : bound.arguments)
        if (!types.chargeType(argument, helper.span))
          return false;
    }
    helper.parameters = owner.parameters;
    helper.bounds = owner.bounds;
    helper.permissionBounds = owner.permissionBounds;
    helper.capabilityBounds = owner.capabilityBounds;
    output.declarations.push_back(std::move(helper));
    bodyHeights.push_back(pending.height);
  }
  pendingReductions.clear();
  return true;
}
bool Checker::retainReductionSources() {
  std::map<unsigned, std::shared_ptr<const SyntaxDeclaration>> retained;
  for (auto &source : reductionSources) {
    auto &syntax = retained[source->owner.index];
    if (!syntax) {
      if (!types.charge(1, output.declarations[source->owner.index].span))
        return false;
      syntax = std::make_shared<SyntaxDeclaration>(
          std::move(*sources[source->owner.index]));
    }
    source->syntax = syntax;
    output.reductions.push_back(source);
  }
  return true;
}
} // namespace zkc::language::detail
