#include "BindingWitness.h"
#include "Reductions.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool same(Span a, Span b) {
  return a.module.index == b.module.index && a.begin == b.begin &&
         a.end == b.end;
}
bool same(ArrayRef<ValueId> a, ArrayRef<ValueId> b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(),
                    [](ValueId x, ValueId y) { return x.index == y.index; });
}
class ExtractionCheck {
  Semantics &types;
  const CheckedStorage &storage;
  const ReductionSource &source;
  const SyntaxDeclaration &syntax;
  const Expression &mapping;
  const Body &outer;
  const Operation &operation;
  const ReductionBinding &witness;
  const Declaration &helper;
  const Body &body;
  Type field;
  std::set<BindingId> defined, seen;
  std::vector<std::pair<BindingId, Span>> captures;
  std::map<BindingId, ValueId> values;
  std::map<uint32_t, ValueId> expressionValues;
  std::set<uint32_t> usedExpressions;
  unsigned cursor = 0;
  bool refuse(Span at) {
    return types.fail(
        "source.reduction-witness",
        "finite reduction differs from its resolved authored body", at);
  }
  bool bounded(unsigned depth, Span at) {
    if (depth > types.work.limits.expressionDepth)
      return types.fail("source.limit", "reduction witness depth exceeded", at);
    return types.charge(1, at);
  }
  // This lexical traversal is independent of extraction's sorted reference
  // collection. BindingIds distinguish shadowed lets, rows and outer names.
  bool freeBody(uint32_t id, unsigned depth) {
    const auto &region = syntax.bodies[id];
    if (!bounded(depth, region.span))
      return false;
    for (const auto &statement : region.statements) {
      if (!freeExpression(statement.expression, depth + 1))
        return false;
      if (statement.kind == Statement::Kind::Let && statement.pattern.binding)
        defined.insert(*statement.pattern.binding);
    }
    for (const auto &result : region.results)
      if (!freeExpression(result.second, depth + 1))
        return false;
    return true;
  }
  bool freeExpression(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions[id];
    if (!bounded(depth, expr.span))
      return false;
    if (expr.kind == Expression::Kind::Name) {
      if (!expr.binding)
        return refuse(expr.span);
      if (!defined.count(*expr.binding) && seen.insert(*expr.binding).second)
        captures.emplace_back(*expr.binding, expr.span);
    }
    for (auto child : expr.children)
      if (!freeExpression(child, depth + 1))
        return false;
    for (auto region : expr.regions)
      if (!freeBody(region, depth + 1))
        return false;
    return true;
  }
  const Operation *next(Span at) {
    if (cursor >= body.operations.size() ||
        !same(body.operations[cursor].span, at)) {
      refuse(at);
      return nullptr;
    }
    return &body.operations[cursor++];
  }
  std::optional<ValueId> result(const Operation &op) {
    if (op.results.size() != 1 ||
        op.results.front().index >= body.values.size()) {
      refuse(op.span);
      return {};
    }
    return op.results.front();
  }
  bool selection(uint32_t id, const CallBinding &binding) {
    const auto &expected = source.inference;
    auto selected = expected.callees.find(id);
    auto arguments = expected.arguments.find(id);
    if (selected == expected.callees.end() ||
        arguments == expected.arguments.end() ||
        binding.target.declaration.index !=
            selected->second.declaration.index ||
        binding.target.component != selected->second.component ||
        binding.arguments != arguments->second)
      return refuse(syntax.expressions[id].span);
    const auto &expr = syntax.expressions[id];
    if (expr.notation) {
      auto original = expected.operators.find(id);
      if (!binding.notation || *binding.notation != *expr.notation ||
          !binding.origin || original == expected.operators.end() ||
          !same(*binding.origin, original->second.binding) ||
          binding.family != original->second.family)
        return refuse(expr.span);
    } else if (binding.notation || binding.origin || !binding.symbol.empty())
      return refuse(expr.span);
    return true;
  }
  std::optional<ValueId> region(uint32_t id, unsigned depth) {
    const auto &block = syntax.bodies[id];
    if (!bounded(depth, block.span))
      return {};
    for (const auto &statement : block.statements) {
      auto value = expression(statement.expression, depth + 1);
      if (!value)
        return {};
      if (statement.kind == Statement::Kind::Let && statement.pattern.binding) {
        auto alias = next(statement.pattern.span);
        auto projection =
            alias ? std::get_if<Projection>(&alias->action) : nullptr;
        if (!projection || !projection->path.empty() ||
            projection->input.index != value->index) {
          refuse(statement.span);
          return {};
        }
        auto bound = result(*alias);
        if (!bound)
          return {};
        values.emplace(*statement.pattern.binding, *bound);
      }
    }
    if (block.results.size() != 1) {
      refuse(block.span);
      return {};
    }
    return expression(block.results.front().second, depth + 1);
  }
  std::optional<ValueId> expression(uint32_t id, unsigned depth) {
    const auto &expr = syntax.expressions[id];
    if (!bounded(depth, expr.span))
      return {};
    std::optional<ValueId> value;
    using K = Expression::Kind;
    if (expr.kind == K::Name) {
      auto found = expr.binding ? values.find(*expr.binding) : values.end();
      if (found != values.end())
        value = found->second;
    } else if (expr.kind == K::Block) {
      value = region(expr.regions.front(), depth + 1);
    } else {
      std::vector<ValueId> operands;
      for (auto child : expr.children) {
        auto operand = expression(child, depth + 1);
        if (!operand)
          return {};
        operands.push_back(*operand);
      }
      auto op = next(expr.span);
      if (!op)
        return {};
      value = result(*op);
      if (expr.kind == K::Decimal) {
        auto literal = std::get_if<MathValue>(&op->action);
        if (!literal ||
            literal->identity != MathematicalIdentity::FieldConstant ||
            literal->literal != expr.text || !literal->operands.empty() ||
            !literal->staticArguments.empty() || !literal->parameters.empty())
          value.reset();
      } else if (expr.kind == K::Call || expr.kind == K::NotationCall) {
        auto order = source.inference.inputs.find(id);
        if (!op->binding || !selection(id, *op->binding) ||
            order == source.inference.inputs.end() ||
            order->second.size() != operands.size())
          value.reset();
        else {
          std::vector<ValueId> parameters(operands.size());
          for (unsigned i = 0; i < operands.size(); ++i) {
            if (order->second[i] >= parameters.size()) {
              value.reset();
              break;
            }
            parameters[order->second[i]] = operands[i];
          }
          if (!same(parameters, op->binding->operands) ||
              !checkCallAction(types, storage.declarations, body, *op))
            value.reset();
        }
      } else if (expr.kind == K::Intrinsic) {
        auto math = std::get_if<MathValue>(&op->action);
        auto intrinsic = mathematicalIntrinsic(expr.text);
        if (!math || !intrinsic || math->identity != intrinsic->identity ||
            !same(math->operands, operands) ||
            math->parameters != expr.labels ||
            math->staticArguments != std::vector<Type>{field})
          value.reset();
      } else
        value.reset();
    }
    auto recorded = expressionValues.find(id);
    if (!value || recorded == expressionValues.end() ||
        value->index != recorded->second.index ||
        value->index >= body.values.size() ||
        body.values[value->index].type != field) {
      if (!types.diagnostic)
        refuse(expr.span);
      return {};
    }
    usedExpressions.insert(id);
    return value;
  }

public:
  ExtractionCheck(Semantics &types, const CheckedStorage &storage,
                  const ReductionSource &source, const Body &outer,
                  const Operation &operation)
      : types(types), storage(storage), source(source), syntax(*source.syntax),
        mapping(syntax.expressions[source.expression]), outer(outer),
        operation(operation), witness(*operation.reduction),
        helper(storage.declarations[source.helper.index]), body(*helper.body),
        field(source.inference.expressions.at(source.expression)
                  .arguments.front()) {}
  bool run(unsigned mapIndex) {
    auto bulk = std::get_if<BulkApplication>(&operation.action);
    const auto &owner = storage.declarations[source.owner.index];
    if (!types.charge(helper.inputs.size() + helper.parameters.size() +
                          witness.inputs.size() + witness.expressions.size() +
                          1,
                      operation.span))
      return false;
    if (!bulk || bulk->callee.index != source.helper.index ||
        !same(operation.span, mapping.span) ||
        helper.kind != Declaration::Kind::Math || helper.isPublic ||
        helper.abstract || helper.primitive || helper.origin ||
        !helper.services.empty() || !helper.parent ||
        helper.parent->index != source.owner.index ||
        helper.module.index != owner.module.index || !helper.anonymous ||
        !helper.generatedReduction ||
        helper.generatedReduction->enclosing.index != source.owner.index ||
        helper.generatedReduction->ordinal != mapping.reductionOrdinal ||
        !same(helper.span, syntax.bodies[mapping.regions.front()].span))
      return refuse(operation.span);
    std::string identity;
    frame(identity, "generated-reduction");
    frame(identity, owner.qualifiedName);
    frame(identity, std::to_string(mapping.reductionOrdinal));
    auto name = "reduction<" + std::to_string(mapping.reductionOrdinal) + ">";
    if (helper.symbol != "zki_" + digest(identity) || helper.name != name ||
        helper.qualifiedName != owner.qualifiedName + "::" + name)
      return refuse(operation.span);
    std::vector<Type> arguments;
    for (const auto &parameter : owner.parameters)
      arguments.push_back(parameterType(parameter));
    if (bulk->arguments != arguments ||
        helper.parameters.size() != arguments.size() ||
        helper.outputs.size() != 1 || helper.outputs.front().type != field ||
        helper.inputs.size() != bulk->operands.size() ||
        body.inputs != helper.inputs.size() ||
        body.values.size() < body.inputs ||
        !same(helper.outputs.front().span, helper.span))
      return refuse(operation.span);
    for (unsigned i = 0; i < owner.parameters.size(); ++i)
      if (parameterType(helper.parameters[i]) != arguments[i])
        return refuse(operation.span);
    for (const auto &row : mapping.index.children)
      if (row.binding)
        defined.insert(*row.binding);
    if (!freeBody(mapping.regions.front(), 1))
      return false;
    const unsigned rows = mapping.children.size();
    if (rows != mapping.index.children.size() ||
        source.collections.size() != rows ||
        bulk->operands.size() != rows + captures.size() ||
        witness.inputs.size() != bulk->operands.size() ||
        bulk->mapped.size() != bulk->operands.size() ||
        mapIndex < captures.size())
      return refuse(operation.span);
    for (unsigned i = 0; i < bulk->operands.size(); ++i) {
      auto expectedBinding = i < rows ? mapping.index.children[i].binding
                                      : std::optional(captures[i - rows].first);
      auto expectedSpan = i < rows
                              ? mapping.index.children[i].span
                              : syntax.bindings[expectedBinding->index].span;
      auto bindingIndex = expectedBinding
                              ? std::optional(expectedBinding->index)
                              : std::nullopt;
      if (witness.inputs[i] != bindingIndex || bulk->mapped[i] != (i < rows) ||
          helper.inputs[i].type != field ||
          !same(helper.inputs[i].span, expectedSpan) ||
          body.values[i].type != field ||
          body.values[i].components != std::vector<unsigned>{i} ||
          !same(body.values[i].span, expectedSpan) ||
          bulk->operands[i].index >= outer.values.size())
        return refuse(operation.span);
      if (expectedBinding)
        values.emplace(*expectedBinding, ValueId{i});
      if (i < rows) {
        if (bulk->operands[i].index != source.collections[i].index ||
            outer.values[bulk->operands[i].index].type !=
                source.inference.expressions.at(source.expression))
          return refuse(operation.span);
      } else {
        auto [binding, at] = captures[i - rows];
        const auto &lexical = syntax.bindings[binding.index];
        auto original = source.environment.find(binding);
        const auto &read =
            outer.operations[mapIndex - captures.size() + i - rows];
        auto projection = std::get_if<Projection>(&read.action);
        if (lexical.mutableBinding || lexical.service ||
            original == source.environment.end() || !projection ||
            !projection->path.empty() ||
            projection->input.index != original->second.index ||
            !same(read.span, at) || read.results.size() != 1 ||
            read.results.front().index != bulk->operands[i].index ||
            outer.values[bulk->operands[i].index].type != field)
          return refuse(operation.span);
      }
    }
    if (operation.results.size() != 1 ||
        operation.results.front().index >= outer.values.size() ||
        outer.values[operation.results.front().index].type !=
            source.inference.expressions.at(source.expression) ||
        mapIndex + 1 >= outer.operations.size())
      return refuse(operation.span);
    const auto &reducer = outer.operations[mapIndex + 1];
    const auto reducerId = mapping.reducerExpression;
    if (!same(reducer.span, syntax.expressions[reducerId].span) ||
        !reducer.binding || !selection(reducerId, *reducer.binding) ||
        !same(reducer.binding->operands, operation.results) ||
        !checkCallAction(types, storage.declarations, outer, reducer))
      return types.diagnostic ? false : refuse(reducer.span);
    if (!reductionTarget(
            types,
            storage.declarations[reducer.binding->target.declaration.index],
            reducer.binding->target, reducer.binding->arguments, reducer.span))
      return false;
    for (auto [id, value] : witness.expressions)
      if (!expressionValues.emplace(id, value).second)
        return refuse(operation.span);
    auto scalar = region(mapping.regions.front(), 1);
    if (!scalar || cursor != body.operations.size() ||
        body.results.size() != 1 ||
        scalar->index != body.results.front().index ||
        usedExpressions.size() != expressionValues.size())
      return types.diagnostic ? false : refuse(operation.span);
    return checkReductionRing(types, storage.declarations, body, field,
                              operation.span);
  }
};
} // namespace
Error checkReductions(const CheckedStorage &storage, Work &work) {
  if (storage.reductions.empty())
    return Error::success();
  Semantics types(storage.declarations, storage.assets, work);
  std::set<unsigned> seen;
  std::function<bool(const Body &, unsigned, unsigned)> visit;
  visit = [&](const Body &body, unsigned owner, unsigned depth) {
    if (depth > work.limits.expressionDepth)
      return types.fail("source.limit",
                        "reduction witness region depth exceeded",
                        storage.declarations[owner].span);
    for (unsigned index = 0; index < body.operations.size(); ++index) {
      const auto &op = body.operations[index];
      if (!types.charge(1, op.span))
        return false;
      auto bulk = std::get_if<BulkApplication>(&op.action);
      bool generated = bulk &&
                       bulk->callee.index < storage.declarations.size() &&
                       storage.declarations[bulk->callee.index]
                           .generatedReduction.has_value();
      if (generated != op.reduction.has_value())
        return types.fail("source.reduction-witness",
                          "missing or unexpected reduction evidence", op.span);
      if (op.reduction) {
        auto id = op.reduction->source;
        if (id >= storage.reductions.size() || !seen.insert(id).second)
          return types.fail("source.reduction-witness",
                            "duplicate or missing reduction source", op.span);
        const auto &source = *storage.reductions[id];
        if (source.owner.index != owner || !source.syntax ||
            source.helper.index >= storage.declarations.size() ||
            !storage.declarations[source.helper.index].body)
          return types.fail("source.reduction-witness",
                            "reduction source owner differs", op.span);
        if (!ExtractionCheck(types, storage, source, body, op).run(index))
          return false;
      }
      if (auto control = std::get_if<LocalControl>(&op.action))
        for (const auto &region : control->regions)
          if (!visit(*region, owner, depth + 1))
            return false;
      if (auto repeat = std::get_if<ProtocolRepeat>(&op.action))
        if (!visit(*repeat->region, owner, depth + 1))
          return false;
    }
    return true;
  };
  for (const auto &decl : storage.declarations)
    if (decl.body && !visit(*decl.body, decl.id.index, 1))
      return types.takeError();
  if (seen.size() != storage.reductions.size())
    return failure("source.reduction-witness",
                   "authored reduction was not emitted");
  return Error::success();
}
} // namespace zkc::language::detail
namespace zkc::language {
Error checkReductionElaboration(const CheckedProject &project,
                                const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  // Operation ceilings belong to each phase. Native comparison may have a
  // smaller selected graph than the completed project, including the prelude.
  if (project.checkedWork() > limits.work ||
      project.checkedDeclarations() > limits.declarations)
    return detail::failure("source.limit",
                           "checked project exceeds reduction witness limits");
  detail::Work work{limits};
  return detail::checkReductions(*project.storage, work);
}
} // namespace zkc::language
