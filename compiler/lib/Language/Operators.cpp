#include "Arguments.h"
#include "BindingWitness.h"
#include "CallableConstraints.h"
#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
StringRef operatorSymbol(const Expression &expression) {
  return (expression.kind == Expression::Kind::NotationCall ||
          expression.kind == Expression::Kind::Subscript) &&
                 expression.notation
             ? StringRef(expression.notation->symbol)
             : StringRef{};
}
std::string operatorBindingKey(const OperatorBinding &binding,
                               ArrayRef<Declaration> declarations) {
  std::string key;
  if (binding.notation) {
    const auto &notation = *binding.notation;
    frame(key, notation.key());
    frame(key, notation.closing);
    frame(key, std::to_string(static_cast<unsigned>(notation.association)));
    frame(key, std::to_string(notation.precedence));
    frame(key, std::to_string(notation.arity));
  }
  frame(key, declarations[binding.target.declaration.index].qualifiedName);
  frame(key, binding.target.module ? typeIdentity(*binding.target.module) : "");
  for (const auto &argument : binding.arguments)
    frame(key, argument ? typeIdentity(*argument) : "");
  if (binding.notation &&
      binding.notation->position == NotationDescriptor::Position::Reduction)
    frame(key, binding.filtered ? "filtered" : "unfiltered");
  if (binding.filtered) {
    frame(
        key,
        declarations[binding.filtered->target.declaration.index].qualifiedName);
    frame(key, binding.filtered->target.module
                   ? typeIdentity(*binding.filtered->target.module)
                   : "");
    for (const auto &argument : binding.filtered->arguments)
      frame(key, argument ? typeIdentity(*argument) : "");
  }
  return key;
}
std::optional<OperatorBinding>
Checker::operatorBinding(const Declaration &context,
                         const SyntaxOperator &source, bool filtered) {
  if (!source.notation || source.symbol != source.notation->symbol) {
    types.fail("source.operator",
               "notation declaration has no resolved descriptor", source.span);
    return {};
  }
  const auto &notation = *source.notation;
  using Position = NotationDescriptor::Position;
  const auto arity = notation.arity;
  bool validArity = false;
  switch (notation.position) {
  case Position::Reduction:
    validArity = arity == 2;
    break;
  case Position::Prefix:
  case Position::Postfix:
    validArity = arity == 1;
    break;
  case Position::Infix:
    validArity = arity == 2;
    break;
  case Position::Index:
  case Position::Delimited:
    if (arity > work.limits.notationHoles) {
      types.fail("source.limit", "notation hole limit exceeded", source.span);
      return {};
    }
    validArity = arity >= (notation.position == Position::Index ? 2u : 1u);
    break;
  }
  if (!validArity) {
    types.fail("source.operator", "notation descriptor has invalid arity",
               source.span);
    return {};
  }
  auto target = callable(context, source.target.name, source.target.span);
  if (!target)
    return {};
  const auto &callee = output.declarations[target->declaration.index];
  if ((callee.kind != Declaration::Kind::Math &&
       callee.kind != Declaration::Kind::Local) ||
      (notation.position != Position::Reduction &&
       callee.inputs.size() != arity) ||
      callee.outputs.size() != 1 ||
      sources[callee.id.index]->outputs.size() != 1) {
    types.fail("source.operator",
               "notation target requires its descriptor's input count and a "
               "written result type",
               source.span, {callee.span});
    return {};
  }
  if (notation.position == Position::Infix && notation.symbol == "==" &&
      callee.outputs.front().type != Type{}) {
    types.fail("source.operator", "equality operators require a Boolean result",
               source.span, {callee.span});
    return {};
  }
  if (source.isPublic && !callee.isPublic) {
    types.fail("source.private", "public notation requires a public callable",
               source.span, {callee.span});
    return {};
  }
  const unsigned inherited =
      target->module && callee.parent
          ? output.declarations[callee.parent->index].parameters.size()
          : 0;
  auto positions =
      bindArguments(types,
                    argumentNames<Parameter>(
                        ArrayRef(callee.parameters).drop_front(inherited)),
                    source.target.arguments.size(), source.target.labels, false,
                    source.target.span, "source.generic");
  if (!positions)
    return {};
  OperatorBinding result{
      source.symbol, *target, {}, source.span, source.notation};
  result.arguments.resize(callee.parameters.size());
  TypeInference equations(types);
  auto signature =
      instantiateCallable(equations, types, callee, *target, source.span);
  for (unsigned i = 0; i < source.target.arguments.size(); ++i) {
    const auto &argument = source.target.arguments[i];
    if (argument.kind == SyntaxType::Kind::Hole)
      continue;
    auto value = type(context, argument);
    if (!value)
      return {};
    const auto position = inherited + (*positions)[i];
    result.arguments[position] = *value;
    equations.equal(signature.parameters.at(callee.parameters[position].atom),
                    equations.known(*value, argument.span), argument.span);
  }
  auto enclosing = enclosingParameters(context, callee, source.span);
  if (!enclosing)
    return {};
  std::vector<bool> written(callee.parameters.size(), false);
  for (auto position : *positions)
    written[inherited + position] = true;
  for (unsigned i = inherited; i < callee.parameters.size(); ++i)
    if ((*enclosing)[i] && !written[i]) {
      auto value = parameterType(callee.parameters[i]);
      result.arguments[i] = value;
      equations.equal(signature.parameters.at(callee.parameters[i].atom),
                      equations.known(value, source.span), source.span);
    }
  equations.solve(source.span);
  (void)callableArguments(equations, types, callee, signature, source.span);
  if (types.diagnostic)
    return {};
  if (notation.position == Position::Reduction &&
      !checkFiniteReductionTarget(types, callee, filtered, source.span))
    return {};
  if (source.filtered) {
    if (notation.position != Position::Reduction || filtered) {
      types.fail("source.reduction-target",
                 "filtered companion requires a reduction binding",
                 source.span);
      return {};
    }
    auto companion = source;
    companion.target = *source.filtered;
    companion.filtered.reset();
    auto resolved = operatorBinding(context, companion, true);
    if (!resolved)
      return {};
    const auto &other = output.declarations[resolved->target.declaration.index];
    auto refuse = [&] {
      types.fail(
          "source.reduction-target",
          "filtered companion has a different generic or callable signature",
          source.span, {callee.span, other.span});
      return std::optional<OperatorBinding>{};
    };
    if (callee.kind != other.kind ||
        callee.parameters.size() != other.parameters.size())
      return refuse();
    Substitution rename;
    for (unsigned i = 0; i < callee.parameters.size(); ++i) {
      const auto &left = callee.parameters[i], &right = other.parameters[i];
      if (left.sort != right.sort || left.domainSort != right.domainSort ||
          left.permissions.copy != right.permissions.copy ||
          left.permissions.drop != right.permissions.drop ||
          left.interface.has_value() != right.interface.has_value() ||
          (left.interface && left.interface->index != right.interface->index))
        return refuse();
      rename.emplace(right.atom, parameterType(left));
    }
    auto same = [&](const Type &left, const Type &right) {
      auto renamed = types.substitute(right, rename, source.span);
      return renamed && *renamed == left;
    };
    for (unsigned i = 0; i < callee.parameters.size(); ++i) {
      const auto &left = callee.parameters[i], &right = other.parameters[i];
      if (left.arguments.size() != right.arguments.size())
        return refuse();
      for (unsigned j = 0; j < left.arguments.size(); ++j)
        if (!same(left.arguments[j], right.arguments[j]))
          return refuse();
      if (result.arguments[i].has_value() !=
              resolved->arguments[i].has_value() ||
          (result.arguments[i] &&
           !same(*result.arguments[i], *resolved->arguments[i])))
        return refuse();
    }
    const auto &body = callee.scopedInputs[0].signature;
    const auto &filteredBody = other.scopedInputs[1].signature;
    if (body.mode != filteredBody.mode ||
        !(body.allowance == filteredBody.allowance) ||
        callee.scopedInputs[0].itemOrigins !=
            other.scopedInputs[1].itemOrigins ||
        !same(callee.domainInputs[0].item, other.domainInputs[0].item) ||
        !same(body.result, filteredBody.result) ||
        !same(callee.outputs[0].type, other.outputs[0].type))
      return refuse();
    result.filtered =
        BoundNotationTarget{resolved->target, std::move(resolved->arguments)};
  }
  return result;
}

bool Checker::prepareOperators() {
  for (auto id : moduleIds) {
    const auto &context = output.declarations[id.index];
    const auto &module = *sources[id.index];
    for (unsigned i = 0; i < module.operators.size(); ++i) {
      auto binding = operatorBinding(context, module.operators[i]);
      if (!binding)
        return false;
      moduleOperators.emplace(OperatorSite{id.index, i}, std::move(*binding));
    }
  }
  return true;
}

std::optional<std::vector<OperatorBinding>>
Checker::operatorCandidates(const Declaration &decl,
                            const SyntaxDeclaration &source,
                            uint32_t expression) {
  const auto &expr = source.expressions[expression];
  auto symbol = operatorSymbol(expr);
  if (symbol.empty() ||
      expr.children.size() !=
          expr.notation->arity + unsigned(expr.filteredReduction)) {
    types.fail("source.operator", "expected an operator occurrence", expr.span);
    return {};
  }
  const auto descriptorKey = expr.notation->key();
  std::vector<OperatorBinding> result;
  auto include = [&](const OperatorBinding &binding) {
    if (!binding.notation)
      return types.fail("source.operator", "notation binding has no descriptor",
                        expr.span);
    if (!types.charge(binding.notation->symbol.size() +
                          binding.notation->closing.size() + 1,
                      expr.span))
      return false;
    if (binding.notation->key() != descriptorKey)
      return true;
    if (*binding.notation != *expr.notation || binding.symbol != symbol)
      return types.fail("source.operator", "notation binding shape differs",
                        expr.span, {binding.span});
    result.push_back(binding);
    return true;
  };
  unsigned depth = 0;
  for (auto scope = expr.scope; scope; scope = source.bodies[*scope].parent) {
    if (*scope >= source.bodies.size() ||
        ++depth > work.limits.expressionDepth) {
      types.fail("source.operator", "invalid notation scope", expr.span);
      return {};
    }
    const auto &bindings = source.bodies[*scope].resolvedOperators;
    if (!types.charge(bindings.size() + 1, expr.span))
      return {};
    for (const auto &binding : bindings)
      if (!include(binding))
        return {};
    if (!result.empty())
      break;
  }
  if (result.empty()) {
    if (!types.charge(visibleOperators[decl.module.index].size() + 1,
                      expr.span))
      return {};
    for (auto site : visibleOperators[decl.module.index]) {
      const auto &binding = moduleOperators.at(site);
      if (!include(binding))
        return {};
    }
  }
  // Canonical identities, rather than import order, determine both overload
  // families and work scheduling. The first source declaration is retained as
  // the diagnostic origin of an identically re-exported binding.
  std::map<std::string, OperatorBinding> unique;
  for (auto &binding : result) {
    auto key = operatorBindingKey(binding, output.declarations);
    if (!types.charge(key.size() + 1, expr.span))
      return {};
    unique.emplace(std::move(key), std::move(binding));
  }
  result.clear();
  for (auto &[key, binding] : unique)
    result.push_back(std::move(binding));
  return result;
}
} // namespace zkc::language::detail
