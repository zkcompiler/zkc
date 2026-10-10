#include "Arguments.h"
#include "CallableConstraints.h"
#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
StringRef operatorSymbol(Expression::Kind kind) {
  switch (kind) {
  case Expression::Kind::Add:
    return "+";
  case Expression::Kind::Subtract:
    return "-";
  case Expression::Kind::Multiply:
    return "*";
  case Expression::Kind::Equal:
    return "==";
  default:
    return {};
  }
}
std::string operatorBindingKey(const OperatorBinding &binding,
                               ArrayRef<Declaration> declarations) {
  std::string key;
  frame(key, declarations[binding.target.declaration.index].qualifiedName);
  frame(key, binding.target.component ? typeIdentity(*binding.target.component)
                                      : "");
  for (const auto &argument : binding.arguments)
    frame(key, argument ? typeIdentity(*argument) : "");
  return key;
}
std::optional<OperatorBinding>
Checker::operatorBinding(const Declaration &context,
                         const SyntaxOperator &source) {
  auto target = callable(context, source.target.name, source.target.span);
  if (!target)
    return {};
  const auto &callee = output.declarations[target->declaration.index];
  if ((callee.kind != Declaration::Kind::Math &&
       callee.kind != Declaration::Kind::Local) ||
      callee.inputs.size() != 2 || callee.outputs.size() != 1 ||
      sources[callee.id.index]->outputs.size() != 1) {
    types.fail("source.operator",
               "operator target requires two inputs and a written result type",
               source.span, {callee.span});
    return {};
  }
  if (source.symbol == "==" && callee.outputs.front().type != Type{}) {
    types.fail("source.operator", "equality operators require a Boolean result",
               source.span, {callee.span});
    return {};
  }
  if (source.isPublic) {
    for (auto id = std::optional(callee.id); id;
         id = output.declarations[id->index].parent)
      if (!output.declarations[id->index].isPublic) {
        types.fail("source.private",
                   "public operator exposes a private callable", source.span,
                   {output.declarations[id->index].span});
        return {};
      }
  }
  const unsigned inherited =
      target->component && callee.parent
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
  OperatorBinding result{source.symbol, *target, {}, source.span};
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
  equations.solve(source.span);
  (void)callableArguments(equations, types, callee, signature, source.span);
  if (types.diagnostic)
    return {};
  return result;
}

bool Checker::prepareOperators() {
  for (const auto &module : syntax) {
    Declaration context{};
    context.module = module.id;
    context.span = Span{module.id, 0, 0};
    for (unsigned i = 0; i < module.operators.size(); ++i) {
      auto binding = operatorBinding(context, module.operators[i]);
      if (!binding)
        return false;
      moduleOperators.emplace(OperatorSite{module.id.index, i},
                              std::move(*binding));
    }
  }
  return true;
}

std::optional<std::vector<OperatorBinding>>
Checker::operatorCandidates(const Declaration &decl,
                            const SyntaxDeclaration &source,
                            uint32_t expression) {
  const auto &expr = source.expressions[expression];
  auto symbol = operatorSymbol(expr.kind);
  if (symbol.empty()) {
    types.fail("source.operator", "expected an operator occurrence", expr.span);
    return {};
  }
  std::vector<OperatorBinding> result;
  for (auto scope = expr.scope; scope; scope = source.bodies[*scope].parent) {
    const auto &bindings = source.bodies[*scope].resolvedOperators;
    if (!types.charge(bindings.size() + 1, expr.span))
      return {};
    for (const auto &binding : bindings) {
      if (binding.symbol != symbol)
        continue;
      result.push_back(binding);
    }
    if (!result.empty())
      break;
  }
  if (result.empty()) {
    if (!types.charge(visibleOperators[decl.module.index].size() + 1,
                      expr.span))
      return {};
    for (auto site : visibleOperators[decl.module.index]) {
      const auto &binding = moduleOperators.at(site);
      if (binding.symbol == symbol)
        result.push_back(binding);
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
