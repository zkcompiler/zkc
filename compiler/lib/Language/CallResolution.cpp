#include "BodyCheck.h"
#include "zkc/Language/Diagnostics.h"
using namespace llvm;
namespace zkc::language::detail {
std::optional<CallableReference>
resolveHomeMethod(Semantics &types, ArrayRef<Declaration> declarations,
                  const DeclarationIndex &index, const Declaration &context,
                  const Type &receiver, StringRef name, Span span) {
  const auto *nominal = types.typeDeclaration(receiver);
  auto home = index.home(receiver);
  if (!home || receiver.kind == Type::Kind::Module) {
    types.fail("source.method", "method receiver requires a nominal type",
               span);
    return {};
  }
  // A field owns its spelling, including when access to that field is private.
  for (const auto &field :
       nominal ? ArrayRef(nominal->fields) : ArrayRef<TypeField>{}) {
    if (!types.charge(1, span))
      return {};
    if (field.name == name) {
      bool accessible = !nominal->sealed &&
                        (field.isPublic ||
                         types.withinModule(context.module, nominal->module));
      types.fail(accessible ? "source.method" : "source.private",
                 "a receiver field cannot be called as a method", span,
                 {field.span});
      return {};
    }
  }
  std::optional<DeclarationId> selected;
  // The index admits direct home declarations and catalog-selected public API
  // forwarding. Arbitrary namespace imports/reexports are not eligibility.
  for (auto id : index.members(*home)) {
    if (!types.charge(1, span))
      return {};
    const auto &candidate = declarations[id.index];
    if (candidate.name != name || candidate.abstract ||
        (candidate.kind != Declaration::Kind::Math &&
         candidate.kind != Declaration::Kind::Local &&
         candidate.kind != Declaration::Kind::Protocol) ||
        candidate.inputs.empty() ||
        (!candidate.inputOrder.empty() &&
         (candidate.inputOrder.front().kind !=
              Declaration::InputSlot::Kind::Data ||
          candidate.inputOrder.front().index != 0)))
      continue;
    const auto *first = types.typeDeclaration(candidate.inputs.front().type);
    auto firstHome = index.home(candidate.inputs.front().type);
    if (!firstHome || firstHome->index != home->index ||
        (nominal && (!first || first->id.index != nominal->id.index)) ||
        (!nominal &&
         (candidate.inputs.front().type.kind != receiver.kind ||
          (receiver.kind == Type::Kind::Builtin &&
           candidate.inputs.front().type.domain != receiver.domain))))
      continue;
    if (selected) {
      types.fail("source.method", "ambiguous canonical home method", span,
                 {declarations[selected->index].span, candidate.span});
      return {};
    }
    selected = id;
  }
  if (!selected) {
    types.fail("source.method", "no eligible canonical home method: " + name,
               span);
    return {};
  }
  const auto &target = declarations[selected->index];
  if (!target.isPublic && !types.withinModule(context.module, *home)) {
    types.fail("source.private", "cannot reference private method: " + name,
               span, {target.span});
    return {};
  }
  return CallableReference{*selected, {}};
}
std::optional<CallableReference> Checker::method(const Declaration &context,
                                                 const Type &receiver,
                                                 StringRef name, Span span) {
  auto target =
      resolveHomeMethod(types, output.declarations, *output.declarationIndex,
                        context, receiver, name, span);
  if (target &&
      !recordReference(context,
                       output.declarations[target->declaration.index].module,
                       target->declaration, name, span))
    return {};
  return target;
}
bool Checker::domainExpression(const Declaration &decl,
                               const SyntaxDeclaration &syntax, uint32_t id) {
  const auto &expr = syntax.expressions[id];
  if (expr.kind == Expression::Kind::Name && expr.binding)
    return syntax.bindings[expr.binding->index].domain;
  if (expr.kind != Expression::Kind::Call || expr.binding ||
      expr.text == "index")
    return false;
  auto target = callable(decl, expr.text, expr.span);
  return target && output.declarations[target->declaration.index].kind ==
                       Declaration::Kind::DomainFunction;
}
std::optional<CallableReference> Checker::callable(const Declaration &decl,
                                                   StringRef name, Span span) {
  auto parts = name.split("::");
  if (!parts.second.empty())
    for (auto &parameter : decl.parameters) {
      if (parameter.name != parts.first || !parameter.interface)
        continue;
      SyntaxType term;
      term.name = parameter.name;
      term.span = span;
      auto module = type(decl, term);
      if (!module)
        return {};
      auto &interface = output.declarations[parameter.interface->index];
      for (auto id : interface.members)
        if (output.declarations[id.index].name == parts.second) {
          if (!signature(id))
            return {};
          if (!recordReference(decl,
                               moduleParameterProviders.at(parameter.atom), id,
                               name, span, formatType(*module)))
            return {};
          return CallableReference{id, *module};
        }
      types.fail("source.call", "unknown interface member", span);
      return {};
    }
  // A bound module member takes precedence over a nominal alternative.
  auto alternative = name.rsplit("::");
  if (!alternative.second.empty()) {
    auto nominal = resolve(decl, alternative.first, span, false);
    if (nominal &&
        output.declarations[nominal->index].kind == Declaration::Kind::Variant)
      return CallableReference{*nominal, {}};
  }
  auto id = resolve(decl, name, span, false);
  if (!id && !types.diagnostic && output.declarationIndex) {
    id = output.declarationIndex->implicit(name);
    if (id && !recordReference(decl, output.declarations[id->index].module, *id,
                               name, span))
      return {};
  }
  if (!id && !types.diagnostic)
    types.fail("source.name", "unknown declaration: " + name, span);
  if (!id || !signature(*id))
    return {};
  if (output.declarations[id->index].abstract &&
      output.declarations[id->index].kind != Declaration::Kind::Associated) {
    types.fail("source.call", "abstract call requires a bound module", span);
    return {};
  }
  return CallableReference{*id, {}};
}
std::optional<ExpressionTypes::Callable>
BodyChecker::callable(const Expression &expr) {
  return checker.callable(decl, expr.text, expr.span);
}
} // namespace zkc::language::detail
