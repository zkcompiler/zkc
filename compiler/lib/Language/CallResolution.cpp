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
        (candidate.kind != Declaration::Kind::View &&
         candidate.kind != Declaration::Kind::Math &&
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
  auto resolved = index.homeMember(SourceAccess{context.id}, *home, name,
                                   {[&] { return types.charge(1, span); }, {}});
  auto *reference = std::get_if<ResolvedReference>(&resolved);
  if (!reference || reference->target.index != selected->index) {
    if (auto *failure = std::get_if<LookupFailure>(&resolved);
        failure && failure->kind == LookupFailureKind::Inaccessible)
      types.fail("source.private", "cannot reference private method", span);
    else if (!types.diagnostic)
      types.fail("source.method", "home member is not an eligible declaration",
                 span);
    return {};
  }
  return CallableReference{*selected, {}, *reference};
}
std::optional<CallableReference> Checker::method(const Declaration &context,
                                                 const Type &receiver,
                                                 StringRef name, Span span) {
  auto target =
      resolveHomeMethod(types, output.declarations, *output.declarationIndex,
                        context, receiver, name, span);
  if (target && !recordReference(context, ReferenceRoute::Method,
                                 target->reference, name, span))
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
  // Classification only: the call records its route when it is checked.
  auto target = callable(decl, expr.text, expr.span, false);
  return target &&
         output.declarations[target->declaration.index].kind ==
             Declaration::Kind::View &&
         output.declarations[target->declaration.index]
             .descriptorResult.has_value();
}
std::optional<CallableReference> Checker::callable(const Declaration &decl,
                                                   StringRef name, Span span,
                                                   bool record) {
  if (!types.charge(decl.parameters.size() + 1, span))
    return {};
  auto parts = name.split("::");
  // Static binders select the root before a declaration or prelude lookup.
  // An uncallable selected binder must never expose an intrinsic homonym.
  if (!name.starts_with("::"))
    for (unsigned slot = 0; slot < decl.parameters.size(); ++slot) {
      const auto &parameter = decl.parameters[slot];
      if (parameter.name != parts.first)
        continue;
      if (parts.second.empty() || !parameter.interface) {
        types.fail("source.call", "selected static binder is not callable",
                   span);
        return {};
      }
      auto module = parameterType(parameter);
      auto result =
          index().member(accessFor(decl), *parameter.interface, parts.second,
                         {[&] { return types.charge(1, span); }, {}});
      auto *selected = std::get_if<ResolvedReference>(&result);
      if (!selected) {
        if (auto *failure = std::get_if<LookupFailure>(&result);
            failure && failure->kind != LookupFailureKind::NotFound)
          acceptFailure(*failure, span, true);
        else
          types.fail("source.call", "unknown interface member", span);
        return {};
      }
      const auto &bound = moduleParameterReferences.at(parameter.atom);
      auto reference = bound.reference;
      reference.target = selected->target;
      reference.category = selected->category;
      reference.path.insert(reference.path.end(), selected->path.begin(),
                            selected->path.end());
      reference.abstract = AbstractMemberContext{module, *parameter.interface,
                                                 bound.owner, bound.slot};
      if (!signature(reference.target) ||
          (record && !recordReference(decl, ReferenceRoute::ModuleMember,
                                      reference, name, span)))
        return {};
      return CallableReference{reference.target, module, reference};
    }
  // Variant alternatives select their nominal declaration as the callee.
  auto alternative = name.rsplit("::");
  if (!alternative.second.empty()) {
    auto nominal = select(decl, alternative.first, span, false);
    if (types.diagnostic)
      return {};
    if (nominal && output.declarations[nominal->target.index].kind ==
                       Declaration::Kind::Variant) {
      if (record && !recordReference(decl, ReferenceRoute::Path, *nominal,
                                     alternative.first, span))
        return {};
      return CallableReference{nominal->target, {}, *nominal};
    }
  }
  auto reference = select(decl, name, span);
  if (!reference)
    return {};
  if (reference->category == ResolutionCategory::ServiceConstructor ||
      reference->category == ResolutionCategory::ServiceMethod) {
    types.fail("source.service",
               "managed declarations require a borrowed service receiver",
               span);
    return {};
  }
  if (!signature(reference->target))
    return {};
  const auto &target = output.declarations[reference->target.index];
  if (target.abstract && target.kind != Declaration::Kind::Associated) {
    types.fail("source.call", "abstract call requires a bound module", span);
    return {};
  }
  if (record &&
      !recordReference(decl, ReferenceRoute::Path, *reference, name, span))
    return {};
  return CallableReference{reference->target, {}, *reference};
}
std::optional<ExpressionTypes::Callable>
BodyChecker::callable(const Expression &expr) {
  SaveAndRestore site(checker.referenceSite, expr.referenceSite);
  return checker.callable(decl, expr.text, expr.span);
}
} // namespace zkc::language::detail
