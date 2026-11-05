#include "CallableConstraints.h"
#include "Effects.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool chargeReference(Semantics &types, const CallableReference &target,
                     Span span) {
  if (!types.charge(target.reference.path.size() + 1, span))
    return false;
  for (const auto &step : target.reference.path)
    if (!types.charge(step.name.size() + 1, span))
      return false;
  return (!target.module || types.chargeType(*target.module, span)) &&
         (!target.reference.abstract ||
          types.chargeType(target.reference.abstract->module, span));
}
} // namespace
bool chargeSelectedCallable(Semantics &types, const SelectedCallable &selection,
                            Span span) {
  if (!chargeReference(types, selection.target, span) ||
      !types.charge(selection.arguments.size() +
                        selection.signature.inputs.size() +
                        selection.effects.dependencies.size() + 1,
                    span) ||
      !types.chargeType(selection.signature.result, span))
    return false;
  for (const auto &argument : selection.arguments)
    if (!types.chargeType(argument, span))
      return false;
  for (const auto &input : selection.signature.inputs)
    if (!types.chargeType(input, span))
      return false;
  return true;
}
bool sameSelectedCallable(const SelectedCallable &a,
                          const SelectedCallable &b) {
  return a.target.declaration.index == b.target.declaration.index &&
         a.target.module == b.target.module &&
         a.target.reference == b.target.reference &&
         a.target.authoredReference == b.target.authoredReference &&
         a.arguments == b.arguments && a.signature == b.signature &&
         a.effects == b.effects;
}
std::optional<SelectedCallable>
selectCallable(Semantics &types, ArrayRef<Declaration> declarations,
               const CallableReference &target, ArrayRef<Type> arguments,
               Span span) {
  if (!chargeReference(types, target, span))
    return {};
  if (target.declaration.index >= declarations.size()) {
    types.fail("source.scoped", "named callable is outside its project", span);
    return {};
  }
  const auto &callee = declarations[target.declaration.index];
  if ((callee.kind != Declaration::Kind::Math &&
       callee.kind != Declaration::Kind::Local) ||
      callee.outputs.size() != 1 || !callee.scopedInputs.empty() ||
      !callee.descriptorInputs.empty() || !callee.services.empty() ||
      !callee.roles.empty() || arguments.size() != callee.parameters.size()) {
    types.fail("source.scoped",
               "expected a complete Math or Local named callable", span);
    return {};
  }
  auto subst = types.substitution(callee, arguments);
  if (target.module && callee.parent)
    subst.emplace("self:" + declarations[callee.parent->index].qualifiedName,
                  *target.module);
  SelectedCallable result{target,
                          {},
                          {callee.kind == Declaration::Kind::Math
                               ? ScopedSignature::Mode::Math
                               : ScopedSignature::Mode::Local,
                           {},
                           {},
                           {}},
                          {}};
  for (const auto &argument : arguments) {
    if (!types.chargeType(argument, span))
      return {};
    result.arguments.push_back(argument);
  }
  for (const auto &port : callee.inputs) {
    auto input = types.substitute(port.type, subst, span);
    if (!input)
      return {};
    result.signature.inputs.push_back(std::move(*input));
  }
  auto output = types.substitute(callee.outputs.front().type, subst, span);
  if (!output)
    return {};
  result.signature.result = std::move(*output);
  const EffectSummary empty;
  const auto &effects = callee.body              ? callee.body->effects
                        : callee.effectAllowance ? *callee.effectAllowance
                                                 : empty;
  if (!types.charge(effects.dependencies.size() + 1, span))
    return {};
  result.effects = effects;
  if (!result.effects.dependencies.empty()) {
    types.fail("source.scoped", "named callable has an open effect environment",
               span);
    return {};
  }
  result.signature.allowance = result.effects.fixed;
  return result;
}
CallableConstraints instantiateCallable(TypeInference &types,
                                        Semantics &semantics,
                                        const Declaration &callee,
                                        ExpressionTypes::Callable target,
                                        Span span, bool includeOutputs) {
  CallableConstraints result{std::move(target), {}, {}, {}};
  using T = Type::Kind;
  for (const auto &parameter : callee.parameters) {
    auto value = types.fresh(span);
    result.parameters.emplace(parameter.atom, value);
    switch (parameter.sort) {
    case Parameter::Sort::Domain:
      types.requireKinds(value, {parameterType(parameter).kind}, span);
      break;
    case Parameter::Sort::Natural:
      types.requireKinds(value, {T::Natural}, span);
      break;
    case Parameter::Sort::OracleKind:
      types.requireKinds(value, {T::OracleKind}, span);
      break;
    case Parameter::Sort::Module:
      types.requireKinds(value, {T::Module}, span);
      break;
    case Parameter::Sort::Asset:
      types.requireKinds(value, {T::Asset}, span);
      break;
    case Parameter::Sort::Type:
      // Executability is checked by ordinary argument validation so named
      // calls retain the source.formal diagnostic at that boundary.
      break;
    }
  }
  if (result.target.module) {
    auto bindings =
        semantics.boundMemberSubstitution(callee, *result.target.module, span);
    if (!bindings)
      return result;
    for (const auto &[name, type] : *bindings) {
      auto value = types.known(type, span);
      if (auto found = result.parameters.find(name);
          found != result.parameters.end())
        types.equal(found->second, value, span);
      else
        result.parameters.emplace(name, value);
    }
  }
  for (const auto &input : callee.inputs)
    result.inputs.push_back(
        types.instantiate(input.type, result.parameters, span, input.span));
  if (includeOutputs)
    for (const auto &output : callee.outputs)
      result.outputs.push_back(
          types.instantiate(output.type, result.parameters, span, output.span));
  return result;
}

std::optional<std::vector<Type>>
callableArguments(TypeInference &types, Semantics &semantics,
                  const Declaration &callee,
                  const CallableConstraints &constraints, Span span) {
  std::vector<std::optional<Type>> known;
  bool complete = true;
  for (const auto &parameter : callee.parameters) {
    auto value = types.get(constraints.parameters.at(parameter.atom), span);
    complete &= value.has_value();
    known.push_back(std::move(value));
  }
  Substitution extra;
  if (constraints.target.module) {
    auto bound = semantics.boundMemberSubstitution(
        callee, *constraints.target.module, span);
    if (!bound)
      return {};
    extra = std::move(*bound);
  }
  if (!semantics.checkKnownArgumentSorts(callee, known, span, extra) ||
      !complete)
    return {};
  std::vector<Type> arguments;
  for (auto &value : known)
    arguments.push_back(std::move(*value));
  return arguments;
}
} // namespace zkc::language::detail
