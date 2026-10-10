#include "CallableConstraints.h"
using namespace llvm;
namespace zkc::language::detail {
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
    case Parameter::Sort::Component:
      types.requireKinds(value, {T::Component}, span);
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
  if (result.target.component) {
    auto bindings = semantics.boundMemberSubstitution(
        callee, *result.target.component, span);
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
  if (constraints.target.component) {
    auto bound = semantics.boundMemberSubstitution(
        callee, *constraints.target.component, span);
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
