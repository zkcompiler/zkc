#ifndef ZKC_LANGUAGE_DESCRIPTORFRAMES_H
#define ZKC_LANGUAGE_DESCRIPTORFRAMES_H
#include "Semantics.h"
#include <algorithm>
namespace zkc::language::detail {
/// Own a temporary static environment through the common Type copy contract.
inline std::optional<Substitution>
descriptorSubstitution(Semantics &types, const Declaration &declaration,
                       llvm::ArrayRef<Type> arguments, Span span) {
  if (!types.charge(sizeof(Substitution), span))
    return {};
  for (unsigned i = 0;
       i < arguments.size() && i < declaration.parameters.size(); ++i)
    if (!types.charge(sizeof(Substitution::value_type) + 4 * sizeof(void *) +
                          declaration.parameters[i].atom.size(),
                      span) ||
        !types.chargeType(arguments[i], span))
      return {};
  return types.substitution(declaration, arguments);
}
/// NaturalArithmetic owns normalized Natural copies and their work debit.
inline std::optional<Type>
descriptorNaturalTerm(Semantics &types, const Natural &source, Span span) {
  if (!types.charge(sizeof(Type), span))
    return {};
  auto value = types.naturals.add(source, Natural{});
  if (!value) {
    types.accept(value.takeError(), span);
    return {};
  }
  Type result(Type::Kind::Natural);
  result.dimension = std::move(*value);
  return result;
}
/// The fixed parameter recipe is owned scratch even when Count is zero.
inline std::optional<std::vector<DescriptorBinding>>
descriptorFrameParameters(Semantics &types, const DescriptorContract &context,
                          const DescriptorContract &state, Span span) {
  if (!types.charge(sizeof(std::vector<DescriptorBinding>) +
                        2 * sizeof(DescriptorBinding) + 2 * sizeof(void *),
                    span) ||
      !types.chargeContract(context, span) ||
      !types.chargeContract(state, span))
    return {};
  std::vector<DescriptorBinding> frame;
  frame.reserve(2);
  frame.push_back(
      {DescriptorBinding::Kind::Parameter, context, {}, {}, 0, 0, span});
  frame.push_back(
      {DescriptorBinding::Kind::Parameter, state, {}, {}, 0, 1, span});
  return frame;
}
/// A cache discriminator over this pass's actual ordered source templates.
/// It does not change public Finite identity or authorize a candidate relation.
inline std::optional<std::string>
descriptorFormationKey(Semantics &types, const DescriptorShape &shape,
                       Span span);
/// Frame immutable lookup data only after charging its retained bytes and any
/// allocation/copy caused by capacity growth. No cache supplies authority.
inline bool descriptorIdentityFrame(Semantics &types, std::string &out,
                                    llvm::StringRef value, Span span) {
  if (out.size() > out.max_size() - 8 ||
      value.size() > out.max_size() - out.size() - 8)
    return types.fail("source.limit", "descriptor identity size overflows",
                      span);
  auto required = out.size() + value.size() + 8;
  if (!types.charge(value.size() + 8, span))
    return false;
  if (required > out.capacity()) {
    auto capacity = out.capacity();
    auto grown = capacity <= out.max_size() / 2 ? 2 * capacity : out.max_size();
    auto selected = std::max(required, grown);
    if (selected > UINT64_MAX / 4 ||
        !types.charge(2 * selected + out.size() + 1, span))
      return types.diagnostic
                 ? false
                 : types.fail("source.limit",
                              "descriptor identity is too large", span);
    out.reserve(selected);
  }
  frame(out, value);
  return true;
}
inline std::optional<std::string>
descriptorFormationKey(Semantics &types, const DescriptorShape &shape,
                       Span span) {
  if (!shape.arena)
    return {};
  std::string key;
  auto append = [&](llvm::StringRef value) {
    return descriptorIdentityFrame(types, key, value, span);
  };
  if (!append(std::to_string(shape.formation)) ||
      !append(std::to_string(shape.arena->blocks.size())))
    return {};
  for (const auto &block : shape.arena->blocks) {
    if (!append(std::to_string(block.size())))
      return {};
    for (const auto &event : block) {
      if (!types.charge(128, span) ||
          !append(std::to_string(unsigned(event.kind))) ||
          !append(event.expression ? std::to_string(*event.expression)
                                   : "none") ||
          !append(std::to_string(event.result)) ||
          !append(event.invocation ? std::to_string(*event.invocation)
                                   : "none") ||
          !append(event.authority) ||
          !append(std::to_string(event.children.size())))
        return {};
      for (auto child : event.children)
        if (!append(std::to_string(child)))
          return {};
    }
  }
  return key;
}
inline bool chargeDescriptorRouteCopy(Semantics &types,
                                      const CallableReference &route,
                                      Span span) {
  if (!types.charge(sizeof(CallableReference) +
                        route.reference.path.size() * sizeof(ResolutionStep),
                    span))
    return false;
  for (const auto &step : route.reference.path)
    if (!types.charge(step.name.size(), span))
      return false;
  return (!route.module || types.chargeType(*route.module, span)) &&
         (!route.reference.abstract ||
          types.chargeType(route.reference.abstract->module, span));
}
/// Precharge owned recipes without introducing a second Type accounting walk.
inline bool chargeDescriptorBindingCopy(Semantics &types,
                                        const DescriptorBinding &node) {
  if (!types.charge(sizeof(DescriptorBinding) +
                        node.operands.size() * sizeof(ValueId) +
                        node.children.size() * sizeof(DescriptorEdge) +
                        node.arguments.size() * sizeof(Type) +
                        node.argumentOrder.size() * sizeof(unsigned),
                    node.span) ||
      !types.chargeContract(node.contract, node.span))
    return false;
  for (const auto &edge : node.children)
    if (!types.chargeContract(edge.contract, node.span))
      return false;
  for (const auto &argument : node.arguments)
    if (!types.chargeType(argument, node.span))
      return false;
  if (node.factory &&
      !chargeDescriptorRouteCopy(types, *node.factory, node.span))
    return false;
  if (node.selectedView) {
    const auto &selection = *node.selectedView;
    if (!chargeDescriptorRouteCopy(types, selection.target, node.span) ||
        !types.charge(selection.arguments.size() * sizeof(Type), node.span) ||
        !types.chargeContract(selection.context, node.span) ||
        !types.chargeContract(selection.state, node.span))
      return false;
    for (const auto &argument : selection.arguments)
      if (!types.chargeType(argument, node.span))
        return false;
  }
  return true;
}
bool descriptorSourceAdmission(Semantics &, llvm::ArrayRef<Declaration>,
                               DeclarationId, llvm::ArrayRef<Type>, Span);
/// Type-only selected-closure admission. There is no fabricated iteration or
/// state payload here. Closed independent failures reject even a zero driver;
/// a genuinely symbolic selector or unsized future state remains residual.
inline bool descriptorClosureAdmission(Semantics &types,
                                       llvm::ArrayRef<Declaration> declarations,
                                       DeclarationId target,
                                       llvm::ArrayRef<Type> arguments,
                                       Span span, std::set<unsigned> &active,
                                       unsigned depth = 1) {
  if (depth > types.work.limits.callDepth || !types.charge(1, span))
    return types.diagnostic
               ? false
               : types.fail("source.limit", "selected closure admission depth",
                            span);
  if (target.index >= declarations.size() ||
      !active.insert(target.index).second)
    return types.fail("source.view-selection",
                      "cyclic selected closure admission", span);
  const auto &member = declarations[target.index];
  if (!member.descriptorDefinition ||
      !types.checkArguments(member, arguments, span))
    return false;
  auto statics = descriptorSubstitution(types, member, arguments, span);
  if (!statics)
    return false;
  for (const auto &bound : member.bounds) {
    auto left = descriptorNaturalTerm(types, bound.lhs, span),
         right = descriptorNaturalTerm(types, bound.rhs, span);
    if (!left || !right)
      return false;
    auto a = types.substitute(*left, *statics, span),
         b = types.substitute(*right, *statics, span);
    if (!a || !b)
      return false;
    auto normalized =
        types.naturals.cancelCommonTerms(a->dimension, b->dimension);
    if (!normalized)
      return types.accept(normalized.takeError(), span);
    if (normalized->first.isClosed() && normalized->second.isClosed() &&
        normalized->first.closedValue() > normalized->second.closedValue())
      return types.fail("source.bound",
                        "independent selected closure bound is false", span);
  }
  const auto &definition = *member.descriptorDefinition;
  for (const auto &node : definition.bindings) {
    if (!types.charge(1 + node.children.size(), node.span))
      return false;
    auto contract = types.substitute(node.contract, *statics, node.span);
    if (!contract)
      return false;
    using Kind = DescriptorBinding::Kind;
    if (node.kind == Kind::ProductProjection ||
        node.kind == Kind::SequenceProjection || node.kind == Kind::Replace) {
      if (node.children.empty())
        return types.fail("source.view-selection",
                          "selected projection has no typed base", node.span);
      auto base =
          types.substitute(node.children.front().contract, *statics, node.span);
      if (!base)
        return false;
      const auto &shape = descriptorType(*base);
      if (node.kind == Kind::ProductProjection) {
        if (shape.kind != Type::Kind::DescriptorProduct ||
            node.axis >= shape.arguments.size())
          return types.fail("source.descriptor-projection",
                            "independent product projection is out of range",
                            node.span);
      } else {
        auto index =
            node.arguments.size() == 1
                ? types.substitute(node.arguments[0], *statics, node.span)
                : std::nullopt;
        if (!index || index->kind != Type::Kind::Natural ||
            shape.kind != Type::Kind::DescriptorSequence)
          return types.fail("source.descriptor-projection",
                            "selected sequence projection is not typed",
                            node.span);
        if (shape.arguments.size() == 2 &&
            shape.arguments[1].dimension.isClosed() &&
            index->dimension.isClosed() &&
            index->dimension.closedValue() >=
                shape.arguments[1].dimension.closedValue())
          return types.fail("source.descriptor-projection",
                            "independent sequence projection is out of range",
                            node.span);
      }
    }
    if ((node.kind == Kind::Application && node.factory) ||
        (node.kind == Kind::Fold && node.selectedView)) {
      const auto &route =
          node.kind == Kind::Fold ? node.selectedView->target : *node.factory;
      const auto &sourceArguments = node.kind == Kind::Fold
                                        ? node.selectedView->arguments
                                        : node.arguments;
      std::vector<Type> arguments;
      if (!types.charge(sourceArguments.size() * sizeof(Type), node.span))
        return false;
      arguments.reserve(sourceArguments.size());
      for (const auto &source : sourceArguments) {
        auto argument = types.substitute(source, *statics, node.span);
        if (!argument)
          return false;
        arguments.push_back(std::move(*argument));
      }
      std::optional<Type> module;
      if (route.module) {
        module = types.substitute(*route.module, *statics, node.span);
        if (!module)
          return false;
      }
      auto selected =
          types.dispatch(module, route.declaration, arguments, node.span);
      if (!selected || (!declarations[selected->declaration.index].abstract &&
                        !descriptorClosureAdmission(
                            types, declarations, selected->declaration,
                            selected->arguments, node.span, active, depth + 1)))
        return false;
    }
  }
  active.erase(target.index);
  return descriptorSourceAdmission(types, declarations, target, arguments,
                                   span);
}
inline std::optional<std::string>
descriptorOccurrenceAuthority(Semantics &types,
                              const DescriptorBinding &binding,
                              const Substitution &statics) {
  std::string key;
  auto append = [&](llvm::StringRef value) {
    if (!types.diagnostic)
      descriptorIdentityFrame(types, key, value, binding.span);
  };
  append(std::to_string(binding.span.source.index));
  append(std::to_string(binding.span.begin));
  append(std::to_string(binding.span.end));
  auto term = [&](const Type &source) {
    auto value = types.substitute(source, statics, binding.span);
    if (!value || !types.chargeIdentity(*value, binding.span))
      return false;
    append(typeIdentity(*value));
    return true;
  };
  auto reference = [&](const CallableReference &route) {
    append(std::to_string(route.declaration.index));
    append(route.module ? "module" : "direct");
    if (route.module && !term(*route.module))
      return false;
    append(std::to_string(route.reference.provider.index));
    append(std::to_string(route.reference.target.index));
    append(std::to_string(unsigned(route.reference.category)));
    append(route.authoredReference ? std::to_string(*route.authoredReference)
                                   : "none");
    append(std::to_string(route.reference.path.size()));
    for (const auto &step : route.reference.path) {
      if (!types.charge(step.name.size() + 1, binding.span))
        return false;
      append(std::to_string(step.owner.index));
      append(step.name);
      append(step.import ? std::to_string(*step.import) : "none");
    }
    append(route.reference.abstract ? "abstract" : "concrete");
    if (route.reference.abstract) {
      const auto &context = *route.reference.abstract;
      if (!term(context.module))
        return false;
      append(std::to_string(context.interface.index));
      append(std::to_string(context.binderOwner.index));
      append(std::to_string(context.binder));
    }
    return true;
  };
  if (!term(descriptorType(binding.contract)))
    return {};
  if (binding.factory && !reference(*binding.factory))
    return {};
  append(std::to_string(binding.arguments.size()));
  for (const auto &argument : binding.arguments)
    if (!term(argument))
      return {};
  append(std::to_string(binding.argumentOrder.size()));
  for (auto slot : binding.argumentOrder)
    append(std::to_string(slot));
  append(binding.selectedView ? "selected" : "ordinary");
  if (binding.selectedView) {
    const auto &selected = *binding.selectedView;
    if (!reference(selected.target) ||
        !term(descriptorType(selected.context)) ||
        !term(descriptorType(selected.state)))
      return {};
    append(std::to_string(selected.iteration));
    append(std::to_string(selected.arguments.size()));
    for (const auto &argument : selected.arguments)
      if (!term(argument))
        return {};
  }
  if (types.diagnostic)
    return {};
  return key;
}
/// Resolve the authored selected route even when its driver has no frames.
/// The reserved iteration argument remains symbolic during this admission;
/// actual iterations check all concrete bounds through normal application.
inline std::optional<Semantics::Dispatch>
descriptorSelection(Semantics &types, llvm::ArrayRef<Declaration> declarations,
                    const DescriptorBinding &binding,
                    const Substitution &statics) {
  if (!binding.selectedView || !types.charge(1, binding.span))
    return {};
  const auto &selection = *binding.selectedView;
  if (selection.target.declaration.index >= declarations.size() ||
      selection.iteration >= selection.arguments.size()) {
    types.fail("source.view-selection", "invalid selected View route",
               binding.span);
    return {};
  }
  if (!types.charge(sizeof(std::vector<Type>) +
                        selection.arguments.size() * sizeof(Type) +
                        2 * sizeof(void *),
                    binding.span))
    return {};
  std::vector<Type> arguments;
  arguments.reserve(selection.arguments.size());
  for (const auto &argument : selection.arguments) {
    auto value = types.substitute(argument, statics, binding.span);
    if (!value)
      return {};
    arguments.push_back(std::move(*value));
  }
  std::optional<Type> module;
  if (selection.target.module) {
    module = types.substitute(*selection.target.module, statics, binding.span);
    if (!module)
      return {};
  }
  auto route = types.dispatch(module, selection.target.declaration, arguments,
                              binding.span);
  if (!route)
    return {};
  const auto &member = declarations[route->declaration.index];
  if (member.kind != Declaration::Kind::View || member.abstract ||
      !member.descriptorDefinition || !member.descriptorResult ||
      !member.inputs.empty() || member.descriptorInputs.size() != 2 ||
      member.parameters.size() != route->arguments.size() ||
      member.parameters.empty() ||
      member.parameters.back().sort != Parameter::Sort::Natural ||
      !types.checkArguments(member, route->arguments, binding.span)) {
    if (!types.diagnostic)
      types.fail("source.view-selection",
                 "selected View has no concrete structural definition",
                 binding.span);
    return {};
  }
  auto substitution =
      descriptorSubstitution(types, member, route->arguments, binding.span);
  if (!substitution)
    return {};
  auto context = types.substitute(member.descriptorInputs[0].contract,
                                  *substitution, binding.span);
  auto state = types.substitute(member.descriptorInputs[1].contract,
                                *substitution, binding.span);
  auto result =
      types.substitute(*member.descriptorResult, *substitution, binding.span);
  auto expectedContext =
      types.substitute(selection.context, statics, binding.span);
  auto expectedState = types.substitute(selection.state, statics, binding.span);
  if (!context || !state || !result || !expectedContext || !expectedState ||
      *context != *expectedContext || *state != *expectedState ||
      *result != *state) {
    if (!types.diagnostic)
      types.fail("source.view-selection",
                 "selected View context or invariant state differs",
                 binding.span);
    return {};
  }
  std::set<unsigned> active;
  if (!descriptorClosureAdmission(types, declarations, route->declaration,
                                  route->arguments, binding.span, active))
    return {};
  return route;
}
inline std::optional<DescriptorBinding>
descriptorFrame(Semantics &types, const DescriptorBinding &binding,
                const Substitution &statics, const DescriptorContract &context,
                const DescriptorContract &state, uint64_t iteration) {
  if (!binding.selectedView)
    return {};
  const auto &selection = *binding.selectedView;
  if (!chargeDescriptorRouteCopy(types, selection.target, binding.span) ||
      !types.chargeContract(context, binding.span) ||
      !types.chargeContract(state, binding.span) ||
      !types.chargeContract(state, binding.span) ||
      !types.charge(selection.arguments.size() * sizeof(Type) +
                        2 * sizeof(DescriptorEdge) + 2 * sizeof(unsigned),
                    binding.span))
    return {};
  auto target = selection.target;
  if (target.module) {
    auto module = types.substitute(*target.module, statics, binding.span);
    if (!module)
      return {};
    target.module = std::move(*module);
  }
  std::vector<Type> arguments;
  arguments.reserve(selection.arguments.size());
  for (const auto &argument : selection.arguments) {
    auto value = types.substitute(argument, statics, binding.span);
    if (!value)
      return {};
    arguments.push_back(std::move(*value));
  }
  if (selection.iteration >= arguments.size())
    return {};
  Type index(Type::Kind::Natural);
  index.dimension = Natural::constant(iteration);
  arguments[selection.iteration] = std::move(index);
  return DescriptorBinding{DescriptorBinding::Kind::Application,
                           state,
                           {},
                           {{0, context}, {1, state}},
                           0,
                           {},
                           binding.span,
                           std::move(target),
                           std::move(arguments),
                           {0, 1},
                           binding.expression};
}
} // namespace zkc::language::detail
#endif
