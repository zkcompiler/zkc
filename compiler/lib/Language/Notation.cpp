#include "Checker.h"
#include "llvm/ADT/STLExtras.h"
using namespace llvm;
namespace zkc::language::detail {
namespace {
using Position = NotationDescriptor::Position;
using Association = NotationDescriptor::Association;
Error insertNotation(NotationEnvironment &environment,
                     const NotationSyntax &syntax, Work &work) {
  const auto &descriptor = *syntax.descriptor;
  if (auto error =
          work.charge(descriptor.symbol.size() + descriptor.closing.size() + 1,
                      syntax.span))
    return error;
  auto conflict = [&](Span other) {
    return failure("source.notation-conflict",
                   "conflicting syntax for " + descriptor.symbol +
                       "; use named calls or select compatible imports",
                   syntax.span, {other});
  };
  auto existing = environment.find(descriptor.key());
  if (existing != environment.end()) {
    if (*existing->second.descriptor != descriptor)
      return conflict(existing->second.span);
    return Error::success();
  }
  if (descriptor.position == Position::Infix ||
      descriptor.position == Position::Postfix) {
    auto other = descriptor;
    other.position = descriptor.position == Position::Infix ? Position::Postfix
                                                            : Position::Infix;
    if (auto found = environment.find(other.key()); found != environment.end())
      return conflict(found->second.span);
  }
  if (environment.size() >= work.limits.notationDescriptors)
    return failure("source.limit", "notation descriptor limit exceeded",
                   syntax.span);
  if (descriptor.position == Position::Delimited &&
      descriptor.arity > work.limits.notationHoles)
    return failure("source.limit", "notation hole limit exceeded", syntax.span);
  environment.emplace(descriptor.key(), syntax);
  work.notationDescriptors =
      std::max<uint64_t>(work.notationDescriptors, environment.size());
  if (descriptor.position == Position::Delimited)
    work.notationHoles =
        std::max<uint64_t>(work.notationHoles, descriptor.arity);
  return Error::success();
}
} // namespace
NotationEnvironment fixedNotationEnvironment(ModuleId module) {
  NotationEnvironment result;
  auto add = [&](StringRef symbol, Position position, unsigned precedence,
                 Association association, unsigned arity) {
    auto descriptor = std::make_shared<NotationDescriptor>();
    descriptor->symbol = symbol.str();
    descriptor->position = position;
    descriptor->precedence = precedence;
    descriptor->association = association;
    descriptor->arity = arity;
    result.emplace(descriptor->key(),
                   NotationSyntax{descriptor, Span{module, 0, 0}});
  };
  add("||", Position::Infix, 10, Association::Left, 2);
  add("&&", Position::Infix, 20, Association::Left, 2);
  add("==", Position::Infix, 50, Association::None, 2);
  add("+", Position::Infix, 65, Association::Left, 2);
  add("-", Position::Infix, 65, Association::Left, 2);
  add("*", Position::Infix, 70, Association::Left, 2);
  add("!", Position::Prefix, 75, Association::None, 1);
  return result;
}
Error resolveNotationSyntax(std::vector<SyntaxOperator> &bindings,
                            NotationEnvironment &environment, Work &work) {
  if (environment.size() > work.limits.notationDescriptors)
    return failure("source.limit", "notation descriptor limit exceeded");
  work.notationDescriptors =
      std::max<uint64_t>(work.notationDescriptors, environment.size());
  for (const auto &[key, syntax] : environment) {
    if (auto error = work.charge(1, syntax.span))
      return error;
    if (syntax.descriptor->position != Position::Delimited)
      continue;
    if (syntax.descriptor->arity > work.limits.notationHoles)
      return failure("source.limit", "notation hole limit exceeded",
                     syntax.span);
    work.notationHoles =
        std::max<uint64_t>(work.notationHoles, syntax.descriptor->arity);
  }
  for (const auto &binding : bindings)
    if (binding.explicitNotation)
      if (auto error = insertNotation(environment,
                                      {binding.notation, binding.span}, work))
        return error;
  for (auto &binding : bindings) {
    if (binding.explicitNotation)
      continue;
    if (auto error = work.charge(environment.size() + 1, binding.span))
      return error;
    std::shared_ptr<const NotationDescriptor> selected;
    for (const auto &[key, syntax] : environment) {
      if (syntax.descriptor->symbol != binding.symbol)
        continue;
      if (selected)
        return failure("source.notation-ambiguous",
                       "short operator declaration requires one visible "
                       "fixity; write an explicit fixity",
                       binding.span);
      selected = syntax.descriptor;
    }
    if (!selected)
      return failure("source.notation-visibility",
                     "operator has no visible syntax declaration: " +
                         binding.symbol,
                     binding.span);
    binding.notation = std::move(selected);
  }
  return Error::success();
}
bool Checker::prepareNotationSyntax() {
  notationEnvironments.resize(syntax.size());
  std::vector<unsigned> order = importOrder;
  if (auto prelude = modules.find("zkc::prelude"); prelude != modules.end()) {
    auto id = prelude->second.index;
    order.erase(std::remove(order.begin(), order.end(), id), order.end());
    order.insert(order.begin(), id);
  }
  for (unsigned id : order) {
    auto environment = fixedNotationEnvironment(ModuleId{id});
    // Imports carry syntax resolved at the binding's original definition site.
    for (auto site : visibleOperators[id]) {
      if (site.first == id)
        continue;
      const auto &binding = syntax[site.first].operators[site.second];
      if (!binding.notation)
        return types.fail(
            "source.notation-visibility",
            "imported notation was not resolved at its definition",
            binding.span);
      if (auto error = insertNotation(environment,
                                      {binding.notation, binding.span}, work)) {
        types.diagnostic = diagnose(std::move(error));
        return false;
      }
    }
    if (auto error =
            resolveNotationSyntax(syntax[id].operators, environment, work)) {
      types.diagnostic = diagnose(std::move(error));
      return false;
    }
    notationEnvironments[id] =
        std::make_shared<const NotationEnvironment>(std::move(environment));
  }
  return true;
}
} // namespace zkc::language::detail
