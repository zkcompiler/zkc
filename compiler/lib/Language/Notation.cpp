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
  if (descriptor.position == Position::Prefix ||
      descriptor.position == Position::Reduction) {
    auto other = descriptor;
    other.position = descriptor.position == Position::Prefix
                         ? Position::Reduction
                         : Position::Prefix;
    if (auto found = environment.find(other.key()); found != environment.end())
      return conflict(found->second.span);
  }
  if (environment.size() >= work.limits.notationDescriptors)
    return failure("source.limit", "notation descriptor limit exceeded",
                   syntax.span);
  if ((descriptor.position == Position::Delimited ||
       descriptor.position == Position::Index) &&
      descriptor.arity > work.limits.notationHoles)
    return failure("source.limit", "notation hole limit exceeded", syntax.span);
  environment.emplace(descriptor.key(), syntax);
  work.notationDescriptors =
      std::max<uint64_t>(work.notationDescriptors, environment.size());
  if ((descriptor.position == Position::Delimited ||
       descriptor.position == Position::Index))
    work.notationHoles =
        std::max<uint64_t>(work.notationHoles, descriptor.arity);
  return Error::success();
}
} // namespace
NotationEnvironment fixedNotationEnvironment(SourceId sourceId) {
  NotationEnvironment result;
  for (const auto &fixed : syntax::defaultNotations()) {
    auto descriptor = std::make_shared<const NotationDescriptor>(fixed);
    result.emplace(descriptor->key(),
                   NotationSyntax{descriptor, Span{sourceId, 0, 0}});
  }
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
    if (syntax.descriptor->position != Position::Delimited &&
        syntax.descriptor->position != Position::Index)
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
      if (syntax.descriptor->position == Position::Reduction ||
          syntax.descriptor->position == Position::Delimited ||
          syntax.descriptor->position == Position::Index ||
          syntax.descriptor->symbol != binding.symbol)
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
  notationEnvironments.resize(sources.size());
  // Syntax depends on the lexical parent and on the original sites of visible
  // notation. Name-only imports do not create syntax dependencies.
  std::vector<unsigned> order, state(sources.size()), height(sources.size());
  auto visit = [&](auto &&self, unsigned id, unsigned depth) -> bool {
    auto span = sources[id]->span;
    if (!types.charge(1, span))
      return false;
    if (depth >= work.limits.importDepth ||
        height[id] > work.limits.importDepth - depth)
      return types.fail("source.limit", "notation dependency depth exceeded",
                        span);
    if (state[id] == 2)
      return true;
    if (state[id] == 1)
      return types.fail("source.cycle", "cyclic lexical and imported notation",
                        span);
    state[id] = 1;
    height[id] = 1;
    auto dependency = [&](unsigned other) {
      if (!self(self, other, depth + 1))
        return false;
      height[id] = std::max(height[id], height[other] + 1);
      return true;
    };
    if (auto parent = output.declarations[id].parent)
      if (!dependency(parent->index))
        return false;
    for (auto site : visibleOperators[id])
      if (site.first != id && !dependency(site.first))
        return false;
    state[id] = 2;
    order.push_back(id);
    return true;
  };
  for (auto id : moduleIds)
    if (!visit(visit, id.index, 0))
      return false;
  for (unsigned id : order) {
    auto environment = fixedNotationEnvironment(sources[id]->span.source);
    // Imports carry syntax resolved at the binding's original definition site.
    for (auto site : visibleOperators[id]) {
      if (site.first == id)
        continue;
      const auto &binding = sources[site.first]->operators[site.second];
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
            resolveNotationSyntax(sources[id]->operators, environment, work)) {
      types.diagnostic = diagnose(std::move(error));
      return false;
    }
    notationEnvironments[id] =
        std::make_shared<const NotationEnvironment>(std::move(environment));
  }
  return true;
}
} // namespace zkc::language::detail
