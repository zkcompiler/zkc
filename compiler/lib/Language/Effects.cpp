#include "Effects.h"
#include "zkc/Language/Builtins.h"
using namespace llvm;

namespace zkc::language::detail {
namespace {
void normalizeEffects(EffectSummary &summary) {
  for (auto it = summary.dependencies.begin();
       it != summary.dependencies.end();) {
    it->second.mayStop &= !summary.fixed.mayStop;
    it->second.opaque &= !summary.fixed.opaque;
    if (!it->second.mayStop && !it->second.opaque)
      it = summary.dependencies.erase(it);
    else
      ++it;
  }
}
} // namespace
bool joinEffects(Semantics &types, EffectSummary &into,
                 const EffectSummary &from, Span span) {
  if (!types.charge(into.dependencies.size() + from.dependencies.size() + 1,
                    span))
    return false;
  into.fixed.mayStop |= from.fixed.mayStop;
  into.fixed.opaque |= from.fixed.opaque;
  for (const auto &[slot, mask] : from.dependencies) {
    auto &target = into.dependencies[slot];
    target.mayStop |= mask.mayStop;
    target.opaque |= mask.opaque;
  }
  normalizeEffects(into);
  return true;
}
bool effectsWithin(Semantics &types, const EffectSummary &actual,
                   const EffectSummary &allowed, Span span) {
  if (!types.charge(
          actual.dependencies.size() + allowed.dependencies.size() + 1, span))
    return false;
  if ((actual.fixed.mayStop && !allowed.fixed.mayStop) ||
      (actual.fixed.opaque && !allowed.fixed.opaque))
    return false;
  for (const auto &[slot, mask] : actual.dependencies) {
    auto found = allowed.dependencies.find(slot);
    Effects covered =
        found == allowed.dependencies.end() ? Effects{} : found->second;
    if ((mask.mayStop && !allowed.fixed.mayStop && !covered.mayStop) ||
        (mask.opaque && !allowed.fixed.opaque && !covered.opaque))
      return false;
  }
  return true;
}
std::optional<EffectSummary>
substituteEffects(Semantics &types, const EffectSummary &summary,
                  ArrayRef<EffectSummary> arguments, Span span) {
  EffectSummary result{summary.fixed};
  for (const auto &[slot, mask] : summary.dependencies) {
    if (!types.charge(1, span))
      return {};
    if (slot >= arguments.size()) {
      types.fail("source.effect",
                 "effect dependency outside callback environment", span);
      return {};
    }
    if (!types.charge(arguments[slot].dependencies.size() + 1, span))
      return {};
    auto selected = arguments[slot];
    selected.fixed.mayStop &= mask.mayStop;
    selected.fixed.opaque &= mask.opaque;
    for (auto &[index, bound] : selected.dependencies) {
      bound.mayStop &= mask.mayStop;
      bound.opaque &= mask.opaque;
    }
    if (!joinEffects(types, result, selected, span))
      return {};
  }
  return result;
}
std::optional<EffectSummary> bindingEffects(Semantics &types, const Body &body,
                                            unsigned index, unsigned depth) {
  if (!types.charge(1, {}) || depth > types.work.limits.callDepth ||
      index >= body.scopedBindings.size()) {
    types.fail("source.limit", "effect binding depth or index exceeded", {});
    return {};
  }
  const auto &binding = body.scopedBindings[index];
  if (binding.parameter) {
    EffectSummary result;
    auto ceiling = binding.signature.allowance;
    if (ceiling.mayStop || ceiling.opaque)
      result.dependencies.emplace(*binding.parameter, ceiling);
    return result;
  }
  if (!binding.computation || !binding.computation->body) {
    types.fail("source.effect", "missing callback effect evidence",
               binding.span);
    return {};
  }
  std::vector<EffectSummary> captures;
  for (auto slot : binding.scopedCaptures) {
    auto effect = bindingEffects(types, body, slot, depth + 1);
    if (!effect)
      return {};
    captures.push_back(std::move(*effect));
  }
  return substituteEffects(types, binding.computation->body->effects, captures,
                           binding.span);
}
std::optional<EffectSummary> inferEffects(Semantics &types,
                                          ArrayRef<Declaration> declarations,
                                          const Body &body, unsigned depth) {
  if (!types.charge(body.operations.size() + 1, {}) ||
      depth > types.work.limits.callDepth) {
    types.fail("source.limit", "effect reconstruction depth exceeded", {});
    return {};
  }
  EffectSummary result{Effects{body.stopped, false}};
  auto absorb = [&](const std::optional<EffectSummary> &summary, Span span) {
    return summary && joinEffects(types, result, *summary, span);
  };
  auto call = [&](DeclarationId id, ArrayRef<unsigned> slots, Span span) {
    if (id.index >= declarations.size())
      return types.fail("source.effect",
                        "effect call target is outside the project", span);
    const auto &callee = declarations[id.index];
    std::vector<EffectSummary> actuals;
    for (auto slot : slots) {
      auto effect = bindingEffects(types, body, slot, depth + 1);
      if (!effect)
        return false;
      actuals.push_back(std::move(*effect));
    }
    if (!callee.body && !callee.effectAllowance) {
      if (callee.kind == Declaration::Kind::Math)
        return true;
      return types.fail("source.effect", "call target has no effect contract",
                        span);
    }
    return absorb(substituteEffects(types,
                                    callee.body ? callee.body->effects
                                                : *callee.effectAllowance,
                                    actuals, span),
                  span);
  };
  for (const auto &operation : body.operations) {
    const auto &action = operation.action;
    if (const auto *invoke = std::get_if<ScopedInvoke>(&action)) {
      if (!absorb(bindingEffects(types, body, invoke->binding, depth + 1),
                  operation.span))
        return {};
    } else if (const auto *helper = std::get_if<HelperCall>(&action)) {
      if (!call(helper->callee, helper->scopedArguments, operation.span))
        return {};
    } else if (const auto *protocol =
                   std::get_if<ProtocolApplication>(&action)) {
      if (!call(protocol->callee, {}, operation.span))
        return {};
    } else if (const auto *finite = std::get_if<FiniteApplication>(&action)) {
      result.fixed.mayStop |= body.mode != Body::Mode::Math;
      if (!absorb(bindingEffects(types, body, finite->body, depth + 1),
                  operation.span))
        return {};
      if (finite->predicate &&
          !absorb(bindingEffects(types, body, *finite->predicate, depth + 1),
                  operation.span))
        return {};
    } else if (const auto *finite = std::get_if<FiniteComputation>(&action)) {
      result.fixed.mayStop |= body.mode != Body::Mode::Math;
      if (!call(finite->body.helper, {}, operation.span))
        return {};
      if (finite->predicate &&
          !call(finite->predicate->helper, {}, operation.span))
        return {};
    } else if (const auto *control = std::get_if<LocalControl>(&action)) {
      for (const auto &region : control->regions)
        if (!absorb(inferEffects(types, declarations, *region, depth + 1),
                    operation.span))
          return {};
    } else if (const auto *repeat = std::get_if<ProtocolRepeat>(&action)) {
      if (!absorb(inferEffects(types, declarations, *repeat->region, depth + 1),
                  operation.span))
        return {};
    } else if (const auto *primitive = std::get_if<LocalPrimitive>(&action)) {
      result.fixed.mayStop |=
          primitive->origin == LocalPrimitive::Origin::Kernel ||
          (primitive->contract != "index.equal" &&
           primitive->contract != "field.constant" &&
           primitive->contract != "bool.constant" &&
           primitive->contract != "index.constant" &&
           !mathematicalIntrinsic(primitive->contract));
    } else if (std::holds_alternative<Require>(action) ||
               std::holds_alternative<BulkApplication>(action))
      result.fixed.mayStop = true;
  }
  if (!types.charge(result.dependencies.size() + 1, {}))
    return {};
  normalizeEffects(result);
  return result;
}
} // namespace zkc::language::detail
