#include "Effects.h"
#include "zkc/Language/Builtins.h"
#include <type_traits>
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
                                            unsigned index, unsigned depth,
                                            Span span) {
  if (!types.charge(1, span))
    return {};
  if (index >= body.scopedBindings.size()) {
    types.fail("source.effect",
               "effect binding index outside callback environment", span);
    return {};
  }
  const auto &binding = body.scopedBindings[index];
  if (depth > types.work.limits.expressionDepth) {
    types.fail("source.limit", "effect capture depth exceeded", binding.span);
    return {};
  }
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
    auto effect = bindingEffects(types, body, slot, depth + 1, binding.span);
    if (!effect)
      return {};
    captures.push_back(std::move(*effect));
  }
  return substituteEffects(types, binding.computation->body->effects, captures,
                           binding.span);
}
std::optional<EffectSummary> inferEffects(Semantics &types,
                                          ArrayRef<Declaration> declarations,
                                          const Body &body) {
  Span bodySpan = !body.operations.empty() ? body.operations.front().span
                  : !body.values.empty()   ? body.values.front().span
                                           : Span{};
  if (!types.charge(body.operations.size() + 1, bodySpan))
    return {};
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
      auto effect = bindingEffects(types, body, slot, 1, span);
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
    auto span = operation.span;
    if (!std::visit(
            [&](const auto &action) -> bool {
              using Action = std::decay_t<decltype(action)>;
              if constexpr (std::is_same_v<Action, ScopedInvoke>) {
                return absorb(
                    bindingEffects(types, body, action.binding, 1, span), span);
              } else if constexpr (std::is_same_v<Action, HelperCall>) {
                return call(action.callee, action.scopedArguments, span);
              } else if constexpr (std::is_same_v<Action,
                                                  ProtocolApplication>) {
                return call(action.callee, {}, span);
              } else if constexpr (std::is_same_v<Action, FiniteApplication>) {
                result.fixed.mayStop |= body.mode != Body::Mode::Math;
                return absorb(bindingEffects(types, body, action.body, 1, span),
                              span) &&
                       (!action.predicate ||
                        absorb(bindingEffects(types, body, *action.predicate, 1,
                                              span),
                               span));
              } else if constexpr (std::is_same_v<Action, FiniteComputation>) {
                result.fixed.mayStop |= body.mode != Body::Mode::Math;
                return call(action.body.helper, {}, span) &&
                       (!action.predicate ||
                        call(action.predicate->helper, {}, span));
              } else if constexpr (std::is_same_v<Action, LocalControl>) {
                for (const auto &region : action.regions) {
                  if (!region)
                    return types.fail("source.effect",
                                      "missing control region effect evidence",
                                      span);
                  if (!joinEffects(types, result, region->effects, span))
                    return false;
                }
                return true;
              } else if constexpr (std::is_same_v<Action, ProtocolRepeat>) {
                if (!action.region)
                  return types.fail("source.effect",
                                    "missing repeat region effect evidence",
                                    span);
                return joinEffects(types, result, action.region->effects, span);
              } else if constexpr (std::is_same_v<Action, LocalPrimitive>) {
                // Explicit kernels retain their ordered boundary. Source
                // constants and mathematical primitives have narrower effects,
                // independently of a backend implementation's failure modes.
                // Executable roots retain checks even when a mathematical
                // intrinsic shares the public name.
                result.fixed.mayStop |=
                    action.origin == LocalPrimitive::Origin::Kernel ||
                    (action.contract != "index.equal" &&
                     action.contract != "field.constant" &&
                     action.contract != "bool.constant" &&
                     action.contract != "index.constant" &&
                     (action.bindingArguments ||
                      !mathematicalIntrinsic(action.contract)));
                return true;
              } else if constexpr (std::is_same_v<Action, HostInvocation> ||
                                   std::is_same_v<Action, Require> ||
                                   std::is_same_v<Action, BulkApplication> ||
                                   std::is_same_v<Action, OracleSend> ||
                                   std::is_same_v<Action, OracleQuery> ||
                                   std::is_same_v<Action,
                                                  OracleSequenceAppend> ||
                                   std::is_same_v<Action, OracleSequenceAt>) {
                result.fixed.mayStop = true;
                return true;
              } else {
                // New operations must explicitly choose their source effects.
                static_assert(std::is_same_v<Action, MathValue> ||
                                  std::is_same_v<Action, Exchange> ||
                                  std::is_same_v<Action, Restriction> ||
                                  std::is_same_v<Action, RoleAssembly> ||
                                  std::is_same_v<Action, Construct> ||
                                  std::is_same_v<Action, Projection> ||
                                  std::is_same_v<Action, Consume> ||
                                  std::is_same_v<Action, ServiceQuery> ||
                                  std::is_same_v<Action, ProtocolCompletion> ||
                                  std::is_same_v<Action, OracleContents> ||
                                  std::is_same_v<Action, OracleRows> ||
                                  std::is_same_v<Action, OracleForgetRows> ||
                                  std::is_same_v<Action, OracleSequenceEmpty> ||
                                  std::is_same_v<Action, OracleSequenceLength>,
                              "operation needs an effect inference rule");
                return true;
              }
            },
            operation.action))
      return {};
  }
  if (!types.charge(result.dependencies.size() + 1, bodySpan))
    return {};
  normalizeEffects(result);
  return result;
}
} // namespace zkc::language::detail
