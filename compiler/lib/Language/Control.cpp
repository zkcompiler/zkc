#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::control(const Expression &expr,
                                            std::optional<Type> expected,
                                            unsigned depth,
                                            bool allowUntypedStop) {
  if (!local()) {
    fail("source.mode", "control flow requires an ordered local function",
         expr.span);
    return {};
  }
  const bool loop = expr.kind == Expression::Kind::For;
  const bool match = expr.kind == Expression::Kind::Match;
  const bool collectingBranch = plan && !loop;
  if (loop && expr.roles) {
    fail("source.mode", "participant loop headers require protocol mode",
         expr.span);
    return {};
  }
  if (loop && expected && expected->kind != Type::Kind::Unit) {
    fail("source.type", "for updates mutable bindings and has unit type",
         expr.span);
    return {};
  }
  LocalControl operation;
  operation.kind = loop    ? LocalControl::Kind::For
                   : match ? LocalControl::Kind::Match
                           : LocalControl::Kind::If;
  std::vector<Alternative> alternatives;
  for (unsigned i = 0; i < (loop ? 2u : 1u); ++i) {
    auto value = expression(expr.children[i],
                            loop ? std::optional<Type>(Type(Type::Kind::Index))
                            : match ? std::nullopt
                                    : std::optional<Type>(Type{}),
                            depth + 1);
    if (!value) {
      if (body.stopped && !checker.types.diagnostic)
        fail("source.unreachable",
             "control follows a condition that always stops", expr.span);
      return {};
    }
    if (!use(*value, expr.span))
      return {};
    operation.operands.push_back(*value);
    if (match) {
      const auto &type = body.values[value->index].type;
      if (restricted(type) && !checker.types.constructorAllowed(decl, type)) {
        fail("source.private",
             "matching a restricted variant needs constructor authority",
             expr.span);
        return {};
      }
      auto alts = checker.types.alternatives(type, expr.span);
      if (!alts)
        return {};
      alternatives = *alts;
      if (alternatives.size() != expr.regions.size()) {
        fail("source.match", "match must cover every alternative exactly once",
             expr.span);
        return {};
      }
    }
  }
  auto summary = regionInputs(expr);
  if (!summary)
    return {};
  auto selected = regionStates(*summary, expr.span);
  if (!selected)
    return {};
  const auto &states = *selected;
  std::vector<std::pair<BindingId, ValueId>> initial;
  for (auto id : states) {
    const auto &state = bindings.at(id);
    if (state.value && available(*state.value)) {
      if (!collectingBranch && !use(*state.value, expr.span))
        return {};
      initial.emplace_back(id, *state.value);
      operation.operands.push_back(*state.value);
    } else if (loop) {
      fail("source.move",
           "loop state needs a wholly available initial value, including for "
           "zero trips",
           expr.span);
      return {};
    }
  }
  operation.carried = loop ? initial.size() : 0;
  std::vector<std::pair<FreePlace, ValueId>> captures;
  for (const auto &p : summary->places) {
    if (llvm::any_of(initial, [&](const auto &state) {
          return state.first == p.binding;
        }))
      continue;
    auto type = projected(bindings.at(p.binding).type, p.path, expr.span);
    if (!type)
      return {};
    if (loop && !checker.types.requireUsage(
                    *type, Usage::Copy, expr.span, &decl, "source.permission",
                    "loop invariants require Copy; declare mutable state and "
                    "supply its successor")) {
      return {};
    }
    // Captures are transferred into the control. Unlike mutable state they
    // are not returned from its arms, so the collector must own fresh inputs.
    auto value = capturePlace(p, expr.span);
    if (!value || !use(*value, expr.span))
      return {};
    captures.emplace_back(p, *value);
    operation.operands.push_back(*value);
  }
  struct Arm {
    std::shared_ptr<Body> body;
    std::unique_ptr<BodyChecker> checker;
    std::optional<ValueId> result;
    std::vector<ValueId> captures;
  };
  std::vector<Arm> arms;
  const auto branch =
      collectingBranch ? plan->usage.branch(expr.regions.size()) : 0;
  std::optional<Type> resultType =
      loop ? std::optional<Type>(Type(Type::Kind::Unit)) : expected;
  std::set<std::string> seen;
  for (unsigned ordinal = 0; ordinal < expr.regions.size(); ++ordinal) {
    unsigned index = ordinal;
    if (match) {
      const auto &alt = alternatives[ordinal];
      operation.alternatives.push_back(alt.name);
      auto found = llvm::find(expr.labels, alt.name);
      if (found == expr.labels.end()) {
        fail("source.match", "missing alternative: " + alt.name, expr.span);
        return {};
      }
      index = found - expr.labels.begin();
      if (!seen.insert(expr.labels[index]).second ||
          alt.fields.size() != expr.payloads[index].size()) {
        fail("source.match", "alternative payload count differs", expr.span);
        return {};
      }
    }
    Arm arm;
    arm.body = std::make_shared<Body>();
    arm.body->mode = Body::Mode::Local;
    arm.body->stage = body.stage;
    arm.checker = std::make_unique<BodyChecker>(checker, decl, syntax,
                                                *arm.body, callDepth);
    auto &nested = *arm.checker;
    nested.usageGuard =
        collectingBranch
            ? plan->usage.intersect(usageGuard,
                                    plan->usage.arm(branch, ordinal, expr.span),
                                    expr.span)
            : usageGuard;
    nested.inference = inference;
    nested.retainExpressionValues = retainExpressionValues;
    if (!inheritScoped(nested))
      return {};
    std::vector<unsigned> selectedDomains;
    if (!inheritDomains(nested, summary->domains, selectedDomains))
      return {};
    if (ordinal == 0)
      operation.domainArguments = std::move(selectedDomains);
    if (loop) {
      auto value = nested.input(Type(Type::Kind::Index), {}, expr.index.span);
      if (!value)
        return {};
      if (expr.index.binding)
        nested.bindings.emplace(
            *expr.index.binding,
            BindingState{Type(Type::Kind::Index), {}, *value, {}});
    }
    // Match payloads precede captures in the existing checked control contract.
    std::vector<ValueId> payloads;
    if (match)
      for (const auto &field : alternatives[ordinal].fields) {
        auto value = nested.input(field.type, {}, expr.span);
        if (!value)
          return {};
        payloads.push_back(*value);
      }
    for (auto &[id, value] : initial) {
      if (!inheritBinding(nested, id, expr.span))
        return {};
      if (collectingBranch)
        nested.usageValues[nested.bindings.at(id).value->index] =
            plan->usage.within(usageValues[value.index], nested.usageGuard,
                               expr.span);
    }
    for (auto id : states)
      if (!nested.bindings.count(id)) {
        const auto &state = bindings.at(id);
        nested.bindings.emplace(id,
                                BindingState{state.type, state.roles, {}, {}});
      }
    for (auto &[p, operand] : captures) {
      arm.captures.push_back(ValueId{uint32_t(arm.body->values.size())});
      if (!importPlace(nested, p, operand, expr.span))
        return {};
      if (loop && !nested.use(arm.captures.back(), expr.span))
        return {};
    }
    if (match)
      for (unsigned i = 0; i < payloads.size(); ++i)
        if (!nested.bindPattern(expr.payloads[index][i], payloads[i]))
          return {};
    auto value =
        nested.tail(syntax.bodies[expr.regions[index]], resultType, true);
    if (checker.types.diagnostic)
      return {};
    if (!arm.body->stopped) {
      if (!value)
        return {};
      resultType = arm.body->values[value->index].type;
      // Transfer the explicit result before deciding which state remains live.
      // Returning a state value therefore cannot also implicitly forward it.
      if (resultType->kind == Type::Kind::Unit) {
        if (!nested.discard(*value, expr.span))
          return {};
      } else {
        arm.result = nested.fresh(*value, expr.span);
        if (!arm.result)
          return {};
      }
    }
    arms.push_back(std::move(arm));
  }
  if (!resultType && allowUntypedStop)
    resultType = Type(Type::Kind::Unit);
  if (!resultType) {
    fail("source.inference",
         "control with no continuing arm needs an expected type", expr.span);
    return {};
  }
  const bool stopped = !loop && llvm::all_of(arms, [](const auto &arm) {
    return arm.body->stopped;
  });
  // Terminal controls have no native result ports, even in a typed context.
  if (stopped)
    resultType = Type(Type::Kind::Unit);
  std::vector<BindingId> joined;
  for (auto id : states) {
    bool any = false, live = true;
    for (auto &arm : arms) {
      if (arm.body->stopped)
        continue;
      any = true;
      auto &state = arm.checker->bindings.at(id);
      live &= state.value && arm.checker->available(*state.value);
    }
    if ((any && live) || (loop && !any))
      joined.push_back(id);
    else if (loop && any) {
      fail("source.move",
           "loop state needs a whole successor on every continuing iteration",
           expr.span);
      return {};
    }
  }
  Type packedType(Type::Kind::Unit);
  std::vector<Type> types;
  if (resultType->kind != Type::Kind::Unit)
    types.push_back(*resultType);
  for (auto id : joined)
    types.push_back(bindings.at(id).type);
  if (types.size() == 1)
    packedType = types.front();
  else if (!types.empty()) {
    packedType.kind = Type::Kind::Tuple;
    packedType.arguments = types;
  }
  for (auto &arm : arms) {
    auto &nested = *arm.checker;
    std::vector<ValueId> forwarded;
    if (!arm.body->stopped) {
      std::vector<ValueId> values;
      if (arm.result)
        values.push_back(*arm.result);
      for (auto id : joined)
        values.push_back(*nested.bindings.at(id).value);
      if (collectingBranch && arm.result && !nested.use(*arm.result, expr.span))
        return {};
      auto packed = collectingBranch ? nested.transport(values, expr.span)
                                     : nested.pack(values, expr.span);
      if (!packed || (!collectingBranch && !nested.use(*packed, expr.span)))
        return {};
      arm.body->results.push_back(*packed);
      if (collectingBranch) {
        // These values leave the arm through the join. Their obligations end
        // at a later use/exit, or disappear if the continuation stops.
        forwarded = values;
        forwarded.push_back(*packed);
      }
      if (loop)
        arm.body->results.insert(arm.body->results.end(), arm.captures.begin(),
                                 arm.captures.end());
    }
    if (!nested.finish(expr.span, forwarded))
      return {};
    body.parameterizedSummary |= arm.body->parameterizedSummary;
    operation.regions.push_back(arm.body);
  }
  if (collectingBranch) {
    usageGuard = UsagePlan::never;
    for (const auto &arm : arms)
      if (!arm.body->stopped)
        usageGuard =
            plan->usage.unite(usageGuard, arm.checker->usageGuard, expr.span);
  }
  auto packed = emit(std::move(operation), packedType, {}, expr.span);
  if (!packed)
    return {};
  if (stopped) {
    body.stopped = true;
    // This terminator is unreachable: every arm already stops with its own
    // reason.
    body.stopReason = arms.front().body->stopReason;
    return {};
  }
  for (auto id : states) {
    bindings.at(id).value.reset();
    bindings.at(id).pieces.clear();
  }
  unsigned offset = resultType->kind != Type::Kind::Unit ? 1 : 0;
  if (collectingBranch && !types.empty()) {
    std::vector<UsagePlan::Value> fields;
    if (offset)
      fields.push_back(types.size() == 1
                           ? usageValues[packed->index]
                           : plan->usage.project(usageValues[packed->index],
                                                 {0}, expr.span));
    for (auto id : joined) {
      UsagePlan::Value state;
      for (const auto &arm : arms) {
        if (arm.body->stopped)
          continue;
        auto &nested = *arm.checker;
        const auto value = *nested.bindings.at(id).value;
        auto origins = plan->usage.within(nested.usageValues[value.index],
                                          nested.usageGuard, expr.span);
        state.insert(state.end(), origins.begin(), origins.end());
      }
      fields.push_back(
          plan->usage.join(std::move(state), bindings.at(id).type, expr.span));
    }
    usageValues[packed->index] = fields.size() == 1
                                     ? fields.front()
                                     : plan->usage.product(fields, expr.span);
  }
  for (unsigned i = 0; i < joined.size(); ++i) {
    auto value = types.size() == 1 ? packed
                 : collectingBranch
                     ? transport(*packed, {i + offset}, expr.span)
                     : project(*packed, {i + offset}, expr.span);
    if (!value)
      return {};
    bindings.at(joined[i]).value = *value;
  }
  if (!offset)
    return pack({}, expr.span);
  return types.size() == 1 ? packed : project(*packed, {0}, expr.span);
}
} // namespace zkc::language::detail
