#include "BodyCheck.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
std::optional<ValueId> BodyChecker::control(const Expression &expr,
                                            std::optional<Type> expected,
                                            unsigned depth,
                                            bool allowUntypedStop) {
  if (oracleMode()) {
    fail("source.mode", "oracle plans do not admit selected control",
         expr.span);
    return {};
  }
  const bool loop = expr.kind == Expression::Kind::For;
  const bool match = expr.kind == Expression::Kind::Match;
  const bool collectingBranch = plan && !loop;
  if (loop && !local()) {
    fail("source.mode", "use bounded protocol repetition or a finite Math fold",
         expr.span);
    return {};
  }
  if (expr.roles && !protocol()) {
    fail("source.roles", "a selected roster requires Protocol mode", expr.span);
    return {};
  }
  auto roster = protocol()
                    ? (expr.roles ? checker.roles(decl, *expr.roles, expr.span)
                                  : std::optional(allRoles()))
                    : std::optional(std::vector<unsigned>{});
  if (!roster || (protocol() && !active(*roster, expr.span)))
    return {};
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
  Control operation;
  operation.kind = loop    ? Control::Kind::For
                   : match ? Control::Kind::Match
                           : Control::Kind::If;
  operation.roles = *roster;
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
    if (protocol() && !demand(*value, *roster, expr.span))
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
      if (protocol() && !active(state.roles, expr.span))
        return {};
      if (protocol() &&
          !std::includes(roster->begin(), roster->end(), state.roles.begin(),
                         state.roles.end())) {
        fail("source.roles", "mutable state extends beyond the branch roster",
             expr.span);
        return {};
      }
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
    if (value && protocol()) {
      const auto &original = body.values[value->index];
      std::vector<unsigned> selected;
      std::set_intersection(original.components.begin(),
                            original.components.end(), roster->begin(),
                            roster->end(), std::back_inserter(selected));
      if (selected.empty()) {
        fail("source.roles", "capture has no branch participant", expr.span);
        return {};
      }
      value = restrictRoles(*value, selected, expr.span);
    }
    if (!value || !use(*value, expr.span))
      return {};
    captures.emplace_back(p, *value);
    operation.operands.push_back(*value);
  }
  std::map<unsigned, ServiceId> serviceRoots;
  for (auto id : summary->services) {
    const auto root = services.at(id);
    if (!llvm::is_contained(*roster, body.services[root.index].owner)) {
      fail("source.roles", "service owner is outside the branch roster",
           expr.span);
      return {};
    }
    if (serviceRoots
            .emplace(root.index, ServiceId{uint32_t(serviceRoots.size())})
            .second)
      operation.services.push_back(root);
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
  for (unsigned ordinal = 0; ordinal < expr.regions.size(); ++ordinal) {
    unsigned index = ordinal;
    if (match) {
      const auto &alt = alternatives[ordinal];
      operation.alternatives.push_back(alt.name);
      const auto &resolved =
          inference->matchArms.at(uint32_t(&expr - syntax.expressions.data()));
      auto found = llvm::find(resolved, ordinal);
      if (found == resolved.end()) {
        fail("source.match", "missing alternative: " + alt.name, expr.span);
        return {};
      }
      index = found - resolved.begin();
      if (alt.fields.size() != expr.payloads[index].size()) {
        fail("source.match", "alternative payload count differs", expr.span);
        return {};
      }
    }
    Arm arm;
    arm.body = std::make_shared<Body>();
    arm.body->mode = body.mode;
    arm.body->stage = body.stage;
    arm.checker = std::make_unique<BodyChecker>(
        checker, decl, syntax, *arm.body, callDepth, lexicalCallbackDepth);
    auto &nested = *arm.checker;
    nested.usageGuard =
        collectingBranch
            ? plan->usage.intersect(usageGuard,
                                    plan->usage.arm(branch, ordinal, expr.span),
                                    expr.span)
            : usageGuard;
    nested.inference = inference;
    nested.enclosing = this;
    nested.completionAllowed = completionAllowed;
    if (protocol())
      nested.activeRoles = *roster;
    for (auto root : operation.services)
      arm.body->services.push_back(body.services[root.index]);
    for (auto id : summary->services)
      nested.services.emplace(id, serviceRoots.at(services.at(id).index));
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
        auto value = nested.input(
            field.type,
            math() ? std::vector<unsigned>{arm.body->inputs} : *roster,
            expr.span);
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
        nested.tail(syntax.bodies[expr.regions[index]], resultType, true,
                    contextualPlacement ? std::optional(*contextualPlacement)
                                        : std::nullopt);
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
  std::optional<Value> joinedValue;
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
      auto packed = (collectingBranch || protocol())
                        ? nested.transport(values, expr.span)
                        : nested.pack(values, expr.span);
      if (!packed || (!collectingBranch && !nested.use(*packed, expr.span)))
        return {};
      const auto &yield = arm.body->values[packed->index];
      if (protocol()) {
        if (joinedValue && (joinedValue->placement != yield.placement ||
                            joinedValue->oracleHolder != yield.oracleHolder ||
                            joinedValue->components != yield.components)) {
          fail("source.placement",
               "branch yields have different placed identities", expr.span);
          return {};
        }
        joinedValue = yield;
      }
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
  Components dependencies;
  if (math()) {
    auto combined = combine(operation.operands, expr.span);
    if (!combined)
      return {};
    dependencies = *combined;
  }
  std::optional<ValueId> packed;
  if (protocol() && joinedValue) {
    auto result = emitResults(std::move(operation), {*joinedValue}, expr.span);
    if (result)
      packed = result->front();
  } else
    packed = emit(std::move(operation), packedType, dependencies, expr.span);
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
