#include "BodySummary.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
std::optional<Dependencies> join(Semantics &types,
                                 ArrayRef<Dependencies> values) {
  Dependencies result;
  for (const auto &value : values) {
    if (!types.charge(value.inputs.size() + 1, {}))
      return {};
    result.parameterized |= value.parameterized;
    result.inputs.insert(result.inputs.end(), value.inputs.begin(),
                         value.inputs.end());
  }
  uint64_t levels = 1;
  for (auto count = result.inputs.size(); count > 1; count >>= 1)
    ++levels;
  if (!types.charge(result.inputs.size() * levels, {}))
    return {};
  llvm::sort(result.inputs);
  result.inputs.erase(std::unique(result.inputs.begin(), result.inputs.end()),
                      result.inputs.end());
  return result;
}
bool chargeBinding(Semantics &types, const ScopedSummaryBinding &binding,
                   unsigned depth, Span span) {
  if (depth > types.work.limits.callDepth)
    return types.fail("source.limit", "scoped summary copy depth", span);
  if (!types.charge(binding.signature.inputs.size() + binding.captures.size() +
                        binding.scoped.size() + binding.domains.size() +
                        binding.statics.size() + 1,
                    span) ||
      !types.chargeType(binding.signature.result, span))
    return false;
  for (const auto &input : binding.signature.inputs)
    if (!types.chargeType(input, span))
      return false;
  for (const auto &[name, value] : binding.statics)
    if (!types.charge(name.size() + 1, span) || !types.chargeType(value, span))
      return false;
  for (const auto &capture : binding.captures)
    if (!types.charge(capture.inputs.size() + 1, span))
      return false;
  for (const auto &domain : binding.domains)
    if (!types.charge(domain.inputs.size() + 1, span))
      return false;
  for (const auto &nested : binding.scoped)
    if (!chargeBinding(types, nested, depth + 1, span))
      return false;
  return true;
}
} // namespace
std::optional<Dependencies>
summarizeDomainBinding(Semantics &types, const Body &body, unsigned index,
                       ArrayRef<Dependencies> values,
                       ArrayRef<Dependencies> environment, unsigned depth,
                       bool identityValues) {
  std::set<unsigned> seen;
  std::vector<unsigned> pending{index};
  std::vector<Dependencies> dependencies;
  if (depth > types.work.limits.callDepth) {
    types.fail("source.limit", "domain summary depth exceeded", {});
    return {};
  }
  while (!pending.empty()) {
    auto current = pending.back();
    pending.pop_back();
    if (!types.charge(1, {}))
      return {};
    if (!seen.insert(current).second)
      continue;
    if (current >= body.domainBindings.size()) {
      types.fail("source.finite-domain", "domain summary edge outside body",
                 {});
      return {};
    }
    const auto &binding = body.domainBindings[current];
    if (!types.charge(binding.operands.size() + binding.children.size() + 1,
                      binding.span))
      return {};
    if (binding.kind == DomainBinding::Kind::Parameter) {
      if (!binding.parameter) {
        types.fail("source.finite-domain", "domain formal has no parameter",
                   binding.span);
        return {};
      }
      if (*binding.parameter < environment.size()) {
        const auto &dependency = environment[*binding.parameter];
        if (!types.charge(dependency.inputs.size() + 1, binding.span))
          return {};
        dependencies.push_back(dependency);
      } else
        dependencies.push_back({{}, true});
    }
    for (auto operand : binding.operands) {
      if (operand.index >=
          (identityValues ? body.values.size() : values.size())) {
        types.fail("source.finite-domain",
                   "domain summary operand outside body", binding.span);
        return {};
      }
      if (identityValues)
        dependencies.push_back({{operand.index}, false});
      else {
        if (!types.charge(values[operand.index].inputs.size() + 1,
                          binding.span))
          return {};
        dependencies.push_back(values[operand.index]);
      }
    }
    pending.insert(pending.end(), binding.children.begin(),
                   binding.children.end());
  }
  return join(types, dependencies);
}
std::optional<ScopedSummaryBinding> summarizeScopedBinding(
    Semantics &types, const Body &body, unsigned index,
    const Substitution &statics, ArrayRef<Dependencies> values,
    ArrayRef<ScopedSummaryBinding> environment, unsigned depth,
    bool identityValues, ArrayRef<Dependencies> domains) {
  if (index >= body.scopedBindings.size() ||
      depth > types.work.limits.callDepth) {
    types.fail("source.limit", "scoped summary depth exceeded", {});
    return {};
  }
  const auto &binding = body.scopedBindings[index];
  if (!types.charge(binding.captures.size() + binding.scopedCaptures.size() + 1,
                    binding.span))
    return {};
  if (binding.parameter) {
    if (*binding.parameter < environment.size()) {
      if (!chargeBinding(types, environment[*binding.parameter], depth,
                         binding.span))
        return {};
      return environment[*binding.parameter];
    }
    return ScopedSummaryBinding{nullptr, binding.signature, statics, {}, {},
                                {}};
  }
  ScopedSummaryBinding result{
      binding.computation.get(), binding.signature, statics, {}, {}, {}};
  for (auto capture : binding.captures) {
    if (capture.index >=
        (identityValues ? body.values.size() : values.size())) {
      types.fail("source.scoped-summary", "invalid capture mapping",
                 binding.span);
      return {};
    }
    if (identityValues)
      result.captures.push_back({{capture.index}, false});
    else {
      if (!types.charge(values[capture.index].inputs.size() + 1, binding.span))
        return {};
      result.captures.push_back(values[capture.index]);
    }
  }
  for (auto capture : binding.scopedCaptures) {
    auto nested =
        summarizeScopedBinding(types, body, capture, statics, values,
                               environment, depth + 1, identityValues, domains);
    if (!nested)
      return {};
    result.scoped.push_back(std::move(*nested));
  }
  for (auto capture : binding.domainCaptures) {
    auto domain = summarizeDomainBinding(types, body, capture, values, domains,
                                         depth + 1, identityValues);
    if (!domain)
      return {};
    result.domains.push_back(std::move(*domain));
  }
  return result;
}
std::optional<BodySummary>
summarizeBody(Semantics &types, ArrayRef<Declaration> declarations,
              const Body &body, const Substitution &statics,
              ArrayRef<Dependencies> inputs,
              ArrayRef<ScopedSummaryBinding> environment, unsigned depth,
              ArrayRef<Dependencies> domains) {
  if (depth > types.work.limits.callDepth || inputs.size() != body.inputs) {
    types.fail("source.limit", "body summary depth or input bound exceeded",
               {});
    return {};
  }
  BodySummary result;
  if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
    return {};
  result.values.resize(body.values.size());
  for (const auto &input : inputs)
    if (!types.charge(input.inputs.size() + 1, {}))
      return {};
  std::copy(inputs.begin(), inputs.end(), result.values.begin());
  auto gather = [&](ArrayRef<ValueId> operands)
      -> std::optional<std::vector<Dependencies>> {
    std::vector<Dependencies> values;
    for (auto operand : operands) {
      if (operand.index >= result.values.size()) {
        types.fail("source.scoped-summary", "invalid SSA operand", {});
        return {};
      }
      if (!types.charge(result.values[operand.index].inputs.size() + 1, {}))
        return {};
      values.push_back(result.values[operand.index]);
    }
    return values;
  };
  std::function<bool(const ScopedSummaryBinding &, std::vector<Dependencies> &)>
      captureDependencies = [&](const ScopedSummaryBinding &binding,
                                std::vector<Dependencies> &values) {
        for (const auto &capture : binding.captures)
          if (!types.charge(capture.inputs.size() + 1, {}))
            return false;
        values.insert(values.end(), binding.captures.begin(),
                      binding.captures.end());
        for (const auto &domain : binding.domains) {
          if (!types.charge(domain.inputs.size() + 1, {}))
            return false;
          values.push_back(domain);
        }
        if (!binding.computation)
          values.push_back({{}, true});
        for (const auto &nested : binding.scoped)
          if (!captureDependencies(nested, values))
            return false;
        return true;
      };
  auto absorb = [&](const BodySummary &nested) {
    for (const auto &formation : nested.formation)
      if (!types.charge(formation.inputs.size() + 1, {}))
        return false;
    result.formation.insert(result.formation.end(), nested.formation.begin(),
                            nested.formation.end());
    result.parameterized |= nested.parameterized;
    return true;
  };
  for (const auto &op : body.operations) {
    if (!types.charge(1, op.span))
      return {};
    Dependencies dependencies;
    if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
      auto binding = summarizeScopedBinding(types, body, invoke->binding,
                                            statics, result.values, environment,
                                            depth, false, domains);
      auto operands = gather(invoke->operands);
      if (!binding || !operands)
        return {};
      if (binding->computation) {
        operands->insert(operands->end(), binding->captures.begin(),
                         binding->captures.end());
        auto nested = summarizeBody(
            types, declarations, *binding->computation->body, binding->statics,
            *operands, binding->scoped, depth + 1, binding->domains);
        if (!nested)
          return {};
        if (!absorb(*nested))
          return {};
        auto combined = join(types, nested->results);
        if (!combined)
          return {};
        dependencies = std::move(*combined);
      } else {
        auto combined = join(types, *operands);
        if (!combined)
          return {};
        dependencies = std::move(*combined);
        dependencies.parameterized = true;
      }
    } else if (std::holds_alternative<FiniteApplication>(op.action) ||
               std::holds_alternative<FiniteComputation>(op.action)) {
      const auto *open = std::get_if<FiniteApplication>(&op.action);
      const auto *closed = std::get_if<FiniteComputation>(&op.action);
      std::optional<Dependencies> domain;
      if (open)
        domain = summarizeDomainBinding(types, body, open->domain,
                                        result.values, domains, depth);
      else {
        auto inputs = gather(closed->domainOperands);
        if (inputs)
          domain = join(types, *inputs);
      }
      const auto kind = open ? open->kind : closed->kind;
      auto operands = gather(open ? open->operands : closed->operands);
      if (!domain || !operands ||
          operands->size() != unsigned(kind == FiniteApplication::Kind::Fold))
        return {};
      // Item/cardinality facts have the domain's dependencies. Concrete
      // callbacks refine result dependencies; formation remains independent.
      Dependencies admission = *domain;
      result.formation.push_back(admission);
      auto invoke =
          [&](bool predicate,
              std::vector<Dependencies> inputs) -> std::optional<Dependencies> {
        std::optional<BodySummary> nested;
        if (closed) {
          const auto &selected = predicate ? *closed->predicate : closed->body;
          auto captures = gather(selected.captures);
          if (!captures || selected.helper.index >= declarations.size())
            return {};
          const auto &helper = declarations[selected.helper.index];
          if (!helper.body || !helper.parameters.empty() ||
              !helper.scopedInputs.empty() || !helper.domainInputs.empty())
            return {};
          inputs.insert(inputs.end(), captures->begin(), captures->end());
          nested = summarizeBody(types, declarations, *helper.body, {}, inputs,
                                 {}, depth + 1);
        } else {
          auto binding = summarizeScopedBinding(
              types, body, predicate ? *open->predicate : open->body, statics,
              result.values, environment, depth, false, domains);
          if (!binding)
            return {};
          if (!binding->computation) {
            auto result = join(types, inputs);
            if (result)
              result->parameterized = true;
            return result;
          }
          inputs.insert(inputs.end(), binding->captures.begin(),
                        binding->captures.end());
          nested =
              summarizeBody(types, declarations, *binding->computation->body,
                            binding->statics, inputs, binding->scoped,
                            depth + 1, binding->domains);
        }
        if (!nested || !absorb(*nested))
          return {};
        return join(types, nested->results);
      };
      if (open ? bool(open->predicate) : bool(closed->predicate)) {
        auto predicate = invoke(true, {*domain});
        auto combined =
            predicate ? join(types, {admission, *predicate}) : std::nullopt;
        if (!combined)
          return {};
        admission = std::move(*combined);
      }
      if (kind == FiniteApplication::Kind::Collect) {
        auto item = invoke(false, {*domain});
        auto combined = item ? join(types, {admission, *item}) : std::nullopt;
        if (!combined)
          return {};
        dependencies = std::move(*combined);
      } else {
        dependencies = operands->front();
        for (;;) {
          auto step = invoke(false, {dependencies, *domain});
          auto next = step ? join(types, {dependencies, admission, *step})
                           : std::nullopt;
          if (!next)
            return {};
          if (dependencies.inputs == next->inputs &&
              dependencies.parameterized == next->parameterized)
            break;
          dependencies = std::move(*next);
        }
      }
    } else if (const auto *call = std::get_if<HelperCall>(&op.action)) {
      auto operands = gather(call->operands);
      if (!operands || call->callee.index >= declarations.size())
        return {};
      auto target = call->callee;
      const auto &known = declarations[target.index];
      // A non-parameterized checked summary is already independent of static
      // callback selection. Reuse it without composing unrelated symbolic
      // natural arguments (which may only become representable at closure).
      if (known.body && known.kind == Declaration::Kind::Math &&
          !known.body->parameterizedSummary && call->scopedArguments.empty() &&
          call->domainArguments.empty() && (!call->component || known.origin)) {
        auto project =
            [&](ArrayRef<unsigned> indices) -> std::optional<Dependencies> {
          std::vector<Dependencies> selected;
          if (!types.charge(indices.size() + 1, op.span))
            return {};
          for (auto index : indices) {
            if (index >= operands->size()) {
              types.fail("source.scoped-summary", "invalid cached dependency",
                         op.span);
              return {};
            }
            if (!types.charge((*operands)[index].inputs.size() + 1, op.span))
              return {};
            selected.push_back((*operands)[index]);
          }
          return join(types, selected);
        };
        std::vector<Dependencies> results;
        for (auto value : known.body->results) {
          auto dependency = project(known.body->values[value.index].components);
          if (!dependency)
            return {};
          results.push_back(std::move(*dependency));
        }
        for (const auto &requirement : known.body->formationRequirements) {
          auto dependency = project(requirement);
          if (!dependency)
            return {};
          result.formation.push_back(std::move(*dependency));
        }
        auto combined = join(types, results);
        if (!combined)
          return {};
        dependencies = std::move(*combined);
      } else {
        std::vector<Dependencies> selectedDomains;
        for (auto domain : call->domainArguments) {
          auto dependency = summarizeDomainBinding(
              types, body, domain, result.values, domains, depth);
          if (!dependency)
            return {};
          selectedDomains.push_back(std::move(*dependency));
        }
        std::vector<Type> arguments;
        for (const auto &argument : call->arguments) {
          auto value = types.substitute(argument, statics, op.span);
          if (!value)
            return {};
          arguments.push_back(*value);
        }
        if (call->component && !known.origin) {
          auto component = types.substitute(*call->component, statics, op.span);
          if (!component)
            return {};
          auto *definition = types.typeDeclaration(*component);
          if (definition && definition->kind == Declaration::Kind::Component)
            for (auto member : definition->members)
              if (declarations[member.index].name ==
                  declarations[target.index].name) {
                target = member;
                arguments = component->arguments;
                break;
              }
        }
        const auto &callee = declarations[target.index];
        if (callee.body && callee.kind == Declaration::Kind::Math) {
          std::vector<ScopedSummaryBinding> selected;
          for (auto scoped : call->scopedArguments) {
            auto binding = summarizeScopedBinding(types, body, scoped, statics,
                                                  result.values, environment,
                                                  depth, false, domains);
            if (!binding)
              return {};
            selected.push_back(std::move(*binding));
          }
          auto nested =
              summarizeBody(types, declarations, *callee.body,
                            types.substitution(callee, arguments), *operands,
                            selected, depth + 1, selectedDomains);
          if (!nested)
            return {};
          if (!absorb(*nested))
            return {};
          auto combined = join(types, nested->results);
          if (!combined)
            return {};
          dependencies = std::move(*combined);
        } else {
          operands->insert(operands->end(), selectedDomains.begin(),
                           selectedDomains.end());
          for (auto scoped : call->scopedArguments) {
            auto binding = summarizeScopedBinding(types, body, scoped, statics,
                                                  result.values, environment,
                                                  depth, false, domains);
            if (!binding)
              return {};
            if (!captureDependencies(*binding, *operands))
              return {};
          }
          auto combined = join(types, *operands);
          if (!combined)
            return {};
          dependencies = std::move(*combined);
          dependencies.parameterized |= (!call->scopedArguments.empty() ||
                                         !call->domainArguments.empty()) &&
                                        callee.kind == Declaration::Kind::Math;
        }
      }
    } else {
      std::vector<ValueId> operands;
      std::visit(
          [&](const auto &action) {
            using T = std::decay_t<decltype(action)>;
            if constexpr (std::is_same_v<T, MathValue> ||
                          std::is_same_v<T, BulkApplication> ||
                          std::is_same_v<T, ProtocolApplication> ||
                          std::is_same_v<T, Construct> ||
                          std::is_same_v<T, LocalPrimitive> ||
                          std::is_same_v<T, LocalControl>)
              operands = action.operands;
            else if constexpr (std::is_same_v<T, Projection> ||
                               std::is_same_v<T, Consume> ||
                               std::is_same_v<T, Restriction>)
              operands = {action.input};
            else if constexpr (std::is_same_v<T, Require>)
              operands = {action.condition};
            else if constexpr (std::is_same_v<T, Exchange>)
              operands = {action.payload};
          },
          op.action);
      auto values = gather(operands);
      if (!values)
        return {};
      if (const auto *control = std::get_if<LocalControl>(&op.action)) {
        for (auto domain : control->domainArguments) {
          auto dependency = summarizeDomainBinding(
              types, body, domain, result.values, domains, depth);
          if (!dependency)
            return {};
          values->push_back(std::move(*dependency));
        }
        for (const auto &binding : environment)
          if (!captureDependencies(binding, *values))
            return {};
        if (environment.empty())
          for (const auto &region : control->regions)
            if (region->parameterizedSummary)
              values->push_back({{}, true});
      }
      auto combined = join(types, *values);
      if (!combined)
        return {};
      dependencies = std::move(*combined);
    }
    result.parameterized |= dependencies.parameterized;
    if (body.mode == Body::Mode::Math)
      result.formation.push_back(dependencies);
    for (auto value : op.results) {
      if (value.index >= result.values.size()) {
        types.fail("source.scoped-summary", "invalid result mapping", op.span);
        return {};
      }
      result.values[value.index] = dependencies;
    }
  }
  for (auto value : body.results) {
    if (value.index >= result.values.size()) {
      types.fail("source.scoped-summary", "invalid body result", {});
      return {};
    }
    if (!types.charge(result.values[value.index].inputs.size() + 1, {}))
      return {};
    result.results.push_back(result.values[value.index]);
  }
  // Formation is a set of obligations, not an expansion trace. Deduplication
  // preserves dead-intermediate checks without exponential summary growth in
  // a shared call DAG. Operation coverage is checked separately.
  uint64_t comparisonWidth = 1;
  for (const auto &requirement : result.formation)
    comparisonWidth =
        std::max(comparisonWidth, uint64_t(requirement.inputs.size() + 1));
  uint64_t levels = 1;
  for (auto count = result.formation.size(); count > 1; count >>= 1)
    ++levels;
  if (!types.charge(result.formation.size() * levels * comparisonWidth, {}))
    return {};
  llvm::sort(result.formation, [](const auto &a, const auto &b) {
    return std::tie(a.inputs, a.parameterized) <
           std::tie(b.inputs, b.parameterized);
  });
  result.formation.erase(
      std::unique(result.formation.begin(), result.formation.end(),
                  [](const auto &a, const auto &b) {
                    return a.inputs == b.inputs &&
                           a.parameterized == b.parameterized;
                  }),
      result.formation.end());
  for (const auto &requirement : result.formation)
    result.parameterized |= requirement.parameterized;
  return result;
}
} // namespace zkc::language::detail
