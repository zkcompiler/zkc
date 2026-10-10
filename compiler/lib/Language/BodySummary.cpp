#include "BodySummary.h"
#include <algorithm>
using namespace llvm;
namespace zkc::language::detail {
namespace {
Dependencies join(ArrayRef<Dependencies> values) {
  Dependencies result;
  for (const auto &value : values) {
    result.parameterized |= value.parameterized;
    result.inputs.insert(result.inputs.end(), value.inputs.begin(),
                         value.inputs.end());
  }
  llvm::sort(result.inputs);
  result.inputs.erase(std::unique(result.inputs.begin(), result.inputs.end()),
                      result.inputs.end());
  return result;
}
} // namespace
std::optional<ScopedSummaryBinding> summarizeScopedBinding(
    Semantics &types, const Body &body, unsigned index,
    const Substitution &statics, ArrayRef<Dependencies> values,
    ArrayRef<ScopedSummaryBinding> environment, unsigned depth) {
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
    if (*binding.parameter < environment.size())
      return environment[*binding.parameter];
    return ScopedSummaryBinding{nullptr, binding.signature, statics, {}, {}};
  }
  ScopedSummaryBinding result{
      binding.computation.get(), binding.signature, statics, {}, {}};
  for (auto capture : binding.captures) {
    if (capture.index >= values.size()) {
      types.fail("source.scoped-summary", "invalid capture mapping",
                 binding.span);
      return {};
    }
    result.captures.push_back(values[capture.index]);
  }
  for (auto capture : binding.scopedCaptures) {
    auto nested = summarizeScopedBinding(types, body, capture, statics, values,
                                         environment, depth + 1);
    if (!nested)
      return {};
    result.scoped.push_back(std::move(*nested));
  }
  return result;
}
std::optional<BodySummary>
summarizeBody(Semantics &types, ArrayRef<Declaration> declarations,
              const Body &body, const Substitution &statics,
              ArrayRef<Dependencies> inputs,
              ArrayRef<ScopedSummaryBinding> environment, unsigned depth) {
  if (depth > types.work.limits.callDepth || inputs.size() != body.inputs) {
    types.fail("source.limit", "body summary depth or input bound exceeded",
               {});
    return {};
  }
  BodySummary result;
  if (!types.charge(body.values.size() + body.operations.size() + 1, {}))
    return {};
  result.values.resize(body.values.size());
  std::copy(inputs.begin(), inputs.end(), result.values.begin());
  // Written effects include primitive checks and explicit terminators; scoped
  // calls are bounded by the definition's allowance even before substitution.
  result.effects = {body.mayStop, body.opaque};
  auto gather = [&](ArrayRef<ValueId> operands)
      -> std::optional<std::vector<Dependencies>> {
    std::vector<Dependencies> values;
    for (auto operand : operands) {
      if (operand.index >= result.values.size()) {
        types.fail("source.scoped-summary", "invalid SSA operand", {});
        return {};
      }
      values.push_back(result.values[operand.index]);
    }
    return values;
  };
  std::function<void(const ScopedSummaryBinding &, std::vector<Dependencies> &)>
      captureDependencies = [&](const ScopedSummaryBinding &binding,
                                std::vector<Dependencies> &values) {
        values.insert(values.end(), binding.captures.begin(),
                      binding.captures.end());
        if (!binding.computation)
          values.push_back({{}, true});
        for (const auto &nested : binding.scoped)
          captureDependencies(nested, values);
      };
  auto absorb = [&](const BodySummary &nested) {
    result.formation.insert(result.formation.end(), nested.formation.begin(),
                            nested.formation.end());
    result.effects.mayStop |= nested.effects.mayStop;
    result.effects.opaque |= nested.effects.opaque;
    result.parameterized |= nested.parameterized;
  };
  for (const auto &op : body.operations) {
    if (!types.charge(1, op.span))
      return {};
    Dependencies dependencies;
    if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
      auto binding =
          summarizeScopedBinding(types, body, invoke->binding, statics,
                                 result.values, environment, depth);
      auto operands = gather(invoke->operands);
      if (!binding || !operands)
        return {};
      if (binding->computation) {
        operands->insert(operands->end(), binding->captures.begin(),
                         binding->captures.end());
        auto nested = summarizeBody(
            types, declarations, *binding->computation->body, binding->statics,
            *operands, binding->scoped, depth + 1);
        if (!nested)
          return {};
        absorb(*nested);
        dependencies = join(nested->results);
      } else {
        dependencies = join(*operands);
        dependencies.parameterized = true;
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
          (!call->component || known.origin)) {
        auto project =
            [&](ArrayRef<unsigned> indices) -> std::optional<Dependencies> {
          std::vector<Dependencies> selected;
          for (auto index : indices) {
            if (index >= operands->size()) {
              types.fail("source.scoped-summary", "invalid cached dependency",
                         op.span);
              return {};
            }
            selected.push_back((*operands)[index]);
          }
          return join(selected);
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
        dependencies = join(results);
        result.effects.mayStop |= known.body->mayStop;
        result.effects.opaque |= known.body->opaque;
      } else {
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
            auto binding =
                summarizeScopedBinding(types, body, scoped, statics,
                                       result.values, environment, depth);
            if (!binding)
              return {};
            selected.push_back(std::move(*binding));
          }
          auto nested = summarizeBody(types, declarations, *callee.body,
                                      types.substitution(callee, arguments),
                                      *operands, selected, depth + 1);
          if (!nested)
            return {};
          absorb(*nested);
          dependencies = join(nested->results);
        } else {
          for (auto scoped : call->scopedArguments) {
            auto binding =
                summarizeScopedBinding(types, body, scoped, statics,
                                       result.values, environment, depth);
            if (!binding)
              return {};
            captureDependencies(*binding, *operands);
          }
          dependencies = join(*operands);
          dependencies.parameterized |= !call->scopedArguments.empty() &&
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
        for (const auto &binding : environment)
          captureDependencies(binding, *values);
        if (environment.empty())
          for (const auto &region : control->regions)
            if (region->parameterizedSummary)
              values->push_back({{}, true});
      }
      dependencies = join(*values);
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
  for (auto value : body.results)
    result.results.push_back(result.values.at(value.index));
  // Formation is a set of obligations, not an expansion trace. Deduplication
  // preserves dead-intermediate checks without exponential summary growth in
  // a shared call DAG. Operation coverage is checked separately.
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
