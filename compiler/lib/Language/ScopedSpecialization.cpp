#include "BodySummary.h"
#include "ClosureInputs.h"
#include "DataRequirements.h"
#include "DomainWitness.h"
#include "Effects.h"
#include "FiniteContracts.h"
#include "zkc/Language/Project.h"
#include <algorithm>
#include <set>
using namespace llvm;
namespace zkc::language::detail {
namespace {
bool same(Span a, Span b) {
  return a.module.index == b.module.index && a.begin == b.begin &&
         a.end == b.end;
}
bool same(ArrayRef<ValueId> a, ArrayRef<ValueId> b) {
  return a.size() == b.size() &&
         std::equal(a.begin(), a.end(), b.begin(),
                    [](auto x, auto y) { return x.index == y.index; });
}
struct Environment {
  DeclarationId helper;
  std::vector<ValueId> captures;
};
/// Relational checking of the candidate under explicit source substitutions.
/// This checker never invokes specialization or generates an expected Body.
class SpecializationCheck {
  const ClosedEntry &entry;
  ArrayRef<Declaration> source, candidate;
  std::vector<Declaration> typeDeclarations;
  Work &work;
  Semantics types;
  std::set<unsigned> active, checked;
  bool
  refuse(Span span,
         StringRef message =
             "specialized scoped computation differs from checked source") {
    return types.fail("source.scoped-specialization", message, span);
  }
  std::optional<Type> type(const Type &value, const Substitution &subst,
                           Span span) {
    return types.substitute(value, subst, span);
  }
  bool typeEqual(const Type &original, const Type &actual,
                 const Substitution &subst, Span span) {
    auto expected = type(original, subst, span);
    return expected &&
           (*expected == actual || refuse(span, "specialized type differs"));
  }
  std::optional<std::vector<Type>>
  arguments(ArrayRef<Type> original, const Substitution &subst, Span span) {
    std::vector<Type> result;
    for (const auto &argument : original) {
      auto value = type(argument, subst, span);
      if (!value)
        return {};
      result.push_back(*value);
    }
    return result;
  }
  Substitution substitution(const Declaration &declaration,
                            ArrayRef<Type> arguments) {
    auto result = types.substitution(declaration, arguments);
    auto parent = declaration.parent;
    while (parent && source[parent->index].kind != Declaration::Kind::Component)
      parent = source[parent->index].parent;
    if (parent) {
      const auto &component = source[parent->index];
      Type self(Type::Kind::Component, component.qualifiedName);
      self.arguments.assign(arguments.begin(),
                            arguments.begin() + component.parameters.size());
      if (component.implementation)
        result.emplace("self:" + component.implementation->domain, self);
    }
    return result;
  }
  std::optional<Environment>
  binding(const Body &body, const Body &closedBody, ValueOrigins &bodyOrigins,
          unsigned index, DeclarationId selected, const Substitution &subst,
          ArrayRef<Environment> environment,
          ArrayRef<DomainEnvironment> domains,
          const std::function<ValueId(ValueId)> &map, unsigned depth) {
    if (index >= body.scopedBindings.size() ||
        selected.index >= candidate.size() || depth > work.limits.callDepth) {
      refuse({}, "invalid scoped environment edge");
      return {};
    }
    const auto &binding = body.scopedBindings[index];
    if (!types.charge(binding.captures.size() + binding.scopedCaptures.size() +
                          1,
                      binding.span))
      return {};
    if (binding.parameter) {
      if (*binding.parameter >= environment.size() ||
          environment[*binding.parameter].helper.index != selected.index) {
        refuse(binding.span, "forwarded scoped target differs");
        return {};
      }
      return environment[*binding.parameter];
    }
    if (!binding.computation) {
      refuse(binding.span);
      return {};
    }
    const auto &computation = *binding.computation;
    const auto &actual = candidate[selected.index];
    if (!actual.scopedOrigin ||
        actual.scopedOrigin->first.index != computation.lexicalOwner.index ||
        actual.scopedOrigin->second != computation.expression ||
        actual.scopedArguments.size() != binding.scopedCaptures.size() ||
        actual.domainArguments.size() != binding.domainCaptures.size()) {
      refuse(binding.span, "selected callback identity differs");
      return {};
    }
    std::vector<Type> statics;
    for (const auto &parameter :
         source[computation.lexicalOwner.index].parameters) {
      auto argument = type(parameterType(parameter), subst, binding.span);
      if (!argument)
        return {};
      statics.push_back(*argument);
    }
    Environment result{selected, {}};
    std::vector<std::optional<ValueId>> authored(
        computation.signature.inputs.size());
    for (auto capture : binding.captures)
      authored.push_back(map(capture));
    std::vector<ValueId> hidden;
    for (unsigned i = 0; i < binding.scopedCaptures.size(); ++i) {
      auto captured =
          this->binding(body, closedBody, bodyOrigins,
                        binding.scopedCaptures[i], actual.scopedArguments[i],
                        subst, environment, domains, map, depth + 1);
      if (!captured)
        return {};
      hidden.insert(hidden.end(), captured->captures.begin(),
                    captured->captures.end());
    }
    for (unsigned i = 0; i < binding.domainCaptures.size(); ++i) {
      if (!actual.domainArguments[i]) {
        refuse(binding.span, "missing captured domain shape");
        return {};
      }
      auto operands = bindDomainInputs(
          types, source, body, closedBody, map, binding.domainCaptures[i],
          subst, domains, *actual.domainArguments[i], &bodyOrigins);
      if (!operands)
        return {};
      hidden.insert(hidden.end(), operands->begin(), operands->end());
    }
    auto inputs = bindClosureInputs(types, closedBody, authored, hidden,
                                    actual.closureLayout, actual.inputs.size(),
                                    binding.span, &bodyOrigins);
    if (!inputs)
      return {};
    for (auto value :
         ArrayRef(*inputs).drop_front(computation.signature.inputs.size())) {
      if (!value) {
        refuse(binding.span, "unbound closed capture input");
        return {};
      }
      result.captures.push_back(*value);
    }
    if (!instance(selected, source[computation.lexicalOwner.index],
                  &computation, statics, actual.scopedArguments, depth, true))
      return {};
    return result;
  }
  bool body(const Body &original, const Body &actual, const Substitution &subst,
            ArrayRef<Environment> environment,
            ArrayRef<DomainEnvironment> domains, unsigned depth,
            const ClosureLayout *layout = nullptr,
            std::optional<unsigned> invariantSuffix = {},
            unsigned regionDepth = 1) {
    if (depth > work.limits.callDepth ||
        regionDepth > work.limits.expressionDepth)
      return types.fail("source.limit", "specialization witness depth exceeded",
                        {});
    if (!types.charge(original.values.size() + original.operations.size() + 1,
                      {}))
      return false;
    ValueOrigins bodyOrigins(types, actual);
    unsigned hidden = 0;
    for (const auto &selected : environment)
      for (auto capture : selected.captures)
        if (capture.index >= original.inputs)
          hidden = std::max(hidden, capture.index - original.inputs + 1);
    for (const auto &domain : domains)
      for (auto operand : domain.operands)
        if (operand.index >= original.inputs)
          hidden = std::max(hidden, operand.index - original.inputs + 1);
    auto map = [&](ValueId value) {
      return ValueId{value.index < original.inputs
                         ? (layout ? layout->inputs[value.index] : value.index)
                         : value.index + hidden};
    };
    auto mapped = [&](ArrayRef<ValueId> values) {
      std::vector<ValueId> result;
      for (auto value : values)
        result.push_back(map(value));
      return result;
    };
    auto results = mapped(original.results);
    if (invariantSuffix && !actual.stopped) {
      if (*invariantSuffix > original.inputs ||
          *invariantSuffix > results.size())
        return refuse({}, "loop invariant result coverage differs");
      for (unsigned i = 0; i < *invariantSuffix; ++i) {
        if (original.results[original.results.size() - *invariantSuffix + i]
                .index != original.inputs - *invariantSuffix + i)
          return refuse({}, "source loop invariant yield differs");
        results[results.size() - *invariantSuffix + i] = {original.inputs -
                                                          *invariantSuffix + i};
      }
      for (unsigned i = original.inputs; i < actual.inputs; ++i)
        results.push_back({i});
    }
    if (actual.mode != original.mode ||
        actual.inputs != original.inputs + hidden ||
        actual.values.size() != original.values.size() + hidden ||
        actual.operations.size() != original.operations.size() ||
        actual.stopped != original.stopped ||
        actual.stopReason != original.stopReason ||
        !actual.scopedBindings.empty() || !actual.domainBindings.empty() ||
        !same(actual.results, results))
      return refuse({});
    for (unsigned i = 0; i < original.values.size(); ++i) {
      const auto &expected = original.values[i];
      const auto &value =
          actual.values[i < original.inputs ? i : map({i}).index];
      if (!typeEqual(expected.type, value.type, subst, expected.span) ||
          !same(expected.span, value.span) ||
          (actual.mode == Body::Mode::Protocol &&
           expected.components != value.components) ||
          (actual.mode == Body::Mode::Local && !value.components.empty()))
        return refuse(expected.span);
    }
    auto effects = inferEffects(types, candidate, actual);
    if (!effects || !effects->dependencies.empty() ||
        *effects != actual.effects)
      return refuse({}, "specialized effect summary differs from operations");
    if (actual.mode == Body::Mode::Math) {
      std::vector<Dependencies> inputs;
      for (unsigned i = 0; i < actual.inputs; ++i)
        inputs.push_back({{i}, false});
      auto summary = summarizeBody(types, candidate, actual, {}, inputs, {});
      if (!summary || summary->parameterized || actual.parameterizedSummary)
        return refuse({});
      std::vector<std::vector<unsigned>> formation;
      for (const auto &requirement : summary->formation)
        formation.push_back(requirement.inputs);
      if (actual.formationRequirements != formation)
        return refuse({}, "formation requirements differ");
      for (unsigned i = 0; i < actual.values.size(); ++i)
        if (actual.values[i].components != summary->values[i].inputs)
          return refuse(actual.values[i].span, "result dependencies differ");
    }
    if (actual.services.size() != original.services.size())
      return refuse({});
    for (unsigned i = 0; i < original.services.size(); ++i)
      if (actual.services[i].name != original.services[i].name ||
          actual.services[i].owner != original.services[i].owner ||
          !typeEqual(original.services[i].field, actual.services[i].field,
                     subst, original.services[i].span))
        return refuse(original.services[i].span);
    for (unsigned i = 0; i < original.operations.size(); ++i) {
      const auto &op = original.operations[i];
      const auto &out = actual.operations[i];
      if (!same(op.span, out.span) || op.statement != out.statement ||
          !same(out.results, mapped(op.results)))
        return refuse(op.span, "operation occurrence differs");
      if (bool(op.binding) != bool(out.binding))
        return refuse(op.span, "call witness coverage differs");
      if (op.binding) {
        const auto &a = *op.binding;
        const auto &b = *out.binding;
        auto statics = arguments(a.arguments, subst, op.span);
        if (!statics || *statics != b.arguments ||
            a.target.declaration.index != b.target.declaration.index ||
            !same(b.operands, mapped(a.operands)) || a.symbol != b.symbol ||
            a.family != b.family || a.scopedSource != b.scopedSource ||
            a.argumentOrder != b.argumentOrder ||
            a.scopedArguments != b.scopedArguments ||
            a.domainArguments != b.domainArguments ||
            bool(a.target.component) != bool(b.target.component) ||
            bool(a.notation) != bool(b.notation) ||
            (a.notation && *a.notation != *b.notation) ||
            bool(a.origin) != bool(b.origin) ||
            (a.origin && !same(*a.origin, *b.origin)))
          return refuse(op.span, "call evidence differs");
        if (a.target.component &&
            !typeEqual(*a.target.component, *b.target.component, subst,
                       op.span))
          return false;
      }
      if (const auto *invoke = std::get_if<ScopedInvoke>(&op.action)) {
        const auto *call = std::get_if<HelperCall>(&out.action);
        if (!call || invoke->binding >= original.scopedBindings.size() ||
            !call->arguments.empty() || call->component || call->owner ||
            !call->scopedArguments.empty() || !call->domainArguments.empty())
          return refuse(op.span);
        auto selected =
            binding(original, actual, bodyOrigins, invoke->binding,
                    call->callee, subst, environment, domains, map, depth + 1);
        if (!selected)
          return false;
        auto operands = mapped(invoke->operands);
        operands.insert(operands.end(), selected->captures.begin(),
                        selected->captures.end());
        if (!same(call->operands, operands))
          return refuse(op.span, "invocation environment mapping differs");
        continue;
      }
      if (const auto *finite = std::get_if<FiniteApplication>(&op.action)) {
        const auto *closed = std::get_if<FiniteComputation>(&out.action);
        if (!closed || closed->kind != finite->kind || !closed->domain ||
            bool(closed->predicate) != bool(finite->predicate) ||
            !same(closed->operands, mapped(finite->operands)))
          return refuse(op.span, "finite operation differs");
        auto operands = bindDomainInputs(types, source, original, actual, map,
                                         finite->domain, subst, domains,
                                         *closed->domain, &bodyOrigins);
        if (!operands || !same(closed->domainOperands, *operands))
          return refuse(op.span, "finite domain mapping differs");
        auto callback = [&](unsigned index, const FiniteCallback &selected) {
          auto expected =
              binding(original, actual, bodyOrigins, index, selected.helper,
                      subst, environment, domains, map, depth + 1);
          return expected && same(selected.captures, expected->captures);
        };
        if (!callback(finite->body, closed->body) ||
            (finite->predicate &&
             !callback(*finite->predicate, *closed->predicate)))
          return refuse(op.span, "finite callback mapping differs");
        continue;
      }
      if (op.action.index() != out.action.index())
        return refuse(op.span, "operation kind differs");
      bool valid = std::visit(
          [&](const auto &action) -> bool {
            using T = std::decay_t<decltype(action)>;
            const auto &value = std::get<T>(out.action);
            if constexpr (std::is_same_v<T, HelperCall> ||
                          std::is_same_v<T, BulkApplication> ||
                          std::is_same_v<T, ProtocolApplication>) {
              if (value.callee.index >= candidate.size())
                return false;
              auto target = action.callee;
              auto statics = arguments(action.arguments, subst, op.span);
              if (!statics)
                return false;
              if constexpr (std::is_same_v<T, HelperCall>) {
                if (bool(action.component) != bool(value.component) ||
                    action.owner != value.owner ||
                    !value.scopedArguments.empty() ||
                    !value.domainArguments.empty())
                  return false;
                if (action.component) {
                  auto component = type(*action.component, subst, op.span);
                  if (!component || *component != *value.component)
                    return false;
                  auto *definition = types.typeDeclaration(*component);
                  if (!definition ||
                      definition->kind != Declaration::Kind::Component)
                    return false;
                  bool found = false;
                  for (auto member : definition->members)
                    if (source[member.index].name ==
                        source[target.index].name) {
                      target = member;
                      *statics = component->arguments;
                      found = true;
                      break;
                    }
                  if (!found)
                    return false;
                }
              }
              const auto &callee = candidate[value.callee.index];
              auto operands = mapped(action.operands);
              std::vector<DeclarationId> selected;
              std::vector<ValueId> hidden;
              if constexpr (std::is_same_v<T, HelperCall>) {
                if (action.scopedArguments.size() !=
                    callee.scopedArguments.size())
                  return false;
                for (unsigned j = 0; j < action.scopedArguments.size(); ++j) {
                  auto scoped = binding(original, actual, bodyOrigins,
                                        action.scopedArguments[j],
                                        callee.scopedArguments[j], subst,
                                        environment, domains, map, depth + 1);
                  if (!scoped)
                    return false;
                  selected.push_back(scoped->helper);
                  hidden.insert(hidden.end(), scoped->captures.begin(),
                                scoped->captures.end());
                }
              }
              if constexpr (std::is_same_v<T, HelperCall>) {
                if (action.domainArguments.size() !=
                    callee.domainArguments.size())
                  return false;
                for (unsigned j = 0; j < action.domainArguments.size(); ++j) {
                  if (!callee.domainArguments[j])
                    return false;
                  auto bound = bindDomainInputs(
                      types, source, original, actual, map,
                      action.domainArguments[j], subst, domains,
                      *callee.domainArguments[j], &bodyOrigins);
                  if (!bound)
                    return false;
                  hidden.insert(hidden.end(), bound->begin(), bound->end());
                }
                std::vector<std::optional<ValueId>> authored;
                for (auto value : operands)
                  authored.push_back(value);
                auto inputs = bindClosureInputs(
                    types, actual, authored, hidden, callee.closureLayout,
                    callee.inputs.size(), op.span, &bodyOrigins);
                if (!inputs)
                  return false;
                operands.clear();
                for (auto input : *inputs) {
                  if (!input)
                    return false;
                  operands.push_back(*input);
                }
              }
              if constexpr (std::is_same_v<T, BulkApplication>)
                if (action.mapped != value.mapped)
                  return false;
              if constexpr (std::is_same_v<T, ProtocolApplication>) {
                if (action.roles != value.roles ||
                    action.services.size() != value.services.size())
                  return false;
                for (unsigned j = 0; j < action.services.size(); ++j)
                  if (action.services[j].index != value.services[j].index)
                    return false;
              }
              return same(value.operands, operands) &&
                     value.arguments == *statics &&
                     instance(value.callee, source[target.index], nullptr,
                              *statics, selected, depth + 1,
                              std::is_same_v<T, HelperCall>);
            } else if constexpr (std::is_same_v<T, MathValue>) {
              auto statics = arguments(action.staticArguments, subst, op.span);
              return statics && *statics == value.staticArguments &&
                     action.identity == value.identity &&
                     action.literal == value.literal &&
                     action.parameters == value.parameters &&
                     same(value.operands, mapped(action.operands));
            } else if constexpr (std::is_same_v<T, LocalPrimitive>) {
              auto statics = arguments(action.staticArguments, subst, op.span);
              if (!statics || *statics != value.staticArguments ||
                  action.contract != value.contract ||
                  action.origin != value.origin ||
                  !same(value.operands, mapped(action.operands)) ||
                  bool(action.bindingArguments) != bool(value.bindingArguments))
                return false;
              if (action.bindingArguments) {
                auto roots =
                    arguments(*action.bindingArguments, subst, op.span);
                if (!roots || *roots != *value.bindingArguments)
                  return false;
              }
              auto parameters = action.parameters;
              for (const auto &asset : action.assetReferences) {
                auto term = type(asset.term, subst, op.span);
                if (!term || asset.position >= parameters.size())
                  return false;
                parameters[asset.position] = term->domain;
              }
              if (!statics->empty())
                parameters = {
                    std::to_string(statics->front().dimension.closedValue())};
              return parameters == value.parameters;
            } else if constexpr (std::is_same_v<T, Projection>)
              return map(action.input).index == value.input.index &&
                     action.path == value.path;
            else if constexpr (std::is_same_v<T, Construct>)
              return action.kind == value.kind &&
                     action.alternative == value.alternative &&
                     same(value.operands, mapped(action.operands));
            else if constexpr (std::is_same_v<T, Consume>)
              return map(action.input).index == value.input.index;
            else if constexpr (std::is_same_v<T, Restriction>)
              return map(action.input).index == value.input.index &&
                     action.roles == value.roles;
            else if constexpr (std::is_same_v<T, Exchange>)
              return map(action.payload).index == value.payload.index &&
                     action.sender == value.sender &&
                     action.receiver == value.receiver;
            else if constexpr (std::is_same_v<T, Require>)
              return map(action.condition).index == value.condition.index &&
                     action.owner == value.owner;
            else if constexpr (std::is_same_v<T, ServiceQuery>) {
              if (action.service.index != value.service.index ||
                  bool(action.bound) != bool(value.bound))
                return false;
              if (!action.bound)
                return true;
              Type term(Type::Kind::Natural);
              term.dimension = *action.bound;
              term.symbolic = !term.dimension.isClosed();
              auto bound = type(term, subst, op.span);
              return bound && bound->dimension == *value.bound;
            } else if constexpr (std::is_same_v<T, ProtocolCompletion>)
              return map(action.condition).index == value.condition.index &&
                     action.owner == value.owner &&
                     action.continuations == value.continuations &&
                     same(value.values, mapped(action.values));
            else if constexpr (std::is_same_v<T, LocalControl>) {
              if (action.kind != value.kind ||
                  action.carried != value.carried ||
                  action.alternatives != value.alternatives ||
                  action.regions.size() != value.regions.size() ||
                  action.regions.size() != value.regionLayouts.size() ||
                  !value.domainArguments.empty() ||
                  value.domainShapes.size() != action.domainArguments.size())
                return false;
              std::vector<ValueId> captures;
              for (const auto &selected : environment)
                captures.insert(captures.end(), selected.captures.begin(),
                                selected.captures.end());
              std::vector<DomainEnvironment> selectedDomains;
              for (unsigned j = 0; j < action.domainArguments.size(); ++j) {
                if (!value.domainShapes[j])
                  return false;
                auto bound =
                    bindDomainInputs(types, source, original, actual, map,
                                     action.domainArguments[j], subst, domains,
                                     *value.domainShapes[j], &bodyOrigins);
                if (!bound)
                  return false;
                captures.insert(captures.end(), bound->begin(), bound->end());
                selectedDomains.push_back(
                    {value.domainShapes[j], std::move(*bound)});
              }
              const bool loop = action.kind == LocalControl::Kind::For;
              unsigned header = loop ? 2 : 1;
              auto operands = mapped(action.operands);
              if (operands.size() < header)
                return false;
              unsigned forwarded = operands.size() - header;
              for (unsigned j = 0; j < action.regions.size(); ++j) {
                const auto &region = *action.regions[j];
                const auto &closed = *value.regions[j];
                if (region.inputs < forwarded ||
                    (loop && (region.inputs != forwarded + 1 ||
                              action.carried > forwarded)))
                  return false;
                std::vector<std::optional<ValueId>> authored(region.inputs -
                                                             forwarded);
                for (unsigned i = 0; i < forwarded; ++i)
                  authored.push_back(
                      loop && i < action.carried
                          ? std::nullopt
                          : std::optional<ValueId>(operands[header + i]));
                const auto &layout = value.regionLayouts[j];
                auto inputs =
                    bindClosureInputs(types, actual, authored, captures, layout,
                                      closed.inputs, op.span, &bodyOrigins);
                if (!inputs)
                  return false;
                for (unsigned k = region.inputs; k < closed.inputs; ++k)
                  if (!(*inputs)[k] || k >= closed.values.size() ||
                      closed.values[k].type !=
                          actual.values[(*inputs)[k]->index].type ||
                      !closed.values[k].components.empty())
                    return false;
                auto expectedOperands = operands;
                for (auto input : ArrayRef(*inputs).drop_front(region.inputs)) {
                  if (!input)
                    return false;
                  expectedOperands.push_back(*input);
                }
                if (!same(value.operands, expectedOperands))
                  return false;
                auto nested = std::vector<Environment>(environment.begin(),
                                                       environment.end());
                auto nestedDomains = selectedDomains;
                unsigned offset = 0;
                for (auto &selected : nested)
                  for (auto &capture : selected.captures)
                    capture = {layout.captures[offset++]};
                for (auto &domain : nestedDomains)
                  for (auto &operand : domain.operands)
                    operand = {layout.captures[offset++]};
                if (!body(region, closed, subst, nested, nestedDomains, depth,
                          &layout,
                          loop ? std::optional<unsigned>(forwarded -
                                                         action.carried)
                               : std::nullopt,
                          regionDepth + 1))
                  return false;
              }
              return true;
            } else if constexpr (std::is_same_v<T, ProtocolRepeat>) {
              Type term(Type::Kind::Natural);
              term.dimension = action.maximum;
              term.symbolic = !term.dimension.isClosed();
              auto maximum = type(term, subst, op.span);
              if (!maximum || maximum->dimension != value.maximum ||
                  action.roles != value.roles ||
                  map(action.count).index != value.count.index ||
                  !same(value.carried, mapped(action.carried)) ||
                  !same(value.captures, mapped(action.captures)) ||
                  action.services.size() != value.services.size())
                return false;
              for (unsigned j = 0; j < action.services.size(); ++j)
                if (action.services[j].index != value.services[j].index)
                  return false;
              std::vector<std::optional<ValueId>> authored(
                  1 + action.carried.size());
              for (auto capture : action.captures)
                authored.push_back(map(capture));
              if (!bindClosureInputs(types, actual, authored, {},
                                     value.regionLayout, value.region->inputs,
                                     op.span, &bodyOrigins))
                return false;
              return body(*action.region, *value.region, subst, {}, {}, depth,
                          &value.regionLayout, {}, regionDepth + 1);
            } else
              return false;
          },
          op.action);
      if (!valid)
        return types.diagnostic ? false : refuse(op.span);
    }
    return true;
  }
  bool construction(const Declaration &original, const Declaration &actual,
                    const Substitution &subst, unsigned depth) {
    if (bool(original.construction) != bool(actual.construction))
      return refuse(actual.span, "construction presence differs");
    if (!original.construction)
      return true;
    const auto &a = *original.construction;
    const auto &b = *actual.construction;
    if (!types.charge(a.rules.size() + a.applications.size() + 1, actual.span))
      return false;
    auto optionalType = [&](const auto &x, const auto &y) {
      return bool(x) == bool(y) &&
             (!x || typeEqual(*x, *y, subst, actual.span));
    };
    auto edge = [&](DeclarationId x, DeclarationId y, ArrayRef<Type> args) {
      auto selected = arguments(args, subst, actual.span);
      return selected && x.index < source.size() &&
             instance(y, source[x.index], nullptr, *selected, {}, depth + 1);
    };
    auto method = [&](const CallableReference &x, const CallableReference &y,
                      ArrayRef<Type> args, ArrayRef<Type> closedArgs) {
      if (x.declaration.index >= source.size() ||
          !optionalType(x.component, y.component))
        return false;
      auto selected = arguments(args, subst, actual.span);
      if (!selected)
        return false;
      auto target = x.declaration;
      if (x.component) {
        auto bound = type(*x.component, subst, actual.span);
        auto *owner = bound ? types.typeDeclaration(*bound) : nullptr;
        if (!owner || owner->kind != Declaration::Kind::Component ||
            !types.charge(owner->members.size(), actual.span))
          return false;
        auto found = llvm::find_if(owner->members, [&](DeclarationId member) {
          return source[member.index].name == source[target.index].name;
        });
        if (found == owner->members.end() ||
            ArrayRef<Type>(bound->arguments) != closedArgs)
          return false;
        target = *found;
        *selected = bound->arguments;
      }
      if (ArrayRef<Type>(*selected) != closedArgs)
        return false;
      return instance(y.declaration, source[target.index], nullptr, *selected,
                      {}, depth + 1);
    };
    if (a.base != b.base || a.root != b.root || a.services != b.services ||
        a.suite != b.suite || a.nativeBase != b.nativeBase ||
        a.rules.size() != b.rules.size() ||
        a.applications.size() != b.applications.size() ||
        bool(a.parent) != bool(b.parent) ||
        bool(a.initializer) != bool(b.initializer) ||
        bool(a.codec) != bool(b.codec) ||
        !optionalType(a.provider, b.provider) ||
        !optionalType(a.state, b.state) || !original.target || !actual.target ||
        !edge(*original.target, *actual.target, original.staticArguments))
      return refuse(actual.span, "construction closure differs");
    auto parentArgs = arguments(a.arguments, subst, actual.span);
    if (!parentArgs || *parentArgs != b.arguments ||
        (a.parent && !edge(*a.parent, *b.parent, a.arguments)) ||
        (a.initializer &&
         !method(*a.initializer, *b.initializer, a.initializerArguments,
                 b.initializerArguments)))
      return refuse(actual.span, "construction provider closure differs");
    if (a.codec) {
      if (a.codec->inputs != b.codec->inputs ||
          !typeEqual(a.codec->provider, b.codec->provider, subst,
                     actual.span) ||
          !typeEqual(a.codec->record, b.codec->record, subst, actual.span))
        return refuse(actual.span, "record codec closure differs");
      for (auto pair : {std::pair{&a.codec->initialize, &b.codec->initialize},
                        std::pair{&a.codec->write, &b.codec->write},
                        std::pair{&a.codec->finish, &b.codec->finish}})
        if (!method(pair.first->target, pair.second->target,
                    pair.first->arguments, pair.second->arguments))
          return refuse(actual.span, "record codec method differs");
    }
    for (unsigned i = 0; i < a.applications.size(); ++i) {
      auto args = arguments(a.applications[i].arguments, subst, actual.span);
      if (!args || *args != b.applications[i].arguments ||
          a.applications[i].path != b.applications[i].path ||
          !edge(a.applications[i].construction, b.applications[i].construction,
                a.applications[i].arguments))
        return refuse(actual.span, "child construction closure differs");
    }
    for (unsigned i = 0; i < a.rules.size(); ++i) {
      const auto &x = a.rules[i];
      const auto &y = b.rules[i];
      auto args = arguments(x.arguments, subst, x.span);
      if (!args || *args != y.arguments || x.kind != y.kind ||
          x.path != y.path || x.inputs != y.inputs ||
          !optionalType(x.payload, y.payload) ||
          !optionalType(x.chunks, y.chunks) ||
          !edge(x.handler, y.handler, x.arguments))
        return refuse(actual.span, "construction handler closure differs");
    }
    return true;
  }
  bool instance(DeclarationId id, const Declaration &original,
                const ScopedComputation *computation, ArrayRef<Type> statics,
                ArrayRef<DeclarationId> selected, unsigned depth,
                bool checkedAliases = false) {
    if (id.index >= candidate.size() || depth > work.limits.callDepth)
      return refuse(original.span, "invalid specialization edge");
    const auto &actual = candidate[id.index];
    if (!types.charge(1, actual.span))
      return false;
    if (ArrayRef<Type>(actual.staticArguments) != statics ||
        actual.scopedArguments.size() != selected.size() ||
        !actual.scopedInputs.empty() || !actual.domainInputs.empty() ||
        !actual.parameters.empty())
      return refuse(actual.span, "static substitution differs");
    for (unsigned i = 0; i < selected.size(); ++i)
      if (actual.scopedArguments[i].index != selected[i].index)
        return refuse(actual.span);
    if (!computation) {
      if (!actual.origin || actual.origin->index != original.id.index ||
          actual.scopedOrigin || actual.kind != original.kind ||
          bool(actual.parent) != bool(original.parent) ||
          (actual.parent && actual.parent->index != original.parent->index))
        return refuse(actual.span, "declaration origin differs");
    } else if (!actual.scopedOrigin ||
               actual.scopedOrigin->first.index !=
                   computation->lexicalOwner.index ||
               actual.scopedOrigin->second != computation->expression ||
               actual.kind !=
                   (computation->signature.mode == ScopedSignature::Mode::Math
                        ? Declaration::Kind::Math
                        : Declaration::Kind::Local) ||
               !actual.anonymous || actual.isPublic || !actual.parent ||
               actual.parent->index != computation->lexicalOwner.index ||
               !actual.specifications.empty())
      return refuse(actual.span);
    // Every edge must justify nontrivial aliases before the instance cache.
    // Protocol applications, maps, relation subjects and roots currently have
    // no alias witness and therefore retain independent authored inputs.
    if (!checkedAliases) {
      if (!actual.closureLayout.captures.empty() ||
          !actual.domainArguments.empty())
        return refuse(actual.span, "unwitnessed hidden input mapping");
      for (unsigned i = 0; i < actual.closureLayout.inputs.size(); ++i)
        if (actual.closureLayout.inputs[i] != i)
          return refuse(actual.span, "unwitnessed authored input alias");
    }
    if (checked.count(id.index))
      return true;
    if (!active.insert(id.index).second)
      return refuse(actual.span, "recursive specialization witness");
    auto subst = substitution(original, statics);
    if (!computation && !construction(original, actual, subst, depth))
      return false;
    if (!computation) {
      if (actual.specifications.size() != original.specifications.size() ||
          actual.roles != original.roles ||
          actual.completes != original.completes)
        return refuse(actual.span);
      auto selector = [](const SpecificationSelector &a,
                         const SpecificationSelector &b) {
        return a.output == b.output && a.port == b.port && a.role == b.role &&
               a.path == b.path;
      };
      auto subject = [&](const RelationApplication &a,
                         const RelationApplication &b) {
        auto args = arguments(a.arguments, subst, a.span);
        if (!args || *args != b.arguments ||
            a.operands.size() != b.operands.size())
          return false;
        for (unsigned i = 0; i < a.operands.size(); ++i)
          if (!selector(a.operands[i], b.operands[i]))
            return false;
        return instance(b.relation, source[a.relation.index], nullptr, *args,
                        {}, 1);
      };
      for (unsigned i = 0; i < original.specifications.size(); ++i) {
        const auto &a = original.specifications[i];
        const auto &b = actual.specifications[i];
        if (a.kind != b.kind || a.name != b.name ||
            bool(a.residual) != bool(b.residual) ||
            bool(a.decision) != bool(b.decision) ||
            (a.decision && !selector(*a.decision, *b.decision)) ||
            !subject(a.subject, b.subject) ||
            (a.residual && !subject(*a.residual, *b.residual)))
          return refuse(actual.span, "specification closure differs");
      }
    }
    const auto *templateBody =
        computation ? computation->body.get() : original.body.get();
    if (actual.body && (actual.body->inputs != actual.inputs.size() ||
                        actual.body->values.size() < actual.inputs.size()))
      return refuse(actual.span, "closed body input coverage differs");
    if (bool(templateBody) != bool(actual.body))
      return refuse(actual.span);
    std::vector<Type> inputs, outputs;
    std::vector<ScopedSignature> signatures;
    std::vector<Type> domainItems;
    if (computation) {
      for (unsigned i = 0; i < templateBody->inputs; ++i)
        inputs.push_back(templateBody->values[i].type);
      outputs.push_back(computation->signature.result);
      for (const auto &binding : templateBody->scopedBindings)
        if (binding.parameter)
          signatures.push_back(binding.signature);
      for (const auto &binding : templateBody->domainBindings)
        if (binding.parameter)
          domainItems.push_back(binding.item);
      if (!actual.effectAllowance ||
          !(*actual.effectAllowance ==
            EffectSummary{computation->signature.allowance}))
        return refuse(actual.span);
    } else {
      for (const auto &port : original.inputs)
        inputs.push_back(port.type);
      for (const auto &port : original.outputs)
        outputs.push_back(port.type);
      for (const auto &parameter : original.scopedInputs)
        signatures.push_back(parameter.signature);
      for (const auto &parameter : original.domainInputs)
        domainItems.push_back(parameter.item);
      std::optional<EffectSummary> expectedAllowance;
      if (original.effectAllowance) {
        std::vector<EffectSummary> effects;
        for (auto callback : selected) {
          if (!types.charge(1, actual.span) ||
              callback.index >= candidate.size() ||
              !candidate[callback.index].body)
            return refuse(actual.span);
          if (!types.charge(
                  candidate[callback.index].body->effects.dependencies.size() +
                      1,
                  actual.span))
            return false;
          effects.push_back(candidate[callback.index].body->effects);
        }
        expectedAllowance = substituteEffects(types, *original.effectAllowance,
                                              effects, actual.span);
        if (!expectedAllowance)
          return false;
      }
      if (actual.effectAllowance != expectedAllowance)
        return refuse(actual.span);
    }
    if (signatures.size() != selected.size() ||
        domainItems.size() != actual.domainArguments.size() ||
        actual.outputs.size() != outputs.size() ||
        actual.inputs.size() < inputs.size())
      return refuse(actual.span);
    for (unsigned i = 0; i < inputs.size(); ++i)
      if (!typeEqual(inputs[i], actual.inputs[i].type, subst, actual.span))
        return false;
    for (unsigned i = 0; i < outputs.size(); ++i)
      if (!typeEqual(outputs[i], actual.outputs[i].type, subst, actual.span))
        return false;
    if (!computation) {
      for (unsigned i = 0; i < inputs.size(); ++i)
        if (actual.inputs[i].roles != original.inputs[i].roles)
          return refuse(actual.span);
      for (unsigned i = 0; i < outputs.size(); ++i)
        if (actual.outputs[i].roles != original.outputs[i].roles)
          return refuse(actual.span);
    }
    const auto &layout = actual.closureLayout;
    if (layout.inputs.size() != inputs.size())
      return refuse(actual.span, "authored closure input count differs");
    for (unsigned i = 0; i < inputs.size(); ++i)
      if (layout.inputs[i] > i ||
          layout.inputs[layout.inputs[i]] != layout.inputs[i] ||
          actual.inputs[i].type != actual.inputs[layout.inputs[i]].type)
        return refuse(actual.span, "invalid authored closure aliases");
    unsigned offset = 0;
    unsigned ports = inputs.size();
    std::vector<Environment> environment;
    for (unsigned i = 0; i < selected.size(); ++i) {
      if (selected[i].index >= candidate.size())
        return refuse(actual.span);
      const auto &helper = candidate[selected[i].index];
      if (!helper.body || helper.inputs.size() < signatures[i].inputs.size() ||
          helper.outputs.size() != 1 ||
          helper.kind != (signatures[i].mode == ScopedSignature::Mode::Math
                              ? Declaration::Kind::Math
                              : Declaration::Kind::Local) ||
          (helper.body->effects.fixed.mayStop &&
           !signatures[i].allowance.mayStop) ||
          (helper.body->effects.fixed.opaque &&
           !signatures[i].allowance.opaque))
        return refuse(actual.span);
      for (unsigned j = 0; j < signatures[i].inputs.size(); ++j)
        if (!typeEqual(signatures[i].inputs[j], helper.inputs[j].type, subst,
                       actual.span))
          return false;
      if (!typeEqual(signatures[i].result, helper.outputs.front().type, subst,
                     actual.span))
        return false;
      Environment binding{selected[i], {}};
      for (unsigned j = signatures[i].inputs.size(); j < helper.inputs.size();
           ++j) {
        if (offset >= layout.captures.size())
          return refuse(actual.span, "missing hidden input mapping");
        auto port = layout.captures[offset++];
        if (port >= actual.inputs.size() || port > ports ||
            actual.inputs[port].type != helper.inputs[j].type || !actual.body ||
            actual.body->values[port].type != helper.inputs[j].type)
          return refuse(actual.span, "hidden input mapping differs");
        if (port == ports)
          ++ports;
        binding.captures.push_back({port});
      }
      environment.push_back(std::move(binding));
    }
    std::vector<DomainEnvironment> domains;
    for (unsigned i = 0; i < actual.domainArguments.size(); ++i) {
      const auto &shape = actual.domainArguments[i];
      if (!shape || shape->result >= shape->nodes.size() ||
          !typeEqual(domainItems[i], shape->nodes[shape->result].item, subst,
                     actual.span))
        return refuse(actual.span, "domain item mapping differs");
      DomainEnvironment domain{shape, {}};
      for (const auto &type : shape->inputs) {
        if (offset >= layout.captures.size())
          return refuse(actual.span, "missing domain input mapping");
        auto port = layout.captures[offset++];
        if (port >= actual.inputs.size() || port > ports ||
            actual.inputs[port].type != type || !actual.body ||
            actual.body->values[port].type != type)
          return refuse(actual.span, "domain input mapping differs");
        if (port == ports)
          ++ports;
        domain.operands.push_back({port});
      }
      domains.push_back(std::move(domain));
    }
    if (offset != layout.captures.size() || ports != actual.inputs.size() ||
        (templateBody && !body(*templateBody, *actual.body, subst, environment,
                               domains, depth, &layout)))
      return refuse(actual.span);
    if (actual.body) {
      if (actual.effectAllowance &&
          !effectsWithin(types, actual.body->effects, *actual.effectAllowance,
                         actual.span))
        return refuse(actual.span, "closed body exceeds its effect contract");
      auto assumptions = mapDataPreconditions(
          types,
          computation ? ArrayRef<DataPrecondition>{}
                      : ArrayRef(original.dataPreconditions),
          layout.inputs);
      if (!assumptions)
        return false;
      Declaration expected = actual;
      expected.dataPreconditions = std::move(*assumptions);
      auto requirements = deriveDataPreconditions(
          types, candidate, expected, *actual.body,
          computation || !original.scopedInputs.empty() ||
              !original.domainInputs.empty());
      if (!requirements || *requirements != actual.dataPreconditions)
        return types.diagnostic
                   ? false
                   : refuse(actual.span, "closed data preconditions differ");
    }
    active.erase(id.index);
    checked.insert(id.index);
    return true;
  }

public:
  SpecializationCheck(const ClosedEntry &entry, Work &work)
      : entry(entry), source(entry.project().declarations()),
        candidate(entry.declarations()),
        typeDeclarations(source.begin(), source.end()), work(work),
        types(typeDeclarations, entry.project().assets(), work) {}
  Error run() {
    const auto &authored = source[entry.entry().id.index];
    if (!authored.target)
      return failure("source.scoped-specialization",
                     "entry has no source target", authored.span);
    const auto &rootLayout = entry.protocol().closureLayout;
    if (!rootLayout.captures.empty() ||
        rootLayout.inputs.size() !=
            source[authored.target->index].inputs.size())
      return failure("source.scoped-specialization",
                     "entry input layout differs", authored.span);
    for (unsigned i = 0; i < rootLayout.inputs.size(); ++i)
      if (rootLayout.inputs[i] != i)
        return failure("source.scoped-specialization",
                       "entry asserts an input alias", authored.span);
    if (!instance(entry.protocol().id, source[authored.target->index], nullptr,
                  authored.staticArguments, {}, 1))
      return types.takeError();
    const auto *proof = authored.proof();
    const auto *closedProof = entry.entry().proof();
    if (proof && proof->selectedConstruction) {
      if (!closedProof || !closedProof->selectedConstruction ||
          proof->selectedConstruction->index >= source.size() ||
          !instance(*closedProof->selectedConstruction,
                    source[proof->selectedConstruction->index], nullptr,
                    proof->constructionArguments, {}, 1))
        return types.diagnostic
                   ? types.takeError()
                   : failure("source.scoped-specialization",
                             "selected construction differs", authored.span);
    }
    for (const auto &declaration : candidate)
      if (declaration.body && !checked.count(declaration.id.index))
        return failure("source.scoped-specialization",
                       "unaccounted closed body", declaration.span);
    return Error::success();
  }
};
} // namespace
} // namespace zkc::language::detail
namespace zkc::language {
llvm::Error checkScopedSpecialization(const ClosedEntry &entry,
                                      const Limits &limits) {
  if (auto error = checkLimits(limits))
    return error;
  detail::Work work{limits};
  return detail::SpecializationCheck(entry, work).run();
}
} // namespace zkc::language
