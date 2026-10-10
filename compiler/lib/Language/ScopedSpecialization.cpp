#include "BodySummary.h"
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
  binding(const Body &body, unsigned index, DeclarationId selected,
          const Substitution &subst, ArrayRef<Environment> environment,
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
        actual.scopedArguments.size() != binding.scopedCaptures.size()) {
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
    for (auto capture : binding.captures)
      result.captures.push_back(map(capture));
    for (unsigned i = 0; i < binding.scopedCaptures.size(); ++i) {
      auto captured = this->binding(body, binding.scopedCaptures[i],
                                    actual.scopedArguments[i], subst,
                                    environment, map, depth + 1);
      if (!captured)
        return {};
      result.captures.insert(result.captures.end(), captured->captures.begin(),
                             captured->captures.end());
    }
    if (!instance(selected, source[computation.lexicalOwner.index],
                  &computation, statics, actual.scopedArguments, depth + 1))
      return {};
    return result;
  }
  bool body(const Body &original, const Body &actual, const Substitution &subst,
            ArrayRef<Environment> environment, unsigned depth) {
    if (depth > work.limits.callDepth)
      return types.fail("source.limit", "specialization witness depth exceeded",
                        {});
    if (!types.charge(original.values.size() + original.operations.size() + 1,
                      {}))
      return false;
    unsigned hidden = 0;
    for (const auto &selected : environment)
      hidden += selected.captures.size();
    auto map = [&](ValueId value) {
      return ValueId{value.index < original.inputs ? value.index
                                                   : value.index + hidden};
    };
    auto mapped = [&](ArrayRef<ValueId> values) {
      std::vector<ValueId> result;
      for (auto value : values)
        result.push_back(map(value));
      return result;
    };
    if (actual.mode != original.mode ||
        actual.inputs != original.inputs + hidden ||
        actual.values.size() != original.values.size() + hidden ||
        actual.operations.size() != original.operations.size() ||
        actual.stopped != original.stopped ||
        actual.stopReason != original.stopReason ||
        actual.mayStop != original.mayStop ||
        actual.opaque != original.opaque || !actual.scopedBindings.empty() ||
        !same(actual.results, mapped(original.results)))
      return refuse({});
    for (unsigned i = 0; i < original.values.size(); ++i) {
      const auto &expected = original.values[i];
      const auto &value = actual.values[map({i}).index];
      if (!typeEqual(expected.type, value.type, subst, expected.span) ||
          !same(expected.span, value.span) ||
          (actual.mode == Body::Mode::Protocol &&
           expected.components != value.components) ||
          (actual.mode == Body::Mode::Local && !value.components.empty()))
        return refuse(expected.span);
    }
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
            !call->scopedArguments.empty())
          return refuse(op.span);
        auto selected = binding(original, invoke->binding, call->callee, subst,
                                environment, map, depth + 1);
        if (!selected)
          return false;
        auto operands = mapped(invoke->operands);
        operands.insert(operands.end(), selected->captures.begin(),
                        selected->captures.end());
        if (!same(call->operands, operands))
          return refuse(op.span, "invocation environment mapping differs");
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
                    !value.scopedArguments.empty())
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
              if constexpr (std::is_same_v<T, HelperCall>) {
                if (action.scopedArguments.size() !=
                    callee.scopedArguments.size())
                  return false;
                for (unsigned j = 0; j < action.scopedArguments.size(); ++j) {
                  auto scoped = binding(original, action.scopedArguments[j],
                                        callee.scopedArguments[j], subst,
                                        environment, map, depth + 1);
                  if (!scoped)
                    return false;
                  selected.push_back(scoped->helper);
                  operands.insert(operands.end(), scoped->captures.begin(),
                                  scoped->captures.end());
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
                              *statics, selected, depth + 1);
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
                  action.regions.size() != value.regions.size())
                return false;
              auto operands = mapped(action.operands);
              for (const auto &selected : environment)
                operands.insert(operands.end(), selected.captures.begin(),
                                selected.captures.end());
              if (!same(value.operands, operands))
                return false;
              for (unsigned j = 0; j < action.regions.size(); ++j) {
                auto nested = std::vector<Environment>(environment.begin(),
                                                       environment.end());
                unsigned next = action.regions[j]->inputs;
                for (auto &selected : nested)
                  for (auto &capture : selected.captures)
                    capture = {next++};
                if (!body(*action.regions[j], *value.regions[j], subst, nested,
                          depth + 1))
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
              return body(*action.region, *value.region, subst, {}, depth + 1);
            } else
              return false;
          },
          op.action);
      if (!valid)
        return types.diagnostic ? false : refuse(op.span);
    }
    return true;
  }
  bool instance(DeclarationId id, const Declaration &original,
                const ScopedComputation *computation, ArrayRef<Type> statics,
                ArrayRef<DeclarationId> selected, unsigned depth) {
    if (id.index >= candidate.size() || depth > work.limits.callDepth)
      return refuse(original.span, "invalid specialization edge");
    const auto &actual = candidate[id.index];
    if (!types.charge(1, actual.span))
      return false;
    if (ArrayRef<Type>(actual.staticArguments) != statics ||
        actual.scopedArguments.size() != selected.size() ||
        !actual.scopedInputs.empty() || !actual.parameters.empty())
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
    if (checked.count(id.index))
      return true;
    if (!active.insert(id.index).second)
      return refuse(actual.span, "recursive specialization witness");
    auto subst = substitution(original, statics);
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
    if (bool(templateBody) != bool(actual.body))
      return refuse(actual.span);
    std::vector<Type> inputs, outputs;
    std::vector<ScopedSignature> signatures;
    if (computation) {
      for (unsigned i = 0; i < templateBody->inputs; ++i)
        inputs.push_back(templateBody->values[i].type);
      outputs.push_back(computation->signature.result);
      for (const auto &binding : templateBody->scopedBindings)
        if (binding.parameter)
          signatures.push_back(binding.signature);
      if (!actual.effectAllowance ||
          !(*actual.effectAllowance == computation->signature.allowance))
        return refuse(actual.span);
    } else {
      for (const auto &port : original.inputs)
        inputs.push_back(port.type);
      for (const auto &port : original.outputs)
        outputs.push_back(port.type);
      for (const auto &parameter : original.scopedInputs)
        signatures.push_back(parameter.signature);
      if (actual.effectAllowance != original.effectAllowance)
        return refuse(actual.span);
    }
    if (signatures.size() != selected.size() ||
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
    unsigned offset = inputs.size();
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
          (helper.body->mayStop && !signatures[i].allowance.mayStop) ||
          (helper.body->opaque && !signatures[i].allowance.opaque))
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
        if (offset >= actual.inputs.size() ||
            actual.inputs[offset].type != helper.inputs[j].type ||
            !actual.body ||
            actual.body->values[offset].type != helper.inputs[j].type)
          return refuse(actual.span, "hidden input mapping differs");
        binding.captures.push_back({offset++});
      }
      environment.push_back(std::move(binding));
    }
    if (offset != actual.inputs.size() ||
        (templateBody &&
         !body(*templateBody, *actual.body, subst, environment, depth)))
      return refuse(actual.span);
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
    if (!authored.target ||
        !instance(entry.protocol().id, source[authored.target->index], nullptr,
                  authored.staticArguments, {}, 1))
      return types.takeError();
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
